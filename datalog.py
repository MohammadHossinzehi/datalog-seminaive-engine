"""datalog: a small, correct Datalog engine.

Features: parser, safety checking, stratified negation (Tarjan SCC),
semi-naive bottom-up evaluation with per-relation hash indexes, a naive
oracle evaluator, comparison builtins, and queries.
"""
import re
import sys
from collections import defaultdict


class DatalogError(Exception):
    pass


class Var:
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, o):
        return isinstance(o, Var) and o.name == self.name

    def __hash__(self):
        return hash(("v", self.name))


class Atom:
    """pred(args); neg=True for negated literals; builtin preds: = != < <= > >=."""
    __slots__ = ("pred", "args", "neg")

    def __init__(self, pred, args, neg=False):
        self.pred, self.args, self.neg = pred, tuple(args), neg

    def vars(self):
        return {a for a in self.args if isinstance(a, Var)}

    def __repr__(self):
        if self.pred in BUILTINS:
            s = f"{self.args[0]} {self.pred} {self.args[1]}"
        else:
            s = f"{self.pred}({', '.join(map(str, self.args))})"
        return ("not " + s) if self.neg else s


BUILTINS = {"=", "!=", "<", "<=", ">", ">="}


class Rule:
    def __init__(self, head, body):
        self.head, self.body = head, body

    def __repr__(self):
        if not self.body:
            return f"{self.head}."
        return f"{self.head} :- {', '.join(map(repr, self.body))}."


TOKEN = re.compile(r'\s*(?:(%[^\n]*)|(:-|!=|<=|>=|\?-)|("[^"]*")|(-?\d+)|([A-Za-z_][A-Za-z0-9_]*)|([(),.=<>]))')


def tokenize(src):
    pos, out = 0, []
    while pos < len(src):
        if not src[pos:].strip():
            break
        m = TOKEN.match(src, pos)
        if not m:
            raise DatalogError(f"bad input near {src[pos:pos+20]!r}")
        pos = m.end()
        if m.group(1):
            continue
        if m.group(2):
            out.append(("op", m.group(2)))
        elif m.group(3):
            out.append(("const", m.group(3)[1:-1]))
        elif m.group(4):
            out.append(("const", int(m.group(4))))
        elif m.group(5):
            w = m.group(5)
            out.append(("var" if (w[0].isupper() or w[0] == "_") else "id", w))
        else:
            out.append(("op", m.group(6)))
    return out


class Parser:
    def __init__(self, src):
        self.t = tokenize(src)
        self.i = 0
        self.anon = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def eat(self, val=None):
        if self.i >= len(self.t):
            raise DatalogError("unexpected end of input")
        tok = self.t[self.i]
        if val is not None and tok[1] != val:
            raise DatalogError(f"expected {val!r}, got {tok[1]!r}")
        self.i += 1
        return tok

    def term(self):
        k, v = self.eat()
        if k == "var":
            if v == "_":
                self.anon += 1
                return Var(f"_G{self.anon}")
            return Var(v)
        if k in ("const", "id"):
            return v
        raise DatalogError(f"unexpected token {v!r}")

    def literal(self):
        neg = False
        if self.peek() == ("id", "not"):
            self.eat()
            neg = True
        k, v = self.peek()
        if k == "id" and self.t[self.i + 1:self.i + 2] == [("op", "(")]:
            self.eat()
            self.eat("(")
            args = []
            if self.peek() != ("op", ")"):
                args.append(self.term())
                while self.peek() == ("op", ","):
                    self.eat()
                    args.append(self.term())
            self.eat(")")
            return Atom(v, args, neg)
        left = self.term()
        _, op = self.eat()
        if op not in BUILTINS:
            raise DatalogError(f"expected comparison, got {op!r}")
        return Atom(op, [left, self.term()], neg)

    def program(self):
        rules, queries = [], []
        while self.i < len(self.t):
            if self.peek() == ("op", "?-"):
                self.eat()
                body = [self.literal()]
                while self.peek() == ("op", ","):
                    self.eat()
                    body.append(self.literal())
                self.eat(".")
                queries.append(body)
                continue
            head = self.literal()
            body = []
            if self.peek() == ("op", ":-"):
                self.eat()
                body.append(self.literal())
                while self.peek() == ("op", ","):
                    self.eat()
                    body.append(self.literal())
            self.eat(".")
            rules.append(Rule(head, body))
        return rules, queries


def parse(src):
    return Parser(src).program()


def check_safety(rule):
    """Every head var and every var in a negated/builtin literal must be bound
    by a positive non-builtin body literal (with '=' able to propagate)."""
    if rule.head.neg or rule.head.pred in BUILTINS:
        raise DatalogError(f"illegal head: {rule}")
    bound = set()
    for a in rule.body:
        if not a.neg and a.pred not in BUILTINS:
            bound |= a.vars()
    changed = True
    while changed:
        changed = False
        for a in rule.body:
            if a.pred == "=" and not a.neg:
                l, r = a.args
                lv = not isinstance(l, Var) or l in bound
                rv = not isinstance(r, Var) or r in bound
                for x, ok in ((l, rv), (r, lv)):
                    if ok and isinstance(x, Var) and x not in bound:
                        bound.add(x)
                        changed = True
    need = set(rule.head.vars())
    for a in rule.body:
        if a.neg or a.pred in BUILTINS:
            need |= a.vars()
    missing = need - bound
    if missing:
        raise DatalogError(f"unsafe rule {rule}: unbound {sorted(v.name for v in missing)}")


def stratify(rules):
    """Return list of strata (lists of rules). Raises if negation is in a cycle."""
    heads = {r.head.pred for r in rules}
    edges = defaultdict(set)  # head -> {(dep, negated)}
    for r in rules:
        for a in r.body:
            if a.pred in heads:
                edges[r.head.pred].add((a.pred, a.neg))
    # Tarjan SCC
    index, low, onstack, stack, comp, n = {}, {}, set(), [], {}, [0]
    sys.setrecursionlimit(10000)

    def strong(v):
        index[v] = low[v] = n[0]
        n[0] += 1
        stack.append(v)
        onstack.add(v)
        for w, _ in edges[v]:
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            while True:
                w = stack.pop()
                onstack.discard(w)
                comp[w] = v
                if w == v:
                    break

    for h in sorted(heads):
        if h not in index:
            strong(h)
    for h in heads:
        for w, neg in edges[h]:
            if neg and comp[h] == comp[w]:
                raise DatalogError(f"not stratifiable: negation cycle through {h!r} and {w!r}")
    # longest-path layering over the SCC DAG
    level = {}

    def lv(c):
        if c in level:
            return level[c]
        level[c] = 0
        best = 0
        for h in heads:
            if comp[h] != c:
                continue
            for w, neg in edges[h]:
                if comp[w] != c:
                    best = max(best, lv(comp[w]) + (1 if neg else 0))
        level[c] = best
        return best

    for h in heads:
        lv(comp[h])
    strata = defaultdict(list)
    for r in rules:
        strata[level[comp[r.head.pred]]].append(r)
    return [strata[k] for k in sorted(strata)]


class Relation:
    """Set of tuples with lazily built hash indexes keyed by bound column sets."""

    def __init__(self):
        self.rows = set()
        self.idx = {}

    def add(self, t):
        if t in self.rows:
            return False
        self.rows.add(t)
        for cols, d in self.idx.items():
            d[tuple(t[c] for c in cols)].append(t)
        return True

    def lookup(self, cols, key):
        if not cols:
            return self.rows
        d = self.idx.get(cols)
        if d is None:
            d = defaultdict(list)
            for t in self.rows:
                d[tuple(t[c] for c in cols)].append(t)
            self.idx[cols] = d
        return d.get(key, ())


def _cmp(op, a, b):
    if op == "=":
        return a == b
    if op == "!=":
        return a != b
    try:
        return {"<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[op]
    except TypeError:
        raise DatalogError(f"cannot compare {a!r} {op} {b!r}")


def _val(x, env):
    return env[x] if isinstance(x, Var) else x


def _join(body, rels, env, delta_pos=None, delta=None):
    """Yield environments satisfying body. Literal at delta_pos reads from `delta`.
    Literals are scheduled greedily: positives first, then ones whose vars are bound."""
    order = _schedule(body, set(env))
    yield from _go(order, 0, rels, env, delta_pos, delta)


def _schedule(body, bound):
    pending = list(enumerate(body))
    out = []
    bound = set(bound)
    while pending:
        pick = None
        for item in pending:
            _, a = item
            if a.pred in BUILTINS or a.neg:
                if a.pred == "=" and not a.neg:
                    if any(not isinstance(x, Var) or x in bound for x in a.args):
                        pick = item
                        break
                elif a.vars() <= bound:
                    pick = item
                    break
            else:
                pick = item if pick is None else pick
        if pick is None:
            raise DatalogError("cannot schedule body (unsafe)")
        # prefer a positive literal sharing bound vars
        pos = [it for it in pending if not it[1].neg and it[1].pred not in BUILTINS]
        if pick[1].pred not in BUILTINS and not pick[1].neg and pos:
            pick = max(pos, key=lambda it: len(it[1].vars() & bound))
        pending.remove(pick)
        out.append(pick)
        if not pick[1].neg:
            bound |= pick[1].vars()
    return out


def _go(order, k, rels, env, dpos, delta):
    if k == len(order):
        yield env
        return
    pos, a = order[k]
    if a.pred in BUILTINS:
        l, r = a.args
        if a.pred == "=" and not a.neg:
            lb = not isinstance(l, Var) or l in env
            rb = not isinstance(r, Var) or r in env
            if lb and rb:
                if _val(l, env) == _val(r, env):
                    yield from _go(order, k + 1, rels, env, dpos, delta)
            elif lb:
                e = dict(env); e[r] = _val(l, env)
                yield from _go(order, k + 1, rels, e, dpos, delta)
            else:
                e = dict(env); e[l] = _val(r, env)
                yield from _go(order, k + 1, rels, e, dpos, delta)
            return
        ok = _cmp(a.pred, _val(l, env), _val(r, env))
        if ok != a.neg:
            yield from _go(order, k + 1, rels, env, dpos, delta)
        return
    rel = delta if (pos == dpos) else rels.get(a.pred)
    if a.neg:
        t = tuple(_val(x, env) for x in a.args)
        if rel is None or t not in rel.rows:
            yield from _go(order, k + 1, rels, env, dpos, delta)
        return
    if rel is None:
        return
    cols, key = [], []
    for i, x in enumerate(a.args):
        if not isinstance(x, Var) or x in env:
            cols.append(i)
            key.append(_val(x, env))
    for t in rel.lookup(tuple(cols), tuple(key)):
        e = env
        copied = False
        ok = True
        for i, x in enumerate(a.args):
            if isinstance(x, Var) and x not in env:
                if x in e and copied:
                    if e[x] != t[i]:
                        ok = False
                        break
                else:
                    if not copied:
                        e = dict(env)
                        copied = True
                    e[x] = t[i]
        if ok:
            yield from _go(order, k + 1, rels, e, dpos, delta)


def _head_tuple(rule, env):
    return tuple(_val(x, env) for x in rule.head.args)


class Engine:
    def __init__(self, src=""):
        self.rules, self.queries = [], []
        self.stats = {"iterations": 0, "derivations": 0}
        if src:
            self.load(src)

    def load(self, src):
        rules, queries = parse(src)
        for r in rules:
            check_safety(r)
        self.rules += rules
        self.queries += queries

    def _edb(self):
        rels = defaultdict(Relation)
        for r in self.rules:
            if not r.body:
                if r.head.vars():
                    raise DatalogError(f"fact with variables: {r}")
                rels[r.head.pred].add(tuple(r.head.args))
        return rels

    def solve(self, seminaive=True):
        rels = self._edb()
        proper = [r for r in self.rules if r.body]
        self.stats = {"iterations": 0, "derivations": 0}
        for stratum in stratify(proper):
            (self._semi if seminaive else self._naive)(stratum, rels)
        return rels

    def _naive(self, rules, rels):
        while True:
            self.stats["iterations"] += 1
            new = []
            for r in rules:
                for env in _join(r.body, rels, {}):
                    new.append((r.head.pred, _head_tuple(r, env)))
                    self.stats["derivations"] += 1
            changed = False
            for p, t in new:
                changed |= rels[p].add(t)
            if not changed:
                return

    def _semi(self, rules, rels):
        stratum_preds = {r.head.pred for r in rules}
        delta = defaultdict(Relation)
        # round 0: evaluate every rule fully
        first = []
        for r in rules:
            for env in _join(r.body, rels, {}):
                self.stats["derivations"] += 1
                first.append((r.head.pred, _head_tuple(r, env)))
        for p, t in first:
            if rels[p].add(t):
                delta[p].add(t)
        self.stats["iterations"] += 1
        while any(d.rows for d in delta.values()):
            self.stats["iterations"] += 1
            new = defaultdict(set)
            for r in rules:
                for pos, a in enumerate(r.body):
                    if a.neg or a.pred in BUILTINS or a.pred not in stratum_preds:
                        continue
                    d = delta.get(a.pred)
                    if d is None or not d.rows:
                        continue
                    for env in _join(r.body, rels, {}, pos, d):
                        t = _head_tuple(r, env)
                        self.stats["derivations"] += 1
                        if t not in rels[r.head.pred].rows:
                            new[r.head.pred].add(t)
            delta = defaultdict(Relation)
            for p, ts in new.items():
                for t in ts:
                    if rels[p].add(t):
                        delta[p].add(t)

    def query(self, body, rels=None):
        if isinstance(body, str):
            _, qs = parse("?- " + body.rstrip(".") + ".")
            body = qs[0]
        rels = rels if rels is not None else self.solve()
        vs = []
        for a in body:
            for x in a.args:
                if isinstance(x, Var) and not x.name.startswith("_G") and x not in vs:
                    vs.append(x)
        out = set()
        for env in _join(body, rels, {}):
            out.add(tuple(env[v] for v in vs))
        return [v.name for v in vs], sorted(out, key=lambda t: tuple(map(str, t)))


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        print("usage: python datalog.py program.dl [--naive] [--stats] [--dump]")
        return 2
    eng = Engine(open(argv[0]).read())
    rels = eng.solve(seminaive="--naive" not in argv)
    for q in eng.queries:
        names, rows = eng.query(q, rels)
        print("?-", ", ".join(map(repr, q)))
        if not names:
            print("  true" if rows else "  false")
        for row in rows:
            print("  " + ", ".join(f"{n}={v}" for n, v in zip(names, row)))
        if names and not rows:
            print("  (no answers)")
    if "--dump" in argv:
        for p in sorted(rels):
            for t in sorted(rels[p].rows, key=lambda t: tuple(map(str, t))):
                print(f"{p}({', '.join(map(str, t))}).")
    if "--stats" in argv:
        print(eng.stats)
    return 0


if __name__ == "__main__":
    sys.exit(main())
