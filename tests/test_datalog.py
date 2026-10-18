import os, random, sys, unittest
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from datalog import Engine, DatalogError, parse, stratify, check_safety

TC = """
path(X,Y) :- edge(X,Y).
path(X,Y) :- path(X,Z), edge(Z,Y).
"""

class T(unittest.TestCase):
    def test_transitive_closure(self):
        e = Engine("edge(1,2). edge(2,3). edge(3,1)." + TC)
        _, rows = e.query("path(1, X)")
        self.assertEqual(sorted(r[0] for r in rows), [1, 2, 3])

    def test_negation_stratified(self):
        e = Engine("n(1). n(2). n(3). e(1,2)." + "r(X) :- e(1,X). u(X) :- n(X), not r(X), X != 1.")
        self.assertEqual(e.query("u(X)")[1], [(3,)])

    def test_unstratifiable(self):
        e = Engine("p(X) :- q(X), not r(X). r(X) :- q(X), not p(X). q(1).")
        with self.assertRaises(DatalogError):
            e.solve()

    def test_unsafe(self):
        for src in ["p(X) :- q(Y).", "p(X) :- q(X), not r(Y).", "p(X) :- q(X), Y < 3."]:
            with self.assertRaises(DatalogError):
                Engine(src)

    def test_equality_binds(self):
        e = Engine("q(1). q(2). p(X,Y) :- q(X), Y = X.")
        self.assertEqual(len(e.query("p(X,Y)")[1]), 2)

    def test_builtin_compare(self):
        e = Engine("q(1). q(5). q(9). big(X) :- q(X), X >= 5.")
        self.assertEqual(e.query("big(X)")[1], [(5,), (9,)])

    def test_repeated_vars(self):
        e = Engine("e(1,1). e(1,2). loop(X) :- e(X,X).")
        self.assertEqual(e.query("loop(X)")[1], [(1,)])

    def test_semi_matches_naive_random(self):
        rng = random.Random(7)
        for _ in range(40):
            n = rng.randint(2, 9)
            facts = " ".join(f"edge({rng.randrange(n)},{rng.randrange(n)})." for _ in range(rng.randint(1, 20)))
            prog = facts + TC + """
                same(X,Y) :- path(X,Z), path(Y,Z), X != Y.
                node(X) :- edge(X,_). node(X) :- edge(_,X).
                iso(X) :- node(X), not path(X,X).
            """
            e = Engine(prog)
            a, b = e.solve(True), e.solve(False)
            for p in set(a) | set(b):
                self.assertEqual(a[p].rows, b[p].rows, p)

    def test_seminaive_does_less_work(self):
        chain = " ".join(f"edge({i},{i+1})." for i in range(40))
        e = Engine(chain + TC)
        e.solve(True); s = e.stats["derivations"]
        e.solve(False); n = e.stats["derivations"]
        self.assertLess(s, n)

    def test_mutual_recursion(self):
        e = Engine("""zero(0). even(X) :- zero(X). succ(0,1). succ(1,2). succ(2,3). succ(3,4).
        even(Y) :- odd(X), succ(X,Y). odd(Y) :- even(X), succ(X,Y).""")
        self.assertEqual([r[0] for r in e.query("even(X)")[1]], [0, 2, 4])

    def test_strata_order(self):
        rules, _ = parse("a(1). b(X) :- a(X). c(X) :- a(X), not b(X). d(X) :- a(X), not c(X).")
        st = stratify([r for r in rules if r.body])
        self.assertEqual(len(st), 3)

    def test_parse_errors(self):
        for src in ["p(", "p(X) :- .", "p(X) q."]:
            with self.assertRaises(DatalogError):
                Engine(src)

    def test_strings_comments_anon(self):
        e = Engine('% c\nname(1, "Al Bo"). has(X) :- name(X, _).')
        self.assertEqual(e.query("has(X)")[1], [(1,)])

if __name__ == "__main__":
    unittest.main()
