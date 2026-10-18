# datalog

A small, correct Datalog engine in pure Python (standard library only). It parses programs, checks rule safety, stratifies negation, and evaluates bottom-up with **semi-naive evaluation** over hash-indexed relations. A deliberately simple **naive evaluator** is included as a test oracle.

## Why

Datalog is the declarative core behind program analysis (Soufflé, Doop), security policy engines, and graph queries. Recursive queries like transitive closure are one-liners, but evaluating them efficiently takes real machinery. This project implements that machinery in about 500 readable lines.

## What it does

- Facts, rules, and `?-` queries; `%` comments; strings, integers, atoms, `_` anonymous variables.
- Comparison builtins: `=`, `!=`, `<`, `<=`, `>`, `>=` (`=` can bind a variable).
- Stratified negation with `not`. Strata come from Tarjan SCCs on the predicate dependency graph; a negation inside a recursive cycle is rejected with a clear error.
- Safety checking: every head variable and every variable under `not` or a comparison must be bound by a positive literal.
- Semi-naive evaluation: each round joins only against the newly derived "delta" tuples for one recursive literal at a time, instead of recomputing everything.
- Per-relation hash indexes built lazily on whichever columns are bound at join time, plus greedy literal scheduling.

## Run

```
python datalog.py examples/graph.dl --stats
python datalog.py examples/graph.dl --naive --stats   # compare work done
python datalog.py examples/graph.dl --dump            # print every derived fact
```

As a library:

```python
from datalog import Engine
e = Engine("edge(1,2). edge(2,3). path(X,Y) :- edge(X,Y). path(X,Y) :- path(X,Z), edge(Z,Y).")
print(e.query("path(1, X)"))   # (['X'], [(2,), (3,)])
```

## Tests

```
python -m unittest discover -s tests
```

The tests cover parsing errors, safety, stratification order, unstratifiable programs, mutual recursion, repeated variables, and builtins. The key test generates 40 random graph programs (recursion plus negation) and asserts the semi-naive and naive evaluators derive identical relations. Another asserts semi-naive does strictly fewer derivations on a 40-node chain.

## Design notes

- Negated literals are only checked once all their variables are bound, so the scheduler delays them; this is why safety is enforced up front.
- Delta relations are rebuilt each round and the join swaps the delta in for exactly one body literal, which keeps results duplicate-free in the set semantics used here.
- Out of scope: aggregation, function symbols, and magic-set rewriting. They are natural next steps.
