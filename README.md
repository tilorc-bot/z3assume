# z3assume

A prototype rewrite of [satassume](https://github.com/tilorc-bot/satassume)
(a rewrite of SymPy's new assumption system) on the
[z3](https://github.com/Z3Prover/z3) SMT solver. Where satassume has its own
SAT solver, rule base and theories, z3assume translates the query into one
z3 problem and lets z3 decide it. Its only runtime dependencies are SymPy
(the input language) and `z3-solver`.

It is written by AI sessions (Claude) for Tilo, a SymPy maintainer. It is a
prototype: expect gaps and changes.

```python
from sympy import Q, symbols
from z3assume import ask

x, y = symbols("x y")
ask(Q.even(x*y), Q.even(x) & Q.integer(y))      # True
ask(Q.positive(x**2 + 1), Q.real(x))             # True
```

`ask(P, A)` is `True` when z3 shows that `A & ~P` has no model, `False`
when `A & P` has none, and `None` otherwise; inconsistent assumptions raise
`ValueError`. See [docs/design.md](docs/design.md) for the encoding.

## Development

```bash
uv sync
uv run pytest -q
uv run ruff check
```
