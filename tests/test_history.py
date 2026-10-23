"""An answer does not depend on the queries asked before it (#7): each
query has its own z3 context, so the same queries in another order give the
same answers and the same unknown checks."""
import sys

import z3
from sympy import Q, symbols

from z3assume import ask

A = sys.modules["z3assume.ask"]
a, b, c, x, y = symbols("a b c x y", real=True)
n = symbols("n", integer=True)
QUERIES = [
    (a * c <= b * c, (a <= b) & (c > 0)),
    (Q.positive(x * y), Q.positive(x) & Q.negative(y)),
    (Q.even(n**2 + n), True),
    (Q.zero(x**3 - y**3), Q.zero(x - y)),
    (Q.integer(x / 2), Q.odd(n) & Q.eq(x, n)),
    (Q.nonnegative(x**2 + y**2 - 2 * x * y), True),
]


def _run(order):
    out = {}
    for i in order:
        A._MEMO.clear()
        out[i] = (ask(*QUERIES[i]), A.last["unknown"])
    return out


def test_order_independent():
    fwd = _run(range(len(QUERIES)))
    assert fwd == _run(reversed(range(len(QUERIES))))
    assert fwd[0][0] is True


def test_own_context(monkeypatch):
    seen = []
    real = A.Encoder

    def spy(ctx=None):
        seen.append(ctx)
        return real(ctx)

    monkeypatch.setattr(A, "Encoder", spy)
    A._MEMO.clear()
    ask(Q.positive(x + 1), Q.positive(x))
    ask(Q.positive(x + 2), Q.positive(x))
    assert len(seen) == 2 and all(c is not None and c is not z3.main_ctx() for c in seen)
    assert seen[0] is not seen[1]
