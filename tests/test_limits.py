"""Answers near the rlimit (decisions 11 and 12, #29, #31): two wester
cases that #26's sum axiom moved across the limit of 1,000,000 steps, and
the fallback."""
import pytest
from sympy import Q, Rational, Symbol, sign

from z3assume import ask

x, y, k, n = (Symbol(s) for s in "xykn")      # plain symbols, as the bench sends them


def test_n2b_power_below_identity():
    # x**4 <= x on [0, 1], so sign(x**4 - x) is 0 or -1
    assert ask(Q.zero(sign(x**4 - x) - 1), Q.real(x) & Q.ge(x, 0) & Q.le(x, 1)) is False


@pytest.mark.xfail(strict=True, reason="needs 1,130,000 steps; the rlimit is 1,000,000 again (#31)")
def test_n6_power_increasing():
    # t -> t**n increases on (0, oo) for n > 0
    a = (Q.real(x) & Q.real(y) & Q.real(k) & Q.real(n) & Q.gt(x, y) & Q.gt(y, Rational(1, 10))
         & Q.lt(x, 10) & Q.gt(k, 0) & Q.gt(n, 0) & Q.lt(n, 10))
    assert ask(Q.zero(sign(k * x**n - k * y**n) - 1), a) is True

