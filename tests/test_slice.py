"""The first slice: the eleven predicates on polynomial and rational
expressions.  Every expected answer has its argument next to it."""
import pytest
from sympy import Eq, Q, Rational, S, Symbol, nan, symbols, zoo

from z3assume import ask

x, y, z = symbols("x y z")

CASES = [
    # (proposition, assumptions, answer, why)
    (Q.real(x + y), Q.real(x) & Q.real(y), True, "R is closed under +"),
    (Q.real(x * y), Q.real(x) & Q.real(y), True, "R is closed under *"),
    (Q.real(x**2), Q.imaginary(x), True, "(b*I)**2 = -b**2"),
    (Q.negative(x**2), Q.imaginary(x), True, "(b*I)**2 = -b**2 < 0 for b != 0"),
    (Q.real(x), Q.imaginary(x), False, "imaginary values are not real"),
    (Q.real(1 / x), Q.real(x) & Q.nonzero(x), True, "1/x is real for real nonzero x"),
    (Q.real(1 / x), Q.zero(x), False, "1/0 = zoo is not real"),
    (Q.rational(x / y), Q.rational(x) & Q.rational(y) & Q.nonzero(y), True, "Q is a field"),
    (Q.rational(x + y), Q.rational(x) & Q.irrational(y), False, "y = (x + y) - x"),
    (Q.rational(x * y), Q.rational(x) & Q.nonzero(x) & Q.irrational(y), False, "y = (x*y)/x"),
    (Q.rational(x * y), Q.zero(x) & Q.irrational(y), True, "0*y = 0"),
    (Q.irrational(x + 1), Q.irrational(x), True, "x = (x + 1) - 1"),
    (Q.rational(x**2), Q.irrational(x), None, "sqrt(2)**2 = 2, pi**2 is irrational"),
    (Q.integer(x * y - x), Q.integer(x) & Q.integer(y), True, "Z is a ring"),
    (Q.integer(x / 2), Q.even(x), True, "x = 2*k"),
    (Q.integer(x / 2), Q.odd(x), False, "x = 2*k + 1"),
    (Q.integer(x + y), Q.integer(x) & Q.noninteger(y) & Q.real(y), False, "y = (x + y) - x"),
    (Q.integer(x), Q.rational(x), None, "1/2 and 1"),
    (Q.positive(x**2 + 1), Q.real(x), True, "x**2 >= 0"),
    (Q.positive(x**2), Q.real(x), None, "x = 0"),
    (Q.positive(x**2), Q.real(x) & Q.nonzero(x), True, "x**2 > 0"),
    (Q.nonnegative(x**2), Q.real(x), True, "x**2 >= 0"),
    (Q.nonpositive(-x**2), Q.real(x), True, "-x**2 <= 0"),
    (Q.positive(x * y), Q.negative(x) & Q.negative(y), True, "sign rule"),
    (Q.negative(x * y), Q.negative(x) & Q.positive(y), True, "sign rule"),
    (Q.positive(x + y), Q.positive(x) & Q.positive(y), True, "positive + positive"),
    (Q.positive(x - y), Q.positive(x) & Q.positive(y), None, "1 - 2, 2 - 1"),
    (Q.positive(x * y), Q.extended_positive(x) & Q.extended_positive(y), None, "oo*1 is not finite"),
    (Q.positive(x**3 - x), Q.integer(x) & Q.gt(x, 1), True, "x**3 - x = (x - 1)*x*(x + 1)"),
    (Q.nonzero(x**2 + x + 1), Q.real(x), True, "discriminant -3 < 0"),
    (Q.zero(x * y), Q.zero(x) & Q.finite(y), True, "0*y = 0 for finite y"),
    (Q.zero(x * y), Q.nonzero(x) & Q.nonzero(y), False, "no zero divisors"),
    (Q.zero(x * y), Q.zero(x), None, "0*oo = nan"),
    (Q.zero(x - y), Q.eq(x, y) & Q.finite(x), True, "x - x = 0"),
    (Q.zero(1 / x), Q.infinite(x), True, "1/oo = 0, 1/zoo = 0"),
    # x**2 = 2 has no rational root, but rationality is not arithmetic for z3
    (Q.nonzero(x**2 - 2), Q.rational(x), None, "known gap: no rational root theorem"),
    (Q.even(x * y), Q.even(x) & Q.integer(y), True, "2*k*y"),
    (Q.odd(x * y), Q.odd(x) & Q.odd(y), True, "(2a+1)(2b+1) = 2(2ab+a+b) + 1"),
    (Q.odd(x + 1), Q.even(x), True, "2k + 1"),
    (Q.even(x + y), Q.odd(x) & Q.odd(y), True, "2a + 1 + 2b + 1"),
    (Q.even(x**2), Q.even(x), True, "4k**2"),
    (Q.odd(x**2), Q.odd(x), True, "odd*odd"),
    (Q.even(x), Q.even(x**2) & Q.integer(x), True, "x odd would make x**2 odd"),
    (Q.even(x), Q.integer(x), None, "0 and 1"),
    (Q.odd(x), Q.rational(x) & ~Q.integer(x), False, "odd values are integers"),
    (Q.even(2 * x), Q.integer(x), True, "2*k"),
    (Q.finite(x + 1), Q.finite(x), True, "x is a number, not nan"),
    (Q.infinite(1 / x), Q.zero(x), True, "1/0 = zoo"),
    (Q.extended_real(x + y), Q.extended_real(x) & Q.extended_real(y), None, "oo - oo = nan"),
    (Q.positive(2), Q.positive(x) & Q.negative(x), True, "a constant is decided without the assumptions"),
    (Q.prime(7), True, True, "7 is prime"),
    (Q.composite(91), True, True, "91 = 7*13"),
    (Q.even(0), True, True, "0 = 2*0"),
    (Q.positive(Rational(-1, 3)), True, False, "-1/3 < 0"),
    (Q.extended_real(zoo), True, False, "zoo is a non-real infinity"),
    (Q.finite(nan), True, None, "nothing is known of nan"),
    (Q.positive(x) | Q.negative(x) | Q.zero(x), Q.real(x), True, "trichotomy"),
    (Q.positive(x) & Q.negative(x), True, False, "exclusive"),
    (Eq(x * y, 0), Q.zero(x) & Q.real(y), True, "0*y = 0"),
    (x * y > 0, Q.positive(x) & Q.positive(y), True, "positive product"),
    (S.true, Q.real(x), True, "true"),
    (Q.nonnegative(x * y), Q.nonnegative(x) & Q.nonnegative(y), True, "sign rule"),
    (Q.negative(x / y), Q.positive(x) & Q.negative(y), True, "sign rule, 1/y < 0"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_inconsistent_assumptions_raise():
    with pytest.raises(ValueError):
        ask(Q.real(x), Q.positive(x) & Q.negative(x))
    with pytest.raises(ValueError):
        ask(Q.real(y), Q.even(x) & Q.odd(x))


def test_declared_assumptions_are_facts():
    p = Symbol("p", positive=True)
    n = Symbol("n", integer=True)
    assert ask(Q.positive(p + 1)) is True
    assert ask(Q.even(2 * n)) is True
    with pytest.raises(ValueError):
        ask(Q.real(x), Q.negative(p))


def test_out_of_scope_is_none():
    A, B = symbols("A B", commutative=False)
    assert ask(Q.real(A * B), Q.real(A)) is None
