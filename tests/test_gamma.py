"""gamma and factorial (issue #21): poles exactly at the nonpositive
integers (value ``zoo``), no zeros, positive on the positive reals, the
sign ``(-1)**floor(x)`` at the negative non-integers, ``(n - 1)!`` at the
positive integers, ``gamma(oo) = oo``; ``factorial(z) = gamma(z + 1)``.
Every expected answer has its argument next to it (design.md, "The truth
standard"); None marks what stays open."""
import random
from fractions import Fraction

import mpmath
import pytest
from sympy import I, Q, Rational, S, factorial, gamma, pi, symbols

from z3assume import ask

x, y, k, n = symbols("x y k n")
half = Rational(1, 2)

CASES = [
    # (proposition, assumptions, answer, why)
    # the positive reals: an integral of a positive function
    (Q.positive(gamma(x)), Q.positive(x), True, "integral of s**(x-1)*e**-s > 0"),
    (Q.zero(gamma(x)), Q.positive(x), False, "positive"),
    (Q.negative(gamma(x)), Q.positive(x), False, "positive"),
    (Q.real(gamma(x)), Q.positive(x), True, "positive"),
    (Q.integer(gamma(x)), Q.positive(x), None, "gamma(1/2) = sqrt(pi); gamma(1) = 1"),
    (Q.rational(gamma(x)), Q.positive(x), None, "gamma(1) = 1; gamma(1/2) = sqrt(pi) is not"),
    # no zeros, poles exactly at the nonpositive integers
    (Q.zero(gamma(x)), Q.finite(x), False, "1/gamma is entire; the poles give zoo"),
    (Q.zero(gamma(x)), True, None, "gamma(-oo): free"),
    (Q.zero(gamma(x)), Q.complex(x), False, "no zeros"),
    (~Q.zero(gamma(x)), Q.complex(x) & ~Q.extended_real(x), True, "no zeros"),
    (Q.finite(gamma(x)), Q.complex(x) & ~Q.integer(x), True, "no pole off the nonpositive integers"),
    (Q.finite(gamma(x)), Q.complex(x), None, "gamma(0) = zoo"),
    (Q.infinite(gamma(x)), Q.integer(x) & Q.nonpositive(x), True, "a pole: zoo"),
    (Q.extended_real(gamma(x)), Q.integer(x) & Q.nonpositive(x), False, "zoo is no extended real"),
    (Q.infinite(gamma(S.Zero, evaluate=False)), True, True, "the pole at 0"),
    (Q.infinite(gamma(-3 * x)), Q.integer(x) & Q.nonnegative(x), True, "-3*x a nonpositive integer"),
    (Q.finite(gamma(x)), Q.integer(x), None, "gamma(1) = 1, gamma(0) = zoo"),
    (Q.real(gamma(x)), Q.complex(x) & ~Q.extended_real(x), None, "gamma is real on a curve off the axis"),
    # the negative non-integers: sign (-1)**floor(x)
    (Q.negative(gamma(x)), Q.gt(x, -1) & Q.lt(x, 0), True, "floor(x) = -1"),
    (Q.positive(gamma(x)), Q.gt(x, -2) & Q.lt(x, -1), True, "floor(x) = -2"),
    (Q.negative(gamma(x)), Q.gt(x, -3) & Q.lt(x, -2), True, "floor(x) = -3"),
    (Q.negative(gamma(-half)), True, True, "-1/2 in (-1, 0)"),
    (Q.positive(gamma(Rational(-3, 2))), True, True, "-3/2 in (-2, -1)"),
    (Q.real(gamma(x)), Q.negative(x) & ~Q.integer(x), True, "real off the poles"),
    (Q.zero(gamma(x)), Q.negative(x) & ~Q.integer(x), False, "no zeros"),
    (Q.negative(gamma(x)), Q.negative(x) & ~Q.integer(x), None, "gamma(-1/2) < 0 < gamma(-3/2)"),
    (Q.negative(gamma(x)), Q.gt(x, -2) & Q.lt(x, 0) & ~Q.integer(x), None, "-1/2 and -3/2"),
    (Q.real(gamma(x)), Q.real(x), None, "gamma(0) = zoo"),
    (Q.positive(gamma(x)), Q.real(x) & ~Q.integer(x), None, "gamma(-1/2) < 0"),
    # the positive integers: (n - 1)!
    (Q.integer(gamma(x)), Q.integer(x) & Q.positive(x), True, "(x - 1)!"),
    (Q.positive(gamma(x)), Q.integer(x) & Q.positive(x), True, "(x - 1)! >= 1"),
    (Q.odd(gamma(x)), Q.integer(x) & Q.positive(x) & Q.lt(x, 3), True, "0! = 1! = 1"),
    (Q.prime(gamma(S(3), evaluate=False)), True, True, "2! = 2"),
    (Q.even(gamma(x)), Q.integer(x) & Q.gt(x, 2), True, "(x - 1)! with the factor 2"),
    (Q.composite(gamma(x)), Q.integer(x) & Q.gt(x, 3), True, "a multiple of 6"),
    (Q.prime(gamma(x)), Q.integer(x) & Q.positive(x), None, "gamma(3) = 2; gamma(1) = 1"),
    # infinities and nan
    (Q.positive_infinite(gamma(x)), Q.positive_infinite(x), True, "gamma(oo) = oo, the limit"),
    (Q.infinite(gamma(x)), Q.negative_infinite(x), None, "gamma(-oo): no limit, free"),
    (Q.infinite(gamma(x)), Q.infinite(x), None, "gamma(zoo): free"),
    (Q.real(gamma(S.NaN, evaluate=False)), True, False, "N1: nan, no number (V1)"),
    # factorial(z) = gamma(z + 1)
    (Q.positive(factorial(x)), Q.integer(x) & Q.positive(x), True, "x! >= 1"),
    (Q.positive(factorial(x)), Q.integer(x), None, "(-1)! = zoo"),
    (Q.positive(factorial(x)), Q.nonnegative(x), True, "gamma(x + 1) for x + 1 > 0"),
    (Q.integer(factorial(x)), Q.integer(x) & Q.nonnegative(x), True, "x! = 1*2*...*x"),
    (Q.integer(factorial(x)), Q.nonnegative(x), None, "factorial(1/2) = sqrt(pi)/2"),
    (Q.odd(factorial(x)), Q.zero(x), True, "0! = 1"),
    (Q.even(factorial(x)), Q.integer(x) & Q.gt(x, 1), True, "x! has the factor 2"),
    (Q.composite(factorial(x)), Q.integer(x) & Q.gt(x, 2), True, "a multiple of 6"),
    (Q.infinite(factorial(x)), Q.integer(x) & Q.negative(x), True, "a negative integer: zoo"),
    (Q.extended_real(factorial(x)), Q.integer(x) & Q.negative(x), False, "zoo"),
    (Q.zero(factorial(x)), Q.finite(x), False, "gamma has no zeros"),
    (Q.negative(factorial(x)), Q.gt(x, -2) & Q.lt(x, -1), True, "x + 1 in (-1, 0)"),
    (Q.real(factorial(x)), Q.real(x) & ~Q.integer(x), True, "real off the poles"),
    (Q.positive_infinite(factorial(x)), Q.positive_infinite(x), True, "factorial(oo) = oo"),
    (Q.zero(factorial(x - 1)), Q.integer(x) & Q.positive(x), False, "(x - 1)! >= 1"),
    (Q.negative(factorial(n - k)), Q.integer(k) & Q.integer(n) & Q.le(k, n), False, "(n - k)! >= 1"),
    (Q.positive(factorial(n - k)), Q.integer(k) & Q.integer(n), None, "n - k = -1: zoo"),
    (Q.positive(factorial(x * pi)), Q.positive(x), True, "x*pi + 1 > 0"),
    (Q.finite(factorial(x)), Q.complex(x) & ~Q.extended_real(x), True, "no pole off the real line"),
    (Q.real(factorial(I * x)), Q.positive(x), None, "not encoded: whether gamma(1 + I*x) is real"),
]


@pytest.mark.parametrize("prop, assumptions, expected, why", CASES,
                         ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_case(prop, assumptions, expected, why):
    assert ask(prop, assumptions) is expected, why


# -- a randomized check against mpmath at real points ---------------------

PREDS = ["positive", "negative", "zero", "nonzero", "real", "integer", "even", "odd", "finite"]
POINTS = [Fraction(p, 4) for p in range(-14, 15)]


def holds(pred, v):
    """``pred`` of the value ``v``: a float, an int (an exact integer value)
    or ``"zoo"``, of which every predicate in ``PREDS`` is False (special
    values V3; ``nonzero`` is ``real & ~zero``)."""
    if v == "zoo":
        return False
    if pred in ("finite", "real"):
        return True
    if pred in ("integer", "even", "odd"):
        if not isinstance(v, int):
            return False
        return pred == "integer" or (v % 2 == 0) == (pred == "even")
    return {"positive": v > 0, "negative": v < 0, "zero": v == 0, "nonzero": v != 0}[pred]


def gamma_value(w: Fraction):
    if w.denominator == 1:
        m = int(w)
        return "zoo" if m <= 0 else int(mpmath.factorial(m - 1))
    v = float(mpmath.gamma(mpmath.mpf(w.numerator) / w.denominator))
    assert v != 0
    return v


@pytest.mark.parametrize("seed", range(4))
def test_definite_answers_hold_numerically(seed):
    """Random ``gamma(c*x + d)``, ``factorial(c*x + d)`` under an interval
    and maybe ``Q.integer(x)``: a definite answer holds at every point of
    the interval (quarter steps)."""
    rng = random.Random(seed)
    definite = 0
    for _ in range(25):
        c, d = rng.choice([1, -1, 2]), Rational(rng.choice([-3, -2, -1, 0, 1, 2]), rng.choice([1, 2]))
        fn = rng.choice([gamma, factorial])
        e = fn(c * x + d)
        lo = rng.choice([-4, -3, -2, -1, 0, 1])
        hi = lo + rng.choice([1, 2, 3])
        integer = rng.random() < 0.5
        a = Q.gt(x, lo) & Q.lt(x, hi)
        if integer:
            a = a & Q.integer(x)
        pred = rng.choice(PREDS)
        try:
            r = ask(getattr(Q, pred)(e), a)
        except ValueError:
            continue
        if r is None:
            continue
        definite += 1
        for p in POINTS:
            if not lo < p < hi or (integer and p.denominator != 1):
                continue
            w = c * p + Fraction(int(d.p), int(d.q)) + (1 if fn is factorial else 0)
            v = gamma_value(w)
            assert holds(pred, v) is r, (pred, e, a, p, v)
    assert definite > 0
