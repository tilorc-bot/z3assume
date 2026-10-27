"""Circular and hyperbolic functions and their inverses (SymPy's principal
branches), with the rational enclosures of ``z3assume.bounds``.  Every
expected answer has its argument next to it (design.md, "The truth
standard"); None marks what stays open."""
import random
from fractions import Fraction

import mpmath
import pytest
from sympy import (Eq, I, Integer, Q, Rational, S, acos, acosh, acot, acoth, asin, asinh, atan, atanh, cos,
                   cosh, cot, coth, csc, csch, exp, im, pi, re, sec, sech, sin, sinh, symbols, tan, tanh)

from z3assume import ask
from z3assume.bounds import cosh_sinh_bounds, sin_cos_bounds
from z3assume.encode import beyond_pi

x, y, t, p = symbols("x y t p")

CASES = [
    # (proposition, assumptions, answer, why)
    # real arguments: values, signs, the identities
    (Q.real(sin(x)), Q.real(x), True, "sin of a real is real"),
    (Q.real(cos(x)), Q.real(x), True, "cos of a real is real"),
    (Q.real(sin(x)), True, None, "x = oo: free; sin(I) = I*sinh(1)"),
    (Q.complex(sin(x)), True, None, "x = oo: no row, free"),
    (Q.finite(sin(x)), Q.finite(x), True, "sin is entire"),
    (Q.nonnegative(1 - sin(x)), Q.real(x), True, "|sin x| <= 1"),
    (Q.nonnegative(cos(x) + 1), Q.real(x), True, "|cos x| <= 1"),
    (Q.zero(cos(x) ** 2 + sin(x) ** 2 - 1), Q.real(x), True, "cos**2 + sin**2 = 1"),
    (Q.negative(-I + I * (cos(2) ** 2 + sin(2) ** 2)), True, False, "it is 0"),
    (Q.nonzero(-1 + cos(1) ** 2 + sin(1) ** 2), True, False, "it is 0"),
    (Q.positive(-sinh(1) ** 2 - 1 + cosh(1) ** 2), True, False, "cosh**2 - sinh**2 = 1"),
    (Q.zero(cosh(x)), Q.real(x), False, "cosh x >= 1"),
    (Q.positive(cosh(x) - 1), Q.real(x), None, "cosh(0) = 1"),
    (Q.positive(cosh(x) - 1), Q.real(x) & Q.nonzero(x), True, "cosh x = 1 + x**2/2 + ..."),
    (Q.zero(cosh(x)), Q.extended_nonnegative(x), False, "cosh >= 1 on the reals, cosh(oo) = oo (decision 10)"),
    (Q.zero(cosh(x)), Q.imaginary(x), None, "cosh(I*pi/2) = cos(pi/2) = 0"),
    (Q.positive(sinh(x)), Q.positive(x), True, "sinh has the sign of x"),
    (Q.negative(sinh(x)), Q.negative(x), True, "sinh has the sign of x"),
    (Q.nonnegative(sinh(x) - x), Q.nonnegative(x), True, "sinh x >= x for x >= 0"),
    (Q.positive(tanh(x)), Q.positive(x), True, "sinh/cosh, both positive"),
    (Q.negative(tanh(x) - 1), Q.real(x), True, "|sinh| < cosh"),
    (Q.zero(coth(x)), Q.real(x), False, "cosh/sinh with cosh >= 1, or zoo at 0"),
    (Q.zero(coth(x)), Q.extended_positive(x), False, "coth > 1 on (0, oo), coth(oo) = 1 (decision 10)"),
    (Q.zero(sech(x)), Q.complex(x), False, "1/cosh: nonzero, or zoo"),
    (Q.zero(csch(x)), Q.imaginary(x), False, "1/sinh: nonzero, or zoo"),
    (Q.positive(exp(x) - sinh(x)), Q.real(x), True, "exp - sinh = cosh > 0 (one exp pair)"),
    # signs on [-pi, pi]
    (Q.zero(sin(x)), Eq(x, 2), False, "0 < 2 < pi"),
    (Q.zero(sin(x)), Q.ge(x, 2) & Q.le(x, 4), None, "sin(pi) = 0"),
    (Q.zero(tan(x)), Q.gt(x, 0) & Q.lt(x, pi / 2), False, "sin > 0 there"),
    (Q.positive(tan(x)), Q.gt(x, 0) & Q.lt(x, pi / 2), True, "sin, cos > 0 there"),
    (Q.zero(cot(x)), Q.gt(x, 1) & Q.lt(x, 3), None, "cot(pi/2) = 0"),
    (Q.zero(cos(x)), Q.ge(x, -pi / 2) & Q.le(x, pi / 2), None, "cos(pi/2) = 0"),
    (Q.zero(cos(x)), Q.gt(x, -pi / 2) & Q.lt(x, pi / 2), False, "cos > 0 there"),
    (Q.zero(sin(x)), Q.integer(x), None, "sin(0) = 0"),
    (Q.zero(sin(x)), Q.integer(x) & Q.positive(x), False, "Hermite-Lindemann: sin(n) is transcendental"),
    (Q.negative(cos(x)), Eq(x, pi), True, "cos(pi) = -1"),
    # sin(pi*c), cos(pi*c)
    (Q.zero(sin(pi * x)), Q.integer(x), True, "the zeros of sin"),
    (Q.zero(sin(pi * x)), Q.real(x) & ~Q.integer(x), False, "the zeros of sin"),
    (Q.positive(cos(pi * x)), Q.even(x), True, "cos(2*pi*m) = 1"),
    (Q.negative(cos(pi * x)), Q.odd(x), True, "cos(pi*(2m + 1)) = -1"),
    (Q.zero(sinh(I * pi * x)), Q.integer(x), True, "sinh(I*pi*n) = I*sin(pi*n) = 0"),
    # values at rational points (enclosures), poles
    (Q.positive(cos(2)), True, False, "pi/2 < 2 < pi"),
    (Q.negative(sin(4)), True, True, "pi < 4 < 2*pi: enclosure sin(4) = -0.7568..."),
    (Q.positive(sin(7)), True, True, "enclosure: sin(7) = 0.6569..."),
    (Q.negative(cos(Rational(355, 113)) + 1), True, False, "|cos| <= 1"),
    (Q.positive(cosh(2) - Rational(376, 100)), True, True, "cosh(2) = 3.7621..."),
    (Q.positive(tan(Rational(3, 2)) - 14), True, True, "tan(3/2) = 14.1014...: sin/cos enclosures"),
    (Q.infinite(tan(x)), Eq(x, pi / 2), True, "1/0 = zoo, zoo times nonzero (M3)"),
    (Q.infinite(cot(x)), Q.zero(x), True, "cot(0) = zoo"),
    (Q.infinite(csch(x)), Q.zero(x), True, "csch(0) = zoo"),
    (Q.finite(tan(x)), Q.real(x), None, "tan(pi/2) = zoo"),
    (Q.finite(tan(x)), Q.gt(x, -pi / 2) & Q.lt(x, pi / 2), True, "cos > 0 there"),
    (Q.real(tan(x)), Q.real(x), None, "tan(pi/2) = zoo"),
    (Q.extended_real(tanh(x)), Q.real(x), True, "real, cosh > 0"),
    # complex arguments
    (Q.zero(sin(x)), Q.complex(x) & ~Q.real(x), False, "the zeros of sin are real"),
    (Q.imaginary(sin(x)), Q.imaginary(x), True, "sin(I*b) = I*sinh(b), b != 0"),
    (Q.positive(cos(x)), Q.imaginary(x), True, "cos(I*b) = cosh(b) >= 1"),
    (Q.real(cosh(x)), Q.imaginary(x), True, "cosh(I*b) = cos(b)"),
    (Q.zero(sin(x)), Q.zero(x), True, "sin(0) = 0"),
    (Q.zero(cos(x) - 1), Q.zero(x), True, "cos(0) = 1"),
    # special values: nan gives nan (N1); infinities are free
    (Q.real(sin(S.NaN, evaluate=False)), True, False, "N1"),
    (Q.finite(cos(x)), Q.infinite(x), None, "no row, free"),
    # Hermite-Lindemann
    (Q.rational(sin(7)), True, False, "sin(7) is transcendental"),
    (Q.algebraic(cos(7)), True, False, "cos(7) is transcendental"),
    (Q.algebraic(tan(7)), True, False, "tan(7) is transcendental"),
    (Q.algebraic(sinh(7)), True, False, "sinh(7) is transcendental"),
    (Q.rational(tan(x)), Q.nonzero(x) & Q.rational(x), False, "transcendental or zoo"),
    (Q.rational(cot(x)), Q.rational(x), False, "transcendental, or zoo at 0"),
    (Q.algebraic(sec(x)), Q.algebraic(x) & Q.nonzero(x), False, "1/cos"),
    (Q.algebraic(csc(x)), Q.algebraic(x) & Q.nonzero(x), False, "1/sin"),
    (Q.rational(sin(x)), Q.rational(x), None, "sin(0) = 0"),
    (Q.rational(cos(x)), Q.rational(x), None, "cos(0) = 1"),
    (Q.transcendental(cos(x)), Q.algebraic(x) & Q.nonzero(x), True, "Hermite-Lindemann, finite"),
    (Q.algebraic(sin(x)), Q.algebraic(x), None, "sin(0) = 0"),
    (Q.irrational(sin(pi / 7)), True, None, "algebraic (not encoded), and irrational"),
    # inverse functions
    (Q.rational(asin(7)), True, False, "asin(7) is transcendental"),
    (Q.rational(asin(x)), Q.rational(x) & Q.nonzero(x), False, "transcendental, as sin(w) = x"),
    (Q.rational(asin(x)), Q.rational(x), None, "asin(0) = 0"),
    (Q.rational(acos(x)), Q.rational(x) & Q.nonzero(x - 1), False, "acos(w) = 0 only at 1"),
    (Q.rational(acot(x)), Q.rational(x), False, "acot never 0 at a finite point"),
    (Q.algebraic(atan(x)), Q.algebraic(x) & Q.nonzero(x), False, "transcendental or infinite (+-I)"),
    (Q.algebraic(acosh(x)), Q.algebraic(x) & Q.nonzero(x - 1), False, "transcendental"),
    (Q.zero(acosh(x)), Eq(x, 1), True, "acosh(1) = 0"),
    (Q.positive(atan(p)), Q.positive(p), True, "range (0, pi/2)"),
    (Q.positive(atan(p)), Q.negative(p), False, "range (-pi/2, 0)"),
    (Q.positive(atan(p)), Q.zero(p), False, "atan(0) = 0"),
    (Q.positive(asin(Rational(1, 7))), True, True, "sign of the argument"),
    (Q.positive(asin(x)), Q.positive(x) & Q.nonpositive(x - 1), True, "(0, 1] -> (0, pi/2]"),
    (Q.positive(asin(x)), Q.positive(x), None, "asin(2) is not real"),
    (Q.real(asin(x)), Q.positive(x - 1), False, "|sin w| <= 1 for real w"),
    (Q.positive(acos(Rational(1, 7))), True, True, "acos(x) > 0 for x < 1"),
    (Q.positive(acos(x)), Q.zero(x), True, "acos(0) = pi/2"),
    (Q.positive(acos(x)), Q.nonnegative(x - 1), False, "acos(1) = 0, not real beyond"),
    (Q.negative(acos(x) - pi), Q.positive(x + 1) & Q.negative(x - 1), True, "range [0, pi], pi only at -1"),
    (Q.positive(acot(x)), Q.positive(x), True, "SymPy's range (-pi/2, pi/2]"),
    (Q.negative(acot(x)), Q.negative(x), True, "SymPy's range (-pi/2, pi/2]"),
    (Q.positive(acot(x)), Q.real(x), None, "acot(-1) = -pi/4"),
    (Q.positive(acot(x)), Q.imaginary(x), False, "cot(w) = x: cot maps the reals into the reals and zoo"),
    (Q.real(atan(x)), Q.complex(x) & ~Q.real(x), False, "tan(w) = x: tan maps the reals into the reals and zoo"),
    (Q.real(acosh(x)), Q.imaginary(x), False, "cosh(w) = x: cosh maps the reals into [1, oo)"),
    (Q.negative(asinh(x)), Q.negative(x), True, "odd, increasing"),
    (Q.nonnegative(acosh(x)), Q.positive(x - 1), True, "[1, oo) -> [0, oo)"),
    (Q.real(acosh(x)), Q.negative(x - 1), False, "cosh(w) >= 1 for real w"),
    (Q.positive(atanh(x)), Q.positive(x) & Q.negative(x - 1), True, "(0, 1) -> (0, oo)"),
    (Q.real(atanh(x)), Q.positive(x - 1), False, "|tanh w| < 1 for real w"),
    (Q.real(acoth(x)), Q.positive(x) & Q.negative(x - 1), False, "|coth w| > 1 for real w != 0"),
    (Q.positive(acoth(x)), Q.positive(x - 1), True, "(1, oo) -> (0, oo)"),
    (Q.real(atan(x)), Q.infinite(x), None, "atan(oo) = pi/2: a limit no row states"),
    (Q.real(asin(S.NaN, evaluate=False)), True, False, "N1"),
    # decision 18: the real part of asin, atan at every finite point
    (Q.zero(asin(x) - y), Q.finite(x) & Q.gt(re(y), 2), False, "|re asin| <= pi/2, cuts included"),
    (Q.zero(atan(x) - y), Q.finite(x) & Q.gt(re(y), 2), False, "|re atan| <= pi/2 where finite"),
    (Q.zero(atan(x) - y), Q.finite(x) & Q.gt(re(y), 1), None, "re atan(I*coth(1)) = pi/2 > 1"),
    (Q.zero(asin(x) - y), Q.finite(x) & Q.ge(re(y), pi / 2), None, "asin(2) = pi/2 - 1.3169...*I"),
    # decision 18: inverse(forward(v)) = v on the principal strip
    (Q.zero(asin(sin(x)) - x), Q.real(x) & Q.ge(x, -pi / 2) & Q.le(x, pi / 2), True, "closed real interval"),
    (Q.zero(asin(sin(x)) - x), Q.real(x) & Q.ge(x, -2) & Q.le(x, 2), None, "asin(sin 2) = pi - 2"),
    (Q.zero(asin(sin(x)) - x), Q.real(x) & Q.gt(x, pi / 2) & Q.lt(x, 2), False, "asin is in [-pi/2, pi/2]"),
    (Q.zero(asin(sin(x)) - x), Q.finite(x) & Q.lt(abs(re(x)), 1), True, "open strip |re| < pi/2"),
    (Q.zero(asin(sin(x)) - x), Q.imaginary(x), True, "re x = 0 is on the strip"),
    (Q.zero(asin(sin(x)) - x), Q.finite(x) & Q.gt(re(x), 1), None, "true up to pi/2, false beyond"),
    (Q.zero(asin(sin(x)) - x), Q.lt(abs(re(x)), 1), None, "x = I*oo: re 0, sin free"),
    (Q.zero(asin(sin(atan(y) / 2)) - atan(y) / 2), Q.real(y), True, "atan(y)/2 is in (-pi/4, pi/4)"),
    (Q.zero(atan(tan(x)) - x), Q.finite(x) & Q.gt(re(x), -1) & Q.lt(re(x), 1), True, "open strip"),
    (Q.zero(atan(tan(x)) - x), Q.real(x), None, "atan(tan 2) = 2 - pi"),
    (Q.zero(atan(tan(x)) - x), Q.finite(x) & ~Q.real(x) & Q.gt(re(x), 2), False, "|re atan| <= pi/2 < 2"),
    (Q.zero(atan(tan(x)) - x), Q.finite(x) & Q.gt(re(x), 2), None, "tan(3*pi/2) = zoo, atan(zoo) is free"),
    (Q.zero(atan(tan(x)) - x), Q.finite(x) & Q.eq(re(x), pi / 2) & ~Q.real(x), None,
     "tan(pi/2 + I*b) = I*coth(b) is on the cut: the side is a convention"),
    (Q.zero(acos(cos(x)) - x), Q.finite(x) & Q.gt(re(x), 0) & Q.lt(re(x), 3), True, "strip 0 < re < pi"),
    (Q.zero(acos(cos(x)) - x), Q.finite(x) & Q.gt(re(x), 0) & Q.lt(re(x), 4), None, "acos(cos 4) = 2*pi - 4"),
    (Q.zero(acos(cos(x)) - abs(x)), Q.real(x) & Q.ge(x, -pi) & Q.le(x, pi), True, "cos x = cos|x|"),
    (Q.zero(acos(cos(x)) + x), Q.real(x) & Q.ge(x, -pi) & Q.le(x, 0), True, "-x in [0, pi]"),
    (Q.zero(acos(cos(x)) - abs(x)), Q.real(x) & Q.le(x, 4), None, "acos(cos 4) = 2*pi - 4"),
    (Q.rational(acos(cos(x))), Q.rational(x) & Q.gt(x, -3) & Q.lt(x, 0), True, "-x"),
    (Q.zero(asinh(sinh(x)) - x), Q.real(x), True, "sinh is a bijection of R"),
    (Q.zero(asinh(sinh(x)) - x), Q.imaginary(x), None, "asinh(sinh(4*I)) = (pi - 4)*I"),
    (Q.zero(atanh(tanh(x)) - x), Q.real(x), True, "tanh: R -> (-1, 1), a bijection"),
    (Q.zero(atanh(tanh(x)) - x), Q.extended_real(x), None, "x = oo: atanh(1) = oo, free"),
    (Q.zero(acosh(cosh(x)) - abs(x)), Q.real(x), True, "cosh x = cosh|x|"),
    (Q.zero(acosh(cosh(x)) - x), Q.real(x), None, "x < 0"),
    (Q.zero(acosh(cosh(x)) - x), Q.negative(x), False, "|x| = -x != x"),
    (Q.integer(acosh(cosh(x))), Q.integer(x), True, "|k|"),
    # decision 10: the hyperbolic functions at +-oo are their limits
    (Q.zero(coth(x)), Q.gt(x, 0), False, "coth > 1 on (0, oo), coth(oo) = 1"),
    (Q.positive(coth(x)), Q.ge(x, 1), True, "coth > 1 on (0, oo), coth(oo) = 1"),
    (Q.zero(coth(x)), Q.extended_real(x), False, "|coth| > 1 on the nonzero reals, coth(0) = zoo, +-1 at +-oo"),
    (Q.negative(tanh(x)), Q.extended_negative(x), True, "odd, increasing, tanh(-oo) = -1"),
    (Q.zero(sech(x)), Q.extended_real(x) & Q.infinite(x), True, "sech(+-oo) = 0"),
    (Q.zero(csch(x)), Q.extended_real(x) & Q.infinite(x), True, "csch(+-oo) = 0"),
    (Q.extended_negative(sinh(x)), Q.extended_negative(x), True, "sinh(-oo) = -oo"),
    (Q.positive(sinh(x)), Q.gt(x, 0), None, "sinh(oo) = oo is not positive"),
    (Q.infinite(cosh(x)), Q.extended_real(x) & Q.infinite(x), True, "cosh(+-oo) = oo"),
    (Q.zero(coth(x)), Q.infinite(x), None, "no limit at oo*I (coth(I*t) = -I*cot(t)) or zoo"),
    (Q.extended_real(cosh(x + I)), Q.positive_infinite(x), None, "x + I is oo or an infinity off the real axis"),
    (Q.positive_infinite(sinh(x + y)), Q.positive_infinite(x) & Q.eq(y, I * pi), None, "sinh(t + I*pi) = -sinh(t)"),
    # decision 19: the sign tables of (cos u, sin u) on [-4*pi, 4*pi]
    (Q.negative(cos(x)), Q.real(x) & Q.gt(x, 11 * pi / 4) & Q.lt(x, 13 * pi / 4), True, "around 3*pi"),
    (Q.negative(cos(x)), Q.real(x) & Q.gt(x, 2 * pi) & Q.lt(x, 3 * pi), None, "cos(2*pi + 1/10) > 0"),
    (Q.positive(sin(x)), Q.real(x) & Q.gt(x, -4 * pi) & Q.lt(x, -3 * pi), True, "(0, pi) - 4*pi"),
    (Q.positive(sin(x)), Q.real(x) & Q.gt(x, -4 * pi) & Q.lt(x, -2 * pi), None, "sin(-5*pi/2) = -1"),
    (Q.zero(cos(x)), Q.eq(x, 7 * pi / 2), True, "zero of cos"),
    (Q.zero(sin(x) + 1), Q.eq(x, -5 * pi / 2), True, "-5*pi/2 = -pi/2 - 2*pi"),
    (Q.zero(cos(x) + 1), Q.eq(x, 3 * pi), True, "cos(3*pi) = -1"),
    (Q.positive(tan(x)), Q.real(x) & Q.gt(x, 2 * pi) & Q.lt(x, 5 * pi / 2), True, "sin, cos > 0"),
    (Q.positive(cos(x)), Q.real(x) & Q.gt(x, -9 * pi / 2) & Q.lt(x, -7 * pi / 2), None,
     "true, but beyond -4*pi the table says nothing"),
    (Q.positive(sinh(y) * sin(x)), Q.real(x) & Q.gt(x, 2 * pi) & Q.lt(x, 3 * pi) & Q.positive(y), True,
     "sin > 0 on (2*pi, 3*pi)"),
    # decision 19: the same table for exp(a + b*I) = e**a*(cos b + I*sin b)
    (Q.negative(re(exp(x))), Q.finite(x) & Q.gt(im(x), 5 * pi / 2) & Q.lt(im(x), 7 * pi / 2), True,
     "cos b < 0"),
    (Q.positive(im(exp(x))), Q.finite(x) & Q.gt(im(x), -4 * pi) & Q.lt(im(x), -3 * pi), True, "sin b > 0"),
    (Q.positive(im(exp(x))), Q.finite(x) & Q.gt(im(x), 2 * pi) & Q.lt(im(x), 4 * pi), None, "sin b < 0 past 3*pi"),
    (Q.zero(exp(x) - exp(re(x))), Q.finite(x) & Q.eq(im(x), -4 * pi), True, "exp(-4*pi*I) = 1"),
    (Q.positive(sin(x)), Q.real(x) & Q.gt(x, 7) & Q.lt(x, 9), True, "(2*pi, 3*pi), a literal > 3"),
    (Q.negative(sin(x + y)), Q.real(x) & Q.real(y) & Q.gt(x, 3) & Q.lt(x, pi) & Q.gt(y, 3) & Q.lt(y, pi),
     None, "true (x + y in (6, 2*pi)), but no number beyond pi: no far signs (decision 19)"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_beyond_pi():
    # decision 19: the far signs only for a query with a number beyond pi
    assert beyond_pi(Q.gt(x, 3 * pi / 2), True)
    assert beyond_pi(True, Q.lt(x, -4))
    assert beyond_pi(Q.zero(cos(x)), Q.eq(x - 7 * pi / 2, y))
    assert not beyond_pi(Q.lt(abs(x), pi), Q.zero(sin(x) ** 2 + cos(x) ** 3))
    assert not beyond_pi(Q.gt(x, -3) & Q.lt(x, S.Infinity) & Q.gt(y, pi / 2))


def test_sympy_forms():
    """The SymPy objects reach the encoder as these classes and values."""
    assert tan(pi / 2) is S.ComplexInfinity and cot(0) is S.ComplexInfinity
    assert acot(0) == pi / 2 and acot(-1) == -pi / 4


# -- the enclosures, cross-checked with mpmath (not the truth standard:
#    bounds.py carries its own argument; this guards the code) ----------

def _mp(f):
    return mpmath.mpf(f.numerator) / f.denominator


@pytest.mark.parametrize("r", [Fraction(7), Fraction(2), Fraction(-1, 3), Fraction(22, 7), Fraction(355, 113),
                               Fraction(256), Fraction(-255, 2), Fraction(1, 10 ** 29)])
def test_sin_cos_bounds(r):
    (slo, shi), (clo, chi) = sin_cos_bounds(r)
    with mpmath.workprec(600):
        v = _mp(r)
        s, c = mpmath.sin(v), mpmath.cos(v)
        assert _mp(slo) < s < _mp(shi) and _mp(clo) < c < _mp(chi)
        assert (_mp(shi) - _mp(slo)) / abs(s) < mpmath.mpf(10) ** -18
        assert (_mp(chi) - _mp(clo)) / abs(c) < mpmath.mpf(10) ** -18


@pytest.mark.parametrize("r", [Fraction(7), Fraction(2), Fraction(-1, 3), Fraction(-10_000), Fraction(1, 7)])
def test_cosh_sinh_bounds(r):
    (clo, chi), (slo, shi) = cosh_sinh_bounds(r)
    with mpmath.workprec(400):
        v = _mp(r)
        c, s = mpmath.cosh(v), mpmath.sinh(v)
        assert _mp(clo) < c < _mp(chi) and _mp(slo) < s < _mp(shi)
        assert (_mp(chi) - _mp(clo)) / c < mpmath.mpf(10) ** -17
        assert (_mp(shi) - _mp(slo)) / abs(s) < mpmath.mpf(10) ** -17


def test_bounds_out_of_range():
    assert sin_cos_bounds(0) is None and sin_cos_bounds(257) is None
    assert cosh_sinh_bounds(0) is None


# -- randomized falsification, as in test_exp_log: a definite answer about
#    the sign, reality or imaginarity must hold at every Gaussian rational
#    point satisfying the assumptions, evaluated with mpmath at 300 bits
#    (it can only find wrong answers).  A pole or a value within EPS of a
#    branch cut or of 0 is skipped.

PREDS = ("real", "positive", "negative", "nonzero", "nonnegative", "nonpositive", "imaginary")
POINTS = [(Fraction(a), Fraction(b)) for a, b in
          ((1, 0), (-2, 0), (Fraction(1, 2), 0), (3, 0), (0, 1), (0, -2), (1, 1), (-3, 4), (Fraction(1, 2), -1),
           (0, 0), (Fraction(-1, 3), 0), (5, 0))]
EPS = mpmath.mpf(10) ** -40


class Undecided(Exception):
    pass


FORWARD = {sin: mpmath.sin, cos: mpmath.cos, tan: mpmath.tan, cot: mpmath.cot, sec: mpmath.sec,
           csc: mpmath.csc, sinh: mpmath.sinh, cosh: mpmath.cosh, tanh: mpmath.tanh, coth: mpmath.coth,
           sech: mpmath.sech, csch: mpmath.csch}
#: mpmath's principal branches; on the real axis outside the domain they
#: differ from SymPy's by the side of the cut, so such points are skipped
#: unless the value is off the cut (predicates about sign and reality do
#: not depend on the side for asin, acos, atanh, acoth off the real line)
INVERSE = {asin: mpmath.asin, acos: mpmath.acos, atan: mpmath.atan, asinh: mpmath.asinh,
           acosh: mpmath.acosh, atanh: mpmath.atanh}
DENOMINATOR = {tan: mpmath.cos, cot: mpmath.sin, sec: mpmath.cos, csc: mpmath.sin, tanh: mpmath.cosh,
               coth: mpmath.sinh, sech: mpmath.cosh, csch: mpmath.sinh}


def value(e, env):
    if e in env:
        return env[e]
    if e is S.ImaginaryUnit:
        return mpmath.mpc(0, 1)
    if isinstance(e, Rational):
        return mpmath.mpc(_mp(Fraction(int(e.p), int(e.q))))
    if e is S.Pi:
        return mpmath.mpc(mpmath.pi)
    if e.func in FORWARD:
        v = value(e.args[0], env)
        if e.func in DENOMINATOR and abs(DENOMINATOR[e.func](v)) < EPS:
            raise Undecided
        return mpmath.mpc(FORWARD[e.func](v))
    if e.func in INVERSE:
        v = value(e.args[0], env)
        if abs(v.imag) < EPS and (e.func in (asin, acos, atanh) and abs(v.real) >= 1
                                  or e.func is acosh and v.real <= 1):
            raise Undecided           # on a branch cut: the side is a convention
        if e.func in (atan, atanh) and (abs(v - 1j) < EPS or abs(v + 1j) < EPS or abs(v - 1) < EPS
                                        or abs(v + 1) < EPS):
            raise Undecided
        if e.func in (atan, asinh) and abs(v.real) < EPS and abs(v.imag) >= 1:
            raise Undecided           # their cuts on the imaginary axis
        return mpmath.mpc(INVERSE[e.func](v))
    vs = [value(a, env) for a in e.args]
    if e.is_Add:
        return mpmath.fsum(vs)
    if e.is_Mul:
        return mpmath.fprod(vs)
    if e.is_Pow:
        if abs(vs[0]) < EPS and e.exp < 0:
            raise Undecided
        return vs[0] ** int(e.exp)
    raise TypeError(e)


def holds(pred, v):
    a, b = v.real, v.imag
    if (b != 0 and abs(b) < EPS) or (a != 0 and abs(a) < EPS):
        raise Undecided
    if pred == "real":
        return b == 0
    if pred == "imaginary":
        return a == 0 and b != 0
    if b != 0:
        return False
    return {"positive": a > 0, "negative": a < 0, "nonzero": a != 0,
            "nonnegative": a >= 0, "nonpositive": a <= 0}[pred]


def random_expr(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice([x, y, x, y, Integer(rng.randint(-2, 3)), I, pi])
    op = rng.choice(["add", "mul", "fun", "fun", "fun", "inv"])
    a = random_expr(rng, depth - 1)
    if op == "fun":
        return rng.choice(list(FORWARD))(a)
    if op == "inv":
        return rng.choice(list(INVERSE))(a)
    b = random_expr(rng, depth - 1)
    return a + b if op == "add" else a * b


@pytest.mark.parametrize("seed", range(4))
def test_definite_answers_hold_numerically(seed):
    rng = random.Random(seed)
    definite = 0
    with mpmath.workprec(300):
        for _ in range(25):
            e = random_expr(rng, 3)
            if not e.free_symbols or e.has(S.NaN, S.ComplexInfinity, S.Infinity, S.NegativeInfinity):
                continue
            base = rng.choice(["real", "complex", "positive"])
            pred = rng.choice(PREDS)
            fact = (rng.choice(PREDS), rng.choice([x, y]))
            a = getattr(Q, base)(x) & getattr(Q, base)(y) & getattr(Q, fact[0])(fact[1])
            try:
                r = ask(getattr(Q, pred)(e), a)
            except ValueError:
                continue
            if r is None:
                continue
            definite += 1
            for px in POINTS:
                for py in POINTS:
                    env = {x: mpmath.mpc(_mp(px[0]), _mp(px[1])), y: mpmath.mpc(_mp(py[0]), _mp(py[1]))}
                    try:
                        if not all(holds(q, env[s]) for q, s in ((base, x), (base, y), fact)
                                   if q != "complex"):
                            continue
                        got = holds(pred, value(e, env))
                    except (Undecided, ZeroDivisionError, ValueError):
                        continue
                    assert got is r, (pred, e, a, env)
    assert definite > 0
