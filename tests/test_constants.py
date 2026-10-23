"""Named constants (pi, E, GoldenRatio, TribonacciConstant, EulerGamma,
Catalan) and the field closure around them.  Every expected answer has its
argument next to it (design.md, "The truth standard")."""
import pytest
from sympy import (Catalan, E, EulerGamma, GoldenRatio, I, Pow, Q, S, TribonacciConstant, pi,
                   symbols)

from z3assume import ask

x, y, k = symbols("x y k")
T = TribonacciConstant

CASES = [
    # (proposition, assumptions, answer, why)
    (Q.positive(pi), True, True, "3.14 < pi"),
    (Q.transcendental(pi), True, True, "Lindemann 1882"),
    (Q.irrational(pi), True, True, "transcendental and real"),
    (Q.integer(pi), True, False, "3 < pi < 4"),
    (Q.transcendental(E), True, True, "Hermite 1873"),
    (Q.positive(pi - 3), True, True, "pi > 3.14"),
    (Q.negative(E - 3), True, True, "e < 2.72"),
    (Q.positive(E - 2), True, True, "e > 2.71"),
    (Q.negative(pi - E - 1), True, True, "pi - e < 3.15 - 2.71 < 1"),
    (Q.rational(pi * x), Q.rational(x) & Q.nonzero(x), False, "pi = (pi*x)/x"),
    (Q.rational(pi * x), Q.zero(x), True, "pi*0 = 0"),
    (Q.irrational(pi + x), Q.rational(x), True, "pi = (pi + x) - x"),
    (Q.transcendental(pi + x), Q.algebraic(x), True, "the algebraic numbers are a field"),
    (Q.algebraic(pi * x), Q.algebraic(x) & Q.nonzero(x), False, "pi = (pi*x)/x"),
    (Q.algebraic(pi + E), True, None, "open problem"),
    (Q.transcendental(pi**2), True, True, "pi is a root of x**2 - pi**2: algebraically closed"),
    (Q.rational((1 + pi)**2), True, False, "(1 + pi)**2 algebraic would make pi algebraic"),
    (Q.algebraic(1 / pi**3), True, False, "pi is a root of t*x**3 - 1"),
    (Q.transcendental(x), Q.algebraic(x**2) & Q.finite(x), False, "x is a root of x**2 - a"),
    # the closure needs a nonzero exponent: b**0 = 1 for every b (design.md)
    (Q.algebraic(Pow(pi, 0, evaluate=False)), True, True, "pi**0 = 1"),
    (Q.transcendental(x), Q.algebraic(Pow(x, 0, evaluate=False)) & Q.finite(x), None, "x**0 = 1 says nothing of x"),
    (Q.zero(pi * k / 2), Q.odd(k), False, "no zero divisors, pi != 0, k != 0"),
    (Q.zero(I * pi / 3), True, False, "pi != 0"),
    (Q.real(I * pi), True, False, "imaginary part pi != 0"),
    (Q.imaginary(I * pi), True, True, "0 + pi*I, pi != 0"),
    (Q.positive(x * pi), Q.positive(x), True, "pi > 0"),
    (Q.algebraic(GoldenRatio), True, True, "root of x**2 - x - 1"),
    (Q.rational(GoldenRatio), True, False, "rational root test: +-1 are no roots"),
    (Q.zero(GoldenRatio**2 - GoldenRatio - 1), True, True, "GoldenRatio**2 = GoldenRatio + 1"),
    (Q.integer(GoldenRatio**2), True, False, "GoldenRatio + 1 is irrational"),
    (Q.algebraic(T), True, True, "root of x**3 - x**2 - x - 1"),
    (Q.irrational(T), True, True, "rational root test: +-1 are no roots"),
    (Q.zero(T**3 - T**2 - T - 1), True, True, "its polynomial"),
    (Q.positive(T - GoldenRatio), True, True, "1.83 > 1.62"),
    (Q.positive(EulerGamma), True, True, "0.577 > 0"),
    (Q.integer(EulerGamma), True, False, "0 < EulerGamma < 1"),
    (Q.rational(EulerGamma), True, None, "open problem"),
    (Q.irrational(EulerGamma), True, None, "open problem"),
    (Q.algebraic(EulerGamma), True, None, "open problem"),
    (Q.transcendental(EulerGamma), True, None, "open problem"),
    (Q.rational(Catalan), True, None, "open problem"),
    (Q.transcendental(Catalan), True, None, "open problem"),
    (Q.negative(Catalan - 1), True, True, "Catalan < 0.92"),
    (Q.positive(Catalan - EulerGamma), True, True, "0.915 > 0.578"),
    (Q.zero(pi), Q.positive(x) & Q.negative(x), False, "a constant is decided without the assumptions"),
    (Q.irrational(x * y), Q.rational(x) & Q.nonzero(x) & Q.irrational(y), True, "y = (x*y)/x"),
    (Q.transcendental(x * y), Q.algebraic(x) & Q.nonzero(x) & Q.transcendental(y), True, "y = (x*y)/x"),
    (Q.transcendental(x + y), Q.algebraic(x) & Q.transcendental(y), True, "y = (x + y) - x"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_constants_are_constants():
    assert S.Exp1 is E
    assert ask(Q.real(pi * x), Q.real(x)) is True
