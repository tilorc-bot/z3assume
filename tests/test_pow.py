"""Powers with an exponent that is not an integer literal (SymPy's principal
value ``exp(x*log(b))``, satassume's special-values rows P1-P6, N1).
Every expected answer has its argument next to it (design.md, "The truth
standard"); None marks what stays open."""
import pytest
from sympy import (Eq, Float, I, Pow, Q, Rational, S, exp, pi, sin, sqrt, symbols)

from z3assume import ask

x, y, k = symbols("x y k")

CASES = [
    # (proposition, assumptions, answer, why)
    # special values
    (Q.integer(x ** y), Q.zero(y), True, "P2: b**0 = 1 for every b but nan"),
    (Q.real(x ** x), Q.zero(x), True, "P2: 0**0 = 1"),
    (Q.zero(x ** y), Q.zero(x) & Q.positive(y), True, "|z**y| = |z|**y -> 0, real y > 0"),
    (Q.infinite(x ** y), Q.zero(x) & Q.negative(y), True, "P1: 0**y = zoo, y < 0"),
    (Q.zero(x ** y), Q.zero(x) & Q.imaginary(y), None, "0**(I*s): SymPy nan, limit 0 or none; free"),
    (Q.positive_infinite(x ** y), Q.positive_infinite(x) & Q.positive(y), True, "P3: oo**y = oo"),
    (Q.zero(x ** y), Q.infinite(x) & Q.negative(y), True, "P3: 0 for y < 0"),
    (Q.negative_infinite(x ** y), Q.negative_infinite(x) & Q.odd(y) & Q.positive(y), True, "P3: (-1)**y = -1"),
    (Q.extended_real(x ** y), Q.negative_infinite(x) & Q.positive(y) & ~Q.integer(y), False,
     "P3: direction exp(I*pi*y) not real"),
    (Q.finite(x ** y), Q.infinite(x) & Q.imaginary(y), None, "no row for a non-real exponent"),
    (Q.zero(2 ** x), Q.negative_infinite(x), True, "P4: 2**(-oo) = 0"),
    (Q.positive_infinite(2 ** x), Q.positive_infinite(x), True, "P4: 2**oo = oo"),
    (Q.extended_real((-2) ** x), Q.positive_infinite(x), False, "P4: (-2)**oo = zoo"),
    (Q.finite(Rational(1, 2) ** x), Q.extended_positive(x), True, "finite, or P4: (1/2)**oo = 0"),
    (Q.positive(x ** y), Q.zero(x - 1) & Q.positive_infinite(y), False, "P5: 1**oo = nan"),
    (Q.zero(x ** y), Q.infinite(x) & Q.negative_infinite(y), True, "P6: 0"),
    (Q.real(Pow(S.NaN, x, evaluate=False)), ~Q.zero(x), False, "N1: nan"),
    (Q.real(Pow(S.NaN, x, evaluate=False)), True, None, "nan**0: N1 says nan, SymPy's convention 1; free"),
    (Q.real(Pow(x, S.NaN, evaluate=False)), True, False, "N1: nan"),
    (Q.prime(x ** y), Q.prime(x) & Eq(y, 1), True, "b**1 = b"),
    (Q.finite(x ** y), Q.nonzero(x) & Q.real(y), True, "exp(y*log(x)) is finite"),
    (Q.finite(x ** y), Q.positive(y) & Q.real(x), True, "0**y = 0, else finite"),
    (Q.zero(x ** y), Q.complex(x) & Q.complex(y) & ~Q.zero(x), False, "exp(w) != 0"),
    # positive and negative bases, real exponents
    (Q.positive(x ** y), Q.positive(x) & Q.real(y), True, "exp of a real"),
    (Q.real(x ** y), Q.positive(x), None, "y = I"),
    (Q.positive(x ** y - 1), Q.positive(x - 1) & Q.positive(y), True, "y*log(x) > 0"),
    (Q.real(x ** y), Q.negative(x) & Q.real(y) & ~Q.integer(y), False, "sin(pi*y) != 0"),
    (Q.positive(x ** y), Q.negative(x) & Q.real(y), None, "y = 2, y = 1"),
    (Q.imaginary(x ** y), Q.negative(x) & Q.real(y) & ~Q.rational(y), False, "cos(pi*y) = 0 only on 1/2 + Z"),
    (Q.imaginary(x ** y), Q.negative(x) & Q.rational(y) & ~Q.integer(2 * y), False, "2*y is no odd integer"),
    (Q.negative(x ** Float(1.4)), Q.real(x), False, "1.4 +- ulp holds no integer: (-1)**y not real"),
    (Q.real(x ** Float(2.0)), Q.negative(x), None, "the interval of 2.0 holds 2"),
    # rational exponents
    (Q.irrational(sqrt(2)), True, True, "2 is no square of a rational"),
    (Q.algebraic(sqrt(2)), True, True, "a root of x**2 - 2"),
    (Q.positive(sqrt(2) - 1), True, True, "s**2 = 2, s > 0"),
    (Q.integer(Pow(8, Rational(2, 3), evaluate=False)), True, True, "8 = 2**3: 2**2 = 4"),
    (Q.rational(2 ** Rational(1, 3)), True, False, "2 is no cube"),
    (Q.algebraic(3 ** Rational(17, 62)), True, True, "a root of x**62 - 3**17"),
    (Q.zero(sqrt(x) - 2), Eq(x, 4), True, "s**2 = 4, re s >= 0"),
    (Q.positive(sqrt(x) - 1), Q.positive(x - 1), True, "log(x)/2 > 0"),
    (Q.zero(sqrt(x)), Q.positive(x), False, "sqrt(x) = 0 iff x = 0"),
    (Q.real(sqrt(x)), Q.negative(x), False, "sqrt(x) = I*sqrt(-x)"),
    (Q.imaginary(sqrt(x)), Q.negative(x), True, "sqrt(x) = I*sqrt(-x)"),
    (Q.real(sqrt(x)), Q.real(x), None, "x = -1"),
    (Q.negative(sqrt(x)), True, False, "re sqrt(x) >= 0; no row makes it -oo"),
    (Q.imaginary(x ** Rational(1, 3)), Q.real(x), False, "x < 0: exp(I*pi/3) has re > 0"),
    (Q.real(x ** Rational(1, 3)), Q.negative(x), False, "exp(I*pi/3) is not real"),
    (Q.imaginary(x ** Rational(1, 4)), Q.negative(x), False, "exp(I*pi/4)"),
    (Q.rational(sqrt(x)), Q.rational(x) & Q.positive(x), None, "x = 4, x = 2"),
    (Q.algebraic(x ** Rational(2, 3)), Q.algebraic(x), True, "a root of t**3 - x**2"),
    (Q.algebraic(sqrt(sin(7))), True, False, "its square sin(7) is transcendental"),
    (Q.transcendental(sqrt(x)), Q.transcendental(x), True, "x = sqrt(x)**2"),
    # integer exponents that are symbols
    (Q.odd((-1) ** k), Q.integer(k), True, "+-1 by parity"),
    (Q.positive((-1) ** k), Q.even(k), True, "(-1)**(2m) = 1"),
    (Q.integer((-1) ** x / 2 - S.Half), Q.integer(x), True, "0 or -1"),
    (Q.integer((-1) ** k), Q.real(k), None, "(-1)**(1/2) = I"),
    (Q.finite((-1) ** (k / 2 + S.Half)), Q.odd(k), True, "+-1"),
    (Q.imaginary(I ** k), Q.odd(k), True, "I**(2m + 1) = I*(-1)**m"),
    (Q.real(I ** k), Q.even(k), True, "I**(2m) = (-1)**m"),
    (Q.positive(x ** k), Q.nonzero(x) & Q.even(k), True, "x**(2m) = (x**m)**2"),
    (Q.negative(x ** k), Q.negative(x) & Q.odd(k), True, "(-1)**k*|x|**k"),
    (Q.negative(x ** k), Q.real(x) & Q.even(k), False, "0, 1, zoo or positive"),
    (Q.imaginary(x ** k), Q.imaginary(x) & Q.odd(k), True, "I**k*s**k"),
    (Q.real(x ** k), Q.imaginary(x) & Q.even(k), True, "I**k*s**k"),
    (Q.imaginary(x ** k), Q.real(x) & Q.integer(k), False, "a real to an integer power"),
    (Q.integer(2 ** k), Q.integer(k) & Q.nonnegative(k), True, "a product of 2s"),
    (Q.integer(2 ** k), Q.integer(k), None, "k = -1"),
    (Q.integer(x ** k), Q.integer(x) & Q.integer(k) & Q.negative(k) & ~Q.zero(x - 1) & ~Q.zero(x + 1), False,
     "0 < |x**k| <= 1/2, or zoo at 0"),
    (Q.even(x ** k), Q.even(x) & Q.integer(k) & Q.positive(k), True, "a multiple of x"),
    (Q.odd(x ** k), Q.odd(x) & Q.integer(k) & Q.nonnegative(k), True, "a product of odd numbers"),
    (Q.prime(4 ** x), Q.integer(x), False, "4, 1, a multiple of 4 or no integer"),
    (Q.prime(x ** k), Q.composite(x) & Q.integer(k), False, "x, 1, a power with factor x, or no integer"),
    (Q.prime(2 ** k), Q.integer(k), None, "2**1 = 2"),
    (Q.rational(x ** k), Q.rational(x) & Q.nonzero(x) & Q.integer(k), True, "field operations"),
    (Q.algebraic(pi ** k), Q.integer(k) & Q.nonzero(k), False, "pi would be algebraic"),
    # literal and imaginary bases
    (Q.real(I ** I), True, True, "exp(I*log(I)) = exp(-pi/2)"),
    (Q.transcendental(I ** I), True, True, "Gelfond-Schneider"),
    (Q.real((-1) ** I), True, True, "exp(-pi)"),
    (Q.imaginary((3 * I) ** I), True, False, "exp(-pi/2)*exp(I*log(3)), cos(log 3) > 0"),
    (Q.imaginary(I ** (3 + I)), True, True, "I**3*I**I = -I*exp(-pi/2)"),
    (Q.real(I ** (2 + I)), True, True, "-exp(-pi/2)"),
    (Q.real(2 ** I), True, False, "exp(I*log 2), 0 < log 2 < pi"),
    (Q.transcendental(2 ** I), True, True, "Gelfond-Schneider"),
    (Q.real(I ** x), Q.imaginary(x), True, "exp(-pi*s/2)"),
    (Q.imaginary(I ** x), Q.even(x), False, "+-1"),
    (Q.rational(2 ** sqrt(2)), True, False, "Gelfond-Schneider"),
    (Q.algebraic(x ** y), Q.algebraic(x) & ~Q.zero(x) & ~Q.zero(x - 1) & Q.algebraic(y) & ~Q.rational(y), False,
     "Gelfond-Schneider"),
    (Q.algebraic(x ** y), Q.algebraic(x) & Q.algebraic(y), None, "y = 1/2; 2**sqrt(2)"),
    # other bases
    (Q.real(exp(x) ** x), Q.imaginary(x), True, "x*log(exp(x)) = I*s*I*arg is real"),
    (Q.imaginary(exp(I * pi * x / 2) ** x), Q.odd(x), True, "(+-I)**x, x odd"),
    # integer literal exponents: the closure facts
    (Q.rational(1 / x), Q.irrational(x), False, "x = 1/(1/x)"),
    (Q.prime(x ** 2), Q.integer(x), False, "x*x"),
    (Q.composite(x ** 2), Q.integer(x) & Q.positive(x - 1), True, "x*x with x >= 2"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer
