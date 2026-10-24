"""Abs, re, im, conjugate and sign, exact on the pair encoding.  Every
expected answer has its argument next to it (design.md, "The truth
standard"); "free" marks a value no written convention fixes."""
import pytest
from sympy import (Abs, E, I, Q, Rational, conjugate, im, nan, oo, pi, re, sign, sqrt, symbols,
                   zoo)

from z3assume import ask

x, y, k = symbols("x y k")

CASES = [
    # (proposition, assumptions, answer, why)
    # Abs: |a + b*I| = sqrt(a**2 + b**2); oo for every infinity (F3)
    (Q.negative(Abs(x)), True, False, "|z| >= 0, |infinity| = oo, x is not nan"),
    (Q.extended_nonnegative(Abs(x)), True, True, "|z| >= 0 or oo"),
    (Q.real(Abs(x)), Q.complex(x), True, "sqrt(a**2 + b**2) is real"),
    (Q.real(Abs(x)), True, None, "x = oo: Abs(oo) = oo"),
    (Q.positive_infinite(Abs(x)), Q.infinite(x), True, "special-values F3, zoo and oo*I included"),
    (Q.positive(Abs(x)), Q.nonzero(x), True, "a != 0"),
    (Q.positive(Abs(x)), Q.imaginary(x), True, "b != 0"),
    (Q.zero(Abs(x)), Q.zero(x), True, "|0| = 0"),
    (Q.zero(x), Q.zero(Abs(x)), True, "a**2 + b**2 = 0"),
    (Q.zero(1 / Abs(x)), Q.real(x), False, "1/|x| is 1/positive or 1/0 = zoo"),
    (Q.zero(1 / Abs(x)), Q.infinite(x), True, "1/oo = 0"),
    (Q.integer(Abs(x)), Q.integer(x), True, "|k| = +-k"),
    (Q.integer(x), Q.integer(Abs(x)) & Q.real(x), True, "x = +-|x|"),
    (Q.integer(Abs(x)), Q.complex(x), None, "|1 + I| = sqrt(2), |3 + 4*I| = 5"),
    (Q.even(Abs(x)), Q.even(x), True, "|k| = +-k, -2m = 2(-m)"),
    (Q.odd(Abs(x)), Q.odd(x), True, "-(2m + 1) = 2(-m - 1) + 1"),
    (Q.prime(Abs(x)), Q.prime(x), True, "a prime is positive, |p| = p"),
    (Q.prime(Abs(x)), Q.integer(x), None, "|-2| = 2, |1| = 1"),
    (Q.rational(Abs(x)), Q.rational(x), True, "rational means real, |q| = +-q"),
    (Q.irrational(Abs(x)), Q.irrational(x), True, "x = +-|x|"),
    (Q.rational(Abs(x)), Q.complex(x) & Q.algebraic(x), None, "|1 + I| = sqrt(2), |1| = 1"),
    (Q.algebraic(Abs(x)), Q.algebraic(x), True, "|z| = sqrt(z*conj(z)), conjugation is a Galois action"),
    (Q.transcendental(Abs(x)), Q.transcendental(x) & Q.real(x), True, "x = +-|x|"),
    (Q.transcendental(Abs(x)), Q.transcendental(x), None, "|exp(I)| = 1, |pi| = pi"),
    (Q.nonnegative(Abs(x) - re(x)), Q.complex(x), True, "sqrt(a**2 + b**2) >= a"),
    (Q.positive(Abs(x) - re(x)), Q.complex(x) & ~Q.real(x), True, "b != 0"),
    (Q.zero(sign(x) * Abs(x) - x), Q.complex(x), True, "z = sign(z)*|z| for finite z"),
    (Q.zero(Abs(x) - 1), Q.complex(x) & Q.zero(re(x) ** 2 + im(x) ** 2 - 1), True, "|z|**2 = a**2 + b**2"),
    (Q.zero(Abs(x - y)), Q.real(x) & Q.real(y) & Q.eq(x, y), True, "|0| = 0"),
    (Q.negative(Abs(x) + y), Q.positive(y), False, "|x| >= 0 or oo"),
    (Q.zero(Abs(nan)), True, False, "N1: Abs(nan) = nan, no number"),
    (Q.finite(Abs(x)), Q.finite(x), True, "sqrt(a**2 + b**2)"),
    (Q.finite(Abs(x - x * oo)), Q.positive(x), False, "x - oo*x = -oo (A1, M2), Abs(-oo) = oo"),
    # re, im: a, b; re(+-oo) = +-oo, im(+-oo) = 0 (limits along t*d, V2)
    (Q.zero(im(x)), Q.real(x), True, "b = 0"),
    (Q.even(im(x)), Q.real(x), True, "im(x) = 0"),
    (Q.zero(im(x)), Q.extended_real(x), True, "im(+-oo) = 0"),
    (Q.zero(im(x)), True, None, "im(I) = 1; im(oo*I) = oo"),
    (Q.real(re(x)), Q.complex(x), True, "a is real"),
    (Q.real(im(x)), Q.complex(x), True, "b is real"),
    (Q.finite(re(x)), True, None, "re(oo) = oo"),
    (Q.positive_infinite(re(x)), Q.positive_infinite(x), True, "re(oo) = oo"),
    (Q.negative_infinite(conjugate(x)), Q.negative_infinite(x), True, "conjugate(-oo) = -oo"),
    (Q.finite(re(x)), Q.infinite(x) & ~Q.extended_real(x), None, "re(oo*I) = 0, re(oo*(1 + I)) = oo"),
    (Q.finite(re(zoo, evaluate=False)), True, None, "re(zoo) = nan, and finite(nan) is open (row V1)"),
    (Q.zero(re(zoo, evaluate=False)), True, None, "re(zoo) = nan, re(oo*I) = 0: the kind does not tell them apart"),
    (Q.zero(im(oo)), True, True, "im(oo) = 0"),
    (Q.even(re(x)), Q.even(x), True, "re(x) = x for real x"),
    (Q.prime(re(x)), Q.prime(x), True, "re(x) = x for real x"),
    (Q.zero(re(x)), Q.imaginary(x), True, "imaginary: a = 0"),
    (Q.positive(im(x)), Q.imaginary(x), None, "I and -I"),
    (Q.rational(re(x)), Q.rational(x), True, "re(q) = q"),
    (Q.algebraic(re(x)), Q.algebraic(x), True, "(z + conj(z))/2"),
    (Q.algebraic(im(x)), Q.algebraic(x), True, "(z - conj(z))/(2*I)"),
    (Q.rational(re(x)), Q.algebraic(x), None, "re(sqrt(2)) and re(1)"),
    (Q.zero(im(nan)), True, False, "N1: im(nan) = nan"),
    (Q.zero(re(x) - x), Q.real(x), True, "re(x) = x for real x"),
    (Q.zero(re(x * y) - re(x) * re(y) + im(x) * im(y)), Q.complex(x) & Q.complex(y), True,
     "re((a + bI)(c + dI)) = ac - bd"),
    (Q.integer(im(x) / pi), Q.real(x), True, "0/pi = 0"),
    # conjugate: a - b*I; conjugate(+-oo) = +-oo
    (Q.zero(x * conjugate(x) - Abs(x) ** 2), Q.complex(x), True, "z*conj(z) = a**2 + b**2"),
    (Q.real(x + conjugate(x)), Q.complex(x), True, "2a"),
    (Q.imaginary(conjugate(x)), Q.imaginary(x), True, "-b*I, b != 0"),
    (Q.algebraic(x), Q.algebraic(conjugate(x)) & Q.complex(x), True, "conjugation is an involution"),
    (Q.odd(conjugate(x)), Q.odd(x), True, "conjugate(x) = x for real x"),
    (Q.finite(conjugate(x)), Q.infinite(x), False, "conjugation keeps the kind of an infinity (decision 7)"),
    (Q.extended_real(conjugate(x)), Q.infinite(x) & ~Q.extended_real(x), False, "conjugate(zoo) = zoo"),
    (Q.extended_real(conjugate(x)), Q.extended_real(x), True, "conjugate(+-oo) = +-oo"),
    # sign: 0 at 0, else z/|z|; sign(+-oo) = +-1
    (Q.integer(sign(x)), Q.real(x), True, "-1, 0 or 1"),
    (Q.integer(sign(x)), Q.extended_real(x), True, "sign(+-oo) = +-1"),
    (Q.integer(sign(x)), True, None, "sign(I) = I"),
    (Q.odd(sign(x)), Q.nonzero(x), True, "+-1"),
    (Q.zero(sign(x)), Q.zero(x), True, "sign(0) = 0"),
    (Q.zero(sign(x)), ~Q.zero(x), False, "z/|z| for finite z != 0; sign(zoo) = nan, sign(oo*u) = u (decision 7)"),
    (Q.finite(sign(x)), Q.positive(re(x)), True, "re(x) > 0 rules out every infinity (re(zoo) = nan)"),
    (Q.finite(sign(x)), ~Q.zero(im(x)), None, "x = zoo: im(zoo) = nan is not 0, sign(zoo) = nan"),
    (Q.real(re(x)), Q.infinite(x) & ~Q.extended_real(x), None, "re(oo*I) = 0, re(oo*(1 + I)) = oo"),
    (Q.positive(sign(x)), Q.positive_infinite(x), True, "sign(oo) = 1"),
    (Q.negative(sign(x)), Q.negative(x), True, "-1"),
    (Q.imaginary(sign(x)), Q.imaginary(x), True, "b*I/|b|"),
    (Q.zero(Abs(sign(x)) - 1), Q.complex(x) & ~Q.zero(x), True, "|z/|z|| = 1"),
    (Q.zero(sign(1 / x)), Q.real(x), False, "x = 0: sign(zoo) is nan (decision 7), else 1/x != 0"),
    (Q.zero(sign(1 / x)), Q.real(x) & Q.nonzero(x), False, "1/x != 0"),
    (Q.zero(sign(1 / x)), Q.infinite(x), True, "1/oo = 0"),
    (Q.algebraic(sign(x)), Q.algebraic(x), True, "z/|z|"),
    (Q.algebraic(sign(x)), Q.complex(x), None, "sign(exp(I)) = exp(I)"),
    (Q.zero(sign(nan)), True, False, "N1: sign(nan) = nan"),
    # constants (evaluated by SymPy, so these mostly check the evaluation agrees)
    (Q.positive(Abs(k) - Rational(1, 2)), Q.odd(k), True, "|odd| >= 1"),
    (Q.zero(re(x) - Rational(1, 2)), Q.rational(x) & Q.zero(x - Rational(1, 2)), True, "re(1/2) = 1/2"),
    (Q.irrational(Abs(x)), Q.zero(x - sqrt(2)) & Q.irrational(x), True, "x = +-|x|"),
    (Q.negative(Abs(x) - pi), Q.zero(x - 3), True, "3 < pi"),
    (Q.transcendental(Abs(x)), Q.zero(x - E), True, "|E| = E, Hermite"),
    (Q.zero(re(x * I)), Q.real(x), True, "re(x*I) = 0 for real x"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_symbolic_arguments_stay_terms():
    # SymPy leaves these unevaluated, so the encoding (not SymPy) decides them
    assert Abs(x).func is Abs and re(x).func is re and sign(x).func is sign
    assert ask(Q.nonnegative(Abs(x)), Q.complex(x)) is True
