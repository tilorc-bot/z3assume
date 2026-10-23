"""Floats: a finite real with its exact sign, strictly within one unit in
the last place (at its precision) of its binary value, and nothing else
(design.md, "Terms" and open question 2).  Every expected answer has its
argument next to it (design.md, "The truth standard")."""
from sympy import Add, Float, Mul, Q, Rational, S, oo, nan, pi, symbols

import pytest

from z3assume import ask

x, k = symbols("x k")
f = Float(0.1)          # binary value v = 0.1000000000000000055..., 53 bits

CASES = [
    # (proposition, assumptions, answer, why)
    (Q.positive(Float(0.5)), True, True, "the sign of a nonzero mpf is exact"),
    (Q.negative(Float(-2.5)), True, True, "the sign of a nonzero mpf is exact"),
    (Q.nonzero(Float(1e-300)), True, True, "a nonzero mpf: only 0 rounds to 0"),
    (Q.zero(Float(0)), True, True, "the zero mpf is 0"),
    (Q.integer(Float(0)), True, True, "the zero mpf is 0, an integer"),
    (Q.finite(Float(3.0)), True, True, "a Float is a finite real"),
    (Q.real(f), True, True, "a Float is a finite real"),
    (Q.extended_real(f), True, True, "a Float is a finite real"),
    (Q.imaginary(f), True, False, "a Float is real"),
    (Q.integer(Float(1.0)), True, None, "the interval holds 1 and non-integers"),
    (Q.integer(Float(0.5)), True, False, "(0.5 - 2**-53, 0.5 + 2**-53) holds no integer"),
    (Q.even(Float(2.0)), True, None, "the interval holds 2 and non-integers"),
    (Q.prime(Float(2.0)), True, None, "the interval holds 2 and non-integers"),
    (Q.rational(Float(1.0)), True, None, "every interval holds rationals and irrationals"),
    (Q.rational(f), True, None, "every interval holds rationals and irrationals"),
    (Q.irrational(f), True, None, "every interval holds rationals and irrationals"),
    (Q.algebraic(f), True, None, "every interval holds algebraic and transcendental reals"),
    (Q.transcendental(f), True, None, "every interval holds algebraic and transcendental reals"),
    (Q.eq(f, Rational(1, 10)), True, None, "1/10 rounds to 0.1 at 53 bits: in the interval"),
    (Q.lt(f, Rational(1, 10)), True, None, "1/10 is inside the interval"),
    (Q.gt(f, Rational(1, 10)), True, None, "SymPy's exact compare says True; 1/10 rounds to it"),
    (Q.lt(f, Rational(11, 100)), True, True, "v + 2**-56 < 0.11"),
    (Q.ne(f, Rational(1, 5)), True, True, "1/5 is outside the interval"),
    (Q.eq(Float(0.5, 15), Float(0.5, 30)), True, None,
     "two precisions are two Floats, each an unknown in its own interval"),
    (Q.zero(Add(f, Mul(-1, f, evaluate=False), evaluate=False)), True, True,
     "one Float object is one value: f - f = 0"),
    (Q.lt(Float(3.14159265358979), pi), True, True, "v + 2**-51 < 3.1415926535897905 < pi"),
    (Q.lt(Float(3.141592653589793), pi), True, None, "pi rounds to it at 53 bits"),
    (Q.positive(Float("1e100000")), True, True, "beyond the exponent bound only the sign is kept"),
    (Q.integer(Float("1e100000")), True, None, "beyond the exponent bound only the sign is kept"),
    (Q.negative(Float(2, 5000)), True, False, "beyond the precision bound only the sign is kept"),
    (Q.integer(Float(2, 5000)), True, None, "beyond the precision bound only the sign is kept"),
    (Q.positive(Float("0.3", 3)), True, True, "13 bits: (4914, 4916)/2**14"),
    (Q.lt(Float("0.3", 3), Rational(3, 10)), True, None, "4914/2**14 < 0.3 < 4916/2**14"),
    (Q.lt(Float("0.3", 3), Rational(3001, 10000)), True, True, "4916/2**14 = 0.30004... < 0.3001"),
    (Q.positive(x + Float(0.5)), Q.positive(x), True, "positive plus positive"),
    (Q.lt(x, Float(0.5)), Q.lt(x, S.Half), None, "the Float may lie below 1/2"),
    (Q.lt(x, Float(0.6)), Q.lt(x, S.Half), True, "the Float lies above 0.59"),
    (Q.integer(Float(2.0) * k), Q.integer(k), None, "2.0 may not be 2"),
    (Q.zero(Float(2.0) * x), Q.nonzero(x), False, "no zero divisors"),
    (Q.rational(f), Q.eq(f, Rational(1, 10)), True, "equal values: 1/10 is rational"),
    (Q.rational(f), Q.eq(f, x), None, "x is any value in the interval"),
    (Q.eq(f, pi / 31), True, False, "pi/31 > 3.14/31 > 0.101 is outside the interval"),
    (Q.eq(f, pi - 3), True, False, "pi - 3 > 0.14 is outside the interval"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_inf_and_nan_floats_are_sympys_objects():
    # Float('inf') and Float('nan') are not Floats; they are encoded as oo, nan
    assert Float("inf") is oo and Float("-inf") is -oo and Float("nan") is nan
    assert ask(Q.infinite(Float("inf"))) is True
