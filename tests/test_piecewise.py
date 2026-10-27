"""Piecewise as a chain of branches (decision 17): the value of the first
branch whose condition holds, free where none is selected.  Every expected
answer has its argument next to it (design.md, "The truth standard"); None
marks what stays open."""
import pytest
from sympy import (Abs, Contains, Eq, Interval, Piecewise, Q, Rational, S, exp, im, pi, real_root, sign,
                   symbols)

from z3assume import ask

x, y = symbols("x y")

#: two branches that differ, so an answer depends on which one is taken
STEP = Piecewise((1, x < 0), (2, True))
#: no True branch: SymPy gives nan where no condition holds
PARTIAL = Piecewise((1, x < 0))
#: a condition the encoding has no meaning for: a free Boolean
OPEN = Piecewise((2, Contains(x, Interval(0, 1))), (3, True))

CASES = [
    # (proposition, assumptions, answer, why)
    # the branch is selected by the condition
    (Q.zero(STEP - 2), Q.positive(x), True, "x < 0 is false, the True branch"),
    (Q.zero(STEP - 1), Q.negative(x), True, "x < 0 holds"),
    (Q.zero(STEP - 1), Q.real(x), None, "either branch: 1 for x < 0, 2 for x >= 0"),
    (Q.zero(STEP - 2), Q.zero(x), True, "0 < 0 is false"),
    (Q.positive(STEP), Q.extended_real(x), True, "1 and 2 are both positive"),
    # an order relation between non-reals has no truth value: free
    (Q.zero(STEP - 2), Q.imaginary(x), None, "I < 0 is undefined (SymPy raises), not false"),
    (Q.positive(STEP), Q.imaginary(x), None, "undefined condition: the value is free"),
    # uncovered points are free (SymPy's nan), covered ones are not
    (Q.zero(PARTIAL - 1), Q.negative(x), True, "x < 0 holds"),
    (Q.zero(PARTIAL - 1), Q.positive(x), None, "no branch: free"),
    (Q.real(PARTIAL), Q.real(x), None, "no branch for x >= 0"),
    # a free condition: either branch
    (Q.positive(OPEN), True, True, "2 and 3 are both positive"),
    (Q.zero(OPEN - 2), Q.positive(x) & Q.lt(x, 1), None, "Contains is not encoded: either branch"),
    (Q.zero(OPEN - 3), Q.gt(x, 5), None, "Contains is not encoded: either branch"),
    # branches equal on their pieces give a definite answer, unequal ones do not
    (Q.zero(Piecewise((x, x > 0), (-x, True)) - Abs(x)), Q.real(x), True, "x for x > 0, -x otherwise"),
    (Q.zero(Piecewise((x, x > 0), (-x, True)) - Abs(x)), Q.complex(x), None, "x > 0 undefined off the reals"),
    (Q.zero(Piecewise((x, x > 0), (x + 1, True)) - x), Q.real(x), None, "x + 1 != x for x <= 0"),
    (Q.zero(Piecewise((x, x > 0), (x + 1, True)) - x), Q.real(x) & Q.lt(x, 0), False, "x + 1 for x <= 0"),
    # predicates other than the numeric ones go with the value
    (Q.rational(Piecewise((pi, x > 0), (Rational(1, 3), True))), Q.negative(x), True, "1/3"),
    (Q.rational(Piecewise((pi, x > 0), (Rational(1, 3), True))), Q.positive(x), False, "pi is irrational"),
    (Q.integer(Piecewise((y, x > 0), (Rational(1, 2), True))), Q.positive(x) & Q.integer(y), True, "y"),
    (Q.even(Piecewise((y, x > 0), (Rational(1, 2), True))), Q.positive(x) & Q.odd(y), False, "y is odd"),
    # Eq conditions; Eq at two other infinities or a nan is open
    (Q.zero(Piecewise((0, Eq(x, y)), (1, True))), Q.eq(x, y), True, "Eq holds"),
    (Q.zero(Piecewise((0, Eq(x, y)), (1, True))), Q.ne(x, y), False, "Eq fails"),
    (Q.zero(Piecewise((0, Eq(x, y)), (1, True))), Q.infinite(x) & Q.infinite(y), None, "zoo = zoo is open"),
    # real_root: the real root on the reals, the principal root elsewhere
    (Q.zero(real_root(y, 3) - y ** Rational(1, 3)), Q.positive(y), True, "|y|**(1/3)*sign(y), y > 0"),
    (Q.zero(real_root(y, 3) - y ** Rational(1, 3)), Q.negative(y), False, "the real root, not the principal"),
    (Q.zero(real_root(y, 3) - y ** Rational(1, 3)), Q.real(y), None, "equal for y >= 0 only"),
    (Q.zero(real_root(y, 3) - y ** Rational(1, 3)), Q.imaginary(y), True, "Eq(im(y), 0) fails"),
    (Q.negative(real_root(y, 7)), Q.negative(y), True, "|y|**(1/7)*sign(y) with sign(y) = -1"),
    (Q.zero(real_root(exp(y), 3) - exp(y / 3)), Q.real(y), True, "exp(y/3) > 0 is the real cube root"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_sympy_forms():
    """The SymPy objects reach the encoder in these forms."""
    assert real_root(y, 3) == Piecewise((Abs(y) ** Rational(1, 3) * sign(y), Eq(im(y), 0)),
                                        (y ** Rational(1, 3), True))
    assert PARTIAL.subs(x, 1) is S.NaN
    assert isinstance(OPEN.args[0].cond, Contains)
    with pytest.raises(TypeError):
        STEP.subs(x, S.ImaginaryUnit)
