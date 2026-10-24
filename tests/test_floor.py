"""floor, ceiling and frac (issue #18): exact on the parts of a finite
argument, SymPy's complex generalization ``floor(a + b*I) = floor(a) +
floor(b)*I``; ``+-oo``, ``zoo`` keep their kind, ``nan`` gives ``nan``.
Every expected answer has its argument next to it (design.md, "The truth
standard"); None marks what stays open."""
import math
import random
from fractions import Fraction

import pytest
from sympy import I, Q, Rational, S, ceiling, floor, frac, im, pi, re, sqrt, symbols

from z3assume import ask

x, y = symbols("x y")
half = Rational(1, 2)

CASES = [
    # (proposition, assumptions, answer, why)
    # the value: finite exactly at a finite argument
    (Q.finite(floor(x)), Q.finite(x), True, "each part rounds to a finite integer"),
    (Q.finite(ceiling(y)), Q.finite(y), True, "each part rounds to a finite integer"),
    (Q.finite(floor(x)), Q.infinite(x), False, "an infinity keeps its kind"),
    (Q.finite(floor(x)), True, None, "x = 1 or x = oo"),
    (Q.positive_infinite(floor(x)), Q.positive_infinite(x), True, "floor(oo) = oo (satassume integer_funcs)"),
    (Q.negative_infinite(ceiling(x)), Q.negative_infinite(x), True, "ceiling(-oo) = -oo"),
    (Q.extended_real(floor(x)), Q.infinite(x) & ~Q.extended_real(x), False, "floor(zoo) = zoo, no extended real"),
    (Q.real(floor(S.NaN, evaluate=False)), True, False, "N1: nan, no number (V1)"),
    # integer and real
    (Q.integer(floor(x)), Q.real(x), True, "the greatest integer <= x"),
    (Q.integer(ceiling(x)), Q.real(x), True, "the least integer >= x"),
    (Q.integer(floor(x)), Q.extended_real(x), None, "x = oo"),
    (Q.integer(floor(x)), Q.complex(x), None, "floor(I) = I"),
    (Q.integer(floor(x)), True, None, "x = oo"),
    (Q.integer(re(floor(y))), Q.finite(y), True, "re(floor(y)) = floor(re(y))"),
    (Q.integer(im(floor(y))), Q.finite(y), True, "im(floor(y)) = floor(im(y))"),
    (Q.integer(re(ceiling(y))), Q.finite(y), True, "re(ceiling(y)) = ceiling(re(y))"),
    (Q.integer(im(ceiling(y))), Q.finite(y), True, "im(ceiling(y)) = ceiling(im(y))"),
    (Q.real(floor(x)), Q.complex(x) & Q.real(x * I), None, "floor(I/2) = 0, floor(I) = I"),
    (Q.algebraic(floor(x)), Q.finite(x), True, "a Gaussian integer is algebraic"),
    (Q.rational(floor(x)), Q.finite(x), None, "floor(I) = I is not rational"),
    (Q.integer(floor(x / pi + half)), Q.real(x), True, "a finite real argument"),
    (Q.integer(floor(x / pi + half)), Q.ge(x, -pi / 2) & Q.le(x, pi / 2), True, "x is a finite real"),
    (Q.finite(x - 2 * pi * floor(x / (2 * pi) + half)), Q.real(x), True, "finite parts"),
    # values
    (Q.zero(floor(x)), Q.ge(x, 0) & Q.lt(x, 1), True, "0 <= x < 1"),
    (Q.zero(ceiling(x)), Q.gt(x, -1) & Q.le(x, 0), True, "-1 < x <= 0"),
    (Q.zero(floor(x)), Q.ge(x, 0) & Q.le(x, 1), None, "x = 1"),
    (Q.nonnegative(x - floor(x)), Q.real(x), True, "floor(x) <= x"),
    (Q.positive(floor(x) + 1 - x), Q.real(x), True, "x < floor(x) + 1"),
    (Q.nonnegative(ceiling(x) - x), Q.real(x), True, "x <= ceiling(x)"),
    (Q.nonnegative(ceiling(x) - floor(x) - 1), Q.real(x) & ~Q.integer(x), True, "ceiling = floor + 1 off Z"),
    (Q.zero(ceiling(x) - floor(x)), Q.integer(x), True, "both are x"),
    (Q.zero(floor(x) - x), Q.integer(x), True, "floor(n) = n"),
    (Q.zero(ceiling(x) + floor(-x)), Q.real(x), True, "ceiling(x) = -floor(-x)"),
    (Q.even(floor(x)), Q.even(x), True, "floor(n) = n"),
    (Q.odd(ceiling(2 * x)), Q.integer(x - half), True, "x = m + 1/2: 2*x = 2*m + 1"),
    (Q.even(floor(x / 2)), Q.integer(x), None, "floor(1) = 0, floor(3/2) = 1"),
    (Q.positive(floor(x)), Q.positive(x), None, "floor(1/2) = 0"),
    (Q.nonnegative(floor(x)), Q.positive(x), True, "x > 0 > -1"),
    (Q.negative(floor(x)), Q.negative(x), True, "floor(x) <= x < 0"),
    (Q.positive(ceiling(x)), Q.positive(x), True, "ceiling(x) >= x > 0"),
    (Q.prime(floor(x)), Q.gt(x, 2) & Q.lt(x, 3), True, "floor = 2"),
    (Q.integer(floor(sqrt(2))), True, True, "a finite real"),
    (Q.zero(floor(pi) - 3), True, True, "3 < pi < 4"),
    (Q.zero(ceiling(pi) - 4), True, True, "3 < pi < 4"),
    # complex arguments
    (Q.real(floor(x)), Q.real(x - I / 2), True, "x = a + I/2: floor(1/2) = 0, so floor(x) = floor(a)"),
    (Q.integer(floor(x)), Q.real(x - I / 2), True, "x = a + I/2: floor(1/2) = 0, so floor(x) = floor(a)"),
    (Q.integer(floor(x)), Q.real(x + I / 2), False, "x = a - I/2: floor(-1/2) = -1, floor(x) = floor(a) - I"),
    (Q.integer(ceiling(x)), Q.real(x - I / 2), False, "ceiling(1/2) = 1: ceiling(a) + I"),
    (Q.integer(ceiling(x)), Q.real(x + I / 2), True, "ceiling(-1/2) = 0: ceiling(a)"),
    (Q.imaginary(floor(x)), Q.imaginary(x) & Q.imaginary(x - I), None, "x = 3*I/2 -> I; x = I/2 -> 0"),
    (Q.zero(re(floor(x))), Q.imaginary(x), True, "floor(0) = 0"),
    # frac
    (Q.nonnegative(frac(x)), Q.real(x), True, "0 <= x - floor(x)"),
    (Q.negative(frac(x) - 1), Q.real(x), True, "x - floor(x) < 1"),
    (Q.zero(frac(x)), Q.integer(x), True, "frac(n) = 0"),
    (Q.zero(frac(x)), Q.real(x) & ~Q.integer(x), False, "x is no integer"),
    (Q.zero(frac(x)), Q.real(x), None, "x = 1/2 or x = 1"),
    (Q.rational(frac(x)), Q.rational(x), True, "x - floor(x), both rational"),
    (Q.irrational(frac(x)), Q.irrational(x), True, "x - floor(x) for real x"),
    (Q.algebraic(frac(x)), Q.finite(x) & ~Q.algebraic(x), False, "z = frac(z) + floor(z)"),
    (Q.rational(frac(x)), Q.complex(x) & ~Q.rational(x), None, "frac(1/2 + I) = 1/2"),
    (Q.finite(frac(x)), Q.infinite(x), None, "frac(oo): no value (free)"),
    (Q.real(frac(x)), Q.extended_real(x), None, "frac(oo): no value (free)"),
]

@pytest.mark.parametrize("prop, assumptions, expected, why", CASES)
def test_case(prop, assumptions, expected, why):
    assert ask(prop, assumptions) is expected, why


# -- a randomized check against exact values at Gaussian-rational points --

def value(e, env):
    """The exact value ``(re, im)`` (Fractions) of ``e`` at ``env``."""
    if e in env:
        return env[e]
    if e.is_Rational:
        return Fraction(int(e.p), int(e.q)), Fraction(0)
    if e is S.ImaginaryUnit:
        return Fraction(0), Fraction(1)
    vs = [value(a, env) for a in e.args]
    if e.is_Add:
        return sum(v[0] for v in vs), sum(v[1] for v in vs)
    if e.is_Mul:
        r = (Fraction(1), Fraction(0))
        for v in vs:
            r = (r[0] * v[0] - r[1] * v[1], r[0] * v[1] + r[1] * v[0])
        return r
    if e.is_Pow and e.exp.is_Integer and e.exp > 0:
        r = (Fraction(1), Fraction(0))
        for _ in range(int(e.exp)):
            r = (r[0] * vs[0][0] - r[1] * vs[0][1], r[0] * vs[0][1] + r[1] * vs[0][0])
        return r
    (a, b), = vs
    if isinstance(e, floor):
        return Fraction(math.floor(a)), Fraction(math.floor(b))
    if isinstance(e, ceiling):
        return Fraction(math.ceil(a)), Fraction(math.ceil(b))
    if isinstance(e, frac):
        return a - math.floor(a), b - math.floor(b)
    raise NotImplementedError(e)


def holds(pred, v):
    a, b = v
    if pred == "real":
        return b == 0
    if pred == "imaginary":
        return a == 0 and b != 0
    if b != 0:
        return False
    if pred in ("integer", "even", "odd"):
        if a.denominator != 1:
            return False
        return {"integer": True, "even": a % 2 == 0, "odd": a % 2 == 1}[pred]
    return {"positive": a > 0, "negative": a < 0, "zero": a == 0,
            "nonnegative": a >= 0, "nonpositive": a <= 0}[pred]


PREDS = ["real", "imaginary", "integer", "even", "odd", "positive", "negative", "zero", "nonnegative"]
POINTS = [Fraction(n, d) for n in range(-5, 6) for d in (1, 2, 3)]


def random_expr(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice([x, y, x, y, Rational(rng.randint(-3, 3), rng.choice([1, 2, 3])), I / 2])
    op = rng.choice(["add", "mul", "floor", "ceiling", "frac", "floor"])
    a = random_expr(rng, depth - 1)
    if op in ("floor", "ceiling", "frac"):
        return {"floor": floor, "ceiling": ceiling, "frac": frac}[op](a)
    b = random_expr(rng, depth - 1)
    return a + b if op == "add" else a * b


@pytest.mark.parametrize("seed", range(6))
def test_definite_answers_hold_exactly(seed):
    rng = random.Random(seed)
    definite = 0
    for _ in range(40):
        e = random_expr(rng, 3)
        if not e.free_symbols or not e.has(floor, ceiling, frac):
            continue
        base = rng.choice(["real", "complex", "rational"])
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
        ims = [Fraction(0)] if base != "complex" else [Fraction(0), Fraction(1, 2), Fraction(-3, 2)]
        for px in POINTS:
            for py in POINTS[::4]:
                for ix in ims:
                    env = {x: (px, ix), y: (py, ims[-1])}
                    if not holds(fact[0], env[fact[1]]):
                        continue
                    assert holds(pred, value(e, env)) is r, (pred, e, a, env)
    assert definite > 0
