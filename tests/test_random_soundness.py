"""Randomized soundness check: a definite answer must hold at every point
that satisfies the assumptions.  The points are Gaussian rationals
``a + b*I`` (real rationals for the real test), evaluated exactly with
pairs of ``fractions.Fraction`` (``Abs`` and ``sign`` only where the
modulus is rational, the point is skipped elsewhere).  This is a
falsification test, not a truth standard: it can only find wrong answers,
and SymPy evaluates nothing in it."""
import random
from fractions import Fraction
from math import isqrt

import pytest
from sympy import Abs, Add, Integer, Mul, Pow, Q, Rational, S, conjugate, im, re, sign, symbols

from z3assume import ask

x, y = symbols("x y")
SYMS = (x, y)
PREDS = ("real", "rational", "integer", "positive", "negative", "zero", "nonzero",
         "nonnegative", "nonpositive", "even", "odd", "imaginary")
REAL_POINTS = [Fraction(n) for n in range(-3, 4)] + [Fraction(1, 2), Fraction(-3, 2), Fraction(5, 3)]
POINTS = [(v, Fraction(0)) for v in REAL_POINTS]
COMPLEX_POINTS = [(Fraction(a), Fraction(b)) for a, b in
                  ((0, 0), (1, 0), (-2, 0), (Fraction(1, 2), 0), (0, 1), (0, -2), (3, 4), (-3, 4),
                   (1, 1), (Fraction(3, 5), Fraction(-4, 5)), (Fraction(1, 2), Fraction(3, 2)))]


class Inexact(Exception):
    """The value is not a Gaussian rational (an irrational modulus)."""


def holds(pred, v):
    """The predicate at a Gaussian rational (all of them are decidable)."""
    a, b = v
    real = b == 0
    if pred == "complex":
        return True
    if pred == "real" or pred == "rational":
        return real
    if pred == "imaginary":
        return a == 0 and b != 0
    if not real:
        return False
    return {
        "integer": a.denominator == 1,
        "positive": a > 0, "negative": a < 0, "zero": a == 0, "nonzero": a != 0,
        "nonnegative": a >= 0, "nonpositive": a <= 0,
        "even": a.denominator == 1 and a.numerator % 2 == 0,
        "odd": a.denominator == 1 and a.numerator % 2 == 1,
    }[pred]


def _mul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def _sqrt(q):
    """The rational square root of q >= 0, or Inexact."""
    n, d = isqrt(q.numerator), isqrt(q.denominator)
    if n * n != q.numerator or d * d != q.denominator:
        raise Inexact
    return Fraction(n, d)


def value(e, env):
    """Exact value as a pair; ZeroDivisionError at a pole, Inexact where
    the value is no Gaussian rational."""
    if e in env:
        return env[e]
    if e is S.ImaginaryUnit:
        return (Fraction(0), Fraction(1))
    if isinstance(e, Rational):
        return (Fraction(int(e.p), int(e.q)), Fraction(0))
    if isinstance(e, Add):
        vs = [value(a, env) for a in e.args]
        return (sum((v[0] for v in vs), Fraction(0)), sum((v[1] for v in vs), Fraction(0)))
    if isinstance(e, Mul):
        r = (Fraction(1), Fraction(0))
        for a in e.args:
            r = _mul(r, value(a, env))
        return r
    if isinstance(e, Pow):
        b, n = value(e.base, env), int(e.exp)
        if n < 0:
            norm = b[0] ** 2 + b[1] ** 2
            b = (b[0] / norm, -b[1] / norm)     # ZeroDivisionError at 0
        r = (Fraction(1), Fraction(0))
        for _ in range(abs(n)):
            r = _mul(r, b)
        return r
    if e.func in (Abs, re, im, conjugate, sign):
        a, b = value(e.args[0], env)
        if e.func is re:
            return (a, Fraction(0))
        if e.func is im:
            return (b, Fraction(0))
        if e.func is conjugate:
            return (a, -b)
        m = _sqrt(a * a + b * b)
        if e.func is Abs:
            return (m, Fraction(0))
        return (a / m, b / m) if m else (Fraction(0), Fraction(0))
    raise TypeError(e)


UNARY = (Abs, re, im, conjugate, sign)


def random_expr(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice([x, y, x, y, Integer(rng.randint(-3, 3))])
    op = rng.choice(["add", "mul", "pow", "sub", "unary"])
    a, b = random_expr(rng, depth - 1), random_expr(rng, depth - 1)
    if op == "add":
        return a + b
    if op == "sub":
        return a - b
    if op == "mul":
        return a * b
    if op == "unary":
        return rng.choice(UNARY)(a)
    e = a ** rng.choice([2, 3, -1, -2])
    return random_expr(rng, depth) if e.has(S.ComplexInfinity, S.NaN) else e


def random_query(rng, base):
    facts = [(rng.choice(PREDS), rng.choice(SYMS + (random_expr(rng, 1),))) for _ in range(rng.randint(1, 3))]
    facts += [(base, x), (base, y)]
    return (rng.choice(PREDS), random_expr(rng, 3)), facts


def check_point(prop, facts, env):
    try:
        if not all(holds(p, value(e, env)) for p, e in facts):
            return None
        return holds(prop[0], value(prop[1], env))
    except (ZeroDivisionError, Inexact):
        return None


def run(seed, base, points, n):
    rng = random.Random(seed)
    definite = 0
    for _ in range(n):
        (pred, e), facts = random_query(rng, base)
        if not e.free_symbols:
            continue
        a = S.true
        for p, t in facts:
            a = a & getattr(Q, p)(t)
        envs = [{x: vx, y: vy} for vx in points for vy in points]
        try:
            r = ask(getattr(Q, pred)(e), a)
        except ValueError:
            # inconsistent: no point may satisfy the facts
            for env in envs:
                assert check_point((pred, e), facts, env) is None, (pred, e, facts, env)
            continue
        if r is None:
            continue
        definite += 1
        for env in envs:
            v = check_point((pred, e), facts, env)
            assert v is None or v is r, (pred, e, facts, env)
    assert definite > 0


@pytest.mark.parametrize("seed", range(8))
def test_definite_answers_hold_at_rational_points(seed):
    run(seed, "real", POINTS, 25)


@pytest.mark.parametrize("seed", range(4))
def test_definite_answers_hold_at_gaussian_rational_points(seed):
    run(100 + seed, "complex", COMPLEX_POINTS, 20)
