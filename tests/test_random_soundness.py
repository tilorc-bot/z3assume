"""Randomized soundness check of the slice: a definite answer must hold at
every rational point that satisfies the assumptions.  The points are
evaluated with exact rational arithmetic (``fractions``), which is a
falsification test, not a truth standard: it can only find wrong answers."""
import random
from fractions import Fraction

import pytest
from sympy import Add, Integer, Mul, Pow, Q, Rational, S, symbols

from z3assume import ask

x, y = symbols("x y")
SYMS = (x, y)
PREDS = ("real", "rational", "integer", "positive", "negative", "zero", "nonzero",
         "nonnegative", "nonpositive", "even", "odd")
POINTS = [Fraction(n) for n in range(-3, 4)] + [Fraction(1, 2), Fraction(-3, 2), Fraction(5, 3)]


def holds(pred, v):
    """The predicate at a rational value (all of them are decidable)."""
    return {
        "real": True, "rational": True,
        "integer": v.denominator == 1,
        "positive": v > 0, "negative": v < 0, "zero": v == 0, "nonzero": v != 0,
        "nonnegative": v >= 0, "nonpositive": v <= 0,
        "even": v.denominator == 1 and v.numerator % 2 == 0,
        "odd": v.denominator == 1 and v.numerator % 2 == 1,
    }[pred]


def value(e, env):
    """Exact value of a rational expression; ZeroDivisionError at a pole."""
    if e in env:
        return env[e]
    if isinstance(e, Rational):
        return Fraction(int(e.p), int(e.q))
    if isinstance(e, Add):
        return sum((value(a, env) for a in e.args), Fraction(0))
    if isinstance(e, Mul):
        r = Fraction(1)
        for a in e.args:
            r *= value(a, env)
        return r
    if isinstance(e, Pow):
        return value(e.base, env) ** int(e.exp)
    raise TypeError(e)


def random_expr(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice([x, y, x, y, Integer(rng.randint(-3, 3))])
    op = rng.choice(["add", "mul", "pow", "sub"])
    a, b = random_expr(rng, depth - 1), random_expr(rng, depth - 1)
    if op == "add":
        return a + b
    if op == "sub":
        return a - b
    if op == "mul":
        return a * b
    e = a ** rng.choice([2, 3, -1, -2])
    return random_expr(rng, depth) if e.has(S.ComplexInfinity, S.NaN) else e


def random_query(rng):
    facts = [(rng.choice(PREDS), rng.choice(SYMS + (random_expr(rng, 1),))) for _ in range(rng.randint(1, 3))]
    facts.append(("real", x))
    facts.append(("real", y))
    return (rng.choice(PREDS), random_expr(rng, 3)), facts


def check_point(prop, facts, env):
    try:
        if not all(holds(p, value(e, env)) for p, e in facts):
            return None
        return holds(prop[0], value(prop[1], env))
    except ZeroDivisionError:
        return None


@pytest.mark.parametrize("seed", range(8))
def test_definite_answers_hold_at_rational_points(seed):
    rng = random.Random(seed)
    checked = definite = 0
    for _ in range(25):
        (pred, e), facts = random_query(rng)
        if not e.free_symbols:
            continue
        a = Q.real(x)
        for p, t in facts:
            a = a & getattr(Q, p)(t)
        try:
            r = ask(getattr(Q, pred)(e), a)
        except ValueError:
            # inconsistent: no point may satisfy the facts
            for vx in POINTS:
                for vy in POINTS:
                    assert check_point((pred, e), facts, {x: vx, y: vy}) is None, (pred, e, facts)
            continue
        if r is None:
            continue
        definite += 1
        for vx in POINTS:
            for vy in POINTS:
                v = check_point((pred, e), facts, {x: vx, y: vy})
                if v is not None:
                    checked += 1
                    assert v is r, (pred, e, facts, vx, vy)
    assert definite > 0
