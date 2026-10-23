"""exp and log (SymPy's principal branch), with the rational enclosures of
``z3assume.bounds``.  Every expected answer has its argument next to it
(design.md, "The truth standard"); None marks what stays open."""
import random
from fractions import Fraction

import mpmath
import pytest
from sympy import (E, Eq, I, Integer, Pow, Q, Rational, S, exp, log, pi, sqrt, symbols)

from z3assume import ask
from z3assume.bounds import exp_bounds, log_bounds

x, y, t = symbols("x y t")

CASES = [
    # (proposition, assumptions, answer, why)
    # exp: finite real argument -> positive real; special values (F1)
    (Q.positive(exp(x)), Q.real(x), True, "e**a > 0"),
    (Q.extended_positive(exp(x)), Q.real(x), True, "e**a > 0"),
    (Q.finite(exp(x)), Q.finite(x), True, "exp is entire"),
    (Q.finite(exp(2)), True, True, "exp(2) < 7.4"),
    (Q.complex(exp(x)), True, None, "exp(oo) = oo (F1)"),
    (Q.positive_infinite(exp(x)), Q.positive_infinite(x), True, "F1: exp(oo) = oo"),
    (Q.zero(exp(x)), Q.negative_infinite(x), True, "F1: exp(-oo) = 0"),
    (Q.zero(exp(x)), True, None, "x = -oo"),
    (Q.zero(exp(x)), Q.complex(x), False, "|exp(z)| = e**re(z) > 0"),
    (Q.finite(exp(x)), Q.infinite(x) & ~Q.extended_real(x), None, "F1: zoo, 0 or nan; the kind does not tell"),
    (Q.real(exp(S.NaN, evaluate=False)), True, False, "N1: nan, no number (V1)"),
    (Q.nonnegative(exp(x) - 1 - x), Q.real(x), True, "tangent: e**x >= 1 + x"),
    (Q.positive(exp(x) - 1 - x), Q.real(x), None, "x = 0"),
    (Q.positive(exp(x) - exp(y)), Q.real(x) & Q.real(y) & Q.positive(x - y), True, "exp is increasing on R"),
    (Q.positive(exp(x) - E), Q.real(x) & Q.positive(x - 1), True, "E = exp(1), increasing"),
    (Q.zero(exp(Integer(1), evaluate=False) - E), True, True, "E = exp(1)"),
    (Q.positive(Pow(E, x, evaluate=False)), Q.real(x), True, "E**x is exp(x)"),
    # values at rational points, from the enclosures
    (Q.positive(exp(2) - 7), True, True, "e**2 = 7.389..."),
    (Q.negative(exp(2) - Rational(739, 100)), True, True, "e**2 = 7.38905..."),
    (Q.positive(exp(-1) - Rational(1, 3)), True, True, "1/e = 0.3678..."),
    (Q.negative(log(7) - 2), True, True, "log(7) = 1.9459..."),
    (Q.positive(log(3) - 1), True, True, "log(3) = 1.0986..."),
    (Q.negative(log(2) - Rational(7, 10)), True, True, "log(2) = 0.6931..."),
    (Q.positive(exp(pi) - 23), True, None, "no enclosure at an irrational point"),
    # Hermite-Lindemann
    (Q.rational(exp(7)), True, False, "exp(7) is transcendental"),
    (Q.algebraic(exp(7)), True, False, "exp(7) is transcendental"),
    (Q.rational(exp(x)), Q.rational(x), None, "exp(0) = 1"),
    (Q.rational(exp(x)), Q.rational(x) & Q.nonzero(x), False, "Hermite-Lindemann"),
    (Q.irrational(exp(x)), Q.rational(x) & Q.nonzero(x), True, "real and transcendental"),
    (Q.algebraic(exp(x)), Q.algebraic(x) & Q.nonzero(x), False, "Hermite-Lindemann"),
    (Q.algebraic(exp(x)), Q.algebraic(x), None, "exp(0) = 1"),
    (Q.integer(exp(x)), Q.zero(x), True, "exp(0) = 1"),
    (Q.rational(log(7)), True, False, "Hermite-Lindemann: log of algebraic not in {0, 1}"),
    (Q.algebraic(log(7)), True, False, "Hermite-Lindemann"),
    (Q.rational(log(x)), Q.rational(x) & Q.nonzero(x - 1), False, "log(0) = zoo is no rational either"),
    (Q.transcendental(log(x)), Q.algebraic(x) & Q.nonzero(x - 1), None, "log(0) = zoo is not complex"),
    (Q.transcendental(log(x)), Q.algebraic(x) & Q.nonzero(x - 1) & Q.nonzero(x), True, "Hermite-Lindemann"),
    (Q.algebraic(log(3) ** 2 / log(2) ** 2), True, None, "Gelfond-Schneider, not encoded"),
    # exp(I*pi*c): (-1)**c for an integer c, not real otherwise; signs of cos, sin on [-pi, pi]
    (Q.positive(exp(I * pi * x)), Q.even(x), True, "exp(2*pi*I*m) = 1"),
    (Q.negative(exp(I * pi * x)), Q.odd(x), True, "exp(pi*I*(2m + 1)) = -1"),
    (Q.positive(exp(I * pi * x)), Q.odd(x), False, "it is -1"),
    (Q.real(exp(I * pi * x / 2)), Q.odd(x), False, "sin(pi*x/2) = +-1"),
    (Q.imaginary(exp(I * pi * x / 2)), Q.odd(x), True, "cos(pi*(2m + 1)/2) = 0, sin = +-1"),
    (Q.imaginary(exp(I * pi * x)), Q.rational(x) & ~Q.integer(2 * x), False, "cos(pi*x) = 0 only on 1/2 + Z"),
    (Q.imaginary(exp(I * pi * Rational(7, 2), evaluate=False)), True, True, "period 2: exp(7*pi*I/2) = -I"),
    (Q.negative(exp(I * pi * Rational(5, 4), evaluate=False)), True, False, "period 2: exp(5*pi*I/4) is not real"),
    (Q.positive(exp(I * pi * x)), Q.real(x), None, "x = 0, x = 1"),
    (Q.real(exp(I * t)), Q.positive(t) & Q.negative(t - pi), False, "sin t > 0 on (0, pi)"),
    (Q.negative(exp(I * t)), Eq(t, pi), True, "exp(pi*I) = -1"),
    (Q.positive(exp(I * t)), Q.real(t), None, "t = 0, t = pi"),
    (Q.zero(exp(I * t)), Q.real(t), False, "|exp(I*t)| = 1"),
    (Q.positive(exp(x)), Q.imaginary(x), None, "exp(2*pi*I) = 1, exp(I) is not real"),
    # log: principal branch, special values (F2)
    (Q.finite(log(x)), Q.zero(x), False, "F2: log(0) = zoo"),
    (Q.extended_real(log(x)), Q.zero(x), False, "F2: log(0) = zoo"),
    (Q.finite(log(x)), Q.infinite(x), False, "F2: oo or zoo"),
    (Q.finite(log(x)), ~Q.zero(x), None, "x = oo; x = 1"),
    (Q.positive_infinite(log(x)), Q.negative_infinite(x), True, "F2: log(-oo) = oo"),
    (Q.extended_positive(log(x)), Q.infinite(x), None, "F2: log(zoo) = zoo"),
    (Q.imaginary(log(x)), Q.positive(x), False, "log of a positive real is real"),
    (Q.positive(log(x)), Q.positive(x - 1), True, "log is increasing, log(1) = 0"),
    (Q.negative(log(x)), Q.positive(x) & Q.negative(x - 1), True, "log is increasing, log(1) = 0"),
    (Q.positive(log(x)), Q.positive(x), None, "x = 1/2, x = 2"),
    (Q.positive(log(x + 2)), Q.positive(x), True, "x + 2 > 1"),
    (Q.zero(log(x)), Eq(x, 1), True, "log(1) = 0"),
    (Q.positive(log(x) - log(y)), Q.positive(x) & Q.positive(y) & Q.positive(x - y), True, "increasing"),
    (Q.nonpositive(log(x) - x + 1), Q.positive(x), True, "tangent: log(x) <= x - 1"),
    (Q.real(log(x)), Q.imaginary(x), False, "arg(+-b*I) = +-pi/2"),
    (Q.positive(log(x)), Q.negative(x), False, "arg(x) = pi"),
    (Q.imaginary(log(x)), Q.negative(x), None, "log(-1) = pi*I, log(-2) = log(2) + pi*I"),
    (Q.imaginary(log(x)), Eq(x, -1), True, "log(-1) = pi*I"),
    (Q.imaginary(log(2) + I * pi / 2), True, False, "log(2) > 0"),
    (Q.zero(x * log(pi)), Q.odd(x), False, "pi > 1, so log(pi) > 0"),
    (Q.zero(y * (log(-x) + I * pi)), Q.negative(x) & Q.odd(y), False, "log(-x) is real"),
    (~Q.negative(log(x) ** 2), Q.positive(x), True, "log of a positive real is real"),
    (Q.imaginary(log(sqrt(2)) + I * pi / 4), True, False, "log(sqrt(2)) is real, log(sqrt(2)) > 0"),
    # inverses
    (Q.rational(log(exp(x))), Q.rational(x), True, "log(exp(x)) = x for real x"),
    (Q.integer(log(exp(x))), Q.integer(x), True, "log(exp(x)) = x for real x"),
    (Q.real(log(exp(x))), Q.imaginary(x), None, "log(exp(2*pi*I)) = 0, log(exp(I)) = I"),
    (Q.rational(exp(log(x), evaluate=False)), Q.rational(x) & Q.nonzero(x), True, "exp(log(x)) = x"),
    (Q.zero(log(E, evaluate=False) - 1), True, True, "E = exp(1)"),
]


@pytest.mark.parametrize("p, a, answer, why", CASES, ids=[f"{c[0]} | {c[1]}" for c in CASES])
def test_answer(p, a, answer, why):
    assert ask(p, a) is answer


def test_sympy_forms():
    """The forms SymPy produces: E**x is exp(x), log(x, b) is a quotient."""
    assert type(E ** x) is exp
    assert log(x, 2) == log(x) / log(2)
    assert ask(Q.positive(log(x, 2)), Q.positive(x - 1)) is True


# -- the enclosures, cross-checked with mpmath (not the truth standard:
#    bounds.py carries its own argument; this guards the code) ----------

def _mp(f):
    return mpmath.mpf(f.numerator) / f.denominator


@pytest.mark.parametrize("r", [Fraction(2), Fraction(7), Fraction(-3), Fraction(1, 3), Fraction(-5, 7),
                               Fraction(10_000), Fraction(-10_000), Fraction(1, 10 ** 29)])
def test_exp_bounds(r):
    lo, hi = exp_bounds(r)
    with mpmath.workprec(400):
        v = mpmath.exp(_mp(r))
        assert _mp(lo) < v < _mp(hi)
        assert (_mp(hi) - _mp(lo)) / v < mpmath.mpf(10) ** -18


@pytest.mark.parametrize("r", [Fraction(7), Fraction(2), Fraction(1, 2), Fraction(4, 9), Fraction(10 ** 30),
                               Fraction(1, 10 ** 30), Fraction(10 ** 29 + 1, 10 ** 29)])
def test_log_bounds(r):
    lo, hi = log_bounds(r)
    with mpmath.workprec(400):
        v = mpmath.log(_mp(r))
        assert _mp(lo) < v < _mp(hi)
        assert _mp(hi) - _mp(lo) < mpmath.mpf(10) ** -17


def test_bounds_out_of_range():
    assert exp_bounds(0) is None and log_bounds(1) is None and log_bounds(-2) is None
    assert exp_bounds(10 ** 5) is None


# -- randomized falsification: a definite answer about the sign, reality
#    or imaginarity must hold at every Gaussian rational point satisfying
#    the assumptions, evaluated with mpmath at 300 bits (a falsification
#    test: it can only find wrong answers).

PREDS = ("real", "positive", "negative", "nonzero", "nonnegative", "nonpositive", "imaginary")
POINTS = [(Fraction(a), Fraction(b)) for a, b in
          ((1, 0), (-2, 0), (Fraction(1, 2), 0), (3, 0), (0, 1), (0, -2), (1, 1), (-3, 4), (Fraction(1, 2), -1))]
EPS = mpmath.mpf(10) ** -40


class Undecided(Exception):
    pass


def value(e, env):
    if e in env:
        return env[e]
    if e is S.ImaginaryUnit:
        return mpmath.mpc(0, 1)
    if isinstance(e, Rational):
        return mpmath.mpc(_mp(Fraction(int(e.p), int(e.q))))
    if e is S.Pi:
        return mpmath.mpc(mpmath.pi)
    if e is S.Exp1:
        return mpmath.mpc(mpmath.e)
    if e.func is exp or (isinstance(e, Pow) and e.base is S.Exp1):
        return mpmath.exp(value(e.args[-1], env))
    if e.func is log:
        v = value(e.args[0], env)
        if abs(v) < EPS:
            raise Undecided
        return mpmath.log(v)
    vs = [value(a, env) for a in e.args]
    if e.is_Add:
        return mpmath.fsum(vs)
    if e.is_Mul:
        return mpmath.fprod(vs)
    if isinstance(e, Pow):
        if abs(vs[0]) < EPS and e.exp < 0:
            raise Undecided
        return vs[0] ** int(e.exp)
    raise TypeError(e)


def holds(pred, v):
    """The predicate at a computed value: an exact 0 is 0 (exact rational
    arithmetic or exp, log at real points), a nonzero component within
    EPS of 0 is not decided."""
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
        return rng.choice([x, y, x, y, Integer(rng.randint(-2, 3)), I * pi])
    op = rng.choice(["add", "mul", "exp", "log", "exp", "log"])
    a = random_expr(rng, depth - 1)
    if op == "exp":
        return exp(a)
    if op == "log":
        return log(a)
    b = random_expr(rng, depth - 1)
    return a + b if op == "add" else a * b


@pytest.mark.parametrize("seed", range(4))
def test_definite_answers_hold_numerically(seed):
    rng = random.Random(seed)
    definite = 0
    with mpmath.workprec(300):
        for _ in range(20):
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
                        if not all(holds(p, env[s]) for p, s in ((base, x), (base, y), fact)
                                   if p != "complex"):
                            continue
                        got = holds(pred, value(e, env))
                    except Undecided:
                        continue
                    assert got is r, (pred, e, a, env)
    assert definite > 0
