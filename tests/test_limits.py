"""Answers near the rlimit (decisions 11 and 12, #29, #31): two wester
cases that #26's sum axiom moved across the limit of 1,000,000 steps, and
the fallback."""
from sympy import Abs, Q, Rational, Symbol, asinh, cos, cosh, im, re, sign, sqrt, tan

from z3assume import ask

x, y, k, n = (Symbol(s) for s in "xykn")      # plain symbols, as the bench sends them


def test_n2b_power_below_identity():
    # x**4 <= x on [0, 1], so sign(x**4 - x) is 0 or -1
    assert ask(Q.zero(sign(x**4 - x) - 1), Q.real(x) & Q.ge(x, 0) & Q.le(x, 1)) is False


def test_n6_power_increasing():
    # t -> t**n increases on (0, oo) for n > 0.  It needed 1,130,000 steps
    # (#31) until Groebner's growth was bounded (#39, decision 15).
    a = (Q.real(x) & Q.real(y) & Q.real(k) & Q.real(n) & Q.gt(x, y) & Q.gt(y, Rational(1, 10))
         & Q.lt(x, 10) & Q.gt(k, 0) & Q.gt(n, 0) & Q.lt(n, 10))
    assert ask(Q.zero(sign(k * x**n - k * y**n) - 1), a) is True



def test_cosh_asinh_tan_imaginary():
    # x = i*t: tan(x) = i*tanh(t), asinh(i*s) = i*asin(s) for |s| < 1, so the
    # left side is sqrt(1 - tanh(t)**2) = 1/cosh(t) = |1/cos(x)| (#39)
    z = Symbol("z")
    assert ask(Q.zero(cosh(asinh(tan(z))) - Abs(1 / cos(z))), Q.imaginary(z) & ~Q.zero(cos(z))) is True


def test_sqrt_product_second_quadrant():
    # arg(a) + arg(b) is in (pi, 2*pi], so sqrt(a*b) = -sqrt(a)*sqrt(b) and the
    # left side is -sqrt(b), which is not sqrt(b) for b != 0 (#39)
    a, b, z = Symbol("a"), Symbol("b"), Symbol("z")
    lhs = sqrt(a * b * Abs(z)**2) / (sqrt(a) * Abs(z))
    assume = (Q.complex(a) & Q.complex(b) & Q.complex(z) & ~Q.zero(z)
              & Q.lt(re(a), 0) & Q.ge(im(a), 0) & Q.lt(re(b), 0) & Q.ge(im(b), 0))
    assert ask(Q.zero(lhs - sqrt(b)), assume) is False
