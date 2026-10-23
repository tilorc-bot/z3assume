"""Rigorous rational enclosures of ``exp(r)`` and ``log(r)`` at rational
points, in exact integer arithmetic (``fractions.Fraction``).  No floating
point and no library evaluation is used: each bound comes with its
argument next to it (docs/design.md, "The truth standard"), and the tests
compare the enclosures with mpmath only as a cross-check.

Both functions return ``(lo, hi)`` with ``lo < f(r) < hi`` strictly, or
None when ``r`` is outside the sizes handled (then no bound is given)."""
from __future__ import annotations

from fractions import Fraction
from math import floor

#: Working precision: every intermediate bound is rounded outward to a
#: multiple of 2**-PREC.
PREC = 160
#: Significant bits of the bounds handed to z3 (rounded outward again).
OUT_BITS = 64
#: Largest |r| for exp, largest numerator/denominator for both.
EXP_MAX = 10_000
SIZE_MAX = 10 ** 30

_ONE = Fraction(1)


def _down(v: Fraction, bits: int = PREC) -> Fraction:
    """The largest multiple of 2**-bits that is <= v."""
    s = 1 << bits
    return Fraction(floor(v * s), s)


def _up(v: Fraction, bits: int = PREC) -> Fraction:
    s = 1 << bits
    return Fraction(-floor(-v * s), s)


def _out(lo: Fraction, hi: Fraction):
    """Round ``lo`` down and ``hi`` up to about OUT_BITS significant bits
    (small numbers for z3); the enclosure only widens."""
    def scale(v):
        m = abs(v.numerator).bit_length() - v.denominator.bit_length()
        return OUT_BITS - m

    s = scale(hi) if hi != 0 else OUT_BITS
    return _round_at(lo, s, down=True), _round_at(hi, s, down=False)


def _round_at(v: Fraction, s: int, down: bool) -> Fraction:
    """Round v to a multiple of 2**-s (s may be negative), down or up."""
    f = Fraction(1 << s) if s >= 0 else Fraction(1, 1 << -s)
    w = v * f
    n = floor(w) if down else -floor(-w)
    return n / f


def _exp_small(y: Fraction):
    """``0 < y <= 1/2``: ``S_N = sum(y**n/n!, n <= N)`` is a strict lower
    bound of ``e**y`` (the omitted terms are positive), and the tail is
    ``sum(y**n/n!, n > N) <= y**(N+1)/(N+1)! * sum((y/(N+2))**j, j >= 0)
    = y**(N+1)/(N+1)! / (1 - y/(N+2)) < 2*y**(N+1)/(N+1)!`` (each ratio of
    consecutive terms is ``y/n <= y/(N+2) <= 1/4``)."""
    s, term, n = Fraction(0), _ONE, 0
    eps = Fraction(1, 1 << (PREC + 8))
    while True:
        s += term
        n += 1
        term = term * y / n          # y**n/n!
        if 2 * term < eps:
            break
    # s = S_{n-1}, the tail is bounded by 2*term
    return _down(s), _up(s + 2 * term)


def exp_bounds(r):
    """``lo < exp(r) < hi`` for a rational ``r != 0``, or None.

    ``x = |r|`` is reduced to ``y = x/2**k <= 1/2``; ``e**x = (e**y)**(2**k)``
    and squaring is increasing on positive numbers, so squaring the bounds
    of ``e**y`` (rounded outward after each step) bounds ``e**x``;
    ``e**-x = 1/e**x`` and ``1/v`` is decreasing, so the bounds swap."""
    r = Fraction(r)
    if r == 0 or abs(r) > EXP_MAX or r.denominator > SIZE_MAX or abs(r.numerator) > SIZE_MAX:
        return None
    x = abs(r)
    k = 0
    while x > Fraction(1, 2):
        x /= 2
        k += 1
    lo, hi = _exp_small(x)
    for _ in range(k):
        lo, hi = _down(lo * lo), _up(hi * hi)
    if r < 0:
        lo, hi = 1 / hi, 1 / lo          # exact; _out rounds outward
    return _out(lo, hi)


def _atanh2(y: Fraction):
    """``0 < y <= 1/3``: ``log((1 + y)/(1 - y)) = 2*sum(y**(2j+1)/(2j+1))``.
    The partial sum ``T_N`` is a strict lower bound (positive terms
    omitted); the tail is ``< 2*y**(2N+3)/(2N+3) * 1/(1 - y**2)
    <= 2*y**(2N+3)/(2N+3) * 9/8`` (each later term has a larger
    denominator, and ``y**2 <= 1/9``)."""
    s, p, j = Fraction(0), y, 0
    eps = Fraction(1, 1 << (PREC + 8))
    y2 = y * y
    while True:
        s += 2 * p / (2 * j + 1)
        j += 1
        p *= y2                      # y**(2j+1)
        tail = 2 * p / (2 * j + 1) * Fraction(9, 8)
        if tail < eps:
            break
    return _down(s), _up(s + tail)


def log_bounds(r):
    """``lo < log(r) < hi`` for a rational ``r > 0``, ``r != 1``, or None.

    ``r = 2**m * s`` with ``1 <= s < 2`` (exact, from the bit lengths);
    ``log(r) = m*log(2) + log(s)``, both by ``_atanh2``: ``log(2)`` at
    ``y = 1/3`` and ``log(s)`` at ``y = (s - 1)/(s + 1) < 1/3`` (exact,
    ``s = 1`` giving ``log(s) = 0``).  Interval sum and the product with
    the integer ``m`` (the bounds swap for ``m < 0``) keep the enclosure
    strict, since ``m != 0`` or ``s != 1``."""
    r = Fraction(r)
    if r <= 0 or r == 1 or r.denominator > SIZE_MAX or r.numerator > SIZE_MAX:
        return None
    m = r.numerator.bit_length() - r.denominator.bit_length()
    s = r / Fraction(2) ** m
    if s < 1:
        m -= 1
        s *= 2
    elif s >= 2:
        m += 1
        s /= 2
    assert 1 <= s < 2 and r == s * Fraction(2) ** m
    l2lo, l2hi = _atanh2(Fraction(1, 3))
    if m >= 0:
        lo, hi = m * l2lo, m * l2hi
    else:
        lo, hi = m * l2hi, m * l2lo
    if s != 1:
        slo, shi = _atanh2((s - 1) / (s + 1))
        lo, hi = lo + slo, hi + shi
    return _out(lo, hi)


#: Largest |r| for sin and cos (the Taylor terms grow to about e**|r|
#: before they fall, so the work grows with |r|).
TRIG_MAX = 256


def sin_cos_bounds(r):
    """``(slo, shi), (clo, chi)`` with ``slo < sin(r) < shi`` and
    ``clo < cos(r) < chi`` for a rational ``r != 0``, or None.

    No argument reduction (it would need an enclosure of ``pi``): for
    ``x = |r|`` the Taylor polynomials ``T_N`` of degree ``N`` of ``sin``
    and ``cos`` at 0 satisfy ``|f(x) - T_N(x)| <= x**(N+1)/(N+1)!``
    (Lagrange's remainder; every derivative of ``sin`` and ``cos`` is
    ``+-sin`` or ``+-cos``, bounded by 1 on R).  The terms ``x**n/n!`` are
    kept as intervals rounded outward to multiples of ``2**-p`` (``x > 0``,
    so each is increasing in the previous one), and the sums with their
    signs are exact sums of such multiples.  ``p = PREC + 2*ceil(x)``: a
    rounding error is multiplied by ``x/n`` in each later term, by at most
    ``e**x < 4**x`` in all.  The loop stops when the next term's upper
    bound, which bounds the remainder, is at most ``2**-(PREC - 8)``
    (rounded up, a term never falls below ``2**-p``); that bound plus one
    more ``2**-PREC`` is added on both sides, which makes the enclosure
    strict.  ``sin`` is odd and
    ``cos`` even."""
    r = Fraction(r)
    if r == 0 or abs(r) > TRIG_MAX or r.denominator > SIZE_MAX or abs(r.numerator) > SIZE_MAX:
        return None
    x = abs(r)
    p = PREC + 2 * (-floor(-x))
    eps = Fraction(1, 1 << (PREC - 8))
    tl = th = _ONE                       # x**0/0!
    s = [Fraction(0), Fraction(0)]       # sin: lo, hi
    c = [_ONE, _ONE]                     # cos: lo, hi
    n = 0
    while True:
        n += 1
        tl, th = _down(tl * x / n, p), _up(th * x / n, p)
        if th <= eps and n > x:
            break
        acc = s if n % 2 else c
        if n % 4 in (1, 0):              # + x/1!, + x**4/4!, ...
            acc[0] += tl
            acc[1] += th
        else:                            # - x**2/2!, - x**3/3!, ...
            acc[0] -= th
            acc[1] -= tl
    # th bounds the remainder x**n/n! after degree n - 1
    pad = th + Fraction(1, 1 << PREC)
    slo, shi = s[0] - pad, s[1] + pad
    clo, chi = c[0] - pad, c[1] + pad
    if r < 0:
        slo, shi = -shi, -slo
    return _out(slo, shi), _out(clo, chi)


def cosh_sinh_bounds(r):
    """``(clo, chi), (slo, shi)`` with ``clo < cosh(r) < chi`` and
    ``slo < sinh(r) < shi`` for a rational ``r != 0``, or None.

    From ``lo < e**r < hi`` (``exp_bounds``): ``e**-r = 1/e**r`` lies in
    ``(1/hi, 1/lo)``; ``cosh = (e**r + e**-r)/2`` is the half sum of the
    two enclosures, and ``sinh = (v - 1/v)/2`` with ``v = e**r`` is
    increasing in ``v > 0``, so its bounds are its values at ``lo`` and
    ``hi``.  All strict, as the enclosure of ``e**r`` is."""
    b = exp_bounds(r)
    if b is None:
        return None
    lo, hi = b
    return (_out((lo + 1 / hi) / 2, (hi + 1 / lo) / 2),
            _out((lo - 1 / lo) / 2, (hi - 1 / hi) / 2))
