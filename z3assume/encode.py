"""Translation of SymPy terms and propositions into z3 (docs/design.md).

One :class:`Encoder` serves one query.  Every SymPy subterm it reaches gets
a :class:`Term` (its z3 variables) and the axioms of its node, collected in
``Encoder.axioms`` in the order the terms were reached (SymPy's argument
order), so the problem z3 sees does not depend on hashing.
"""
from __future__ import annotations

import math
from fractions import Fraction
from math import lcm

import z3
from sympy import Basic, S, Symbol
from sympy.core.add import Add
from sympy.core.mul import Mul
from sympy.core.numbers import (ComplexInfinity, Float, ImaginaryUnit, Infinity, Integer, NaN,
                                NegativeInfinity, NumberSymbol, Rational)
from sympy.core.power import Pow
from sympy.core.relational import Relational
from sympy.functions.elementary.complexes import Abs, conjugate, im as Im, re as Re, sign
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.elementary.hyperbolic import (acosh, acoth, asinh, atanh, cosh, coth, csch, sech, sinh,
                                                   tanh)
from sympy.functions.elementary.trigonometric import acos, acot, asin, atan, cos, cot, csc, sec, sin, tan
from sympy.logic.boolalg import (And, BooleanFalse, BooleanTrue, Equivalent, ITE, Implies, Not, Or,
                                 Xor)
from sympy.assumptions.assume import AppliedPredicate

from .bounds import cosh_sinh_bounds, exp_bounds, log_bounds, sin_cos_bounds
from .predicates import BASIS, DEFINITIONS, PREDICATES, RULES
from .primes import is_prime


#: SymPy's named constants (``NumberSymbol``), by class name: the first 20
#: decimals ``d`` of the published expansion, so ``d < c < d + 10**-20``
#: (strictly: the published digits after the 20th are neither all 0 nor
#: all 9), and what is proven about c: "transcendental",
#: or the coefficients (leading first) of an irreducible integer polynomial
#: with c as a root (algebraic, the interval picks the root; irrational by
#: the rational root test, its only candidates +-1 are no roots), or None
#: when rationality and algebraicity are open problems (never assumed).
#: The digits were cross-checked with mpmath.
CONSTANTS = {
    # OEIS A000796; transcendental: Lindemann 1882
    "Pi": ("3.14159265358979323846", "transcendental"),
    # OEIS A001113; transcendental: Hermite 1873
    "Exp1": ("2.71828182845904523536", "transcendental"),
    # OEIS A001622; (1 + sqrt(5))/2 is the positive root of x**2 - x - 1
    # (at +-1: -1, 1)
    "GoldenRatio": ("1.61803398874989484820", (1, -1, -1)),
    # OEIS A058265; the real root of x**3 - x**2 - x - 1 (at +-1: -2, -2)
    "TribonacciConstant": ("1.83928675521416113255", (1, -1, -1, -1)),
    # OEIS A001620; real, rationality open
    "EulerGamma": ("0.57721566490153286060", None),
    # OEIS A006752; real (sum of (-1)**n/(2n+1)**2), rationality open
    "Catalan": ("0.91596559417721901505", None),
}


#: A Float whose mantissa or binary exponents (of its value and of its ulp)
#: need more bits than this gets only its sign: its interval's endpoints
#: would be rationals of thousands of digits (``Float('1e100000')``).
FLOAT_EXP_BOUND = 4096


#: The twelve circular and hyperbolic functions (docs/design.md "Terms"):
#: (family, numerator, denominator), the value being numerator/denominator
#: with "E" the even function of the family (cos, cosh), "O" the odd one
#: (sin, sinh), 1 the number one and None no denominator.
TRIG = {
    cos: ("circ", "E", None), sin: ("circ", "O", None), tan: ("circ", "O", "E"),
    cot: ("circ", "E", "O"), sec: ("circ", 1, "E"), csc: ("circ", 1, "O"),
    cosh: ("hyp", "E", None), sinh: ("hyp", "O", None), tanh: ("hyp", "O", "E"),
    coth: ("hyp", "E", "O"), sech: ("hyp", 1, "E"), csch: ("hyp", 1, "O"),
}

#: The inverse functions (SymPy's principal branches), by the value of the
#: forward function at 0 (0, 1, or None for the pole of cot and coth).
INVERSE = {asin: 0, acos: 1, atan: 0, acot: None, asinh: 0, acosh: 1, atanh: 0, acoth: None}


def _iroot(n: int, q: int) -> int:
    """The integer part of the ``q``-th root of ``n >= 0`` (bisection)."""
    lo, hi = 0, 1 << (n.bit_length() // q + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** q <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def _polar_literal(w):
    """``(r, c0)`` with ``w = r*exp(I*pi*c0)`` for a literal nonzero
    rational, ``I`` or rational multiple of ``I``: ``r`` a positive
    Fraction, ``c0`` one of ``0, 1, 1/2, -1/2``; else None."""
    if isinstance(w, Rational) and w != 0:
        f = Fraction(int(w.p), int(w.q))
        return abs(f), Fraction(0 if f > 0 else 1)
    if w is S.ImaginaryUnit:
        return Fraction(1), Fraction(1, 2)
    if isinstance(w, Mul) and len(w.args) == 2 and w.args[1] is S.ImaginaryUnit \
            and isinstance(w.args[0], Rational) and w.args[0] != 0:
        f = Fraction(int(w.args[0].p), int(w.args[0].q))
        return abs(f), Fraction(1, 2) if f > 0 else Fraction(-1, 2)
    return None


class Unsupported(Exception):
    """The proposition is outside what z3assume encodes."""


class Term:
    """The z3 variables of one SymPy term."""

    __slots__ = ("expr", "fin", "pinf", "ninf", "cinf", "nan", "re", "im", "k", "h", "r", "atoms")

    def __init__(self, expr, n: int, ctx):
        self.expr = expr
        b = lambda s: z3.Bool(f"{s}{n}", ctx)  # noqa: E731
        self.fin, self.pinf, self.ninf, self.cinf, self.nan = (b(s) for s in ("fin", "pinf", "ninf", "cinf", "nan"))
        self.re, self.im = z3.Real(f"re{n}", ctx), z3.Real(f"im{n}", ctx)
        self.k, self.h, self.r = z3.Int(f"k{n}", ctx), z3.Int(f"h{n}", ctx), z3.Int(f"r{n}", ctx)
        self.atoms = {p: b(f"{p}_") for p in BASIS}

    def real(self):
        """The value is a finite real."""
        return z3.And(self.fin, self.im == 0)

    def ext_real(self):
        return z3.Or(self.real(), self.pinf, self.ninf)

    def infinite(self):
        return z3.Not(z3.Or(self.fin, self.nan))


def _lit(atoms, pred, pos):
    a = atoms[pred]
    return a if pos else z3.Not(a)


class Encoder:
    """Collects the terms and axioms of one query."""

    def __init__(self, ctx):
        self.ctx = ctx
        self.terms = {}
        self.axioms = []
        self.opaque = {}
        self._congruent = set()
        self._pairs = []
        self._trig = {}
        self._lin = {}
        self._n = 0

    def _count(self) -> int:
        self._n += 1
        return self._n

    # -- terms ---------------------------------------------------------

    def term(self, e) -> Term:
        t = self.terms.get(e)
        if t is not None:
            return t
        if not isinstance(e, Basic) or not e.is_commutative:
            raise Unsupported(f"not a commutative scalar: {e!r}")
        args = [self.term(a) for a in e.args] if isinstance(e, (Add, Mul)) else None
        t = Term(e, len(self.terms), self.ctx)
        self.terms[e] = t
        self._lin[t] = self._scaled(t, e, args)
        self._shape(t)
        self._node(t, e, args)
        return t

    def _add(self, *fs):
        self.axioms.extend(fs)

    def _shape(self, t: Term):
        """The kind is one of five; the basis Booleans are the numeric
        definitions unless the value is nan, the rules always; nan is no
        number."""
        kinds = [t.fin, t.pinf, t.ninf, t.cinf, t.nan]
        self._add(z3.PbEq([(k, 1) for k in kinds], 1))
        a = t.atoms
        defs = {
            "finite": t.fin,
            "complex": t.fin,
            "extended_real": t.ext_real(),
            "extended_positive": z3.Or(z3.And(t.real(), t.re > 0), t.pinf),
            "extended_negative": z3.Or(z3.And(t.real(), t.re < 0), t.ninf),
            "zero": z3.And(t.real(), t.re == 0),
            "imaginary": z3.And(t.fin, t.re == 0, t.im != 0),
        }
        for p, d in defs.items():
            self._add(z3.Implies(z3.Not(t.nan), a[p] == d))
        # satassume's convention for nan (docs/special-values.md row V1):
        # every predicate is False except finite (and infinite) and polar;
        # commutative is True of every term in scope (design.md)
        self._add(*(z3.Implies(t.nan, z3.Not(a[p])) for p in BASIS if p not in ("finite", "polar")))
        notnan = z3.Not(t.nan)
        # integer witnesses: z3 reasons about integers in the Int sort
        self._add(z3.Implies(z3.And(notnan, a["integer"]),
                             z3.And(t.real(), t.re == z3.ToReal(t.k), t.k == 2 * t.h + t.r, t.r >= 0, t.r <= 1)),
                  self._non_integer(t),
                  z3.Implies(notnan, a["even"] == z3.And(a["integer"], t.r == 0)),
                  z3.Implies(z3.And(notnan, a["prime"]), z3.And(a["integer"], t.k >= 2)),
                  z3.Implies(z3.And(notnan, a["integer"], z3.Or(t.k == 2, t.k == 3)), a["prime"]),
                  z3.Implies(z3.And(notnan, a["prime"], a["even"]), t.k == 2),
                  z3.Implies(notnan, a["composite"] == z3.And(a["integer"], t.k >= 2, z3.Not(a["prime"]))),
                  z3.Implies(z3.And(notnan, a["rational"]), t.real()))
        for prem, concl in RULES:
            self._add(z3.Implies(z3.And([_lit(a, p, s) for p, s in prem]),
                                 z3.Or([_lit(a, p, s) for p, s in concl])))

    def _non_integer(self, t: Term):
        """A finite real non-integer: ``Not(IsInt(re_t))``, unless ``t`` has a
        scaled witness ``n/d`` with ``d > 1``: under its ``cond`` the integer
        facts of ``t`` are stated over the integers instead (``t`` is an
        integer iff ``d`` divides ``n``, and then ``k_t = n/d``), as z3 does
        not decide ``IsInt`` of a real with rational coefficients over
        integers (issue #12)."""
        d, n, cond = self._lin[t]
        a = t.atoms
        noint = z3.And(z3.Not(t.nan), t.real(), z3.Not(a["integer"]))
        if d == 1 or cond is True:
            return z3.Implies(noint, z3.Not(z3.IsInt(t.re)))
        c = self._count()
        q, r = z3.Int(f"dq{c}", self.ctx), z3.Int(f"dr{c}", self.ctx)
        return z3.And(z3.Implies(cond, z3.And(n == d * q + r, r >= 0, r < d, a["integer"] == (r == 0))),
                      z3.Implies(z3.And(cond, a["integer"]), t.k == q),
                      z3.Implies(z3.And(noint, z3.Not(cond)), z3.Not(z3.IsInt(t.re))))

    def _scaled(self, t: Term, e, args):
        """The scaled integer witness of ``t`` (docs/design.md, "Values"):
        ``(d, n, cond)`` with ``d`` a positive Python integer, ``n`` a Python
        integer or a z3 integer and ``cond`` True or a z3 Boolean, such that
        under ``cond`` the value of ``t`` is the finite real ``n/d``.  From
        the terms' own witnesses ``k`` (under ``integer``) through rational
        constants, sums, and products with at most one non-constant factor;
        it reads only the forms of the arguments."""
        if isinstance(e, Rational):                 # Integer included
            return int(e.q), int(e.p), True
        forms = [self._lin[x] for x in args] if args is not None else None
        if isinstance(e, Add):
            d = lcm(*(f[0] for f in forms))
            n = sum(f[1] * (d // f[0]) for f in forms)
        elif isinstance(e, Mul) and sum(f[2] is not True for f in forms) <= 1:
            d, n = 1, 1
            for f in forms:
                d, n = d * f[0], n * f[1]
        else:
            return 1, t.k, t.atoms["integer"]
        conds = [f[2] for f in forms if f[2] is not True]
        return d, n, z3.And(conds) if conds else True

    def _value(self, t: Term, re, im):
        self._add(t.fin, t.re == re, t.im == im)

    def _node(self, t: Term, e, args):
        a = t.atoms
        if isinstance(e, Pow) and e.exp == 0:
            e = Integer(1)      # x**0 = 1 for every x, nan included (design.md)
        if isinstance(e, Integer):
            n = int(e)
            self._value(t, n, 0)
            self._add(t.k == n, a["rational"], a["algebraic"])
            p = is_prime(n)
            if p is not None:
                self._add(a["prime"] if p else z3.Not(a["prime"]))
        elif isinstance(e, Rational):
            self._value(t, z3.Q(int(e.p), int(e.q), self.ctx), 0)
            self._add(a["rational"], a["algebraic"])
        elif isinstance(e, Float):
            self._float(t, e)
        elif isinstance(e, ImaginaryUnit):
            self._value(t, 0, 1)
            self._add(a["algebraic"])
        elif isinstance(e, Infinity):
            self._add(t.pinf)
        elif isinstance(e, NegativeInfinity):
            self._add(t.ninf)
        elif isinstance(e, ComplexInfinity):
            self._add(t.cinf)
        elif isinstance(e, NaN):
            self._add(t.nan)
        elif (isinstance(e, NumberSymbol) and type(e).__name__ in CONSTANTS
              and type(e).__module__ == "sympy.core.numbers"):     # not a user class
            self._constant(t, *CONSTANTS[type(e).__name__])
            if type(e).__name__ == "Exp1":
                self._exp_pair(z3.BoolVal(True, self.ctx), z3.RealVal(1, self.ctx), t.re)   # E = exp(1)
        elif isinstance(e, Symbol):
            self._add(z3.Not(t.nan))
            self._declared(t, e)
        elif isinstance(e, Add):
            self._sum(t, args)
        elif isinstance(e, Mul):
            self._product(t, args)
        elif isinstance(e, Pow) and isinstance(e.exp, Integer):
            self._power(t, self.term(e.base), int(e.exp))
        elif isinstance(e, Pow) and e.base is S.Exp1:
            # E**z (unevaluated) is exp(z): the principal value
            # exp(z*log(E)) with log(E) = 1
            self._exp(t, self.term(e.exp))
        elif isinstance(e, Pow) and type(e) is Pow:   # not a user subclass
            self._pow(t, e)
        elif type(e) is exp and len(e.args) == 1:     # not a user subclass
            self._exp(t, self.term(e.args[0]))
        elif type(e) is log and len(e.args) == 1:     # not a user subclass
            self._log(t, self.term(e.args[0]))
        elif isinstance(e, (Abs, Re, Im, conjugate, sign)) and len(e.args) == 1:
            self._complex_part(t, type(e), self.term(e.args[0]))
        elif type(e) in TRIG and len(e.args) == 1:
            self._trig_function(t, *TRIG[type(e)], self.term(e.args[0]))
        elif type(e) in INVERSE and len(e.args) == 1:
            self._inverse(t, type(e), self.term(e.args[0]))
        else:
            self._opaque(t, e)

    def _constant(self, t: Term, digits: str, facts):
        """A named constant: a real in its 20-digit interval, plus its
        proven facts (``CONSTANTS``)."""
        whole, frac = digits.split(".")
        lo = int(whole + frac)
        den = 10 ** len(frac)
        self._add(t.fin, t.im == 0, t.re > z3.Q(lo, den, self.ctx), t.re < z3.Q(lo + 1, den, self.ctx))
        a = t.atoms
        if facts == "transcendental":
            self._add(z3.Not(a["algebraic"]))
        elif facts is not None:
            v = z3.RealVal(facts[0], self.ctx)
            for c in facts[1:]:
                v = v * t.re + c
            self._add(v == 0, a["algebraic"], z3.Not(a["rational"]))

    def _float(self, t: Term, e):
        """A Float (design.md "Terms", decision 2): a finite real with
        the sign of its mpf ``(-1)**s * man * 2**exp``, 0 exactly when the
        mpf is 0, and otherwise strictly within one unit in the last place
        (at the Float's precision ``p`` bits) of that binary value ``v``:
        every real that rounds to ``v`` at ``p`` bits, in any rounding mode,
        lies there.  Nothing more: whether it is an integer, rational or
        algebraic follows only where the interval decides it."""
        s, man, exp, bc = e._mpf_
        if not man:
            self._value(t, 0, 0)            # fzero: the only mpf that rounds from 0
            return
        sgn = -1 if s else 1
        self._add(t.fin, t.im == 0, t.re > 0 if sgn > 0 else t.re < 0)
        if max(bc, abs(exp), abs(exp + bc - e._prec)) > FLOAT_EXP_BOUND:
            return
        v = sgn * man * Fraction(2) ** exp
        ulp = Fraction(2) ** (exp + bc - e._prec)
        q = lambda f: z3.Q(f.numerator, f.denominator, self.ctx)  # noqa: E731
        self._add(t.re > q(v - ulp), t.re < q(v + ulp))

    def _declared(self, t: Term, s):
        """Old-style assumptions of a symbol are facts about it."""
        for k, v in s.assumptions0.items():
            if k in PREDICATES and v is not None:
                f = self.pred(k, t)
                self._add(f if v else z3.Not(f))

    def _opaque(self, t: Term, e):
        """A term outside the encoding: any value, nan included."""

    def _sum(self, t: Term, args):
        allfin = z3.And([x.fin for x in args])
        self._add(z3.Implies(allfin, z3.And(t.fin, t.re == z3.Sum([x.re for x in args]),
                                            t.im == z3.Sum([x.im for x in args]))))
        allint = z3.And([x.atoms["integer"] for x in args])
        self._add(z3.Implies(z3.And(allfin, allint), z3.And(t.atoms["integer"],
                                                            t.k == z3.Sum([x.k for x in args]))))
        self._add(z3.Implies(z3.Or([x.nan for x in args]), t.nan))
        for inf, other in ((t.pinf, "ninf"), (t.ninf, "pinf")):
            pick = (lambda x: x.pinf) if other == "ninf" else (lambda x: x.ninf)
            self._add(z3.Implies(z3.And(z3.Or([pick(x) for x in args]),
                                        z3.And([z3.Or(x.fin, pick(x)) for x in args])), inf))
        self._add(z3.Implies(z3.And(z3.Or([x.pinf for x in args]), z3.Or([x.ninf for x in args])), t.nan))
        for i, x in enumerate(args):
            rest = [y.fin for j, y in enumerate(args) if j != i]
            self._add(z3.Implies(z3.And(x.cinf, *rest), t.cinf))
        self._closure(t, args, allfin, lambda y: z3.BoolVal(True, self.ctx))

    def _closure(self, t: Term, args, allfin, cancel):
        """Field closure of rationals and algebraic numbers among finite
        values; ``cancel(y)`` is the condition under which ``y`` can be
        taken out of the operation (any summand; a nonzero factor)."""
        for p in ("rational", "algebraic"):
            self._add(z3.Implies(z3.And(allfin, *[x.atoms[p] for x in args]), t.atoms[p]))
            if len(args) > 1:
                for i, x in enumerate(args):
                    rest = [z3.And(y.atoms[p], cancel(y)) for j, y in enumerate(args) if j != i]
                    self._add(z3.Implies(z3.And(allfin, t.atoms[p], *rest), x.atoms[p]))

    def _product(self, t: Term, args):
        allfin = z3.And([x.fin for x in args])
        re, im = args[0].re, args[0].im
        for x in args[1:]:
            re, im = self._fresh_mul(re, im, x.re, x.im)
        self._add(z3.Implies(allfin, z3.And(t.fin, t.re == re, t.im == im)))
        allint = z3.And([x.atoms["integer"] for x in args])
        k = args[0].k
        for x in args[1:]:
            k = k * x.k
        self._add(z3.Implies(z3.And(allfin, allint), z3.And(t.atoms["integer"], t.k == k)))
        self._infinite_product(t, args)
        self._closure(t, args, allfin, lambda y: z3.Not(y.atoms["zero"]))
        # (+-1/q)*x for an integer q: x = +-q*t is an integer when t is
        var = [x for x in args if not isinstance(x.expr, Rational)]
        c = Mul(*[x.expr for x in args if isinstance(x.expr, Rational)])
        if len(var) == 1 and abs(c.p) == 1 and c.q > 1:
            self._add(z3.Implies(z3.And(var[0].fin, t.atoms["integer"]), var[0].atoms["integer"]))

    def _fresh_mul(self, a, b, c, d):
        """(a + b*I)*(c + d*I) as two fresh reals."""
        n = self._count()
        re, im = z3.Real(f"pre{n}", self.ctx), z3.Real(f"pim{n}", self.ctx)
        self._add(re == a * c - b * d, im == a * d + b * c)
        return re, im

    def _infinite_product(self, t: Term, args):
        """0 * infinity is nan; nonzero values with an infinity among them
        give an infinity, signed when all are extended real."""
        anynan = z3.Or([x.nan for x in args])
        anyinf = z3.Or([x.infinite() for x in args])
        anyzero = z3.Or([x.atoms["zero"] for x in args])
        self._add(z3.Implies(anynan, t.nan), z3.Implies(z3.And(anyinf, anyzero), t.nan))
        nonzero = z3.And([z3.Not(z3.Or(x.nan, x.atoms["zero"])) for x in args])
        self._add(z3.Implies(z3.And(anyinf, nonzero), t.infinite()))
        allext = z3.And([x.ext_real() for x in args])
        neg = z3.BoolVal(False, self.ctx)
        for x in args:
            neg = z3.Xor(neg, x.atoms["extended_negative"])
        self._add(z3.Implies(z3.And(anyinf, nonzero, allext), z3.If(neg, t.ninf, t.pinf)))

    def _power(self, t: Term, b: Term, n: int):
        # n != 0: _node encodes b**0 as 1; the closure axioms below need it
        assert n != 0
        m = abs(n)
        # b**m by repeated squaring over fresh reals
        re, im, k = None, None, None
        sq = (b.re, b.im, b.k)
        e = m
        while e:
            if e & 1:
                if re is None:
                    re, im, k = sq
                else:
                    re, im = self._fresh_mul(re, im, sq[0], sq[1])
                    k = self._fresh_int(k * sq[2])
            e >>= 1
            if e:
                sre, sim = self._fresh_mul(sq[0], sq[1], sq[0], sq[1])
                sq = (sre, sim, self._fresh_int(sq[2] * sq[2]))
        a, ba = t.atoms, b.atoms
        self._add(z3.Implies(b.nan, t.nan))
        if n > 0:
            self._add(z3.Implies(b.fin, z3.And(t.fin, t.re == re, t.im == im)),
                      z3.Implies(z3.And(b.fin, ba["integer"]), z3.And(a["integer"], t.k == k)),
                      z3.Implies(b.infinite(), t.infinite()),
                      z3.Implies(b.pinf, t.pinf),
                      z3.Implies(b.ninf, t.pinf if n % 2 == 0 else t.ninf))
            for p in ("rational", "algebraic"):
                self._add(z3.Implies(z3.And(b.fin, ba[p]), a[p]))
            # b is a root of x**n - t: algebraic t makes b algebraic (the
            # algebraic numbers are algebraically closed); pi**2 is
            # transcendental
            self._add(z3.Implies(z3.And(b.fin, a["algebraic"]), ba["algebraic"]))
            if n >= 2:
                # b**n = b * b**(n - 1) for an integer b: 0 or +-1 for |b| <= 1,
                # else two factors of modulus >= 2, so never a prime
                self._add(z3.Implies(z3.And(b.fin, ba["integer"]), z3.Not(a["prime"])))
        else:
            # t = 1/b**m: exact for b finite nonzero, zoo for 0, 0 for an infinity
            norm = re * re + im * im
            self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"])),
                                 z3.And(t.fin, t.re * norm == re, t.im * norm == -im)),
                      z3.Implies(ba["zero"], t.cinf),
                      z3.Implies(b.infinite(), z3.And(t.fin, t.re == 0, t.im == 0)))
            for p in ("rational", "algebraic"):
                self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"]), ba[p]), a[p]))
            # b is a root of t*x**m - 1 (algebraic closure, as above)
            self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"]), a["algebraic"]), ba["algebraic"]))
            if n == -1:
                # b = 1/t: rational t gives rational b
                self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"]), a["rational"]), ba["rational"]))

    # -- powers with an exponent that is not an integer literal -----------

    def _pow(self, t: Term, e):
        """``b**x`` for an exponent ``x`` that is not an integer literal:
        SymPy's principal value ``exp(x*log(b))`` for finite ``b != 0`` and
        finite ``x``, and satassume's special-values rows elsewhere.

        Special values (satassume special-values, docs/special-values.md of
        satassume#293): N1 a ``nan`` exponent gives ``nan``, a ``nan`` base
        too unless ``x = 0``, which is left free (``nan**0 = 1`` is SymPy's
        convention for a literal 0, design.md, and N1 says ``nan``); P2
        ``b**0 = 1`` for every other ``b``; ``b**1 = b`` (``exp(log b) = b``,
        ``0**1 = 0``, P3 with ``d**1 = d``); ``0**x = 0`` for real ``x > 0``
        (``|z**x| = |z|**x -> 0`` as ``z -> 0``, as SymPy evaluates it) and
        P1 ``0**x = zoo`` for real ``x < 0``; ``0**x`` for non-real ``x`` is
        free (SymPy gives ``nan``, the limit would be ``0`` for ``re x >
        0``: no convention to follow).  P3, an infinite ``b`` to a real
        nonzero ``x``: ``0`` for ``x < 0``; for ``x > 0`` ``oo**x = oo``,
        ``(-oo)**x`` has the direction ``(-1)**x = exp(I*pi*x)``: ``oo``,
        ``-oo`` for an even, odd integer, a non-real direction otherwise,
        and the other infinities stay infinite.  P4, P5, P6 for an infinite
        ``x = +-oo``: the limits of ``b**t`` (``0``, ``oo`` for a growing
        positive ``b``, ``zoo`` for another growing one), and ``nan`` for
        ``|b| = 1``.  An infinite ``b`` to a non-real finite ``x`` and every
        ``b`` to an infinity other than ``+-oo`` are free (no row).

        Finite ``b != 0``, finite ``x``: ``b**x`` is the term
        ``exp(x*log(b))`` (unevaluated SymPy objects, encoded by ``_exp``,
        ``_log`` and ``_product``), so it is finite and nonzero, real and
        positive for a positive ``b`` and real ``x``, and so on.  For a
        literal base ``b = r*exp(I*pi*c0)``, ``r`` a positive rational and
        ``c0`` one of ``0, 1, 1/2, -1/2`` (a rational, ``I`` or a rational
        multiple of ``I``), ``log(b) = log(r) + I*pi*c0`` (principal: ``pi*c0``
        lies in ``(-pi, pi]``), so ``b**x = exp(x*log(r)) *
        exp(I*pi*c0*x)``, with the ``I*pi*c`` facts of ``_exp`` for the
        second factor; when ``x`` is a sum with summands that have the
        factor ``I``, that factor is split by them, ``exp(I*pi*c0*(u + v)) =
        exp(I*pi*c0*u)*exp(I*pi*c0*v)`` (all summands finite).  For a real
        negative ``b`` and real ``x``, ``log b = log|b| + I*pi``, so ``b**x =
        |b|**x * exp(I*pi*x)`` with ``|b|**x > 0``: the signs of the real and
        imaginary parts are those of ``exp(I*pi*x)`` (not real for a
        non-integer ``x``, imaginary for ``x`` in ``1/2 + Z``).

        Integer ``x`` (symbolic: an integer literal is ``_power``), where
        ``b**x`` is the ``|x|``-fold product or its inverse: for real ``b !=
        0`` it is real, positive for ``b > 0``, with the sign ``(-1)**x`` for
        ``b < 0``; for imaginary ``b = I*s`` it is ``I**x * s**x``, real for
        even ``x`` and imaginary for odd ``x``; for an integer ``b`` and ``x
        >= 0`` an integer, even for an even ``b`` and ``x >= 1``, odd for an
        odd ``b``; for ``|b| >= 2``: never prime for ``x >= 2`` (``b`` and
        ``b**(x-1)`` are nontrivial factors), and ``0 < |b**x| <= 1/2`` for
        ``x <= -1``, so no integer (encoded as the weaker ``-1 < t < 1,
        t != 0``, which is all that is needed); a rational ``b != 0`` gives a rational.

        Algebraic numbers: for a rational ``x = p/q`` and finite ``b != 0``,
        ``(b**x)**q = exp(p*log b) = b**p``, so ``b**x`` is algebraic for an
        algebraic ``b``, and ``b`` is algebraic for an algebraic ``b**x``
        (``x != 0``; for ``b = 0`` trivially).  Gelfond-Schneider (1934):
        for algebraic ``b`` other than ``0``, ``1`` and algebraic ``x`` that
        is not rational, every value of ``b**x`` is transcendental.  For a
        literal positive rational ``b = n/d`` (lowest terms) and literal
        ``x = p/q``: ``b**x`` is rational iff ``n`` and ``d`` are ``q``-th
        powers (``n**p/d**p = (u/v)**q`` in lowest terms on both sides
        forces ``n**p = u**q``, so ``q`` divides every exponent of ``n``'s
        prime factorisation, as ``gcd(p, q) = 1``; likewise ``d``), and then
        its value is exact.

        Roots: ``sqrt(b)`` is exactly ``s`` with ``s**2 = b`` and ``re s >
        0`` or ``re s = 0 <= im s`` (``arg s = arg(b)/2`` lies in ``(-pi/2,
        pi/2]``), for every finite ``b``; for a real ``b >= 0``,
        ``b**(1/3)`` is the real ``s >= 0`` with ``s**3 = b`` and
        ``b**(-1/2)``, ``b**(-1/3)`` (``b > 0``) the ``s > 0`` with ``s**q * b
        = 1``."""
        b, x = self.term(e.base), self.term(e.exp)
        ctx = self.ctx
        a, ba, xa = t.atoms, b.atoms, x.atoms
        one, zero = z3.IntVal(1, ctx), z3.IntVal(0, ctx)
        bzero = z3.And(b.fin, b.re == 0, b.im == 0)
        bnz = z3.And(b.fin, z3.Or(b.re != 0, b.im != 0))
        bone = z3.And(b.fin, b.re == 1, b.im == 0)
        xzero = z3.And(x.fin, x.re == 0, x.im == 0)
        xone = z3.And(x.fin, x.re == 1, x.im == 0)
        xreal, binf = x.real(), b.infinite()
        # N1, P2, b**1 = b
        self._add(z3.Implies(x.nan, t.nan), z3.Implies(z3.And(b.nan, z3.Not(xzero)), t.nan))
        self._int_value(t, z3.And(xzero, z3.Not(b.nan)), one)
        self._add(z3.Implies(xone, z3.And(t.fin == b.fin, t.pinf == b.pinf, t.ninf == b.ninf, t.cinf == b.cinf,
                                          t.nan == b.nan, z3.Implies(b.fin, z3.And(t.re == b.re, t.im == b.im)))))
        self._same(t, b, xone)
        # 0**x for real x != 0 (P1)
        self._int_value(t, z3.And(bzero, xreal, x.re > 0), zero)
        self._add(z3.Implies(z3.And(bzero, xreal, x.re < 0), t.cinf))
        # P4, P5: finite b, x = +-oo
        nb = self._fresh_real("pownorm")
        self._add(z3.Implies(z3.And(b.fin, z3.Or(x.pinf, x.ninf)), nb == b.re * b.re + b.im * b.im))
        bpos = z3.And(b.fin, b.im == 0, b.re > 0)
        self._int_value(t, z3.And(b.fin, z3.Or(z3.And(x.pinf, nb < 1), z3.And(x.ninf, nb > 1))), zero)
        self._add(z3.Implies(z3.And(b.fin, z3.Or(z3.And(x.pinf, nb > 1), z3.And(x.ninf, nb < 1))),
                             z3.If(bpos, t.pinf, t.cinf)),
                  z3.Implies(z3.And(b.fin, nb == 1, z3.Or(x.pinf, x.ninf)), t.nan))
        # P6, P3: infinite b
        self._int_value(t, z3.And(binf, z3.Or(x.ninf, z3.And(xreal, x.re < 0))), zero)
        xpos = z3.And(xreal, x.re > 0)
        self._add(z3.Implies(z3.And(binf, x.pinf), z3.If(b.pinf, t.pinf, t.cinf)),
                  z3.Implies(z3.And(b.pinf, xpos), t.pinf),
                  z3.Implies(z3.And(b.cinf, xpos), t.infinite()),
                  z3.Implies(z3.And(b.ninf, xpos),
                             z3.If(xa["integer"], z3.If(x.r == 0, t.pinf, t.ninf), t.cinf)))
        # finite b != 0, finite x: exp(x*log(b))
        cond = z3.And(bnz, x.fin)
        if e.base is not S.Zero:
            self._principal(t, e.base, e.exp, x, cond)
        # integer x
        xint = z3.And(x.fin, xa["integer"])
        breal = z3.And(b.fin, b.im == 0, b.re != 0)
        bimag = z3.And(b.fin, b.re == 0, b.im != 0)
        bint = z3.And(b.fin, ba["integer"])
        big = z3.Or(b.k >= 2, b.k <= -2)
        self._add(z3.Implies(z3.And(xint, breal),
                             z3.And(t.fin, t.im == 0, z3.Implies(b.re > 0, t.re > 0),
                                    z3.Implies(b.re < 0, z3.If(x.r == 0, t.re > 0, t.re < 0)))),
                  z3.Implies(z3.And(xint, bimag),
                             z3.And(t.fin, z3.If(x.r == 0, z3.And(t.im == 0, t.re != 0),
                                                 z3.And(t.re == 0, t.im != 0)))),
                  z3.Implies(z3.And(bint, xint, x.k >= 0), a["integer"]),
                  z3.Implies(z3.And(bint, ba["even"], xint, x.k >= 1), a["even"]),
                  z3.Implies(z3.And(bint, z3.Not(ba["even"]), xint, x.k >= 0),
                             z3.And(a["integer"], z3.Not(a["even"]))),
                  z3.Implies(z3.And(bint, big, xint, x.k >= 2), z3.Not(a["prime"])),
                  z3.Implies(z3.And(bint, big, xint, x.k <= -1),
                             z3.And(t.fin, t.im == 0, t.re > -1, t.re < 1, t.re != 0)),
                  z3.Implies(z3.And(bnz, ba["rational"], xint), a["rational"]))
        # algebraic numbers: rational x, Gelfond-Schneider
        xrat = z3.And(x.fin, xa["rational"])
        self._add(z3.Implies(z3.And(bnz, ba["algebraic"], xrat), a["algebraic"]),
                  z3.Implies(z3.And(b.fin, xrat, z3.Not(xzero), t.fin, a["algebraic"]), ba["algebraic"]),
                  z3.Implies(z3.And(bnz, ba["algebraic"], z3.Not(bone), x.fin, xa["algebraic"],
                                    z3.Not(xa["rational"])), z3.Not(a["algebraic"])))
        if isinstance(e.exp, Rational):
            self._rational_power(t, b, e.base, Fraction(int(e.exp.p), int(e.exp.q)))

    def _principal(self, t: Term, base, xe, x: Term, cond):
        """Under ``cond`` (finite ``b != 0``, finite ``x``) ``t`` is the
        principal value ``exp(x*log(b))`` (``_pow``)."""
        lit = _polar_literal(base)
        if lit is None:
            val = exp(Mul(xe, log(base, evaluate=False), evaluate=False), evaluate=False)
            # a real negative b: the direction is that of exp(I*pi*x)
            b = self.term(base)
            d = self.term(exp(Mul(S.ImaginaryUnit, S.Pi, xe, evaluate=False), evaluate=False))
            self._add(z3.Implies(z3.And(cond, b.real(), b.re < 0, x.real()),
                                 z3.And((t.re > 0) == (d.re > 0), (t.re < 0) == (d.re < 0),
                                        (t.im > 0) == (d.im > 0), (t.im < 0) == (d.im < 0))))
        else:
            r, c0 = lit
            factors = []
            if r != 1:
                factors.append(exp(Mul(xe, log(Rational(r.numerator, r.denominator), evaluate=False),
                                       evaluate=False), evaluate=False))
            if c0:
                groups = [xe]
                if isinstance(xe, Add):
                    imag = [g for g in xe.args if g is S.ImaginaryUnit
                            or (isinstance(g, Mul) and S.ImaginaryUnit in g.args)]
                    rest = [g for g in xe.args if g not in imag]
                    if imag and rest:
                        groups = [g[0] if len(g) == 1 else Add(*g, evaluate=False) for g in (rest, imag)]
                        cond = z3.And(cond, *[self.term(g).fin for g in xe.args])
                for g in groups:
                    if isinstance(g, Rational):
                        c = Rational(c0.numerator, c0.denominator) * g
                    elif c0 == 1:
                        c = g
                    else:
                        c = Mul(Rational(c0.numerator, c0.denominator), g, evaluate=False)
                    factors.append(exp(Mul(S.ImaginaryUnit, S.Pi, c, evaluate=False), evaluate=False))
            if not factors:
                self._int_value(t, cond, z3.IntVal(1, self.ctx))
                return
            val = factors[0] if len(factors) == 1 else Mul(*factors, evaluate=False)
        v = self.term(val)
        self._add(z3.Implies(cond, z3.And(t.fin, t.re == v.re, t.im == v.im)))
        self._same(t, v, cond)

    def _rational_power(self, t: Term, b: Term, base, f: Fraction):
        """A literal rational exponent ``p/q`` (``_pow``): roots, and the
        rationality of a power of a literal positive rational."""
        p, q = f.numerator, f.denominator
        if f == Fraction(1, 2):
            sre, sim = self._fresh_mul(t.re, t.im, t.re, t.im)
            self._add(z3.Implies(b.fin, z3.And(t.fin, sre == b.re, sim == b.im,
                                               z3.Or(t.re > 0, z3.And(t.re == 0, t.im >= 0)))))
        elif abs(p) == 1 and q in (2, 3):
            s = t.re
            sq = s * s if q == 2 else s * s * s
            if p == 1:
                self._add(z3.Implies(z3.And(b.real(), b.re >= 0), z3.And(t.fin, t.im == 0, s >= 0, sq == b.re)))
            else:
                self._add(z3.Implies(z3.And(b.real(), b.re > 0), z3.And(t.fin, t.im == 0, s > 0, sq * b.re == 1)))
        if isinstance(base, Rational) and base > 0:
            n, d = int(base.p), int(base.q)
            rn, rd = _iroot(n, q), _iroot(d, q)
            if rn ** q == n and rd ** q == d:
                v = Fraction(rn, rd) ** p
                self._add(t.fin, t.im == 0, t.re == self._q(v), t.atoms["rational"])
            else:
                self._add(z3.Not(t.atoms["rational"]))

    def _same(self, t: Term, z: Term, cond):
        """Under ``cond`` the value of ``t`` is that of ``z``: the
        predicates without a numeric definition agree."""
        a, za = t.atoms, z.atoms
        self._add(z3.Implies(cond, z3.And([a[p] == za[p] for p in
                                           ("integer", "rational", "algebraic", "prime", "composite", "even")])),
                  z3.Implies(z3.And(cond, za["integer"]), z3.And(t.k == z.k, t.r == z.r)))

    def _int_value(self, t: Term, cond, k):
        """Under ``cond`` the value of ``t`` is the integer ``k``."""
        self._add(z3.Implies(cond, z3.And(t.fin, t.im == 0, t.re == z3.ToReal(k), t.atoms["integer"], t.k == k)))

    def _complex_part(self, t: Term, f, z: Term):
        """``Abs``, ``re``, ``im``, ``conjugate``, ``sign`` of ``z``, exact on
        the pair ``re_z + im_z*I``.  ``nan`` gives ``nan`` (satassume
        special-values N1); an infinity ``t*d`` (t real -> +oo, satassume
        special-values V2) gives the limit of the function, which only
        ``Abs`` (row F3: ``oo``) has for every infinity: ``re``, ``im``,
        ``conjugate`` and ``sign`` of ``+-oo`` are ``+-oo``, ``0``, ``+-oo``,
        ``+-1``, and are left free for the other infinities (``zoo`` has no
        direction).  Number theory: the algebraic numbers are closed under
        complex conjugation (a root of a rational polynomial ``p`` has its
        conjugate as a root of ``p``), the field operations and square
        roots, so ``re = (z + conj z)/2``, ``im = (z - conj z)/(2*I)``,
        ``|z| = sqrt(z*conj z)`` and ``z/|z|`` of an algebraic ``z`` are
        algebraic."""
        a, za = t.atoms, z.atoms
        zre, zim = z.re, z.im
        real = z.real()
        self._add(z3.Implies(z.nan, t.nan))
        if f is Abs:
            self._add(z3.Implies(z.infinite(), t.pinf),
                      z3.Implies(z.fin, z3.And(t.fin, t.im == 0, t.re >= 0, t.re * t.re == zre * zre + zim * zim,
                                               t.re >= zre, t.re >= -zre, t.re >= zim, t.re >= -zim)),
                      # a real z is +-|z|: the same rationality, |k| with the parity of k
                      z3.Implies(real, t.re == z3.If(zre >= 0, zre, -zre)),
                      z3.Implies(real, z3.And([a[p] == za[p] for p in ("integer", "rational", "algebraic")])),
                      z3.Implies(z3.And(real, za["integer"]),
                                 z3.And(t.k == z3.If(z.k >= 0, z.k, -z.k), t.r == z.r)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))
            self._same(t, z, z3.And(real, zre >= 0))
        elif f is Re:
            self._add(z3.Implies(z.pinf, t.pinf), z3.Implies(z.ninf, t.ninf),
                      z3.Implies(z.fin, z3.And(t.fin, t.im == 0, t.re == zre)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))
            self._same(t, z, real)
        elif f is Im:
            self._int_value(t, z3.Or(z.pinf, z.ninf, real), z3.IntVal(0, self.ctx))
            self._add(z3.Implies(z.fin, z3.And(t.fin, t.im == 0, t.re == zim)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))
        elif f is conjugate:
            self._add(z3.Implies(z.pinf, t.pinf), z3.Implies(z.ninf, t.ninf),
                      z3.Implies(z.fin, z3.And(t.fin, t.re == zre, t.im == -zim)),
                      # conjugation is an involution
                      z3.Implies(z.fin, a["algebraic"] == za["algebraic"]))
            self._same(t, z, real)
        else:  # sign: 0 at 0, else z/|z|
            one = z3.IntVal(1, self.ctx)
            self._int_value(t, z.pinf, one)
            self._int_value(t, z.ninf, -one)
            self._int_value(t, real, z3.If(zre > 0, one, z3.If(zre < 0, -one, z3.IntVal(0, self.ctx))))
            # z/|z| for non-real z (real z above, linear), with the term of
            # Abs(z) (unevaluated: SymPy's evaluation is not used)
            m = self.term(Abs(z.expr, evaluate=False)).re
            self._add(z3.Implies(z3.And(z.fin, zim != 0), z3.And(t.fin, t.re * m == zre, t.im * m == zim,
                                                                             t.re * t.re + t.im * t.im == 1)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))

    def _fresh_real(self, name):
        return z3.Real(f"{name}{self._count()}", self.ctx)

    def _exp_pair(self, cond, u, v):
        """Under ``cond``, ``v = e**u`` for reals ``u``, ``v``.  The facts:
        ``e**u > 0``; the tangent at 0, ``e**u >= 1 + u`` (convexity; it is
        ``log(v) <= v - 1`` read the other way); ``e**0 = 1``; and, since
        ``u -> e**u`` is strictly increasing on R, for every pair
        registered before, ``u < u'`` iff ``v < v'`` and ``u = u'`` iff
        ``v = v'``: finitely many ground instances, quadratic in the number
        of ``exp``/``log`` terms of the query.  ``log(1) = 0``,
        ``log(exp(x)) = x`` for real ``x`` and the sign of ``log(x)`` against
        ``x - 1`` follow from these."""
        one = z3.RealVal(1, self.ctx)
        self._add(z3.Implies(cond, z3.And(v > 0, v >= one + u, (u < 0) == (v < one), (u == 0) == (v == one))))
        for c2, u2, v2 in self._pairs:
            self._add(z3.Implies(z3.And(cond, c2), z3.And((u < u2) == (v < v2), (u == u2) == (v == v2))))
        self._pairs.append((cond, u, v))

    def _exp(self, t: Term, z: Term):
        """``exp(z)``, ``z = a + b*I``: ``e**a * (cos b + I*sin b)``.

        Infinities and nan (satassume special-values): N1 ``nan -> nan``;
        F1 ``exp(oo) = oo``, ``exp(-oo) = 0``, and for the other kind
        (``zoo -> nan``; ``oo*d`` with ``|d| = 1`` non-real gives ``zoo``,
        ``0`` or ``nan`` by the sign of ``re(d)``) one of ``cinf``, ``0``,
        ``nan`` and nothing more, the kind not telling which.

        Finite ``z``: ``|exp(z)| = e**a`` with ``e**a`` the fresh real
        ``m`` (an exp pair with ``a``, see ``_exp_pair``), so
        ``exp(z) != 0``, and ``exp(z) = m`` for real ``z``.  The signs of
        ``cos b`` and ``sin b`` for ``-pi <= b <= pi`` (linear in ``b`` and
        ``pi``): ``sin b > 0`` on ``(0, pi)``, ``< 0`` on ``(-pi, 0)``,
        ``cos b > 0`` for ``|b| < pi/2``, ``= 0`` at ``|b| = pi/2``, ``< 0``
        for ``pi/2 < |b| <= pi``, and ``exp(+-pi*I) = -1``.  For
        ``z = I*pi*c`` (a product with the factors ``I`` and ``pi``) and
        real ``c``: ``exp(z) = cos(pi*c) + I*sin(pi*c)``, which is
        ``(-1)**c`` for an integer ``c`` and not real otherwise
        (``sin(pi*c) = 0`` iff ``c`` is an integer), and imaginary iff
        ``c - 1/2`` is an integer (``cos(pi*c) = 0``); for a literal
        rational ``c`` the signs of ``cos(pi*c)``, ``sin(pi*c)`` after
        reducing ``c`` mod 2 (period ``2*pi*I``).  ``exp(0) = 1``.
        Hermite-Lindemann: ``e**w`` is transcendental for algebraic
        ``w != 0``.  ``exp(log(w)) = w`` for finite ``w != 0`` (``log(w)``
        is a logarithm of ``w``).  At a rational point ``r``, ``m`` lies in
        the rational enclosure of ``e**r`` (``bounds.exp_bounds``).
        Not encoded (z3 did not decide the even/odd case of the integer
        witness ``b = n*pi`` within the limits): "``exp(z)`` real iff
        ``b/pi`` is an integer" for ``b`` not of the form ``pi*c``."""
        a, za = t.atoms, z.atoms
        ctx = self.ctx
        self._add(z3.Implies(z.nan, t.nan), z3.Implies(z.pinf, t.pinf),
                  z3.Implies(z.cinf, z3.Or(t.cinf, t.nan, z3.And(t.fin, t.re == 0, t.im == 0))))
        self._int_value(t, z.ninf, z3.IntVal(0, ctx))
        zero = z3.And(z.fin, z.re == 0, z.im == 0)
        self._int_value(t, zero, z3.IntVal(1, ctx))
        m = self._fresh_real("expm")
        self._add(z3.Implies(z.fin, z3.And(t.fin, t.re * t.re + t.im * t.im == m * m)),
                  z3.Implies(z3.And(z.fin, z.im == 0), z3.And(t.re == m, t.im == 0)))
        self._exp_pair(z.fin, z.re, m)
        pi = self.term(S.Pi).re
        b, re, im = z.im, t.re, t.im
        self._add(z3.Implies(z.fin, z3.And(
            z3.Implies(z3.And(b > 0, b < pi), im > 0),
            z3.Implies(z3.And(b < 0, b > -pi), im < 0),
            z3.Implies(z3.And(2 * b < pi, 2 * b > -pi), re > 0),
            z3.Implies(z3.Or(2 * b == pi, 2 * b == -pi), re == 0),
            z3.Implies(z3.Or(z3.And(2 * b > pi, b <= pi), z3.And(2 * b < -pi, b >= -pi)), re < 0),
            z3.Implies(z3.Or(b == pi, b == -pi), z3.And(re == -m, im == 0)))))
        w = z.expr
        if isinstance(w, Mul) and S.ImaginaryUnit in w.args and S.Pi in w.args:
            rest = list(w.args)
            rest.remove(S.ImaginaryUnit)
            rest.remove(S.Pi)
            c = self.term(Mul(*rest))
            one = z3.IntVal(1, ctx)
            self._int_value(t, z3.And(c.real(), c.atoms["integer"]), z3.If(c.r == 0, one, -one))
            self._add(z3.Implies(z3.And(c.real(), z3.Not(c.atoms["integer"])), im != 0))
            if isinstance(c.expr, Rational):
                # period 2*pi*I: exp(I*pi*c) = exp(I*pi*c') with c' = c - 2*n
                # in (-1, 1], and pi*c' in (-pi, pi] has the signs above
                f = Fraction(int(c.expr.p), int(c.expr.q))
                f -= 2 * math.ceil((f - 1) / 2)
                self._add(im > 0 if 0 < f < 1 else im < 0 if -1 < f < 0 else im == 0,
                          re > 0 if abs(f) < Fraction(1, 2) else re == 0 if abs(f) == Fraction(1, 2) else re < 0)
            else:
                # cos(pi*c) = 0 iff c - 1/2 is an integer (the zeros of cos)
                h = self.term(Add(c.expr, Rational(-1, 2), evaluate=False))
                self._add(z3.Implies(c.real(), (re == 0) == h.atoms["integer"]))
                ce = c.expr
                if isinstance(ce, Mul) and len(ce.args) == 2 and ce.args[0] in (S.Half, -S.Half):
                    # c = +-y/2 lies in 1/2 + Z iff y is an odd integer (the
                    # same fact, on y's integer witness)
                    y = self.term(ce.args[1])
                    self._add(z3.Implies(y.real(), (re == 0) == z3.And(y.atoms["integer"], y.r == 1)))
        # Hermite-Lindemann (1882)
        self._add(z3.Implies(z3.And(z.fin, za["algebraic"], z3.Not(zero)), z3.Not(a["algebraic"])))
        if isinstance(w, log) and len(w.args) == 1:
            v = self.term(w.args[0])
            ok = z3.And(v.fin, z3.Not(z3.And(v.re == 0, v.im == 0)))
            self._add(z3.Implies(ok, z3.And(t.fin, t.re == v.re, t.im == v.im)))
            self._same(t, v, ok)
        if isinstance(w, Rational):
            b = exp_bounds(Fraction(int(w.p), int(w.q)))
            if b is not None:
                self._add(m > self._q(b[0]), m < self._q(b[1]))

    def _log(self, t: Term, z: Term):
        """``log(z)``, SymPy's principal branch ``log|z| + I*arg(z)``,
        ``-pi < arg(z) <= pi``.

        Special values (satassume special-values): N1 ``nan -> nan``; F2
        ``log(0) = zoo`` and ``log(zoo) = zoo`` (conventions), ``log`` of a
        directed infinity is ``oo`` (``log(-oo) = oo``, "Choices" A1); so
        the other kind gives ``oo`` or ``cinf``.

        Finite ``z = a + b*I != 0``: ``re = log|z|``, an exp pair with
        ``|z|`` (``_exp_pair``); ``im = arg(z)``, by the quadrant of
        ``(a, b)``: ``0`` on the positive axis, ``pi`` on the negative
        axis, in ``(0, pi)`` for ``b > 0`` and ``(-pi, 0)`` for ``b < 0``,
        ``+-pi/2`` on the imaginary axis, ``|arg| < pi/2`` for ``a > 0``
        and ``> pi/2`` for ``a < 0``.  ``log(1) = 0``.  Hermite-Lindemann:
        a logarithm ``w`` (any branch) of an algebraic ``z`` other than
        ``0``, ``1`` is transcendental (``w`` is not ``0``, and ``e**w = z``
        would be transcendental for algebraic ``w``).  ``log(exp(x)) = x``
        for real ``x``.  At a rational point ``r``, ``re`` lies in the
        rational enclosure of ``log|r|`` (``bounds.log_bounds``)."""
        a, za = t.atoms, z.atoms
        ctx = self.ctx
        self._add(z3.Implies(z.nan, t.nan), z3.Implies(z3.Or(z.pinf, z.ninf), t.pinf),
                  z3.Implies(z.cinf, z3.Or(t.pinf, t.cinf)),
                  z3.Implies(z3.And(z.fin, z.re == 0, z.im == 0), t.cinf))
        x, y, th = z.re, z.im, t.im
        nz = z3.And(z.fin, z3.Not(z3.And(x == 0, y == 0)))
        m = self._fresh_real("logm")
        self._add(z3.Implies(nz, z3.And(t.fin, m > 0, m * m == x * x + y * y, m >= x, m >= -x, m >= y, m >= -y)),
                  z3.Implies(z3.And(nz, y == 0), m == z3.If(x >= 0, x, -x)))
        self._exp_pair(nz, t.re, m)
        pi = self.term(S.Pi).re
        self._add(z3.Implies(nz, z3.And(
            z3.Implies(y > 0, z3.And(th > 0, th < pi)),
            z3.Implies(y < 0, z3.And(th < 0, th > -pi)),
            z3.Implies(z3.And(y == 0, x > 0), th == 0),
            z3.Implies(z3.And(y == 0, x < 0), th == pi),
            z3.Implies(x > 0, z3.And(2 * th < pi, 2 * th > -pi)),
            z3.Implies(z3.And(x == 0, y > 0), 2 * th == pi),
            z3.Implies(z3.And(x == 0, y < 0), 2 * th == -pi),
            z3.Implies(z3.And(x < 0, y > 0), 2 * th > pi),
            z3.Implies(z3.And(x < 0, y < 0), 2 * th < -pi))))
        one = z3.And(z.fin, x == 1, y == 0)
        self._int_value(t, one, z3.IntVal(0, ctx))
        # Hermite-Lindemann (1882)
        self._add(z3.Implies(z3.And(nz, za["algebraic"], z3.Not(one)), z3.Not(a["algebraic"])))
        w = z.expr
        if isinstance(w, exp) and len(w.args) == 1:
            v = self.term(w.args[0])
            self._add(z3.Implies(v.real(), z3.And(t.fin, t.re == v.re, t.im == 0)))
            self._same(t, v, v.real())
        if isinstance(w, Rational) and w != 0:
            b = log_bounds(abs(Fraction(int(w.p), int(w.q))))
            if b is not None:
                self._add(t.re > self._q(b[0]), t.re < self._q(b[1]))

    # -- circular and hyperbolic functions ------------------------------

    def _component(self, z: Term, part: str):
        """``re`` or ``im`` of ``z`` (a z3 real), and its value when ``z`` is
        a literal rational ``r`` or ``r*I`` (else None)."""
        u = z.re if part == "re" else z.im
        w, r = z.expr, None
        if isinstance(w, Rational):
            r = Fraction(int(w.p), int(w.q)) if part == "re" else Fraction(0)
        elif w is S.ImaginaryUnit:
            r = Fraction(0) if part == "re" else Fraction(1)
        elif isinstance(w, Mul) and len(w.args) == 2 and w.args[1] is S.ImaginaryUnit \
                and isinstance(w.args[0], Rational):
            c = w.args[0]
            r = Fraction(0) if part == "re" else Fraction(int(c.p), int(c.q))
        return u, r

    def _pi_multiple(self, z: Term, part: str):
        """The term of ``c`` when ``z`` is ``pi*c`` (part ``re``) or
        ``I*pi*c`` (part ``im``), a product with these factors; then, for
        real ``c``, that part of ``z`` is ``pi*c``."""
        w = z.expr
        if not isinstance(w, Mul) or S.Pi not in w.args or (S.ImaginaryUnit in w.args) != (part == "im"):
            return None
        rest = list(w.args)
        rest.remove(S.Pi)
        if part == "im":
            rest.remove(S.ImaginaryUnit)
        return self.term(Mul(*rest))

    def _circ(self, z: Term, part: str):
        """``(cos u, sin u)`` for the real ``u`` = that part of ``z``, as two
        fresh reals ``C``, ``S``, valid when ``z`` is finite.  The facts:
        ``C**2 + S**2 = 1`` (and so both in ``[-1, 1]``); ``cos 0 = 1``,
        ``sin 0 = 0``; the signs of ``cos u`` and ``sin u`` for ``-pi <= u
        <= pi``, linear in ``u`` and the ``pi`` term, as for ``exp``:
        ``sin u > 0`` on ``(0, pi)`` and ``< 0`` on ``(-pi, 0)``, ``cos u >
        0`` for ``|u| < pi/2``, ``= 0`` at ``|u| = pi/2``, ``< 0`` for
        ``pi/2 < |u| <= pi``, and ``(C, S) = (-1, 0)`` at ``u = +-pi``.
        For ``u = pi*c`` with real ``c`` (``_pi_multiple``):
        ``sin(pi*c) = 0`` iff ``c`` is an integer (the zeros of ``sin`` are
        the integer multiples of ``pi``), and then ``cos(pi*c) = (-1)**c``.
        At a rational point ``r``, ``C`` and ``S`` lie in the rational
        enclosures of ``bounds.sin_cos_bounds`` (Taylor polynomial with
        Lagrange's remainder).  Nothing about periodicity outside
        ``[-pi, pi]`` for other arguments (it needs an integer witness for
        ``u/pi``, see ``_exp``)."""
        key = (z.expr, part, "circ")
        if key in self._trig:
            return self._trig[key]
        u, r = self._component(z, part)
        cos_u, sin_u = self._fresh_real("cos"), self._fresh_real("sin")
        self._trig[key] = (cos_u, sin_u)
        pi = self.term(S.Pi).re
        C, S_ = cos_u, sin_u
        self._add(z3.Implies(z.fin, z3.And(
            C * C + S_ * S_ == 1, C >= -1, C <= 1, S_ >= -1, S_ <= 1,
            z3.Implies(u == 0, z3.And(C == 1, S_ == 0)),
            z3.Implies(z3.And(u > 0, u < pi), S_ > 0),
            z3.Implies(z3.And(u < 0, u > -pi), S_ < 0),
            z3.Implies(z3.And(2 * u < pi, 2 * u > -pi), C > 0),
            z3.Implies(z3.Or(2 * u == pi, 2 * u == -pi), C == 0),
            z3.Implies(z3.Or(z3.And(2 * u > pi, u <= pi), z3.And(2 * u < -pi, u >= -pi)), C < 0),
            z3.Implies(z3.Or(u == pi, u == -pi), z3.And(C == -1, S_ == 0)))))
        c = self._pi_multiple(z, part)
        if c is not None:
            ok = z3.And(z.fin, c.real())
            one = z3.RealVal(1, self.ctx)
            self._add(z3.Implies(z3.And(ok, c.atoms["integer"]), z3.And(S_ == 0, C == z3.If(c.r == 0, one, -one))),
                      z3.Implies(z3.And(ok, z3.Not(c.atoms["integer"])), S_ != 0))
        if r is not None and r != 0:
            b = sin_cos_bounds(r)
            if b is not None:
                (slo, shi), (clo, chi) = b
                self._add(z3.Implies(z.fin, z3.And(S_ > self._q(slo), S_ < self._q(shi),
                                                   C > self._q(clo), C < self._q(chi))))
        return cos_u, sin_u

    def _hyp(self, z: Term, part: str):
        """``(cosh u, sinh u)`` for the real ``u`` = that part of ``z``, as
        two fresh reals ``H``, ``K``, valid when ``z`` is finite:
        ``H**2 - K**2 = 1``, ``H >= 1``, ``K`` has the sign of ``u`` and
        ``|K| >= |u|`` (``sinh u = u + u**3/3! + ...``, all terms of the
        sign of ``u``), ``cosh 0 = 1``, ``sinh 0 = 0``, and ``H + K = e**u``,
        an exp pair (``_exp_pair``: positive, increasing, ``e**u >= 1 +
        u``).  At a rational point ``r``, the enclosures of
        ``bounds.cosh_sinh_bounds`` (from those of ``e**r``)."""
        key = (z.expr, part, "hyp")
        if key in self._trig:
            return self._trig[key]
        u, r = self._component(z, part)
        H, K = self._fresh_real("cosh"), self._fresh_real("sinh")
        self._trig[key] = (H, K)
        self._add(z3.Implies(z.fin, z3.And(
            H * H - K * K == 1, H >= 1, (K > 0) == (u > 0), (K < 0) == (u < 0),
            z3.Implies(u >= 0, K >= u), z3.Implies(u <= 0, K <= u),
            z3.Implies(u == 0, z3.And(H == 1, K == 0)))))
        self._exp_pair(z.fin, u, H + K)
        if r is not None and r != 0:
            b = cosh_sinh_bounds(r)
            if b is not None:
                (clo, chi), (slo, shi) = b
                self._add(z3.Implies(z.fin, z3.And(H > self._q(clo), H < self._q(chi),
                                                   K > self._q(slo), K < self._q(shi))))
        return H, K

    def _even_odd(self, z: Term, family: str):
        """The even and odd function of the family at finite ``z = a + b*I``,
        each as a pair of fresh reals (shared by all functions of ``z``):
        ``cos z = cos a cosh b - I sin a sinh b``, ``sin z = sin a cosh b
        + I cos a sinh b`` (the addition theorems with ``cos(I*b) = cosh
        b``, ``sin(I*b) = I sinh b``), and ``cosh z = cosh a cos b + I sinh
        a sin b``, ``sinh z = sinh a cos b + I cosh a sin b`` (``cosh z =
        cos(I*z)``, ``sinh z = -I sin(I*z)``)."""
        key = (z.expr, family)
        if key in self._trig:
            return self._trig[key]
        C, S_, H, K = self._quad(z, family)
        if family == "circ":
            parts = ((C, H), (-1, S_, K), (S_, H), (C, K))
        else:
            parts = ((H, C), (K, S_), (K, C), (H, S_))
        vals = [self._fresh_product(z, *p) for p in parts]
        res = self._trig[key] = ((vals[0], vals[1]), (vals[2], vals[3]))
        return res

    def _quad(self, z: Term, family: str):
        """``C, S, H, K``: cos and sin of the circular part, cosh and sinh
        of the hyperbolic part (``re``, ``im`` for the circular family,
        ``im``, ``re`` for the hyperbolic one)."""
        circ, hyp = ("re", "im") if family == "circ" else ("im", "re")
        return self._circ(z, circ) + self._hyp(z, hyp)

    def _fresh_product(self, z: Term, *factors):
        """A fresh real equal to the product (a leading -1 negates it) when
        ``z`` is finite."""
        v = self._fresh_real("tv")
        prod = factors[0] * factors[1] if len(factors) == 2 else -(factors[1] * factors[2])
        self._add(z3.Implies(z.fin, v == prod))
        return v

    def _trig_function(self, t: Term, family: str, num, den, z: Term):
        """``cos``, ``sin``, ``tan``, ``cot``, ``sec``, ``csc`` and their
        hyperbolic counterparts of ``z``.

        Special values: ``nan`` gives ``nan`` (satassume special-values
        N1).  An infinite argument leaves the value free: the table has no
        row for these functions (it names ``sin(oo)`` as a point no row
        covers), and none of them has a limit at every infinity.

        Finite ``z``: ``cos``, ``sin`` (``cosh``, ``sinh``) exactly by
        their real and imaginary parts (``_even_odd``).  The other four are
        quotients, ``tan = sin/cos``, ``cot = cos/sin``, ``sec = 1/cos``,
        ``csc = 1/sin``, each ``n/d = n*conj(d)/|d|**2`` with the real
        denominator ``|d|**2``, which is ``C**2 + K**2`` for ``d = cos z``
        (``C**2*H**2 + S**2*K**2 = C**2*(1 + K**2) + (1 - C**2)*K**2``)
        and ``S**2 + K**2`` for ``d = sin z``, likewise ``C**2 + K**2`` for
        ``cosh`` and ``S**2 + K**2`` for ``sinh`` (``C, S, H, K`` as in
        ``_even_odd``).  For ``tan`` the numerator is ``sin z *
        conj(cos z) = (S*H + I*C*K)*(C*H + I*S*K) = S*C*(H**2 - K**2) +
        I*H*K*(S**2 + C**2) = S*C + I*H*K``, for ``cot`` ``S*C - I*H*K``,
        for ``tanh`` ``H*K + I*S*C``, for ``coth`` ``H*K - I*S*C``, and for
        the reciprocals ``conj(d)``.  (A real denominator keeps z3's
        nonlinear search small: ``t*d = n`` with complex ``d`` made it time
        out on ``Q.algebraic(tan(x))``.)  Where the denominator is nonzero
        the value ``t`` is finite with ``t*|d|**2 = n*conj(d)``; where
        ``d = 0`` it is ``zoo``: ``1/0 = zoo`` (design.md, satassume's
        convention) and ``n*zoo = zoo`` for the numerator ``n != 0``
        (special-values M3; ``cos`` and ``sin`` have no common zero, as
        ``cos**2 + sin**2 = 1``).  So ``tan(pi/2) = cot(0) = csc(0) =
        sec(pi/2) = coth(0) = csch(0) = zoo``, as SymPy evaluates them.

        Hermite-Lindemann: for algebraic ``z != 0`` the value is
        transcendental or ``zoo``.  With ``w = e**(I*z)`` (``e**z`` for the
        hyperbolic family), transcendental by Hermite-Lindemann (``I*z`` is
        algebraic and nonzero): ``cos z = c`` would make ``w`` a root of
        ``w**2 - 2*c*w + 1``, ``sin z = s`` of ``w**2 - 2*I*s*w - 1``, so
        neither is algebraic; ``tan z = (w**2 - 1)/(I*(w**2 + 1)) = t``
        gives ``(1 - I*t)*w**2 = 1 + I*t``, so for algebraic ``t`` either
        ``w**2`` (and so ``w``) is algebraic or ``1 - I*t = 0 = 1 + I*t``,
        impossible; ``cot``, ``sec``, ``csc`` are reciprocals of these,
        and the reciprocal of a nonzero algebraic number is algebraic.  The
        hyperbolic functions are the same with ``e**z`` (``cosh z = (w +
        1/w)/2``, ...)."""
        a, za = t.atoms, z.atoms
        self._add(z3.Implies(z.nan, t.nan))
        even, odd = self._even_odd(z, family)
        pick = {"E": even, "O": odd}
        if den is None:
            v = pick[num]
            self._add(z3.Implies(z.fin, z3.And(t.fin, t.re == v[0], t.im == v[1])))
        else:
            C, S_, H, K = self._quad(z, family)
            norm = self._fresh_real("tnorm")
            self._add(z3.Implies(z.fin, norm == (C * C if den == "E" else S_ * S_) + K * K))
            if num == 1:                        # conj(d)
                d = pick[den]
                n = (d[0], -d[1])
            else:                               # S*C +- I*H*K, or H*K +- I*S*C
                sc, hk = self._fresh_product(z, S_, C), self._fresh_product(z, H, K)
                sgn = 1 if num == "O" else -1
                n = (sc, sgn * hk) if family == "circ" else (hk, sgn * sc)
            self._add(z3.Implies(z3.And(z.fin, norm == 0), t.cinf),
                      z3.Implies(z3.And(z.fin, norm != 0),
                                 z3.And(t.fin, t.re * norm == n[0], t.im * norm == n[1])))
        zero = z3.And(z.fin, z.re == 0, z.im == 0)
        self._add(z3.Implies(z3.And(z.fin, za["algebraic"], z3.Not(zero)), z3.Not(a["algebraic"])))

    def _inverse(self, t: Term, f, x: Term):
        """The inverse functions, SymPy's principal branches.

        Every branch of each is a right inverse where it is finite: the
        principal values are logarithms of algebraic expressions in ``x``
        (``asin x = -I*log(I*x + sqrt(1 - x**2))``, ``atan x = log((1 +
        I*x)/(1 - I*x))/(2*I)``, ``acos = pi/2 - asin``, ``acot x = atan(1/x)``,
        ``acot(0) = pi/2``, ``asinh x = log(x + sqrt(x**2 + 1))``, ...), and
        ``e**log(v) = v`` for every branch of ``log`` and ``sqrt``, so a
        finite value ``w`` of ``f^-1(x)`` satisfies ``f(w) = x``.  From
        that alone:

        - ``w = 0`` only if ``x = f(0)`` (``0`` for ``asin``, ``atan``,
          ``asinh``, ``atanh``, ``1`` for ``acos``, ``acosh``; never for
          ``acot``, ``acoth``, as ``cot(0) = coth(0) = zoo``); and ``w = 0``
          at that point (the principal values: ``log 1 = 0``).
        - Hermite-Lindemann: for algebraic ``x`` and finite ``w != 0``,
          ``w`` is transcendental, since ``f(w)`` is transcendental or
          ``zoo`` for algebraic ``w != 0`` (``_trig_function``).
        - On the real axis, the principal values are the real inverse
          functions where ``x`` is in the range of ``f`` on R: ``asin`` on
          ``[-1, 1]`` into ``[-pi/2, pi/2]``, ``acos`` on ``[-1, 1]`` into
          ``[0, pi]`` (decreasing: ``0`` only at 1, ``pi/2`` at 0, ``pi``
          only at -1), ``atan`` on R into
          ``(-pi/2, pi/2)``, ``acot`` on R into ``(-pi/2, pi/2]`` (SymPy's
          range: ``atan(1/x)`` for ``x != 0``, ``pi/2`` at 0), ``asinh`` on
          R, ``acosh`` on ``[1, oo)`` into ``[0, oo)``, ``atanh`` on
          ``(-1, 1)``, ``acoth`` on ``|x| > 1``; the odd ones keep the sign
          of ``x``.  For a real ``x`` outside that range (``|x| > 1`` for
          ``asin``, ``acos``, ``atanh``; ``x < 1`` for ``acosh``; ``|x| <
          1`` for ``acoth``) ``w`` is not real, since ``f(w) = x`` and
          ``f`` maps the reals into its range.
        - ``asin``, ``acos``, ``asinh``, ``acosh`` of a finite ``x`` are
          finite: the logarithm's argument is never 0 (``(I*x + s)*(-I*x +
          s) = s**2 + x**2 = 1`` for ``s**2 = 1 - x**2``, likewise for the
          others).

        ``nan`` gives ``nan`` (N1); infinities leave the value free (no
        row; ``atan(oo) = pi/2`` is a limit nobody wrote down)."""
        a, xa = t.atoms, x.atoms
        ctx = self.ctx
        pi = self.term(S.Pi).re
        xr, w = x.re, t.re
        real = x.real()
        tzero = z3.And(t.fin, t.re == 0, t.im == 0)
        treal = z3.And(t.fin, t.im == 0)
        self._add(z3.Implies(x.nan, t.nan))
        f0 = INVERSE[f]
        if f0 is None:
            self._add(z3.Implies(z3.And(x.fin, t.fin), z3.Not(tzero)))
        else:
            self._add(z3.Implies(z3.And(x.fin, tzero), z3.And(xr == f0, x.im == 0)))
            self._int_value(t, z3.And(x.fin, xr == f0, x.im == 0), z3.IntVal(0, ctx))
        self._add(z3.Implies(z3.And(x.fin, xa["algebraic"], t.fin, z3.Not(tzero)), z3.Not(a["algebraic"])))
        if f in (asin, acos, asinh, acosh):
            self._add(z3.Implies(x.fin, t.fin))
        sign = z3.And((w > 0) == (xr > 0), (w < 0) == (xr < 0))
        inside = outside = None
        if f is asin:
            inside, outside = z3.And(xr >= -1, xr <= 1), z3.Or(xr < -1, xr > 1)
            facts = z3.And(sign, 2 * w >= -pi, 2 * w <= pi, z3.Implies(xr == 1, 2 * w == pi),
                           z3.Implies(xr == -1, 2 * w == -pi))
        elif f is acos:
            inside, outside = z3.And(xr >= -1, xr <= 1), z3.Or(xr < -1, xr > 1)
            facts = z3.And(w >= 0, w <= pi, (w > 0) == (xr < 1), (2 * w < pi) == (xr > 0),
                           (2 * w == pi) == (xr == 0), (w < pi) == (xr > -1))
        elif f is atan:
            inside = z3.BoolVal(True, ctx)
            facts = z3.And(sign, 2 * w > -pi, 2 * w < pi)
        elif f is acot:
            inside = z3.BoolVal(True, ctx)
            facts = z3.And(2 * w > -pi, 2 * w <= pi, z3.Implies(xr > 0, z3.And(w > 0, 2 * w < pi)),
                           z3.Implies(xr < 0, w < 0), z3.Implies(xr == 0, 2 * w == pi))
        elif f is asinh:
            inside = z3.BoolVal(True, ctx)
            facts = sign
        elif f is acosh:
            inside, outside = xr >= 1, xr < 1
            facts = z3.And(w >= 0, (w > 0) == (xr > 1))
        elif f is atanh:
            inside, outside = z3.And(xr > -1, xr < 1), z3.Or(xr < -1, xr > 1)
            facts = sign
        else:  # acoth
            inside, outside = z3.Or(xr < -1, xr > 1), z3.And(xr > -1, xr < 1)
            facts = sign
        self._add(z3.Implies(z3.And(real, inside), z3.And(treal, facts)))
        if outside is not None:
            self._add(z3.Implies(z3.And(real, outside), z3.Not(treal)))

    def _q(self, f: Fraction):
        return z3.Q(f.numerator, f.denominator, self.ctx) if f.denominator != 1 else z3.RealVal(f.numerator, self.ctx)

    def _fresh_int(self, v):
        k = z3.Int(f"pk{self._count()}", self.ctx)
        self._add(k == v)
        return k

    # -- propositions --------------------------------------------------

    def pred(self, name: str, t: Term):
        if name in DEFINITIONS:
            op, lits = DEFINITIONS[name]
            fs = [_lit(t.atoms, p, s) for p, s in lits]
            if op == "and":
                return z3.And(fs) if fs else z3.BoolVal(True, self.ctx)
            return z3.Or(fs)
        return t.atoms[name]

    def _free(self, e):
        """A fresh Boolean for an opaque proposition (one per object)."""
        b = self.opaque.get(e)
        if b is None:
            b = self.opaque[e] = z3.Bool(f"opaque{len(self.opaque)}", self.ctx)
        return b

    def formula(self, e, opaque: bool = False):
        """The z3 formula of a SymPy Boolean.  With ``opaque`` (the
        assumptions), what cannot be encoded becomes a free Boolean;
        otherwise it raises :class:`Unsupported`."""
        try:
            return self._formula(e, opaque)
        except Unsupported:
            if opaque:
                return self._free(e)
            raise

    def _formula(self, e, opaque):
        f = lambda x: self.formula(x, opaque)  # noqa: E731
        if isinstance(e, bool) or isinstance(e, (BooleanTrue, BooleanFalse)):
            return z3.BoolVal(bool(e), self.ctx)
        if isinstance(e, And):
            return z3.And([f(a) for a in e.args])
        if isinstance(e, Or):
            return z3.Or([f(a) for a in e.args])
        if isinstance(e, Not):
            return z3.Not(f(e.args[0]))
        if isinstance(e, Implies):
            return z3.Implies(f(e.args[0]), f(e.args[1]))
        if isinstance(e, Equivalent):
            fs = [f(a) for a in e.args]
            return z3.And([fs[0] == g for g in fs[1:]])
        if isinstance(e, Xor):
            r = z3.BoolVal(False, self.ctx)
            for a in e.args:
                r = z3.Xor(r, f(a))
            return r
        if isinstance(e, ITE):
            return z3.If(f(e.args[0]), f(e.args[1]), f(e.args[2]))
        if isinstance(e, AppliedPredicate):
            return self._applied(e)
        if isinstance(e, Relational):
            return self._relation(type(e).__name__, e.lhs, e.rhs)
        raise Unsupported(f"proposition {e!r}")

    _RELATIONS = {"Q.eq": "Equality", "Q.ne": "Unequality", "Q.lt": "StrictLessThan",
                  "Q.le": "LessThan", "Q.gt": "StrictGreaterThan", "Q.ge": "GreaterThan"}

    def _applied(self, e):
        name = str(e.function)
        if name in self._RELATIONS:
            if len(e.arguments) != 2:
                raise Unsupported(str(e))
            return self._relation(self._RELATIONS[name], *e.arguments)
        p = name[2:] if name.startswith("Q.") else None
        if p not in PREDICATES or len(e.arguments) != 1:
            raise Unsupported(f"predicate {name}")
        return self.pred(p, self.term(e.arguments[0]))

    def _relation(self, kind, lhs, rhs):
        a, b = self.term(lhs), self.term(rhs)
        if kind == "Equality":
            return self._eq(a, b)
        if kind == "Unequality":
            return z3.Not(self._eq(a, b))
        if kind == "StrictLessThan":
            return self._lt(a, b)
        if kind == "StrictGreaterThan":
            return self._lt(b, a)
        if kind == "LessThan":
            return z3.And(a.ext_real(), b.ext_real(), z3.Not(self._lt(b, a)))
        if kind == "GreaterThan":
            return z3.And(a.ext_real(), b.ext_real(), z3.Not(self._lt(a, b)))
        raise Unsupported(kind)

    def _lt(self, a: Term, b: Term):
        """Both extended real and a < b in the extended order."""
        return z3.And(a.ext_real(), b.ext_real(),
                      z3.Or(z3.And(a.ninf, z3.Not(b.ninf)), z3.And(b.pinf, z3.Not(a.pinf)),
                            z3.And(a.fin, b.fin, a.re < b.re)))

    def _eq(self, a: Term, b: Term):
        """Equal values; two other infinities, or a nan, leave it open."""
        # equality is symmetric: one free Boolean for both orders (a set:
        # the z3 names come from the insertion order, not from hashing)
        key = ("eq", frozenset((a.expr, b.expr)))
        free = self._free(key)
        same = z3.Or(z3.And(a.fin, b.fin, a.re == b.re, a.im == b.im),
                     z3.And(a.pinf, b.pinf), z3.And(a.ninf, b.ninf))
        # congruence: a predicate is a property of the value, so equal
        # values have the same atoms (issue #4); not polar, which the value
        # does not decide (design.md); the atoms of two zoo or of a nan stay
        # apart, as their equality does
        if key not in self._congruent:
            self._congruent.add(key)
            self._add(z3.Implies(same, z3.And([a.atoms[p] == b.atoms[p] for p in BASIS if p != "polar"])))
        return z3.Or(same, z3.And(z3.Or(z3.And(a.cinf, b.cinf), a.nan, b.nan), free))
