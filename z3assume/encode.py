"""Translation of SymPy terms and propositions into z3 (docs/design.md).

One :class:`Encoder` serves one query.  Every SymPy subterm it reaches gets
a :class:`Term` (its z3 variables) and the axioms of its node, collected in
``Encoder.axioms`` in the order the terms were reached (SymPy's argument
order), so the problem z3 sees does not depend on hashing.
"""
from __future__ import annotations

import ctypes
import math
from fractions import Fraction
from math import lcm

import z3
from z3 import z3core as _C
from sympy import Basic, S, Symbol
from sympy.core.add import Add
from sympy.core.mul import Mul
from sympy.core.numbers import (ComplexInfinity, Float, ImaginaryUnit, Infinity, Integer, NaN,
                                NegativeInfinity, NumberSymbol, Rational)
from sympy.core.power import Pow
from sympy.core.relational import Relational
from sympy.functions.elementary.complexes import Abs, conjugate, im as Im, re as Re, sign
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.elementary.integers import ceiling, floor, frac
from sympy.functions.elementary.hyperbolic import (acosh, acoth, asinh, atanh, cosh, coth, csch, sech, sinh,
                                                   tanh)
from sympy.functions.elementary.trigonometric import acos, acot, asin, atan, cos, cot, csc, sec, sin, tan
from sympy.functions.combinatorial.factorials import factorial
from sympy.functions.special.gamma_functions import gamma
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

    __slots__ = ("expr", "fin", "pinf", "ninf", "cinf", "nan", "re", "im", "k", "h", "r", "atoms", "p")

    def __init__(self, expr, n: int, ctx, raw):
        self.expr = expr
        b = lambda s: raw.const(f"{s}{n}", "bool")  # noqa: E731
        self.fin, self.pinf, self.ninf, self.cinf, self.nan = (b(s) for s in ("fin", "pinf", "ninf", "cinf", "nan"))
        self.re, self.im = raw.const(f"re{n}", "real"), raw.const(f"im{n}", "real")
        self.k, self.h, self.r = raw.const(f"k{n}", "int"), raw.const(f"h{n}", "int"), raw.const(f"r{n}", "int")
        self.atoms = {p: b(f"{p}_") for p in BASIS}
        #: the same variables as raw pointers (``_Raw``)
        self.p = _Ptrs(self)

    def real(self):
        """The value is a finite real."""
        return z3.And(self.fin, self.im == 0)

    def ext_real(self):
        return z3.Or(self.real(), self.pinf, self.ninf)

    def infinite(self):
        return z3.Not(z3.Or(self.fin, self.nan))


class _Ptrs:
    """The raw pointers of a term's variables, held by its AstRefs."""

    __slots__ = ("fin", "pinf", "ninf", "cinf", "nan", "re", "im", "k", "h", "r", "atoms")

    def __init__(self, t: Term):
        for v in self.__slots__[:-1]:
            setattr(self, v, getattr(t, v).as_ast())
        self.atoms = {p: x.as_ast() for p, x in t.atoms.items()}


def _ast(x):
    """The raw pointer of an AstRef, or ``x`` itself if it is one."""
    return x.as_ast() if isinstance(x, z3.AstRef) else x


def _reflected(a: type, b: type) -> bool:
    """Whether the wrapper's comparison ``x < y`` (``==``, ...) of an AstRef
    of class ``a`` with one of class ``b`` runs as ``y > x``: Python tries
    the reflected comparison first when ``b`` is a proper subclass of
    ``a``, as a numeral's RatNumRef is of ArithRef."""
    return a is not b and issubclass(b, a)


def _lit(atoms, pred, pos):
    a = atoms[pred]
    return a if pos else z3.Not(a)


class _Raw:
    """z3 terms built with the C API (``z3core``: each call checks z3's
    error code) on raw AST pointers, without the Python wrapper's AstRef,
    coercion and reference counting per node, which were most of the
    encoding time (issue #15).  The callers make the calls the wrapper
    code would make, in the same order, so z3 gets the same hash-consed
    terms with the same ids.

    A raw node lives only until the next API call unless something holds
    it, and z3's simplifiers treat a node held more than once (shared)
    differently, which changes the rlimit count.  So the references are
    those of the wrapper code: ``keep`` holds the axioms (as the list of
    AstRefs did), and ``tmp`` the nodes being built (as the wrapper's
    temporary AstRefs did) until ``release``, after which only their
    parents hold them."""

    def __init__(self, ctx):
        self.ctx, self.ref = ctx, ctx.ref()
        self.keep = z3.AstVector(ctx=ctx)
        self.tmp = z3.AstVector(ctx=ctx)
        self._int, self._real = z3.IntSort(ctx).ast, z3.RealSort(ctx).ast
        self._sorts = {"bool": (z3.BoolSort(ctx).ast, z3.BoolRef), "int": (self._int, z3.ArithRef),
                       "real": (self._real, z3.ArithRef)}

    def const(self, name: str, sort: str):
        """``z3.Bool``, ``z3.Int``, ``z3.Real``: an AstRef (the wrapper code
        uses the terms' variables)."""
        s, cls = self._sorts[sort]
        return cls(_C.Z3_mk_const(self.ref, _C.Z3_mk_string_symbol(self.ref, name), s), self.ctx)

    def _new(self, a):
        _C.Z3_ast_vector_push(self.ref, self.tmp.vector, a)
        return a

    def temp(self, a):
        """The pointer ``a`` of a live AstRef, held until ``release``."""
        return self._new(a)

    def mark(self) -> int:
        return _C.Z3_ast_vector_size(self.ref, self.tmp.vector)

    def release(self, mark: int):
        """Drop the nodes made since ``mark`` (the wrapper's temporaries
        die when the function that made them returns)."""
        _C.Z3_ast_vector_resize(self.ref, self.tmp.vector, mark)

    def hold(self, a):
        """``a`` held as an axiom."""
        _C.Z3_ast_vector_push(self.ref, self.keep.vector, a)
        return a

    def truncate(self, n: int):
        """Only the first ``n`` axioms held."""
        _C.Z3_ast_vector_resize(self.ref, self.keep.vector, n)

    def int(self, n: int):
        """``IntVal(n)``, as the wrapper makes it to coerce ``n``."""
        return self._new(_C.Z3_mk_numeral(self.ref, str(n), self._int))

    def real(self, n: int):
        """``RealVal(n)``."""
        return self._new(_C.Z3_mk_numeral(self.ref, str(n), self._real))

    def _array(self, args):
        return len(args), (_C.Ast * len(args))(*args)

    def not_(self, a):
        return self._new(_C.Z3_mk_not(self.ref, a))

    def and_(self, *args):
        return self._new(_C.Z3_mk_and(self.ref, *self._array(args)))

    def or_(self, *args):
        return self._new(_C.Z3_mk_or(self.ref, *self._array(args)))

    def true(self):
        return self._new(_C.Z3_mk_true(self.ref))

    def false(self):
        return self._new(_C.Z3_mk_false(self.ref))

    def xor(self, a, b):
        return self._new(_C.Z3_mk_xor(self.ref, a, b))

    def ite(self, c, a, b):
        return self._new(_C.Z3_mk_ite(self.ref, c, a, b))

    def implies(self, a, b):
        return self._new(_C.Z3_mk_implies(self.ref, a, b))

    def eq(self, a, b):
        return self._new(_C.Z3_mk_eq(self.ref, a, b))

    def ne(self, a, b):
        """``a != b``: the wrapper makes ``distinct(a, b)``."""
        return self._new(_C.Z3_mk_distinct(self.ref, *self._array((a, b))))

    def lt(self, a, b):
        return self._new(_C.Z3_mk_lt(self.ref, a, b))

    def le(self, a, b):
        return self._new(_C.Z3_mk_le(self.ref, a, b))

    def gt(self, a, b):
        return self._new(_C.Z3_mk_gt(self.ref, a, b))

    def ge(self, a, b):
        return self._new(_C.Z3_mk_ge(self.ref, a, b))

    def neg(self, a):
        """``-a``."""
        return self._new(_C.Z3_mk_unary_minus(self.ref, a))

    def add(self, *args):
        return self._new(_C.Z3_mk_add(self.ref, *self._array(args)))

    def mul(self, *args):
        return self._new(_C.Z3_mk_mul(self.ref, *self._array(args)))

    def to_real(self, a):
        return self._new(_C.Z3_mk_int2real(self.ref, a))

    def is_int(self, a):
        return self._new(_C.Z3_mk_is_int(self.ref, a))

    def pbeq(self, args, k: int):
        """``PbEq`` with all coefficients 1."""
        n, arr = self._array(args)
        return self._new(_C.Z3_mk_pbeq(self.ref, n, arr, (ctypes.c_int * n)(*[1] * n), k))


def _scoped(method):
    """The raw nodes the method makes (``_Raw.tmp``) are dropped when it
    returns, or raises, as the wrapper's temporaries die with its frame."""
    def scoped(self, *args):
        R = self._raw
        mark = R.mark()
        try:
            return method(self, *args)
        finally:
            R.release(mark)
    scoped.__name__, scoped.__doc__ = method.__name__, method.__doc__
    return scoped


class Encoder:
    """Collects the terms and axioms of one query."""

    def __init__(self, ctx):
        self.ctx = ctx
        self.terms = {}
        #: raw pointers (``_Raw``), held by ``self._raw.keep``, in order
        self.axioms = []
        self._raw = _Raw(ctx)
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
        t = Term(e, len(self.terms), self.ctx, self._raw)
        self.terms[e] = t
        self._lin[t] = self._scaled(t, e, args)
        self._shape(t)
        self._node(t, e, args)
        return t

    def _add(self, *fs):
        self.axioms.extend(self._raw.hold(f.as_ast()) for f in fs)

    def _add_raw(self, a):
        self.axioms.append(self._raw.hold(a))

    @_scoped
    def _shape(self, t: Term):
        """The kind is one of five; the basis Booleans are the numeric
        definitions unless the value is nan, the rules always; nan is no
        number.

        These are most of the axioms (about 50 per term), so they are made
        raw (``_Raw``).  The comments give the wrapper code each axiom
        stands for: the raw calls make its nodes in its order (Python's:
        the arguments of a call left to right, then the call; a node made
        again is the same node)."""
        R, add = self._raw, self._add_raw
        T = t.p
        fin, pinf, ninf, cinf, nan, re, im, k, h, r, a = (T.fin, T.pinf, T.ninf, T.cinf, T.nan, T.re, T.im,
                                                          T.k, T.h, T.r, T.atoms)
        # PbEq([(k, 1) for k in kinds], 1)
        add(R.pbeq([fin, pinf, ninf, cinf, nan], 1))
        real = R.and_(fin, R.eq(im, R.real(0)))                               # t.real()
        defs = {
            "finite": fin,
            "complex": fin,
            "extended_real": R.or_(real, pinf, ninf),                         # t.ext_real()
            "extended_positive": R.or_(R.and_(real, R.gt(re, R.real(0))), pinf),
            "extended_negative": R.or_(R.and_(real, R.lt(re, R.real(0))), ninf),
            "zero": R.and_(real, R.eq(re, R.real(0))),
            "imaginary": R.and_(fin, R.eq(re, R.real(0)), R.ne(im, R.real(0))),
        }
        notnan = R.not_(nan)
        for p, d in defs.items():
            add(R.implies(notnan, R.eq(a[p], d)))       # Implies(Not(t.nan), a[p] == d)
        # satassume's convention for nan (docs/special-values.md row V1):
        # every predicate is False except finite (and infinite) and polar;
        # commutative is True of every term in scope (design.md)
        nots = {}
        for p in BASIS:
            if p not in ("finite", "polar"):
                nots[p] = R.not_(a[p])
                add(R.implies(nan, nots[p]))            # Implies(t.nan, Not(a[p]))
        # integer witnesses: z3 reasons about integers in the Int sort
        # Implies(And(notnan, a["integer"]),
        #         And(t.real(), t.re == ToReal(t.k), t.k == 2 * t.h + t.r, t.r >= 0, t.r <= 1))
        add(R.implies(R.and_(notnan, a["integer"]),
                      R.and_(real, R.eq(re, R.to_real(k)), R.eq(k, R.add(R.mul(R.int(2), h), r)),
                             R.ge(r, R.int(0)), R.le(r, R.int(1)))))
        add(self._non_integer(t, R.and_(notnan, real, nots["integer"])))
        # Implies(notnan, a["even"] == And(a["integer"], t.r == 0))
        add(R.implies(notnan, R.eq(a["even"], R.and_(a["integer"], R.eq(r, R.int(0))))))
        # Implies(And(notnan, a["prime"]), And(a["integer"], t.k >= 2))
        add(R.implies(R.and_(notnan, a["prime"]), R.and_(a["integer"], R.ge(k, R.int(2)))))
        # Implies(And(notnan, a["integer"], Or(t.k == 2, t.k == 3)), a["prime"])
        add(R.implies(R.and_(notnan, a["integer"], R.or_(R.eq(k, R.int(2)), R.eq(k, R.int(3)))), a["prime"]))
        # Implies(And(notnan, a["prime"], a["even"]), t.k == 2)
        add(R.implies(R.and_(notnan, a["prime"], a["even"]), R.eq(k, R.int(2))))
        # Implies(notnan, a["composite"] == And(a["integer"], t.k >= 2, Not(a["prime"])))
        add(R.implies(notnan, R.eq(a["composite"], R.and_(a["integer"], R.ge(k, R.int(2)), nots["prime"]))))
        # Implies(And(notnan, a["rational"]), t.real())
        add(R.implies(R.and_(notnan, a["rational"]), real))
        lit = lambda p, s: a[p] if s else nots[p]  # noqa: E731
        for prem, concl in RULES:
            add(R.implies(R.and_(*[lit(p, s) for p, s in prem]), R.or_(*[lit(p, s) for p, s in concl])))

    def _non_integer(self, t: Term, noint):
        """A finite real non-integer (``noint``, the raw
        ``And(Not(t.nan), t.real(), Not(a["integer"]))``):
        ``Not(IsInt(re_t))``, unless ``t`` has a
        scaled witness ``n/d`` with ``d > 1``: under its ``cond`` the integer
        facts of ``t`` are stated over the integers instead (``t`` is an
        integer iff ``d`` divides ``n``, and then ``k_t = n/d``), as z3 does
        not decide ``IsInt`` of a real with rational coefficients over
        integers (issue #12).  A raw axiom; the rarer second case is made
        with the wrapper."""
        d, n, cond = self._lin[t]
        R = self._raw
        if d == 1 or cond is True:
            return R.implies(noint, R.not_(R.is_int(t.p.re)))
        a = t.atoms
        noint = z3.BoolRef(noint, self.ctx)
        c = self._count()
        q, r = z3.Int(f"dq{c}", self.ctx), z3.Int(f"dr{c}", self.ctx)
        f = z3.And(z3.Implies(cond, z3.And(n == d * q + r, r >= 0, r < d, a["integer"] == (r == 0))),
                   z3.Implies(z3.And(cond, a["integer"]), t.k == q),
                   z3.Implies(z3.And(noint, z3.Not(cond)), z3.Not(z3.IsInt(t.re))))
        return R.temp(f.as_ast())           # held before the AstRef f goes

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
            # P2: b**0 = 1 for every b but nan; nan**0 is free (N1 says nan,
            # SymPy's Pow table 1; design.md, decision 3)
            b = self.term(e.base)
            start = len(self.axioms)
            self._node(t, Integer(1), None)
            one = self.axioms[start:]
            # Implies(Not(b.nan), And(one)), raw as the axioms are; then
            # only it holds them
            R, mark = self._raw, self._raw.mark()
            try:
                f = R.implies(R.not_(b.p.nan), R.and_(*one))
                del self.axioms[start:]
                R.truncate(start)
                self._add_raw(f)
            finally:
                R.release(mark)
            return
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
        elif type(e) in (floor, ceiling, frac) and len(e.args) == 1:   # not a user subclass
            self._round(t, type(e), self.term(e.args[0]))
        elif type(e) is gamma and len(e.args) == 1:                    # not a user subclass
            self._gamma(t, self.term(e.args[0]))
        elif type(e) is factorial and len(e.args) == 1:
            self._factorial(t, self.term(e.args[0]))
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

    # Sums and products are in most queries, so their axioms are raw too
    # (as _shape's: the wrapper code in the comments, its nodes in its
    # order); x.p are the raw variables of the term x.

    @_scoped
    def _sum(self, t: Term, args):
        R, add = self._raw, self._add_raw
        T, xs = t.p, [x.p for x in args]
        allfin = R.and_(*[x.fin for x in xs])                     # And([x.fin for x in args])
        # Implies(allfin, And(t.fin, t.re == Sum([x.re ...]), t.im == Sum([x.im ...])))
        add(R.implies(allfin, R.and_(T.fin, R.eq(T.re, R.add(*[x.re for x in xs])),
                                     R.eq(T.im, R.add(*[x.im for x in xs])))))
        allint = R.and_(*[x.atoms["integer"] for x in xs])
        # Implies(And(allfin, allint), And(t.atoms["integer"], t.k == Sum([x.k ...])))
        add(R.implies(R.and_(allfin, allint), R.and_(T.atoms["integer"], R.eq(T.k, R.add(*[x.k for x in xs])))))
        # not for a constant sum (#33): its summands' kinds come from their
        # own axioms, and the converse only lets the nonlinear core split
        # on the integer witnesses of radicals (seconds in one Groebner call)
        if len(xs) > 1 and t.expr.free_symbols:
            # the integers are closed under subtraction (#23): an integer
            # sum of integers and one more summand makes that one an integer
            for i, x in enumerate(xs):
                rest = [y.atoms["integer"] for j, y in enumerate(xs) if j != i]
                # Implies(And(allfin, t.atoms["integer"], *rest), x.atoms["integer"])
                add(R.implies(R.and_(allfin, T.atoms["integer"], *rest), x.atoms["integer"]))
        add(R.implies(R.or_(*[x.nan for x in xs]), T.nan))      # Implies(Or([x.nan ...]), t.nan)
        # a sum with an infinity among its summands is an infinity or nan,
        # never a number, whatever the kinds (zoo + oo is open otherwise)
        add(R.implies(T.fin, allfin))                             # Implies(t.fin, allfin)
        # +-oo among real values and the same infinity; among finite values
        # (oo + I: oo for SymPy, an infinity off the real axis for
        # satassume, decision 3) +-oo or the other kind
        for inf, kind in ((T.pinf, "pinf"), (T.ninf, "ninf")):
            some = R.or_(*[getattr(x, kind) for x in xs])
            # Implies(And(some, And([Or(x.real(), x.<kind>) ...])), inf)
            add(R.implies(R.and_(some, R.and_(*[R.or_(R.and_(x.fin, R.eq(x.im, R.real(0))), getattr(x, kind))
                                                for x in xs])), inf))
            # Implies(And(some, And([Or(x.fin, x.<kind>) ...])), Or(inf, t.cinf))
            add(R.implies(R.and_(some, R.and_(*[R.or_(x.fin, getattr(x, kind)) for x in xs])), R.or_(inf, T.cinf)))
        # Implies(And(Or([x.pinf ...]), Or([x.ninf ...])), t.nan)
        add(R.implies(R.and_(R.or_(*[x.pinf for x in xs]), R.or_(*[x.ninf for x in xs])), T.nan))
        for i, x in enumerate(xs):
            rest = [y.fin for j, y in enumerate(xs) if j != i]
            add(R.implies(R.and_(x.cinf, *rest), T.cinf))         # Implies(And(x.cinf, *rest), t.cinf)
        self._closure(T, xs, allfin, lambda y: R.true())          # BoolVal(True)

    def _closure(self, T, xs, allfin, cancel):
        """Field closure of rationals and algebraic numbers among finite
        values; ``cancel(y)`` is the condition under which ``y`` can be
        taken out of the operation (any summand; a nonzero factor).  Raw:
        ``T``, ``xs`` are the pointers of the term and its arguments."""
        add = self._add_raw
        R = self._raw
        for p in ("rational", "algebraic"):
            # Implies(And(allfin, *[x.atoms[p] ...]), t.atoms[p])
            add(R.implies(R.and_(allfin, *[x.atoms[p] for x in xs]), T.atoms[p]))
            if len(xs) > 1:
                for i, x in enumerate(xs):
                    # Implies(And(allfin, t.atoms[p], *[And(y.atoms[p], cancel(y)) for the others]), x.atoms[p])
                    rest = [R.and_(y.atoms[p], cancel(y)) for j, y in enumerate(xs) if j != i]
                    add(R.implies(R.and_(allfin, T.atoms[p], *rest), x.atoms[p]))

    @_scoped
    def _product(self, t: Term, args):
        R, add = self._raw, self._add_raw
        T, xs = t.p, [x.p for x in args]
        allfin = R.and_(*[x.fin for x in xs])
        re, im = args[0].re, args[0].im
        for x in args[1:]:
            re, im = self._fresh_mul(re, im, x.re, x.im)
        # Implies(allfin, And(t.fin, t.re == re, t.im == im))
        add(R.implies(allfin, R.and_(T.fin, R.eq(T.re, re.as_ast()), R.eq(T.im, im.as_ast()))))
        allint = R.and_(*[x.atoms["integer"] for x in xs])
        k = xs[0].k
        for x in xs[1:]:
            k = R.mul(k, x.k)                                     # k = k * x.k
        # Implies(And(allfin, allint), And(t.atoms["integer"], t.k == k))
        add(R.implies(R.and_(allfin, allint), R.and_(T.atoms["integer"], R.eq(T.k, k))))
        self._infinite_product(T, xs)
        self._closure(T, xs, allfin, lambda y: R.not_(y.atoms["zero"]))   # Not(y.atoms["zero"])
        # (+-1/q)*x for an integer q: x = +-q*t is an integer when t is
        var = [x for x in args if not isinstance(x.expr, Rational)]
        c = Mul(*[x.expr for x in args if isinstance(x.expr, Rational)])
        if len(var) == 1 and abs(c.p) == 1 and c.q > 1:
            # Implies(And(var[0].fin, t.atoms["integer"]), var[0].atoms["integer"])
            add(R.implies(R.and_(var[0].p.fin, T.atoms["integer"]), var[0].p.atoms["integer"]))

    def _fresh_mul(self, a, b, c, d):
        """(a + b*I)*(c + d*I) as two fresh reals."""
        n = self._count()
        re, im = z3.Real(f"pre{n}", self.ctx), z3.Real(f"pim{n}", self.ctx)
        self._add(re == a * c - b * d, im == a * d + b * c)
        return re, im

    def _infinite_product(self, T, xs):
        """0 * infinity is nan; nonzero values with an infinity among them
        give an infinity, signed when all are extended real.  Raw, as
        ``_closure``."""
        R, add = self._raw, self._add_raw
        infinite = lambda x: R.not_(R.or_(x.fin, x.nan))         # noqa: E731 (x.infinite())
        anynan = R.or_(*[x.nan for x in xs])
        anyinf = R.or_(*[infinite(x) for x in xs])
        anyzero = R.or_(*[x.atoms["zero"] for x in xs])
        add(R.implies(anynan, T.nan))                             # Implies(anynan, t.nan)
        add(R.implies(R.and_(anyinf, anyzero), T.nan))            # Implies(And(anyinf, anyzero), t.nan)
        # And([Not(Or(x.nan, x.atoms["zero"])) ...])
        nonzero = R.and_(*[R.not_(R.or_(x.nan, x.atoms["zero"])) for x in xs])
        add(R.implies(R.and_(anyinf, nonzero), infinite(T)))      # Implies(And(anyinf, nonzero), t.infinite())
        # And([x.ext_real() ...]), x.ext_real() = Or(And(x.fin, x.im == 0), x.pinf, x.ninf)
        allext = R.and_(*[R.or_(R.and_(x.fin, R.eq(x.im, R.real(0))), x.pinf, x.ninf) for x in xs])
        neg = R.false()                                           # BoolVal(False)
        for x in xs:
            neg = R.xor(neg, x.atoms["extended_negative"])
        # Implies(And(anyinf, nonzero, allext), If(neg, t.ninf, t.pinf))
        add(R.implies(R.and_(anyinf, nonzero, allext), R.ite(neg, T.ninf, T.pinf)))

    def _power(self, t: Term, b: Term, n: int):
        # n != 0: _node encodes b**0 (1 unless b is nan); the closure axioms below need it
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

    @_scoped
    def _pow(self, t: Term, e):
        """``b**x`` for an exponent ``x`` that is not an integer literal:
        SymPy's principal value ``exp(x*log(b))`` for finite ``b != 0`` and
        finite ``x``, and satassume's special-values rows elsewhere.

        Special values (satassume special-values, docs/special-values.md of
        satassume#293): N1 a ``nan`` exponent gives ``nan``, a ``nan`` base
        too unless ``x = 0``, which is left free (``nan**0 = 1`` is SymPy's
        ``Pow`` table and N1 says ``nan``; design.md, decision 3); P2
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
        # raw, as _shape (the wrapper code in the comments; numerals made
        # where the wrapper's coercion makes them); b.p, x.p, t.p are the
        # raw variables
        R, add = self._raw, self._add_raw
        T, B, X = t.p, b.p, x.p
        a, ba, xa = T.atoms, B.atoms, X.atoms
        eq, ne, gt, lt, num = R.eq, R.ne, R.gt, R.lt, R.real
        one, zero = R.int(1), R.int(0)                                      # IntVal(1), IntVal(0)
        bzero = R.and_(B.fin, eq(B.re, num(0)), eq(B.im, num(0)))           # And(b.fin, b.re == 0, b.im == 0)
        # And(b.fin, Or(b.re != 0, b.im != 0))
        bnz = R.and_(B.fin, R.or_(ne(B.re, num(0)), ne(B.im, num(0))))
        bone = R.and_(B.fin, eq(B.re, num(1)), eq(B.im, num(0)))
        xzero = R.and_(X.fin, eq(X.re, num(0)), eq(X.im, num(0)))
        xone = R.and_(X.fin, eq(X.re, num(1)), eq(X.im, num(0)))
        # x.real(), b.infinite()
        xreal, binf = R.and_(X.fin, eq(X.im, num(0))), R.not_(R.or_(B.fin, B.nan))
        # N1, P2, b**1 = b
        add(R.implies(X.nan, T.nan))                                        # Implies(x.nan, t.nan)
        add(R.implies(R.and_(B.nan, R.not_(xzero)), T.nan))                 # Implies(And(b.nan, Not(xzero)), t.nan)
        self._int_value(t, R.and_(xzero, R.not_(B.nan)), one)               # And(xzero, Not(b.nan))
        # Implies(xone, And(t.fin == b.fin, t.pinf == b.pinf, t.ninf == b.ninf, t.cinf == b.cinf,
        #                   t.nan == b.nan, Implies(b.fin, And(t.re == b.re, t.im == b.im))))
        add(R.implies(xone, R.and_(eq(T.fin, B.fin), eq(T.pinf, B.pinf), eq(T.ninf, B.ninf), eq(T.cinf, B.cinf),
                                   eq(T.nan, B.nan), R.implies(B.fin, R.and_(eq(T.re, B.re), eq(T.im, B.im))))))
        self._same(t, b, xone)
        # 0**x for real x != 0 (P1)
        self._int_value(t, R.and_(bzero, xreal, gt(X.re, num(0))), zero)    # And(bzero, xreal, x.re > 0)
        add(R.implies(R.and_(bzero, xreal, lt(X.re, num(0))), T.cinf))      # ... x.re < 0), t.cinf)
        # P4, P5: finite b, x = +-oo
        nb = self._fresh_real("pownorm")
        NB = nb.as_ast()
        # Implies(And(b.fin, Or(x.pinf, x.ninf)), nb == b.re * b.re + b.im * b.im)
        add(R.implies(R.and_(B.fin, R.or_(X.pinf, X.ninf)), eq(NB, R.add(R.mul(B.re, B.re), R.mul(B.im, B.im)))))
        bpos = R.and_(B.fin, eq(B.im, num(0)), gt(B.re, num(0)))            # And(b.fin, b.im == 0, b.re > 0)
        # And(b.fin, Or(And(x.pinf, nb < 1), And(x.ninf, nb > 1)))
        self._int_value(t, R.and_(B.fin, R.or_(R.and_(X.pinf, lt(NB, num(1))), R.and_(X.ninf, gt(NB, num(1))))), zero)
        # Implies(And(b.fin, Or(And(x.pinf, nb > 1), And(x.ninf, nb < 1))), If(bpos, t.pinf, t.cinf))
        add(R.implies(R.and_(B.fin, R.or_(R.and_(X.pinf, gt(NB, num(1))), R.and_(X.ninf, lt(NB, num(1))))),
                      R.ite(bpos, T.pinf, T.cinf)))
        # Implies(And(b.fin, nb == 1, Or(x.pinf, x.ninf)), t.nan)
        add(R.implies(R.and_(B.fin, eq(NB, num(1)), R.or_(X.pinf, X.ninf)), T.nan))
        # P6, P3: infinite b
        # And(binf, Or(x.ninf, And(xreal, x.re < 0)))
        self._int_value(t, R.and_(binf, R.or_(X.ninf, R.and_(xreal, lt(X.re, num(0))))), zero)
        xpos = R.and_(xreal, gt(X.re, num(0)))                              # And(xreal, x.re > 0)
        add(R.implies(R.and_(binf, X.pinf), R.ite(B.pinf, T.pinf, T.cinf)))  # Implies(And(binf, x.pinf), If(...))
        add(R.implies(R.and_(B.pinf, xpos), T.pinf))
        add(R.implies(R.and_(B.cinf, xpos), R.not_(R.or_(T.fin, T.nan))))   # t.infinite()
        # Implies(And(b.ninf, xpos), If(xa["integer"], If(x.r == 0, t.pinf, t.ninf), t.cinf))
        add(R.implies(R.and_(B.ninf, xpos), R.ite(xa["integer"], R.ite(eq(X.r, R.int(0)), T.pinf, T.ninf), T.cinf)))
        # finite b != 0, finite x: exp(x*log(b))
        cond = R.and_(bnz, X.fin)                                           # And(bnz, x.fin)
        if e.base is not S.Zero:
            self._principal(t, e.base, e.exp, x, cond)
        # integer x
        xint = R.and_(X.fin, xa["integer"])
        breal = R.and_(B.fin, eq(B.im, num(0)), ne(B.re, num(0)))           # And(b.fin, b.im == 0, b.re != 0)
        bimag = R.and_(B.fin, eq(B.re, num(0)), ne(B.im, num(0)))           # And(b.fin, b.re == 0, b.im != 0)
        bint = R.and_(B.fin, ba["integer"])
        big = R.or_(R.ge(B.k, R.int(2)), R.le(B.k, R.int(-2)))              # Or(b.k >= 2, b.k <= -2)
        # Implies(And(xint, breal), And(t.fin, t.im == 0, Implies(b.re > 0, t.re > 0),
        #                               Implies(b.re < 0, If(x.r == 0, t.re > 0, t.re < 0))))
        add(R.implies(R.and_(xint, breal),
                      R.and_(T.fin, eq(T.im, num(0)), R.implies(gt(B.re, num(0)), gt(T.re, num(0))),
                             R.implies(lt(B.re, num(0)),
                                       R.ite(eq(X.r, R.int(0)), gt(T.re, num(0)), lt(T.re, num(0)))))))
        # Implies(And(xint, bimag),
        #         And(t.fin, If(x.r == 0, And(t.im == 0, t.re != 0), And(t.re == 0, t.im != 0))))
        add(R.implies(R.and_(xint, bimag),
                      R.and_(T.fin, R.ite(eq(X.r, R.int(0)), R.and_(eq(T.im, num(0)), ne(T.re, num(0))),
                                          R.and_(eq(T.re, num(0)), ne(T.im, num(0)))))))
        add(R.implies(R.and_(bint, xint, R.ge(X.k, R.int(0))), a["integer"]))                   # x.k >= 0
        add(R.implies(R.and_(bint, ba["even"], xint, R.ge(X.k, R.int(1))), a["even"]))         # x.k >= 1
        # Implies(And(bint, Not(ba["even"]), xint, x.k >= 0), And(a["integer"], Not(a["even"])))
        add(R.implies(R.and_(bint, R.not_(ba["even"]), xint, R.ge(X.k, R.int(0))),
                      R.and_(a["integer"], R.not_(a["even"]))))
        add(R.implies(R.and_(bint, big, xint, R.ge(X.k, R.int(2))), R.not_(a["prime"])))       # x.k >= 2
        # Implies(And(bint, big, xint, x.k <= -1), And(t.fin, t.im == 0, t.re > -1, t.re < 1, t.re != 0))
        add(R.implies(R.and_(bint, big, xint, R.le(X.k, R.int(-1))),
                      R.and_(T.fin, eq(T.im, num(0)), gt(T.re, num(-1)), lt(T.re, num(1)), ne(T.re, num(0)))))
        add(R.implies(R.and_(bnz, ba["rational"], xint), a["rational"]))
        # algebraic numbers: rational x, Gelfond-Schneider
        xrat = R.and_(X.fin, xa["rational"])
        add(R.implies(R.and_(bnz, ba["algebraic"], xrat), a["algebraic"]))
        # Implies(And(b.fin, xrat, Not(xzero), t.fin, a["algebraic"]), ba["algebraic"])
        add(R.implies(R.and_(B.fin, xrat, R.not_(xzero), T.fin, a["algebraic"]), ba["algebraic"]))
        # Implies(And(bnz, ba["algebraic"], Not(bone), x.fin, xa["algebraic"], Not(xa["rational"])),
        #         Not(a["algebraic"]))
        add(R.implies(R.and_(bnz, ba["algebraic"], R.not_(bone), X.fin, xa["algebraic"], R.not_(xa["rational"])),
                      R.not_(a["algebraic"])))
        if isinstance(e.exp, Rational):
            self._rational_power(t, b, e.base, Fraction(int(e.exp.p), int(e.exp.q)))

    @_scoped
    def _principal(self, t: Term, base, xe, x: Term, cond):
        """Under ``cond`` (finite ``b != 0``, finite ``x``; raw) ``t`` is the
        principal value ``exp(x*log(b))`` (``_pow``).  Raw, as ``_pow``."""
        R, T, num = self._raw, t.p, self._raw.real
        lit = _polar_literal(base)
        if lit is None:
            val = exp(Mul(xe, log(base, evaluate=False), evaluate=False), evaluate=False)
            # a real negative b: the direction is that of exp(I*pi*x)
            b = self.term(base)
            d = self.term(exp(Mul(S.ImaginaryUnit, S.Pi, xe, evaluate=False), evaluate=False))
            B, D, X = b.p, d.p, x.p
            sign = lambda f, u, v: R.eq(f(u, num(0)), f(v, num(0)))     # noqa: E731 (f(u, 0) == f(v, 0))
            # Implies(And(cond, b.real(), b.re < 0, x.real()),
            #         And((t.re > 0) == (d.re > 0), (t.re < 0) == (d.re < 0),
            #             (t.im > 0) == (d.im > 0), (t.im < 0) == (d.im < 0)))
            self._add_raw(R.implies(R.and_(cond, R.and_(B.fin, R.eq(B.im, num(0))), R.lt(B.re, num(0)),
                                           R.and_(X.fin, R.eq(X.im, num(0)))),
                                    R.and_(sign(R.gt, T.re, D.re), sign(R.lt, T.re, D.re),
                                           sign(R.gt, T.im, D.im), sign(R.lt, T.im, D.im))))
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
                        cond = R.and_(cond, *[self.term(g).p.fin for g in xe.args])
                for g in groups:
                    if isinstance(g, Rational):
                        c = Rational(c0.numerator, c0.denominator) * g
                    elif c0 == 1:
                        c = g
                    else:
                        c = Mul(Rational(c0.numerator, c0.denominator), g, evaluate=False)
                    factors.append(exp(Mul(S.ImaginaryUnit, S.Pi, c, evaluate=False), evaluate=False))
            if not factors:
                self._int_value(t, cond, R.int(1))
                return
            val = factors[0] if len(factors) == 1 else Mul(*factors, evaluate=False)
        v = self.term(val)
        # Implies(cond, And(t.fin, t.re == v.re, t.im == v.im))
        self._add_raw(R.implies(cond, R.and_(T.fin, R.eq(T.re, v.p.re), R.eq(T.im, v.p.im))))
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

    # _same and _int_value are raw (as _shape); ``cond`` and ``k`` are
    # AstRefs, which the caller holds, or raw pointers (_ast)

    @_scoped
    def _same(self, t: Term, z: Term, cond):
        """Under ``cond`` the value of ``t`` is that of ``z``: the
        predicates without a numeric definition agree."""
        R, cond = self._raw, _ast(cond)
        T, Z = t.p, z.p
        a, za = T.atoms, Z.atoms
        # Implies(cond, And([a[p] == za[p] for p in (...)]))
        self._add_raw(R.implies(cond, R.and_(*[R.eq(a[p], za[p]) for p in
                                              ("integer", "rational", "algebraic", "prime", "composite", "even")])))
        # Implies(And(cond, za["integer"]), And(t.k == z.k, t.r == z.r))
        self._add_raw(R.implies(R.and_(cond, za["integer"]), R.and_(R.eq(T.k, Z.k), R.eq(T.r, Z.r))))

    @_scoped
    def _int_value(self, t: Term, cond, k):
        """Under ``cond`` the value of ``t`` is the integer ``k``."""
        R, cond, k, T = self._raw, _ast(cond), _ast(k), t.p
        # Implies(cond, And(t.fin, t.im == 0, t.re == ToReal(k), t.atoms["integer"], t.k == k)),
        # where t.k == k is k == t.k for a numeral k: its AstRef (IntNumRef)
        # is a subclass of t.k's (ArithRef), so Python tries its reflected
        # comparison first
        numeral = _C.Z3_is_numeral_ast(R.ref, k)
        self._add_raw(R.implies(cond, R.and_(T.fin, R.eq(T.im, R.real(0)), R.eq(T.re, R.to_real(k)),
                                             T.atoms["integer"], R.eq(k, T.k) if numeral else R.eq(T.k, k))))

    def _complex_part(self, t: Term, f, z: Term):
        """``Abs``, ``re``, ``im``, ``conjugate``, ``sign`` of ``z``, exact on
        the pair ``re_z + im_z*I``.  ``nan`` gives ``nan`` (satassume
        special-values N1); an infinity ``t*d`` (t real -> +oo, satassume
        special-values V2) gives the limit of the function, which only
        ``Abs`` (row F3: ``oo``) has for every infinity: ``re``, ``im``,
        ``conjugate`` and ``sign`` of ``+-oo`` are ``+-oo``, ``0``, ``+-oo``,
        ``+-1``.  For the other kind (``zoo`` and the directed non-real
        infinities ``oo*u``) only what every value of that kind gives is
        stated (decision 7): along ``t*d`` with ``d/|d| = u`` non-real,
        ``re = t*re(d)`` tends to ``+-oo`` or is ``0``, ``im = t*im(d)``
        tends to ``+-oo``, ``conjugate = t*conj(d)`` is again of the other
        kind and ``sign = u`` is a non-real unit; ``zoo`` has no direction,
        and each of the four has no limit there (``re(c + I*s)`` is ``c``
        as ``s -> oo``, for every ``c``) and no value by the table's
        arithmetic (``(zoo + zoo)/2`` is ``nan``, row A3), so ``re``,
        ``im`` and ``sign`` of ``zoo`` are ``nan`` (V1: no value), while
        ``conjugate``, the reflection of the Riemann sphere, fixes ``zoo``.
        Number theory: the algebraic numbers are closed under
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
                      z3.Implies(z.cinf, z3.Or(t.pinf, t.ninf, t.nan,
                                               z3.And(t.fin, t.im == 0, t.re == 0, a["integer"], t.k == 0))),
                      z3.Implies(z.fin, z3.And(t.fin, t.im == 0, t.re == zre)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))
            self._same(t, z, real)
        elif f is Im:
            self._int_value(t, z3.Or(z.pinf, z.ninf, real), z3.IntVal(0, self.ctx))
            self._add(z3.Implies(z.cinf, z3.Or(t.pinf, t.ninf, t.nan)),
                      z3.Implies(z.fin, z3.And(t.fin, t.im == 0, t.re == zim)),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))
        elif f is conjugate:
            self._add(z3.Implies(z.pinf, t.pinf), z3.Implies(z.ninf, t.ninf), z3.Implies(z.cinf, t.cinf),
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
                      z3.Implies(z.cinf, z3.Or(t.nan, z3.And(t.fin, t.im != 0, t.re * t.re + t.im * t.im == 1))),
                      z3.Implies(z3.And(z.fin, za["algebraic"]), a["algebraic"]))

    def _round(self, t: Term, f, z: Term):
        """``floor``, ``ceiling`` and ``frac`` of ``z`` (docs/design.md
        "Terms", issue #18).

        Finite ``z = a + b*I``: SymPy's definition (the docstrings of
        ``floor`` and ``ceiling``: "generalizes floor to complex numbers by
        taking the floor of the real and imaginary parts separately";
        satassume's templates/integer_funcs.py and functions.py state the
        same) is ``floor(z) = floor(a) + floor(b)*I``.  z3's ``ToInt`` is
        exactly the floor of a real (the integer ``n`` with
        ``n <= a < n + 1``), so the parts are exact; ``ceiling(a) =
        -floor(-a)`` (the least integer ``>= a`` is minus the greatest
        integer ``<= -a``).  ``frac(z) = z - floor(z)``: SymPy defines
        ``frac(x) = x - floor(x)`` for real ``x`` and rewrites ``frac(x)``
        as ``x - floor(x)`` for any ``x``; with the documented complex
        floor that is the formula for complex ``z`` too (the docstring's
        complex example agrees, but an example is an evaluation, not the
        ground).

        The value of ``floor``/``ceiling`` is a Gaussian integer: algebraic
        (a root of ``w**2 - 2*m*w + m**2 + n**2``), real exactly when the
        rounded imaginary part is ``0``, and then the integer ``k``.  For
        ``frac``: ``z = frac(z) + floor(z)`` with a Gaussian integer
        ``floor(z)``, and the algebraic numbers are a field, so ``frac(z)``
        is algebraic iff ``z`` is; for real ``z`` likewise rational iff
        ``z`` is rational (the integers are in the rational field).

        Special values: ``nan`` gives ``nan`` (special-values N1).  An
        infinity: ``floor(+-oo) = +-oo`` and ``floor(zoo) = zoo``, as
        satassume's templates/integer_funcs.py states them (the
        "Values follow SymPy's conventions" paragraph).  They are the
        limits, too: ``|floor(w) - w| < 2`` for every finite ``w`` (each
        part moves by less than 1), so ``floor(w)`` tends to the same
        point at infinity as ``w``: along ``t*d`` (row V2) to the infinity
        of direction ``d`` (``+-oo`` for ``d = +-1``, a directed non-real
        infinity otherwise), and to ``zoo`` on the Riemann sphere.  So the
        kind is kept: ``+-oo`` to ``+-oo``, the other kind (``zoo`` and
        the directed non-real infinities) to that kind.  Likewise for
        ``ceiling``.  ``frac`` of an infinity is free: no definition and
        no row gives it a value (SymPy writes ``AccumBounds(0, 1)`` for
        ``frac(oo)``, a set, not a value, and ``nan`` for ``frac(zoo)``,
        an evaluation result only)."""
        a, za = t.atoms, z.atoms
        fl = lambda v: z3.ToReal(z3.ToInt(v))  # noqa: E731
        self._add(z3.Implies(z.nan, t.nan))
        if f is frac:
            self._add(z3.Implies(z.fin, z3.And(t.fin, t.re == z.re - fl(z.re), t.im == z.im - fl(z.im))),
                      z3.Implies(z.fin, a["algebraic"] == za["algebraic"]),
                      z3.Implies(z.real(), a["rational"] == za["rational"]))
            return
        if f is floor:
            ki, re, im = z3.ToInt(z.re), fl(z.re), fl(z.im)
        else:
            ki, re, im = -z3.ToInt(-z.re), -fl(-z.re), -fl(-z.im)
        self._add(z3.Implies(z.pinf, t.pinf), z3.Implies(z.ninf, t.ninf), z3.Implies(z.cinf, t.cinf),
                  z3.Implies(z.fin, z3.And(t.fin, t.re == re, t.im == im, a["algebraic"])),
                  # a real Gaussian integer is the integer k
                  z3.Implies(z3.And(z.fin, im == 0), z3.And(a["integer"], t.k == ki)))

    def _factorial(self, t: Term, z: Term):
        """``factorial(z) = gamma(z + 1)`` (``_gamma``, decision 9), the
        sum unevaluated.  A finite ``z`` is an integer iff ``z + 1`` is
        (stated here: the sum's axioms give one direction only, and z3 did
        not find the other through ``IsInt`` within the rlimit)."""
        w = self.term(Add(z.expr, S.One, evaluate=False))
        self._add(z3.Implies(z.fin, w.atoms["integer"] == z.atoms["integer"]))
        self._gamma(t, w)

    def _gamma(self, t: Term, w: Term):
        """``gamma(w)`` (docs/design.md "Terms", issue #21); ``factorial(z)``
        is ``gamma(z + 1)`` with ``w`` the term of ``z + 1``.

        ``factorial``: SymPy defines it on the nonnegative integers, with
        ``n! = gamma(n + 1)`` there and "factorial of a negative integer is
        complex infinity" (its docstring), which is ``gamma(n + 1)`` at a
        pole (below); off the integers its derivative, ``evalf`` and
        ``rewrite(gamma)`` are those of ``gamma(z + 1)``, and satassume
        states the same convention (templates/integer_funcs.py:
        ``factorial(n) == zoo`` for a negative integer ``n``,
        ``factorial(oo) == oo``, ``factorial(x) == gamma(x + 1)`` off the
        integers).  Decision 9.

        The facts, each a theorem about Euler's gamma function (Whittaker
        and Watson, ch. 12):

        - Poles: ``gamma`` is meromorphic on C with simple poles exactly at
          the nonpositive integers (``gamma(w) = gamma(w + n + 1)/(w*(w +
          1)*...*(w + n))``, the numerator finite and nonzero at ``w = -n``).
          At a pole ``|gamma(w')| -> oo`` as ``w' -> w`` from every
          direction, so the value is the point at infinity of the Riemann
          sphere, ``zoo``, as ``1/0 = zoo``; it is SymPy's value and
          satassume's convention (templates/gamma_functions.py:
          ``gamma(-n) == zoo``; the special-values table has no row).
          Decision 9.
        - No zeros: ``1/gamma`` is entire (Weierstrass product), so at
          every other finite ``w`` the value is a finite nonzero number.
        - The positive reals: ``gamma(x) = integral of s**(x - 1)*e**-s
          over (0, oo)``, an integral of a positive function, so real and
          positive.
        - The negative non-integers: ``gamma(x) = gamma(x + n)/(x*(x +
          1)*...*(x + n - 1))`` with ``n = -floor(x)``, so ``x + n`` lies in
          ``(0, 1)`` and ``gamma(x + n) > 0``, and of the ``n`` factors of
          the denominator exactly ``n`` are negative: the sign is
          ``(-1)**n = (-1)**floor(x)``.  With a fresh integer ``h``:
          ``x`` in ``(2*h, 2*h + 1)`` and the value positive, or ``x`` in
          ``(2*h - 1, 2*h)`` and the value negative (``h = floor(x)/2`` or
          ``(floor(x) + 1)/2``; either interval fixes the parity of
          ``floor(x)``).
        - The positive integers: ``gamma(n) = (n - 1)!`` (``gamma(1) = 1``,
          ``gamma(w + 1) = w*gamma(w)``), so ``1, 1, 2`` at ``n = 1, 2, 3``,
          and for ``n >= 4`` a multiple of ``3! = 6``: even and ``>= 6``
          (so composite).
        - Infinities: ``gamma(oo) = oo``, the limit along the real axis
          (``gamma`` is log-convex on ``(0, oo)`` with ``gamma(1) =
          gamma(2)``, so increasing on ``[2, oo)``, and ``gamma(x) >=
          (floor(x) - 1)!`` grows without bound), SymPy's value and
          satassume's convention (``gamma(oo) == oo``).  ``gamma(-oo)``
          (no limit: poles accumulate) and ``gamma`` of the other kind are
          free.  ``nan`` gives ``nan`` (special-values N1).

        Not encoded: ``gamma(conjugate(w)) = conjugate(gamma(w))``, values
        and enclosures at other points (``gamma(1/2) = sqrt(pi)``), and
        number theory beyond the integers (whether ``gamma`` is rational or
        algebraic at a rational is open but at a few points)."""
        a, za = t.atoms, w.atoms
        one = z3.IntVal(1, self.ctx)
        pole = z3.And(za["integer"], w.k <= 0)
        self._add(z3.Implies(w.nan, t.nan), z3.Implies(w.pinf, t.pinf),
                  z3.Implies(z3.And(w.fin, pole), t.cinf),
                  z3.Implies(z3.And(w.fin, z3.Not(pole)), z3.And(t.fin, z3.Or(t.re != 0, t.im != 0))),
                  z3.Implies(z3.And(w.real(), w.re > 0), z3.And(t.im == 0, t.re > 0)))
        h = z3.ToReal(z3.Int(f"gh{self._count()}", self.ctx))
        self._add(z3.Implies(z3.And(w.real(), z3.Not(za["integer"]), w.re < 0), z3.And(t.im == 0, z3.Or(
            z3.And(2 * h < w.re, w.re < 2 * h + 1, t.re > 0),
            z3.And(2 * h - 1 < w.re, w.re < 2 * h, t.re < 0)))))
        self._int_value(t, z3.And(za["integer"], w.k >= 1, w.k <= 2), one)
        self._int_value(t, z3.And(za["integer"], w.k == 3), z3.IntVal(2, self.ctx))
        self._add(z3.Implies(z3.And(za["integer"], w.k >= 4), z3.And(a["integer"], t.r == 0, t.k >= 6)))

    def _fresh_real(self, name):
        return z3.Real(f"{name}{self._count()}", self.ctx)

    @_scoped
    def _exp_pair(self, cond, u, v):
        """Under ``cond``, ``v = e**u`` for reals ``u``, ``v``.  The facts:
        ``e**u > 0``; the tangent at 0, ``e**u >= 1 + u`` (convexity; it is
        ``log(v) <= v - 1`` read the other way); ``e**0 = 1``; and, since
        ``u -> e**u`` is strictly increasing on R, for every pair
        registered before, ``u < u'`` iff ``v < v'`` and ``u = u'`` iff
        ``v = v'``: finitely many ground instances, quadratic in the number
        of ``exp``/``log`` terms of the query.  ``log(1) = 0``,
        ``log(exp(x)) = x`` for real ``x`` and the sign of ``log(x)`` against
        ``x - 1`` follow from these.

        Raw, as ``_pow``; ``cond``, ``u``, ``v`` are AstRefs, kept in
        ``_pairs`` as the wrapper code kept them (their references count at
        check time), and their classes decide the order of a comparison
        (``_reflected``)."""
        R, add, num = self._raw, self._add_raw, self._raw.real
        C, U, V = cond.as_ast(), u.as_ast(), v.as_ast()
        one = num(1)                                                        # RealVal(1)
        r = _reflected(type(v), z3.RatNumRef)                               # v < one is one > v
        # Implies(cond, And(v > 0, v >= one + u, (u < 0) == (v < one), (u == 0) == (v == one)))
        add(R.implies(C, R.and_(R.gt(V, num(0)), R.ge(V, R.add(one, U)),
                                R.eq(R.lt(U, num(0)), R.gt(one, V) if r else R.lt(V, one)),
                                R.eq(R.eq(U, num(0)), R.eq(one, V) if r else R.eq(V, one)))))
        lt = lambda a, b, r: R.gt(b, a) if r else R.lt(a, b)               # noqa: E731 (a < b)
        eq = lambda a, b, r: R.eq(b, a) if r else R.eq(a, b)               # noqa: E731 (a == b)
        for c2, u2, v2 in self._pairs:
            ru, rv = _reflected(type(u), type(u2)), _reflected(type(v), type(v2))
            U2, V2 = u2.as_ast(), v2.as_ast()
            # Implies(And(cond, c2), And((u < u2) == (v < v2), (u == u2) == (v == v2)))
            add(R.implies(R.and_(C, c2.as_ast()), R.and_(R.eq(lt(U, U2, ru), lt(V, V2, rv)),
                                                         R.eq(eq(U, U2, ru), eq(V, V2, rv)))))
        self._pairs.append((cond, u, v))

    @_scoped
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
        R, add, num = self._raw, self._add_raw, self._raw.real
        eq, ne, gt, lt, ge, le, neg = R.eq, R.ne, R.gt, R.lt, R.ge, R.le, R.neg
        T, Z = t.p, z.p
        a, za = T.atoms, Z.atoms
        add(R.implies(Z.nan, T.nan))                                        # Implies(z.nan, t.nan)
        add(R.implies(Z.pinf, T.pinf))
        # Implies(z.cinf, Or(t.cinf, t.nan, And(t.fin, t.re == 0, t.im == 0)))
        add(R.implies(Z.cinf, R.or_(T.cinf, T.nan, R.and_(T.fin, eq(T.re, num(0)), eq(T.im, num(0))))))
        self._int_value(t, Z.ninf, R.int(0))
        zero = R.and_(Z.fin, eq(Z.re, num(0)), eq(Z.im, num(0)))            # And(z.fin, z.re == 0, z.im == 0)
        self._int_value(t, zero, R.int(1))
        m = self._fresh_real("expm")
        M = m.as_ast()
        # Implies(z.fin, And(t.fin, t.re * t.re + t.im * t.im == m * m))
        add(R.implies(Z.fin, R.and_(T.fin, eq(R.add(R.mul(T.re, T.re), R.mul(T.im, T.im)), R.mul(M, M)))))
        # Implies(And(z.fin, z.im == 0), And(t.re == m, t.im == 0))
        add(R.implies(R.and_(Z.fin, eq(Z.im, num(0))), R.and_(eq(T.re, M), eq(T.im, num(0)))))
        self._exp_pair(z.fin, z.re, m)
        pi = self.term(S.Pi).p.re
        b, re, im = Z.im, T.re, T.im
        b2 = lambda: R.mul(num(2), b)                                       # noqa: E731 (2 * b)
        # Implies(z.fin, And(
        #     Implies(And(b > 0, b < pi), im > 0),
        #     Implies(And(b < 0, b > -pi), im < 0),
        #     Implies(And(2 * b < pi, 2 * b > -pi), re > 0),
        #     Implies(Or(2 * b == pi, 2 * b == -pi), re == 0),
        #     Implies(Or(And(2 * b > pi, b <= pi), And(2 * b < -pi, b >= -pi)), re < 0),
        #     Implies(Or(b == pi, b == -pi), And(re == -m, im == 0))))
        add(R.implies(Z.fin, R.and_(
            R.implies(R.and_(gt(b, num(0)), lt(b, pi)), gt(im, num(0))),
            R.implies(R.and_(lt(b, num(0)), gt(b, neg(pi))), lt(im, num(0))),
            R.implies(R.and_(lt(b2(), pi), gt(b2(), neg(pi))), gt(re, num(0))),
            R.implies(R.or_(eq(b2(), pi), eq(b2(), neg(pi))), eq(re, num(0))),
            R.implies(R.or_(R.and_(gt(b2(), pi), le(b, pi)), R.and_(lt(b2(), neg(pi)), ge(b, neg(pi)))),
                      lt(re, num(0))),
            R.implies(R.or_(eq(b, pi), eq(b, neg(pi))), R.and_(eq(re, neg(M)), eq(im, num(0)))))))
        w = z.expr
        if isinstance(w, Mul) and S.ImaginaryUnit in w.args and S.Pi in w.args:
            rest = list(w.args)
            rest.remove(S.ImaginaryUnit)
            rest.remove(S.Pi)
            c = self.term(Mul(*rest))
            Ct = c.p
            real = lambda: R.and_(Ct.fin, eq(Ct.im, num(0)))               # noqa: E731 (c.real())
            one = R.int(1)                                                  # IntVal(1)
            # And(c.real(), c.atoms["integer"]), If(c.r == 0, one, -one)
            self._int_value(t, R.and_(real(), Ct.atoms["integer"]), R.ite(eq(Ct.r, R.int(0)), one, neg(one)))
            # Implies(And(c.real(), Not(c.atoms["integer"])), im != 0)
            add(R.implies(R.and_(real(), R.not_(Ct.atoms["integer"])), ne(im, num(0))))
            if isinstance(c.expr, Rational):
                # period 2*pi*I: exp(I*pi*c) = exp(I*pi*c') with c' = c - 2*n
                # in (-1, 1], and pi*c' in (-pi, pi] has the signs above
                f = Fraction(int(c.expr.p), int(c.expr.q))
                f -= 2 * math.ceil((f - 1) / 2)
                add(gt(im, num(0)) if 0 < f < 1 else lt(im, num(0)) if -1 < f < 0 else eq(im, num(0)))
                add(gt(re, num(0)) if abs(f) < Fraction(1, 2) else eq(re, num(0)) if abs(f) == Fraction(1, 2)
                    else lt(re, num(0)))
            else:
                # cos(pi*c) = 0 iff c - 1/2 is an integer (the zeros of cos)
                h = self.term(Add(c.expr, Rational(-1, 2), evaluate=False))
                # Implies(c.real(), (re == 0) == h.atoms["integer"])
                add(R.implies(real(), eq(eq(re, num(0)), h.p.atoms["integer"])))
                ce = c.expr
                if isinstance(ce, Mul) and len(ce.args) == 2 and ce.args[0] in (S.Half, -S.Half):
                    # c = +-y/2 lies in 1/2 + Z iff y is an odd integer (the
                    # same fact, on y's integer witness)
                    Y = self.term(ce.args[1]).p
                    # Implies(y.real(), (re == 0) == And(y.atoms["integer"], y.r == 1))
                    add(R.implies(R.and_(Y.fin, eq(Y.im, num(0))),
                                  eq(eq(re, num(0)), R.and_(Y.atoms["integer"], eq(Y.r, R.int(1))))))
        # Hermite-Lindemann (1882)
        # Implies(And(z.fin, za["algebraic"], Not(zero)), Not(a["algebraic"]))
        add(R.implies(R.and_(Z.fin, za["algebraic"], R.not_(zero)), R.not_(a["algebraic"])))
        if isinstance(w, log) and len(w.args) == 1:
            v = self.term(w.args[0])
            V = v.p
            # And(v.fin, Not(And(v.re == 0, v.im == 0)))
            ok = R.and_(V.fin, R.not_(R.and_(eq(V.re, num(0)), eq(V.im, num(0)))))
            add(R.implies(ok, R.and_(T.fin, eq(T.re, V.re), eq(T.im, V.im))))   # Implies(ok, And(...))
            self._same(t, v, ok)
        if isinstance(w, Rational):
            b = exp_bounds(Fraction(int(w.p), int(w.q)))
            if b is not None:
                # m > q, m < q: q (a RatNumRef) compares first (_reflected)
                lo = self._q(b[0])
                add(lt(lo.as_ast(), M))
                hi = self._q(b[1])
                add(gt(hi.as_ast(), M))

    @_scoped
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
        R, add, num = self._raw, self._add_raw, self._raw.real
        eq, gt, lt, ge, neg = R.eq, R.gt, R.lt, R.ge, R.neg
        T, Z = t.p, z.p
        a, za = T.atoms, Z.atoms
        add(R.implies(Z.nan, T.nan))                                        # Implies(z.nan, t.nan)
        add(R.implies(R.or_(Z.pinf, Z.ninf), T.pinf))                       # Implies(Or(z.pinf, z.ninf), t.pinf)
        add(R.implies(Z.cinf, R.or_(T.pinf, T.cinf)))                       # Implies(z.cinf, Or(t.pinf, t.cinf))
        # Implies(And(z.fin, z.re == 0, z.im == 0), t.cinf)
        add(R.implies(R.and_(Z.fin, eq(Z.re, num(0)), eq(Z.im, num(0))), T.cinf))
        x, y, th = Z.re, Z.im, T.im
        nz = R.and_(Z.fin, R.not_(R.and_(eq(x, num(0)), eq(y, num(0)))))   # And(z.fin, Not(And(x == 0, y == 0)))
        m = self._fresh_real("logm")
        M = m.as_ast()
        # Implies(nz, And(t.fin, m > 0, m * m == x * x + y * y, m >= x, m >= -x, m >= y, m >= -y))
        add(R.implies(nz, R.and_(T.fin, gt(M, num(0)), eq(R.mul(M, M), R.add(R.mul(x, x), R.mul(y, y))),
                                 ge(M, x), ge(M, neg(x)), ge(M, y), ge(M, neg(y)))))
        # Implies(And(nz, y == 0), m == If(x >= 0, x, -x))
        add(R.implies(R.and_(nz, eq(y, num(0))), eq(M, R.ite(ge(x, num(0)), x, neg(x)))))
        self._exp_pair(z3.BoolRef(nz, self.ctx), t.re, m)
        pi = self.term(S.Pi).p.re
        th2 = lambda: R.mul(num(2), th)                                     # noqa: E731 (2 * th)
        # Implies(nz, And(
        #     Implies(y > 0, And(th > 0, th < pi)),
        #     Implies(y < 0, And(th < 0, th > -pi)),
        #     Implies(And(y == 0, x > 0), th == 0),
        #     Implies(And(y == 0, x < 0), th == pi),
        #     Implies(x > 0, And(2 * th < pi, 2 * th > -pi)),
        #     Implies(And(x == 0, y > 0), 2 * th == pi),
        #     Implies(And(x == 0, y < 0), 2 * th == -pi),
        #     Implies(And(x < 0, y > 0), 2 * th > pi),
        #     Implies(And(x < 0, y < 0), 2 * th < -pi)))
        add(R.implies(nz, R.and_(
            R.implies(gt(y, num(0)), R.and_(gt(th, num(0)), lt(th, pi))),
            R.implies(lt(y, num(0)), R.and_(lt(th, num(0)), gt(th, neg(pi)))),
            R.implies(R.and_(eq(y, num(0)), gt(x, num(0))), eq(th, num(0))),
            R.implies(R.and_(eq(y, num(0)), lt(x, num(0))), eq(th, pi)),
            R.implies(gt(x, num(0)), R.and_(lt(th2(), pi), gt(th2(), neg(pi)))),
            R.implies(R.and_(eq(x, num(0)), gt(y, num(0))), eq(th2(), pi)),
            R.implies(R.and_(eq(x, num(0)), lt(y, num(0))), eq(th2(), neg(pi))),
            R.implies(R.and_(lt(x, num(0)), gt(y, num(0))), gt(th2(), pi)),
            R.implies(R.and_(lt(x, num(0)), lt(y, num(0))), lt(th2(), neg(pi))))))
        one = R.and_(Z.fin, eq(x, num(1)), eq(y, num(0)))                   # And(z.fin, x == 1, y == 0)
        self._int_value(t, one, R.int(0))
        # Hermite-Lindemann (1882)
        # Implies(And(nz, za["algebraic"], Not(one)), Not(a["algebraic"]))
        add(R.implies(R.and_(nz, za["algebraic"], R.not_(one)), R.not_(a["algebraic"])))
        w = z.expr
        if isinstance(w, exp) and len(w.args) == 1:
            v = self.term(w.args[0])
            V = v.p
            real = lambda: R.and_(V.fin, eq(V.im, num(0)))                 # noqa: E731 (v.real())
            # Implies(v.real(), And(t.fin, t.re == v.re, t.im == 0))
            add(R.implies(real(), R.and_(T.fin, eq(T.re, V.re), eq(T.im, num(0)))))
            self._same(t, v, real())
        if isinstance(w, Rational) and w != 0:
            b = log_bounds(abs(Fraction(int(w.p), int(w.q))))
            if b is not None:
                # t.re > q, t.re < q: q (a RatNumRef) compares first (_reflected)
                lo = self._q(b[0])
                add(lt(lo.as_ast(), T.re))
                hi = self._q(b[1])
                add(gt(hi.as_ast(), T.re))

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
        N1).  The hyperbolic functions at ``+-oo`` are their limits
        (decision 10).  Any other infinite argument leaves the value free:
        the table has no row for these functions (it names ``sin(oo)`` as
        a point no row covers), and none of them has a limit at every
        infinity.

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
        if family == "hyp":
            # decision 10: the limits at +-oo (satassume's templates/hyperbolic.py)
            for inf, s in ((z.pinf, 1), (z.ninf, -1)):
                if den is None:                 # cosh -> oo, sinh -> +-oo
                    v = t.pinf if num == "E" or s == 1 else t.ninf
                else:                           # tanh, coth -> +-1; sech, csch -> 0
                    c = 0 if num == 1 else s
                    v = z3.And(t.fin, t.re == c, t.im == 0)
                self._add(z3.Implies(inf, v))
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
          ``f`` maps the reals into its range.  For a finite non-real
          ``x`` ``w`` is not real either: each forward function ``f``
          (``sin``, ``cos``, ``tan``, ``cot`` and their hyperbolic versions)
          maps the reals into the reals and ``zoo`` (``tan``, ``cot``,
          ``coth`` have real poles).
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
        # off the real axis w is not real: f(w) = x, and f maps the reals
        # into the reals and zoo
        self._add(z3.Implies(z3.And(x.fin, x.im != 0), z3.Not(treal)))

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
