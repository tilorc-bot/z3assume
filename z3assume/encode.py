"""Translation of SymPy terms and propositions into z3 (docs/design.md).

One :class:`Encoder` serves one query.  Every SymPy subterm it reaches gets
a :class:`Term` (its z3 variables) and the axioms of its node, collected in
``Encoder.axioms`` in the order the terms were reached (SymPy's argument
order), so the problem z3 sees does not depend on hashing.
"""
from __future__ import annotations

import z3
from sympy import Basic, Symbol
from sympy.core.add import Add
from sympy.core.mul import Mul
from sympy.core.numbers import (ComplexInfinity, ImaginaryUnit, Infinity, Integer, NaN,
                                NegativeInfinity, Rational)
from sympy.core.power import Pow
from sympy.core.relational import Relational
from sympy.logic.boolalg import (And, BooleanFalse, BooleanTrue, Equivalent, ITE, Implies, Not, Or,
                                 Xor)
from sympy.assumptions.assume import AppliedPredicate

from .predicates import BASIS, DEFINITIONS, PREDICATES, RULES
from .primes import is_prime


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

    def __init__(self, ctx=None):
        self.ctx = ctx or z3.main_ctx()
        self.terms = {}
        self.axioms = []
        self.opaque = {}
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
        # every predicate is False except finite (and infinite) and polar
        self._add(*(z3.Implies(t.nan, z3.Not(a[p])) for p in BASIS if p not in ("finite", "polar")))
        notnan = z3.Not(t.nan)
        # integer witnesses: z3 reasons about integers in the Int sort
        self._add(z3.Implies(z3.And(notnan, a["integer"]),
                             z3.And(t.real(), t.re == z3.ToReal(t.k), t.k == 2 * t.h + t.r, t.r >= 0, t.r <= 1)),
                  z3.Implies(z3.And(notnan, t.real(), z3.Not(a["integer"])), z3.Not(z3.IsInt(t.re))),
                  z3.Implies(notnan, a["even"] == z3.And(a["integer"], t.r == 0)),
                  z3.Implies(z3.And(notnan, a["prime"]), z3.And(a["integer"], t.k >= 2)),
                  z3.Implies(z3.And(notnan, a["integer"], z3.Or(t.k == 2, t.k == 3)), a["prime"]),
                  z3.Implies(z3.And(notnan, a["prime"], a["even"]), t.k == 2),
                  z3.Implies(notnan, a["composite"] == z3.And(a["integer"], t.k >= 2, z3.Not(a["prime"]))),
                  z3.Implies(z3.And(notnan, a["rational"]), t.real()))
        for prem, concl in RULES:
            self._add(z3.Implies(z3.And([_lit(a, p, s) for p, s in prem]),
                                 z3.Or([_lit(a, p, s) for p, s in concl])))

    def _value(self, t: Term, re, im):
        self._add(t.fin, t.re == re, t.im == im)

    def _node(self, t: Term, e, args):
        a = t.atoms
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
        elif isinstance(e, Symbol):
            self._add(z3.Not(t.nan))
            self._declared(t, e)
        elif isinstance(e, Add):
            self._sum(t, args)
        elif isinstance(e, Mul):
            self._product(t, args)
        elif isinstance(e, Pow) and isinstance(e.exp, Integer):
            self._power(t, self.term(e.base), int(e.exp))
        else:
            self._opaque(t, e)

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
        else:
            # t = 1/b**m: exact for b finite nonzero, zoo for 0, 0 for an infinity
            norm = re * re + im * im
            self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"])),
                                 z3.And(t.fin, t.re * norm == re, t.im * norm == -im)),
                      z3.Implies(ba["zero"], t.cinf),
                      z3.Implies(b.infinite(), z3.And(t.fin, t.re == 0, t.im == 0)))
            for p in ("rational", "algebraic"):
                self._add(z3.Implies(z3.And(b.fin, z3.Not(ba["zero"]), ba[p]), a[p]))

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
        key = ("eq", a.expr, b.expr)
        free = self._free(key)
        return z3.Or(z3.And(a.fin, b.fin, a.re == b.re, a.im == b.im),
                     z3.And(a.pinf, b.pinf), z3.And(a.ninf, b.ninf),
                     z3.And(z3.Or(z3.And(a.cinf, b.cinf), a.nan, b.nan), free))
