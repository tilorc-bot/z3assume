"""Compare satassume's and z3assume's answers on one query stream.

    PYTHONPATH=.:/path/to/sympy python tools/compare_answers.py \\
        STREAM SAT.json Z3.json NAME [--outdir DIR]

``SAT.json`` comes from satassume's ``tools/stream_answers.py``, ``Z3.json``
from this repository's ``tools/stream_answers.py``, both on ``STREAM``.
Each query falls in one category:

* agree       same answer (both "error" included)
* more        satassume None, z3assume True/False
* less        satassume True/False, z3assume None
* CONTRADICT  one True, the other False
* error-diff  exactly one side "error" (or a z3assume "crash")

Prints a table per predicate (the Q-predicate of a single
AppliedPredicate, "compound" for And/Or/Not/..., else the class name),
writes every CONTRADICT and error-diff query to
``DIR/NAME-contradictions.txt`` and classifies the "less" queries by the
SymPy constructs in the proposition and the assumptions.
"""
import argparse
import collections
import json
import os
import pickle

from sympy import (Abs, Basic, Float, Max, Min, Mod,
                   NumberSymbol, Piecewise, Pow, Rational, arg, ceiling,
                   conjugate, exp, floor, im, log, preorder_traversal, re,
                   sign)
from sympy.assumptions.assume import AppliedPredicate
from sympy.core.function import AppliedUndef, Function
from sympy.core.numbers import Exp1, ImaginaryUnit, Pi
from sympy.core.relational import Relational
from sympy.functions.combinatorial.factorials import (CombinatorialFunction,
                                                      binomial, factorial)
from sympy.functions.elementary.hyperbolic import HyperbolicFunction
from sympy.functions.elementary.trigonometric import (
    InverseTrigonometricFunction, TrigonometricFunction)
from sympy.functions.special.gamma_functions import gamma
from sympy.logic.boolalg import Boolean, BooleanFunction
from sympy.matrices.expressions import MatrixExpr

CATS = ["agree", "more", "less", "CONTRADICT", "error-diff"]
ERR = ("error", "crash")


def category(s, z):
    if s == z and type(s) is type(z):
        return "agree"
    if s in ERR or z in ERR:
        return "error-diff"
    if s is None:
        return "more"
    if z is None:
        return "less"
    return "CONTRADICT"


def predicate(p):
    if isinstance(p, AppliedPredicate):
        f = p.function
        return getattr(f, "name", None) or str(f)
    if isinstance(p, BooleanFunction):
        return "compound"
    return type(p).__name__


def constructs(*exprs):
    """The "special" SymPy constructs in ``exprs`` (a set of labels)."""
    out = set()
    for e in exprs:
        if not isinstance(e, Basic):
            continue
        for n in preorder_traversal(e):
            if isinstance(n, Float):
                out.add("Float")
            elif isinstance(n, Pi):
                out.add("pi")
            elif isinstance(n, Exp1):
                out.add("E")
            elif isinstance(n, NumberSymbol):
                out.add("other NumberSymbol")
            elif isinstance(n, ImaginaryUnit):
                out.add("I")
            elif n.is_Number and not n.is_Rational:
                out.add("oo/zoo/nan")
            elif isinstance(n, Rational) and not n.is_Integer:
                out.add("non-integer Rational")
            elif isinstance(n, Pow):
                x = n.exp
                if x.is_Integer:
                    if x.is_negative:
                        out.add("Pow negative integer exp")
                elif x.is_Rational:
                    out.add("Pow rational exp")
                else:
                    out.add("Pow symbolic exp")
            elif isinstance(n, exp):
                out.add("exp")
            elif isinstance(n, log):
                out.add("log")
            elif isinstance(n, (TrigonometricFunction, HyperbolicFunction,
                                InverseTrigonometricFunction)):
                out.add("trig/hyperbolic")
            elif isinstance(n, (Abs, re, im, sign, arg, conjugate)):
                out.add("Abs/re/im/sign")
            elif isinstance(n, AppliedUndef):
                out.add("AppliedUndef")
            elif isinstance(n, Piecewise):
                out.add("Piecewise")
            elif isinstance(n, (Min, Max)):
                out.add("Min/Max")
            elif isinstance(n, (factorial, gamma, binomial,
                                CombinatorialFunction)):
                out.add("factorial/gamma")
            elif isinstance(n, (floor, ceiling)):
                out.add("floor/ceiling")
            elif isinstance(n, Mod):
                out.add("Mod")
            elif isinstance(n, MatrixExpr):
                out.add("matrix")
            elif isinstance(n, Relational):
                out.add("relation")
            elif isinstance(n, AppliedPredicate) and n.function.name in (
                    "eq", "ne", "gt", "ge", "lt", "le"):
                out.add("relation")
            elif isinstance(n, Function) and not isinstance(n, Boolean):
                out.add("other: " + type(n).__name__)
    return out


def short(e, n=2000):
    s = str(e)
    return s if len(s) <= n else s[:n] + " ..."


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("stream")
    ap.add_argument("sat")
    ap.add_argument("z3")
    ap.add_argument("name")
    ap.add_argument("--outdir", default=".")
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()
    stream = pickle.load(open(args.stream, "rb"))
    sat = json.load(open(args.sat))
    z3 = json.load(open(args.z3))
    sa, za = sat["answers"], z3["answers"]
    assert len(sa) == len(za) == len(stream), (len(sa), len(za), len(stream))
    tos = z3.get("timeout", [0] * len(za))

    table = collections.defaultdict(collections.Counter)
    bad, less = [], []
    for i, ((p, a, rec), s, z) in enumerate(zip(stream, sa, za)):
        c = category(s, z)
        row = table[predicate(p)]
        row["n"] += 1
        row[c] += 1
        row["timeouts"] += bool(tos[i])
        if c in ("CONTRADICT", "error-diff"):
            bad.append((i, c, p, a, s, z, rec))
        elif c == "less":
            less.append((i, p, a))

    cols = ["n"] + CATS + ["timeouts"]
    w = max(len(k) for k in list(table) + ["predicate"])
    print(f"== {args.name}: satassume {sat.get('seconds', 0):.0f}s, "
          f"z3assume {z3.get('seconds', 0):.0f}s wall "
          f"({z3.get('jobs', '?')} jobs), z3 crashes {len(z3.get('crash', []))}")
    print(f"{'predicate':<{w}} " + " ".join(f"{c:>10}" for c in cols))
    tot = collections.Counter()
    for k in sorted(table, key=lambda k: -table[k]["n"]):
        tot.update(table[k])
        print(f"{k:<{w}} " + " ".join(f"{table[k][c]:>10}" for c in cols))
    print(f"{'TOTAL':<{w}} " + " ".join(f"{tot[c]:>10}" for c in cols))

    path = os.path.join(args.outdir, f"{args.name}-contradictions.txt")
    with open(path, "w") as f:
        for i, c, p, a, s, z, rec in bad:
            f.write(f"[{i}] {c}  satassume={s} z3assume={z} sympy={rec}\n"
                    f"  p: {short(p)}\n  a: {short(a)}\n")
    print(f"\n{len(bad)} CONTRADICT/error-diff -> {path}")

    classes = collections.Counter()
    only = collections.Counter()
    examples = collections.defaultdict(list)
    for i, p, a in less:
        cs = constructs(p, a) or {"(none)"}
        for c in cs:
            classes[c] += 1
            examples[c].append((len(str(p)) + len(str(a)), i, p, a))
        if len(cs) == 1:
            only[next(iter(cs))] += 1
    ndist = len({(p, a) for _, p, a in less})
    print(f"\n{len(less)} less-definite queries ({ndist} distinct); "
          "constructs (count / only):")
    for c, k in classes.most_common(args.top):
        print(f"  {c:<28} {k:>6} {only[c]:>6}")
        seen = set()
        for _, i, p, a in sorted(examples[c], key=lambda t: t[:2]):
            if (p, a) in seen:
                continue
            seen.add((p, a))
            if len(seen) > 2:
                break
            print(f"      [{i}] {short(p, 100)}  |  {short(a, 100)}")
    rest = [c for c, _ in classes.most_common()[args.top:]]
    if rest:
        print("  others: " + ", ".join(f"{c} {classes[c]}" for c in rest))


if __name__ == "__main__":
    main()
