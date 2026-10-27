"""``ask(P, A)``: entailment checks with z3 (docs/design.md, "Answering")."""
from __future__ import annotations

import time
from typing import Optional

import z3
from z3.z3core import Z3_solver_assert
from sympy import Basic
from sympy.core.function import AppliedUndef

from .encode import Encoder, Unsupported

#: z3's resource limit per check: a count of internal steps, so an answer
#: does not depend on the machine's speed or load (decision 12, #31).
RLIMIT = 1_000_000
#: Wall-clock backstop (ms) of a query: z3 checks the rlimit only at some
#: points, and in its nonlinear solver a step can take far longer than
#: elsewhere.  Each side of a decision (``A & ~P``, ``A & P``) gets half of
#: it, at most what is left of the query's.  When it fires the check is
#: unknown, so the answer is None; it is counted in ``last["timeout"]``
#: (decision 16).
TIMEOUT_MS = 10_000
#: The fallback check (``_check``): tactics with no wall-clock timers of
#: their own (``qfnia`` has ``try_for``), and its rlimit; 0
#: turns it off.
FALLBACK = ("simplify", "propagate-values", "solve-eqs", "smt")
FALLBACK_RLIMIT = 250_000

#: z3 parameters of every check.  Groebner's growth per step is bounded
#: (z3's defaults are 2): a Groebner call is one z3 step, and with the
#: default growth one call on the polynomials of complex products (real
#: and imaginary parts) runs for seconds (#39, decision 15).
PARAMS = (("smt.arith.nl.grobner_expr_degree_growth", 1),
          ("smt.arith.nl.grobner_expr_size_growth", 1))

_MEMO = {}
MEMO_SIZE = 100_000

#: z3 Solver statistics of the last query (for the tools).
last = {"checks": 0, "unknown": 0, "timeout": 0}


def _check(enc: Encoder, deadline, *fs):
    """One check in a fresh solver: z3 preprocesses a non-incremental
    problem (solve-eqs, ...), and after a push it would not.  When the
    default solver gives up on its rlimit, one more try with the tactics
    ``FALLBACK`` and a smaller rlimit (``FALLBACK_RLIMIT``): the default
    solver's nonlinear search depends on term ids and caches, and a
    problem it misses in one term order (#29) the plain preprocessing and
    smt core often decide in a fraction of the steps.  Both runs share
    the side's wall-clock budget: half of ``TIMEOUT_MS``, at most what is
    left until ``deadline``."""
    last["checks"] += 1
    end = min(time.monotonic() + TIMEOUT_MS / 2000, deadline)
    r, timed_out = _run(enc, z3.Solver(ctx=enc.ctx), RLIMIT, end, fs)
    if r == z3.unknown and FALLBACK_RLIMIT and not timed_out:
        r, _ = _run(enc, z3.Then(*FALLBACK, ctx=enc.ctx).solver(), FALLBACK_RLIMIT, end, fs)
    if r == z3.unknown:
        last["unknown"] += 1
    return r


def _run(enc: Encoder, s, rlimit, end, fs):
    ms = int((end - time.monotonic()) * 1000)
    if ms < 1:                      # z3's timeout 0 would mean none
        last["timeout"] += 1
        return z3.unknown, True
    s.set("rlimit", rlimit)
    s.set("timeout", ms)
    for k, v in PARAMS:
        s.set(k, v)
    c, solver = enc.ctx.ref(), s.solver
    for f in enc.axioms:            # raw pointers, in order (s.add would wrap each)
        Z3_solver_assert(c, solver, f)
    s.add(*fs)
    r = s.check()
    timed_out = r == z3.unknown and s.reason_unknown() == "timeout"
    last["timeout"] += int(timed_out)
    return r, timed_out


def _is_constant(p) -> bool:
    return isinstance(p, Basic) and not p.free_symbols and not p.atoms(AppliedUndef)


def _decide(proposition, assumptions, deadline) -> Optional[bool]:
    """True, False or None; raises ValueError for inconsistent assumptions."""
    # a fresh context per query: in a shared one, z3's term ids and caches,
    # and so the search, would depend on the queries asked before (#7)
    enc = Encoder(z3.Context())
    try:
        p = enc.formula(proposition)
    except Unsupported:
        return None
    a = enc.formula(assumptions, opaque=True)
    r_not = _check(enc, deadline, a, z3.Not(p))
    r_pos = _check(enc, deadline, a, p)
    if r_not == z3.unsat and r_pos == z3.unsat:
        raise ValueError("inconsistent assumptions")
    # one side unsat and the other not shown unsat: the assumptions entail
    # the answer; they are inconsistent only if the other side is unsat too
    if r_not == z3.unsat:
        return True
    if r_pos == z3.unsat:
        return False
    return None


def ask(proposition, assumptions=True) -> Optional[bool]:
    """Truth value of ``proposition`` under ``assumptions``: True when z3
    shows ``assumptions & ~proposition`` unsatisfiable, False when it shows
    ``assumptions & proposition`` unsatisfiable, None otherwise.
    Inconsistent assumptions raise ValueError, except for a proposition
    about constants that is decided without them."""
    key = (proposition, assumptions)
    try:
        hit = _MEMO.get(key, _MEMO)
    except TypeError:          # unhashable input
        key, hit = None, _MEMO
    if hit is not _MEMO:
        return hit
    r = _ask(proposition, assumptions)
    # a None from the wall-clock backstop depends on the load: not memoized
    if key is not None and not last["timeout"]:
        if len(_MEMO) >= MEMO_SIZE:
            _MEMO.clear()
        _MEMO[key] = r
    return r


def _ask(proposition, assumptions):
    last["checks"] = last["unknown"] = last["timeout"] = 0
    deadline = time.monotonic() + TIMEOUT_MS / 1000
    if assumptions is not True and _is_constant(proposition):
        r = _decide(proposition, True, deadline)
        if r is not None:
            return r
    return _decide(proposition, assumptions, deadline)
