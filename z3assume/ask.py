"""``ask(P, A)``: entailment checks with z3 (docs/design.md, "Answering")."""
from __future__ import annotations

from typing import Optional

import z3
from z3.z3core import Z3_solver_assert
from sympy import Basic
from sympy.core.function import AppliedUndef

from .encode import Encoder, Unsupported

#: z3's resource limit per check: a count of internal steps, so an answer
#: does not depend on the machine's speed or load.
RLIMIT = 2_000_000
#: Wall-clock backstop (ms): z3 checks the rlimit only at some points and
#: can overrun it on nonlinear integer problems.  When it fires the check
#: is unknown, so the answer is None; it is counted in ``last["timeout"]``.
TIMEOUT_MS = 10_000
#: rlimit of the fallback check (``_check``); 0 turns it off.
FALLBACK_RLIMIT = 250_000

_MEMO = {}
MEMO_SIZE = 100_000

#: z3 Solver statistics of the last query (for the tools).
last = {"checks": 0, "unknown": 0, "timeout": 0}


def _check(enc: Encoder, *fs):
    """One check in a fresh solver: z3 preprocesses a non-incremental
    problem (solve-eqs, ...), and after a push it would not.  When the
    default solver gives up on its rlimit, one more try with the qfnia
    tactic and a smaller rlimit (``FALLBACK_RLIMIT``): the default
    solver's nonlinear search depends on term ids and caches, and a
    problem it misses in one term order (#29) qfnia often decides in a
    fraction of the steps."""
    last["checks"] += 1
    r, timed_out = _run(enc, z3.Solver(ctx=enc.ctx), RLIMIT, fs)
    # not after the wall-clock backstop: that would double it
    if r == z3.unknown and FALLBACK_RLIMIT and not timed_out:
        r, _ = _run(enc, z3.Tactic("qfnia", ctx=enc.ctx).solver(), FALLBACK_RLIMIT, fs)
    if r == z3.unknown:
        last["unknown"] += 1
    return r


def _run(enc: Encoder, s, rlimit, fs):
    s.set("rlimit", rlimit)
    s.set("timeout", TIMEOUT_MS)
    c, solver = enc.ctx.ref(), s.solver
    for f in enc.axioms:            # raw pointers, in order (s.add would wrap each)
        Z3_solver_assert(c, solver, f)
    s.add(*fs)
    r = s.check()
    timed_out = r == z3.unknown and s.reason_unknown() == "timeout"
    last["timeout"] += timed_out
    return r, timed_out


def _is_constant(p) -> bool:
    return isinstance(p, Basic) and not p.free_symbols and not p.atoms(AppliedUndef)


def _decide(proposition, assumptions) -> Optional[bool]:
    """True, False or None; raises ValueError for inconsistent assumptions."""
    # a fresh context per query: in a shared one, z3's term ids and caches,
    # and so the search, would depend on the queries asked before (#7)
    enc = Encoder(z3.Context())
    try:
        p = enc.formula(proposition)
    except Unsupported:
        return None
    a = enc.formula(assumptions, opaque=True)
    r_not = _check(enc, a, z3.Not(p))
    r_pos = _check(enc, a, p)
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
    if assumptions is not True and _is_constant(proposition):
        r = _decide(proposition, True)
        if r is not None:
            return r
    return _decide(proposition, assumptions)
