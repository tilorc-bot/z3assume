"""Replay a recorded query stream through z3assume and save the answers.

    PYTHONHASHSEED=0 PYTHONPATH=.:/path/to/sympy python \\
        tools/stream_answers.py STREAM OUT.json [--jobs N] [--limit N]

``STREAM`` is a pickle of ``(prop, assum, rec)`` triples (satassume's
``stream.pkl`` format; ``tools/gate2_stream.py`` in satassume makes one
from gate2).  Writes the JSON shape of satassume's
``tools/stream_answers.py``: ``{"mode", "seconds", "answers"}`` with one
answer per query (true / false / null / "error" for a ValueError, i.e.
inconsistent assumptions), plus per-query lists ``"timeout"`` (number of
z3 checks stopped by the wall-clock backstop), ``"unknown"`` (z3 checks
answered unknown), ``"seconds"`` (as ``"query_seconds"``) and, for any
other exception, ``"crash"`` entries ``[index, repr]`` (the answer is then
``"crash"``).

The queries are independent, so ``--jobs`` workers (default 6) take
contiguous chunks in order; each answer is placed by its index.  Each
worker keeps its own memo of (prop, assum) -> result, so a repeated query
reports the timeouts of its first evaluation.
"""
import argparse
import json
import multiprocessing as mp
import pickle
import signal
import sys
import time

_STREAM = None
_MEMO = {}
QUERY_TIMEOUT = 300  # s; a guard for a query that hangs outside z3


class _Hang(Exception):
    pass


def _alarm(*_):
    raise _Hang()


def _one(p, a):
    from z3assume import ask
    askmod = sys.modules["z3assume.ask"]
    askmod.last.update(checks=0, unknown=0, timeout=0)
    t0 = time.perf_counter()
    crash = None
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(QUERY_TIMEOUT)
    try:
        ans = ask(p, a)
    except ValueError:
        ans = "error"
    except _Hang:
        ans, crash = "crash", f"hang > {QUERY_TIMEOUT}s"
    except Exception as e:  # noqa: BLE001
        ans, crash = "crash", repr(e)[:300]
    finally:
        signal.alarm(0)
    dt = time.perf_counter() - t0
    return ans, askmod.last["timeout"], askmod.last["unknown"], dt, crash


def _chunk(rng):
    out = []
    for i in range(*rng):
        p, a, _rec = _STREAM[i]
        try:
            key = (p, a)
            hit = _MEMO.get(key)
        except TypeError:
            key, hit = None, None
        if hit is not None:
            ans, to, unk, _dt, crash = hit
            out.append((i, ans, to, unk, 0.0, crash))
            continue
        r = _one(p, a)
        if key is not None:
            _MEMO[key] = r
        out.append((i,) + r)
    return out


def main():
    global _STREAM
    ap = argparse.ArgumentParser()
    ap.add_argument("stream")
    ap.add_argument("out")
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--chunk", type=int, default=25)
    args = ap.parse_args()
    _STREAM = pickle.load(open(args.stream, "rb"))
    n = len(_STREAM) if args.limit is None else min(args.limit, len(_STREAM))
    ranges = [(s, min(s + args.chunk, n)) for s in range(0, n, args.chunk)]
    answers = [None] * n
    timeout = [0] * n
    unknown = [0] * n
    qsec = [0.0] * n
    crashes = []
    t0 = time.perf_counter()
    done = 0
    ctx = mp.get_context("fork")
    with ctx.Pool(args.jobs) as pool:
        for res in pool.imap(_chunk, ranges):
            for i, ans, to, unk, dt, crash in res:
                answers[i], timeout[i], unknown[i], qsec[i] = ans, to, unk, dt
                if crash:
                    crashes.append([i, crash])
            done += len(res)
            if done % 1000 < args.chunk:
                print(f"{done}/{n} {time.perf_counter() - t0:.0f}s", flush=True)
    dt = time.perf_counter() - t0
    print(f"z3assume: {n} queries in {dt:.1f}s, {sum(1 for t in timeout if t)} "
          f"with timeouts, {len(crashes)} crashes", flush=True)
    json.dump({"mode": "z3assume", "seconds": dt, "jobs": args.jobs,
               "answers": answers, "timeout": timeout, "unknown": unknown,
               "query_seconds": qsec, "crash": crashes},
              open(args.out, "w"))


if __name__ == "__main__":
    sys.exit(main())
