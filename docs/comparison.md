# Comparison with satassume

z3assume is compared with satassume (main at 9bafaa5) on two of satassume's
corpora, using the same SymPy on both sides (1.15.dev, the checkout
satassume's tools use):

- the refine stream (`stream.pkl`, 16,232 queries recorded from SymPy's
  `refine`), and
- gate2 (`gate2-frozen.jsonl`, 2,863 queries), replayed through satassume's
  `tools/gate2_stream.py`.

Per query: **agree** (same answer, both raising included), **more**
(satassume None, z3assume definite), **less** (satassume definite,
z3assume None), **CONTRADICT** (True against False) and **error-diff** (only
one side raises ValueError). Each contradiction must be either a z3assume bug,
which gets fixed, or a satassume bug with a mathematical argument, which gets
filed on satassume.

## How to run

    PY=/path/to/venv/bin/python   # sympy 1.15.dev and z3-solver
    SYMPY=/path/to/sympy
    PYTHONHASHSEED=0 PYTHONPATH=SATASSUME:$SYMPY $PY SATASSUME/tools/stream_answers.py stream.pkl sat.json default
    PYTHONHASHSEED=0 PYTHONPATH=.:$SYMPY $PY tools/stream_answers.py stream.pkl z3.json --jobs 6
    PYTHONHASHSEED=0 PYTHONPATH=.:$SYMPY $PY tools/compare_answers.py stream.pkl sat.json z3.json stream

`tools/compare_answers.py` prints the table per predicate, the contradictions
and error-diffs, and the constructs found in the "less" queries.

## Results, 23 Oct 2026 (z3assume 0f84081, satassume 9bafaa5)

| corpus | n | agree | more | less | CONTRADICT | error-diff | z3 timeouts |
|---|---|---|---|---|---|---|---|
| stream | 16,232 | 15,042 | 49 | 1,137 | 0 | 4 | 0 |
| gate2 | 2,863 | 2,288 | 30 | 545 | 0 | 0 | 0 |

The tables per predicate are in the PR that added this file
(tilorc-bot/z3assume#2).

The four error-diffs (stream 6796, 6798, 6813 and 6815) are expected. Each
asks `Q.zero(pi)` or `Q.negative(pi)` under assumptions that contain
`Q.negative(x) & Q.positive(x)`, so the assumptions are inconsistent.
satassume decides a constant proposition first, without the assumptions,
and answers False. z3assume does not encode `pi` yet, so it gets None from
that first step and then raises on the inconsistent set. That is the
documented behaviour, and the four will agree once `pi` is encoded.

Most of the "less" answers come from constructs the first slice treats as
opaque:

- **Stream:** `pi` (692 queries), non-integer Rationals mixed with them
  (404), `Abs`/`re`/`im`/`sign` (390) and `1/x` of such terms (248).
- **gate2:** symbolic powers such as `I**I` and `3**I` (145), trig at
  numbers such as `sin(7)` (116), `pi` (113), named constants (`E`,
  `GoldenRatio`), `exp`/`log` at numbers, and Floats.

These classes set the order in which coverage is widened.

Timing (single process, for scale only; bench-container numbers will
replace these): satassume answers the stream in 11 s; z3assume needs about
800 s of CPU, about 50 ms per query, two z3 checks each.
