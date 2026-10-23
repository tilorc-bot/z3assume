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
one side raises ValueError, or z3assume crashes). Each contradiction must be either a z3assume bug,
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

## Arguments for the newly definite answers

79 queries (49 stream, 30 gate2; 24 + 26 distinct `(prop, assum)` pairs) get
`None` from satassume and a definite answer from z3assume. Each one is
justified below by a definition, a theorem, or a convention written down in
z3assume's docs/design.md ("Values", "Predicates", "Terms", "Relations") or in
satassume's docs (theories.md "What relations mean", special-values row V1).
SymPy's own evaluation is used for none of them. No answer is wrong: every
class has a short proof, and no query is left unjustified.

All symbols are plain `Symbol`s with no declared assumptions (so any value
of D except `nan`, z3assume's and satassume's convention), except in gate2
2855, where `a`, `b`, `c` are declared `real=True` (finite reals).

| Class | stream / gate2 | Example | z3assume |
|---|---|---|---|
| N. `nan` is no number | 0 / 23 | `Q.integer(nan)`, `Q.nonzero(nan)`, `Q.hermitian(nan)` | False |
| P. Parity of `n` and `n + 1` | 24 / 0 | `Q.odd(k/2 + 1/2)` given `Q.odd(k) & Q.even(k/2 - 1/2)` | True |
| T. Parity of a rational multiple | 7 / 2 | `Q.odd(2*k/3)` given `Q.odd(k)`; `Q.even(2*x)` given `~Q.integer(x)` | False |
| Z. A zero factor | 9 / 0 | `Q.zero(x)` given `Q.negative(x*y)`; `Q.positive(x*y)` given `Q.zero(y)` | False |
| L. Integer bounds | 7 / 0 | `Q.negative(k + x - 1)` given `k, x` integers, `k >= 0`, `x > 0` | False |
| I. An interval with `pi` | 2 / 0 | `Q.integer(-t/(2*pi) + 1/2)` given `Q.positive(t) & Q.negative(t - pi)` | False |
| E. Sums of same-signed infinities | 0 / 4 | `Q.finite(x + y + z)` given `Q.finite(x)`, `y`, `z` both `-oo` | False |
| M. Monotonicity of multiplication | 0 / 1 | `a*c <= b*c` given `(a <= b) & (c > 0)`, `a, b, c` real | True |

**N.** satassume's special-values row V1, adopted in z3assume's design.md
("Predicates"): `nan` is no number, and every predicate except `finite`,
`infinite` (and `polar`) is False of it. All 23 queries ask one of
`integer, rational, algebraic, real, extended_real, complex, irrational,
imaginary, positive, negative, nonzero, zero, even, odd, prime, composite,
hermitian, antihermitian, transcendental` of `nan` under no assumptions.

**P.** Let `k` be odd and `m = (k - 1)/2`, an integer. Then
`k/2 - 1/2 = m` and `k/2 + 1/2 = m + 1`. For an integer, `m` even iff `m + 1`
odd. So `even(m)` gives `odd(k/2 + 1/2)` True and `even(k/2 + 1/2)` False,
and `odd(m)` the reverse.

**T.** By the definition of `even`/`odd` (integers with remainder 0/1).
`2k/3` with `k` odd: if `2k/3 = n` is an integer, `3n = 2k` is even, so `n`
is even; if not an integer it is not odd. Same for `x/3` with `x` even
(`3n = x` even forces `n` even). `2x` even means `2x = 2m` for an integer
`m`, so `x = m` is an integer, contradicting `~Q.integer(x)` (an infinite
`x` gives an infinite `2x`, not an integer).

**Z.** `negative` implies a finite nonzero real. If `x = 0` then `x*y` is
`0` (finite `y`) or `nan` (infinite `y`, convention `0*oo = nan`, design.md
"Values"/"Terms: Mul"); neither is negative, so `x`, `-x`, `y`, `-y` are not
zero. With `y = 0`, `x*y` is `0` or `nan`; `0` is not (extended) positive or
negative, and not `imaginary` (SymPy's definition: `I*b` with `b` real
nonzero; design.md: `im != 0`); `nan` is none of them by V1.

**L.** Integer `k >= 0`, `x >= 1`: `k + x - 1 >= 0` (not negative) and
`-k - x + 1 <= 0` (not positive). Integer `k <= -1`, `x >= 1`:
`k - x + 1 <= -1` and `-k + x - 1 >= 1`, both nonzero. Integers `k, x >= 1`:
`k + x - 1 >= 1`, so it is neither zero nor negative, and `-k - x + 1 <= -1`
is not positive. (Positive/negative assumptions also make `k`, `x` finite.)

**I.** `positive(t)` and `negative(t - pi)` give a real `t` with
`0 < t < pi`. `pi` is still opaque in z3assume, but the assumptions alone
make it real with `pi = t - (t - pi) > t > 0`; so `0 < t/(2*pi) < 1/2`. So `-t/(2*pi)` lies in
`(-1/2, 0)` and `-t/(2*pi) + 1/2` in `(0, 1/2)`: no integer in either.

**E.** Extended-real addition (design.md "Terms: Add"): `-oo` plus finite or
`-oo` terms is `-oo`, likewise `+oo`. With `x` finite and `y = -oo`, `z` is
`-oo` or (extended_negative) a finite negative or `-oo`; the sum is `-oo`,
not finite. Symmetrically for `+oo` and extended_positive.

**M.** `a, b, c` are declared real, so finite; `c > 0` and `a <= b` give
`(b - a)*c >= 0` in the ordered field R, i.e. `a*c <= b*c` (both sides
real, so the relation's extended-real conjuncts hold). Note: with plain
symbols this would be False-able (`a = 0`, `b = 1`, `c = oo`:
`0*oo = nan`); z3assume answers None there, correctly.

Indices per class (raw, duplicates included):

- N gate2: 392-404, 407-411, 2215-2218, 2226
- P stream: 132, 133, 142, 143, 166, 167, 175, 176, 657, 658, 667, 668,
  691, 692, 700, 701, 1136, 1137, 1205, 1206, 1428, 1429, 1459, 1460
- T stream: 3077, 3083, 3089, 3095, 3101, 3107, 13881; gate2: 1134, 1698
- Z stream: 10169, 10171, 10172, 10196, 12409-12413
- L stream: 14531, 14532, 14998, 15049, 15136, 15140, 15141
- I stream: 11829, 11834
- E gate2: 2792, 2795, 2803, 2806
- M gate2: 2855

Most of the "less" answers come from constructs the first slice treats as
opaque:

- **Stream:** `pi` (692 queries), non-integer Rationals mixed with them
  (404), `Abs`/`re`/`im`/`sign` (390) and `1/x` of such terms (248).
- **gate2:** symbolic powers such as `I**I` and `3**I` (145), trig at
  numbers such as `sin(7)` (116), `pi` (113), named constants (`E`,
  `GoldenRatio`), `exp`/`log` at numbers, and Floats.

These classes set the order in which coverage is widened.

## Later steps

Each widening step re-runs the comparison. Every answer it changes must
move to "agree", or to "more" with an argument given here.

| step | stream less | gate2 less | CONTRADICT | new "more" |
|---|---|---|---|---|
| first slice | 1,137 | 545 | 0 | 79 (above) |
| named constants (#3) | 593 | 405 | 0 | none |
| `Abs`, `re`, `im`, `conjugate`, `sign` (#5) | 269 | 390 | 0 | 16 distinct, stream only |
| `Eq` carries the predicates (#6) | 269 | 389 | 0 | none |
| symmetric `Eq` (#8) | 261 | 389 | 0 | none |
| Floats (#9) | 261 | 368 | 0 | 15 stream, 3 gate2 (all distinct) |
| one z3 context per query (#10) | 261 | 368 | 0 | none |
| `exp`, `log` (#11) | 228 | 313 | 0 | 2 stream (distinct) |
| trigonometric and hyperbolic (#12) | 197 | 200 | 0 | 9 stream, 7 gate2 (13 distinct) |

Arguments for the 16 new answers of the `Abs` step:

- **`re` of a real in an interval with `pi`** (11 queries, False): for a
  real `x`, `re(x) = x`. With `0 < x <= pi/2`, `x/pi` lies in `(0, 1/2]` and
  so is not an integer. The `2*pi` and `-t/(2*pi) + 1/2` variants are the
  same argument.
- **`x**2` real in `[0, pi/2]`** (one query, True): `x = a + b*I` gives
  `x**2 = a**2 - b**2 + 2*a*b*I`. Real means `a*b = 0`, and nonnegative
  means `b = 0` (if `a = 0`, then `-b**2 >= 0`). `x` is finite because `x**2`
  is. So `im(x) = 0`, and `im(x)/pi = 0` is an integer.
- **An imaginary `x = b*I`** (4 queries): `-I*x = b = im(x)`, so the sign of
  `im(x)` decides `positive(-I*x)`, and the other way round.
- **`sign` of an odd integer is `1` or `-1`** (4 queries, True):
  `sign(n) + 2 > 0`, `-2 < sign(n)`, `-sign(n) < 2`.

Arguments for the 18 new answers of the Float step (the reading of a
Float is design.md "Terms: `Float`": a finite real with its exact sign,
strictly within one ulp at its precision of its binary value):

- **A Float bound makes a symbol finite** (14 stream queries 4911-4996,
  `real(x)` True, `infinite(x)` and `infinite(x/pi + 1/2)` False, given
  `Q.le(x, F)` with a Float `F` (`1.5707963267948966`, `4.712`, `1.571`)
  and `Q.ge(x, -pi/2)`, `Q.gt(x, -pi/2)` or `Q.ge(x, pi/2)`): a relation
  holds only between extended reals (design.md "Relations"); `x <= F` with
  `F` finite excludes `x = +oo`, `x >= -pi/2` excludes `-oo`, so `x` is a
  finite real, and so is `x/pi + 1/2` (`pi` finite, nonzero).
- **Below `pi/2`** (stream 4930, `integer(x/pi + 1/2)` False given
  `x <= 1.5707963267948966` and `x > -pi/2`): this Float has 60 bits; its
  binary value is `pi/2 - 1.96e-17` and its ulp `2**-59 < 1.8e-18`, so its
  interval lies below `pi/2 - 1.7e-17` (and `pi`'s interval is `10**-20`
  wide). So `-pi/2 < x < pi/2` and `x/pi + 1/2` lies in `(0, 1)`. (The
  decimal `1.5707963267948966` is itself below `pi/2 = 1.5707963267948966192...`.)
  With `Q.ge(x, -pi/2)` instead, `x = -pi/2` gives `0` and z3assume
  answers None.
- **`1.0` is not even, prime or composite** (gate2 246, 249, 250, False):
  the interval of `Float(1.0)` is `(1 - 2**-52, 1 + 2**-52)`; its only
  integer is `1`, which is odd and neither prime nor composite, and a
  non-integer is none of the three. (`Q.integer(1.0)` and `Q.odd(1.0)` stay
  None.)

The other Float answers that moved (gate2 240-269, `Q.positive(1.0)`,
`Q.integer(7.2123)`, ...) now agree with satassume. The one Float query
still "less" is `Q.negative(x**1.4)` (gate2 1625): a Float exponent is not
an integer power and stays opaque.

Of four runs of the stream for this step on a shared machine (load
average 13 to 19), two had one check stopped by the 10 s backstop, each
in a query without a Float (stream 9500 and 3617, 0.05 s and 0.25 s in the
`Eq` step's run); 3617 kept its answer (False) and 9500 its None. The last
run, the one in the table, had none.

Arguments for the 2 new answers of the `exp`/`log` step (design.md
"Terms: `exp`, `log`"; satassume None, z3assume False):

- **`exp(I*t)` for `0 < t < pi` is not real** (stream 11818
  `Q.positive(exp(I*t))`, 11819 `Q.negative(exp(I*t))`, both under
  `Q.positive(t) & Q.negative(t - pi)`): `t` is a finite real in
  `(0, pi)`, so `exp(I*t) = cos t + I*sin t` with `sin t > 0`. Its
  imaginary part is nonzero, so it is not real, hence neither positive
  nor negative.

The other 33 stream and 55 gate2 answers that moved now agree with
satassume: `exp` of a real is positive (`Q.positive(exp(x))` given
`Q.real(x)`), `exp(z) != 0` (`Q.zero(exp(I*t))` given `Q.real(t)`, and
`Q.zero(sign(exp(x)))`), `log` of a positive real is real, `arg` on the
axes (`Q.real(log(x))` given `Q.imaginary(x)`), `log(pi) > 0`, the special
values `log(0) = zoo` and `log` of an infinity infinite, Hermite-Lindemann
(`Q.rational(exp(7))`, `Q.algebraic(log(7))`, `Q.rational(log(x))` given
`Q.rational(x) & Q.nonzero(x - 1)`), the enclosure of `exp(2)`, and
`exp(I*pi*x)` for an even or odd `x`. The `exp`/`log` queries still "less"
need a symbolic power (`exp(x)**x`, step 5), `sqrt` (`log(sqrt(2))`), or
trig.

In the final run one check of stream 6776 (no `exp`/`log`; `Q.integer(t/pi
+ 1/2)` with `tan`) hit the 10 s backstop; the other check was unsat, so
the answer (False) did not change, and alone the query takes 3.9 s with no
timeout. Wall times (6 jobs, shared machine, load average 7 to 12): stream
133 s, gate2 23 s (the Float step's run: 191 s, 36 s). Run back to back
with main (551bdb9, before the Float step) on gate2: 27.7 s and 31.9 s for
main, 38.5 s and 36.7 s for this step. The z3 problem of a query without
`exp`, `log` or `E` is unchanged (checked on the slowest movers), yet the
time of such queries alone varies by up to 5x between runs under this
load, so this gap is not measured well; a pinned benchmark was not run.

Arguments for the 16 new answers of the trigonometric and hyperbolic
step (design.md "Terms: `sin`, `cos`, ..."; satassume None, z3assume
False unless stated):

- **`sin` on `(0, pi)`** (stream 3260 `Q.zero(sin(x))` under
  `Q.positive(x) & Q.le(x, pi/2)`, 5176 under `Q.ge(x, 1) & Q.le(x, 2)`,
  5214 under `Q.eq(x, pi/2)`): a relation holds only between extended
  reals, so `x` is a finite real in `(0, pi)` (`2 < pi`), where
  `sin x > 0`.
- **`tan` without a zero in the interval** (stream 4048, 4080, 5336,
  5340, 6754, `Q.zero(tan(x))` under `0 < x < pi/2`, `-pi/2 < x < 0`,
  `0 < x < pi`, `-pi < x < 0`): `x` is a finite real with `sin x != 0`
  (the sign of `sin` on `(-pi, 0)` and `(0, pi)`); `tan x` is either
  `sin x/cos x != 0` or, where `cos x = 0`, `zoo` (`1/0 = zoo`, row M3),
  and neither is zero.
- **`x*tan(t)` real for `-pi/2 < t < pi/2`** (stream 6771, True, under
  `Q.positive(x)`): `t` is a finite real with `cos t > 0`, so `tan t =
  sin t/cos t` is real, and so is its product with the real `x`.
- **`cosh(1)**2 - sinh(1)**2 - 1` and `cos(1)**2 + sin(1)**2 - 1` are 0**
  (gate2 1621, 1763, 1784, 1810, 1831, `Q.negative`/`Q.positive` of the
  first, 1661 `Q.nonzero` of the second): `cosh**2 - sinh**2 = 1` and
  `cos**2 + sin**2 = 1` at a real point; the value is the number 0.
- **`acos(x)` for `x >= 1` is not positive** (gate2 2169, under
  `Q.nonnegative(x - 1)`): `acos(1) = 0`, and for real `x > 1` `acos(x)`
  is not real, as `cos` maps the reals into `[-1, 1]` and `cos(acos x) =
  x` for every branch.

The other 31 stream and 113 gate2 answers that moved now agree with
satassume: Hermite-Lindemann for the twelve functions and the inverse
ones (`Q.rational(sin(7))`, `Q.algebraic(acos(x))` given
`Q.algebraic(x) & Q.nonzero(x - 1)`, `Q.rational(cot(x))` given
`Q.rational(x)` with `cot(0) = zoo`), `cosh x >= 1` and the reciprocals
never zero (`Q.zero(sech(x))` given `Q.complex(x)`), `sin`, `cos` of a
real real, the signs of `atan`, `asin`, `acos`, `acot` on the real axis,
and `sin(2) > 0`. Still "less": `cosh`, `coth` at `oo` (6 stream queries
under `Q.extended_nonnegative(x)`, `Q.ge(x, 0)`, ...: an infinite
argument is free, no row of satassume's table gives `cosh(oo)`), `sqrt`
(`Q.algebraic(sqrt(sin(7)))`, step 5), and `acot` of an imaginary
argument (gate2 2172, not encoded).

No check hit the 10 s backstop on either stream. Wall times (6 jobs,
shared machine, load average 4 to 7): stream 112 s, gate2 17 s; the
summed query times 669 s and 97 s, against 794 s and 136 s for the
`exp`/`log` step's run (load average 7 to 12), so the step costs no
measurable time on these streams. A first version encoded `tan = sin/cos`
as `t*cos = sin` with a complex denominator; it took 10 s on gate2 2005
(`Q.algebraic(tan(x))` given `Q.algebraic(x)`, None either way) and was
replaced by the real denominator `|cos z|**2`, 0.3 s alone. Probes with a
non-real argument of `tan` (`Q.algebraic(tan(x))` given `Q.complex(x)`)
still can take seconds, depending on what the z3 context saw before:
nonlinear model search, the answer None either way.

## Speed

z3assume is about 70 to 80 times slower than satassume. Measured with
`bench-container` on one Cortex-A720 core (BENCH_CPU=10, 2.5 GHz), Python
3.13, z3-solver 5.3.1, one process per run, three interleaved rounds after
a warmup (spread under 2%), 23 Oct 2026, z3assume 7ce67e8 (this PR's tools,
encoding as on main) and satassume 9bafaa5:

| stream | queries | satassume | z3assume | ratio |
|---|---|---|---|---|
| every 8th query of the refine stream | 2,029 | 1.08 s | 75.8 s | 70x |
| gate2 | 2,863 | 0.92 s | 72.8 s | 79x |

Per query z3assume takes 20 ms at the median, 86 ms at p90, 405 ms at p99
and 0.89 s at most on the stream sample (gate2: 12, 49, 197 ms, 0.80 s);
satassume about 0.5 ms. Each query is two fresh z3 checks. Both tools
answer a repeated `(prop, assum)` pair from a memo (z3assume's tool from
its own per-worker memo), so repeats cost little on both sides. No check
hit the 10 s backstop; on the full stream 195 checks (in 194 queries) came back `unknown`
from the rlimit or from z3's incompleteness (the answer is then None).
The setup is in `~/dev/z3assume-bench/` on Tilo's machine.
