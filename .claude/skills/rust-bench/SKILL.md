---
name: rust-bench
description: Adding a criterion benchmark for a newly translated CompPoly operation in cpoly/src — freezing its first translation into the genesis baseline, writing a case that measures the operation and nothing else, and proving that it does with adversarial review agents before any number is trusted
---

# Benchmarking a New Translation

Everything benchmark-related lives in `cpoly/benches/`: the cases, `support/`,
the frozen `genesis/` crate, and `harness.py`. Read this **before** adding a
case, and read `support/mod.rs` — its module doc is the design, this file is the
procedure.

Criterion wall-clock time is the *only* fitness function of this project. Every
accept/reject decision the optimization loop makes is downstream of a number
produced here. A benchmark that measures the wrong thing does not produce a
wrong decision occasionally — it produces a confidently wrong one, repeatedly,
in the direction that looks like success.

## The one rule: a benchmark is guilty until proven innocent

A bench that compiles, runs, and prints a plausible microsecond figure has
demonstrated nothing. All three of the ways it fails are silent:

* it measures **less** than it claims (the optimizer deleted work nobody looked at),
* it measures **more** than it claims (setup, cloning, or a second operation leaked
  into the timed region),
* it measures **something else entirely** (the wrong overload, a degenerate input
  that skips the loop).

Each of those makes a number go *down*, which is the direction an autonomous
loop reads as a win. So the bench does not exist until it has survived §4.

## What the harness already does for you

Do not re-solve these; do not work around them.

| Guarantee | Mechanism |
|---|---|
| The timed body and the verified body are the same code | one body per case, `support::run*` either times it or digests it |
| `now` and `genesis` cannot drift apart | one `define_cases!` macro, instantiated against `cpoly` and `cpoly_genesis` |
| An "optimization" that changes an answer fails loudly | `case!` digests both variants and `assert_eq!`s them **before** timing |
| The baseline is never a stale remembered number | `genesis/` is re-measured every run, in the same session |
| The frozen baseline cannot be quietly edited | `make bench-check` verifies every frozen item against its git blob |
| The two crates get symmetric codegen | `lto = "fat"`; thin LTO measured identical source 28% apart |
| Background load cannot inflate a verdict | the reported time is the mean of the 3 fastest *settled* samples, not the slope |
| A/B bias is known, not assumed | `_control/*` runs identical code as both variants, one per bench binary |
| A change under the harness's own error is not a result | a flat threshold: the worst control, floored at 5% (a target — measured noise reaches 6%) |
| A run that fails its own self-test is thrown away | A/B bias > 10% → every verdict marked unusable, exit non-zero |
| Filtered-out cases cannot republish stale rows | `make run-bench` stamps the clock, `report --since` cuts on it |
| A number that survives none of this is not published | only `vs genesis` is a comparison; absolute times are not |

## 1 · Freeze the first translation

**Before** the bench, and in lockstep with the source. `benches/genesis/` is the
starting point every future measurement is scored against; it is append-only and
must contain each operation *as first written*.

```bash
git add cpoly/src/<module>.rs && git commit      # genesis names a commit, so src goes first
# copy the new items VERBATIM into cpoly/benches/genesis/src/<module>.rs
make bench-stamp                                 # derives `@genesis <sha> <date>` from git
git add cpoly/benches/genesis && git commit      # or --amend to fold into one
```

`bench-stamp` finds the earliest commit whose `cpoly/src/<module>.rs` contains
the item's text verbatim, so it cannot be talked into a wrong sha — but it also
cannot stamp text that is not in any commit, which is why the source is
committed first.

**Copy, do not retype, and do not tidy.** The check is byte-exact. A reflowed
comment fails it, and rightly: the point is a guarantee that the baseline is the
original, and "I only changed a comment" is not a guarantee.

### If you discover a missing baseline late

`make bench-check` lists items in `cpoly/src` with no frozen counterpart. If one
has *already been optimized* since it was written, **do not copy today's code** —
that would freeze the optimized version and silently report all its gains as
zero. Recover the original:

```bash
git log --oneline --reverse -- cpoly/src/<module>.rs      # find where it first appeared
git show <sha>:cpoly/src/<module>.rs                      # take the ORIGINAL text
```

Paste that, then `make bench-stamp`. The stamper will confirm the sha by finding
the same text; if it names a later commit than you expected, you copied the
wrong version.

## 2 · Write the case

One body, in the `define_cases!` macro, taking `Mode` and the size parameter.
Pick the runner by how the operation treats its input:

| Operation shape | Runner | Why |
|---|---|---|
| returns a value or a fresh `Vec` | `support::run` | `Bencher::iter` black-boxes the result; allocation and drop are the caller's real cost |
| per-element, result into a buffer | `support::run_into` | a per-element accumulator would cost as much as a field op |
| **consumes** or mutates its input | `support::run_batched` | `iter_batched` builds inputs and drops outputs *outside* the timed region (verified in criterion 0.7's source, and 0.8's) |

Using `run` where `run_batched` is needed is the single most common way to turn a
transform benchmark into a `Vec::clone` benchmark. `trim`, `to_evals`,
`to_coeffs` and `from_coeffs` all take `self`/`Vec` by value.

Then, non-negotiably:

* **Every input through `black_box`**, at every use inside the body. An input the
  optimizer can see through is an input it can fold the whole loop against.
* **Different corpus tags per operand.** `words(0x01, n)` twice is `x * x`, and
  squaring is not what `mul` is for.
* **Non-degenerate inputs, deliberately chosen.** The corpus is non-zero for a
  reason. Ask what input would make the loop exit early and make sure yours is
  not it: `trim` needs real trailing zeros (a random polynomial exits after one
  comparison); `from_coeffs` needs a short list or the `resize` is a no-op;
  `Fp::new` needs *unreduced* words or the `%` is free; a multilinear point must
  be off the hypercube or `lagrange_basis` collapses.
* **Sizes justified in a comment.** One size unless the *shape* of the algorithm
  is what an optimization would change — an exponent cannot be seen at a single
  point.
* **A `// @covers <path>` marker** on the `bench_case!` line, with the exact item
  path `harness.py` prints. `make bench-check` fails on a path that names no
  item, so a typo cannot silently drop the coverage claim.

If a mirrored item genuinely should not be benched, add it to
`benches/exclusions.toml` **with a reason that can be checked by reading it**.
The bar is "a criterion run would measure the harness, not the item" — a type, a
`const`, a single shift. It is not "this is not on the hot path".

## 3 · Make it run

```bash
make bench-check                                   # genesis intact + coverage complete
make run-bench BENCH='<module>/<case>'             # one case, still full rigour
```

The digest assertion in `case!` runs for **every** case in the file even under a
`BENCH=` filter, so a semantic disagreement between `cpoly` and the baseline
surfaces on the first run regardless of what you filtered to.

What a filtered run does **not** validate: the `_control/*` self-test cases
do not match the filter, so the report prints that `vs genesis` is
unvalidated — the digest oracle stands, but the timing delta carries no
error bar. An accept/reject decision takes a full `make run-bench`, never a
filtered one.

## 4 · Adversarial review — mandatory, before the case is trusted

Do **not** review your own bench by rereading it. You wrote it believing it was
right; rereading mostly re-confirms that. Spawn agents whose job is to *refute*
it, give each a different lens, and require evidence rather than opinion.

The claim under attack, stated per case:

> `<case>` measures the cost of `<item>` at size `<n>`, and nothing else.

Fan the lenses out with the Workflow tool — one agent per lens per case, verify
stage adversarial:

```js
export const meta = {
  name: 'bench-audit',
  description: 'Refute the claim that each new bench case measures what it says',
  phases: [{ title: 'Refute' }, { title: 'Adjudicate' }],
}
const LENSES = [
  { key: 'dead-work',     prompt: `...` },
  { key: 'contamination', prompt: `...` },
  { key: 'wrong-thing',   prompt: `...` },
  { key: 'fairness',      prompt: `...` },
]
const findings = await pipeline(
  CASES.flatMap(c => LENSES.map(l => ({ c, l }))),
  ({ c, l }) => agent(l.prompt.replace('$CASE', c),
                      { label: `${l.key}:${c}`, phase: 'Refute', schema: VERDICT }),
  (v, { c, l }) => v.refuted
      ? agent(`A reviewer claims ${c} is broken: ${v.evidence}. Try to show they are
               WRONG. Run the commands yourself. Default to agreeing only on evidence.`,
              { label: `adjudicate:${l.key}:${c}`, phase: 'Adjudicate', schema: VERDICT })
      : null,
)
```

Instruct every agent: **run commands, quote numbers**. "Looks fine" is not a
verdict; neither is "this could theoretically be optimized away".

### Lens A · dead work — is any of it being deleted?

* **Scaling.** Temporarily add a second size and check the ratio against the
  documented complexity: `O(n)` doubles, `O(n²)` quadruples, a layer over `2^vars`
  doubles per var. A flat curve where the complexity says otherwise means the
  work is gone or the input is degenerate.
* **First-principles floor.** Count the field operations the case must perform
  and divide by a plausible per-op cost (`field/ext4_mul` on this M2 is ≈14 ns
  per `Ext4` multiply, ≈1 ns per `Fp` multiply). A measured time *below* the
  floor is proof, not suspicion.
* **Ablation.** Delete the body and confirm the time collapses; swap an input for
  a constant and confirm the time moves. If neither changes anything, nothing was
  being measured.

### Lens B · contamination — is anything extra being measured?

* Is corpus construction, `clone`, or buffer allocation inside the closure rather
  than above it?
* Does a `run_batched` case do its cloning in `setup`, or has it leaked into the
  routine?
* Is the digest computed inside the timed region? It must not be — that is the
  entire reason `Mode` exists.
* Does the body call anything besides the item under test? Compare against the
  neighbouring case that shares most of the work: `poly_eval` minus
  `monomial_basis` should be about `dot`. If it is not, one of the three is wrong.

### Lens C · wrong thing — right function, right inputs?

* Does the `@covers` path name the function the body actually calls? **The two
  readings are the trap**: `MultilinearPoly::eval` dots against a monomial basis,
  `MultilinearEvals::eval` against a Lagrange one; they wrap the same bytes and
  swapping them still compiles.
* Is the input degenerate in a way that skips the work (see §2)?
* Do the two operands of a binary operation come from different tags?
* Is the size the one the comment claims, and is that size representative?

### Lens D · fairness — is the A/B honest?

* Are both variants generated from one `define_cases!` body, or has someone
  hand-written a second copy?
* If a genesis adapter exists (because the API diverged), does it do work the
  measured function should be doing? An adapter that pre-allocates for genesis is
  a rigged race.
* Did the `_control/*` rows come out near 0% in the run being used as evidence?
  Read the harness self-test block before believing any margin. It is the only
  error bar there is — everything is compared within one run, because comparing
  across runs was measured to be worse than useless (75% and 373% drift on frozen
  code) and was removed.
* Is the reported change larger than the printed threshold? A "win" at or below
  the A/B bias is not a win.
* Is the margin an *absolute* time or a `vs genesis` delta? Only the delta is
  trustworthy — see "Trusting an absolute time" below.
* Does the new case make `_control/*` worse? A case that changes the binary's
  layout can move the controls; if the self-test degrades when the case is added,
  the case is the problem.

### Adjudicating

Any **confirmed** finding blocks the case; fix and re-run the audit. A refutation
that the adjudicator overturns is recorded in the case's comment so nobody
re-litigates it. If the lenses disagree and no command settles it, that is itself
a defect: the bench is not legible enough to be trusted, so make it simpler.

## 5 · Run it for real

```bash
make run-bench                # the only mode; ~18 min
```

The harness stores nothing between runs and reads nothing from a previous one;
every comparison is made inside a single run. If a number needs keeping, take it
from `JSON=<path>` and keep it somewhere with a reason attached.

**Read the self-test block before the table.** If the A/B bias is near the size
of the effect you are looking at, you have not measured the effect. Close what
else is running and measure again — nothing inside the harness will shrink it.

## Failure modes with teeth

**`cargo bench` handing criterion's flags to libtest.** `--benches` selects every
target with `bench = true`, which defaults true on the lib *and* on every
auto-discovered integration test. `cpoly/Cargo.toml` pins `autotests = false`,
`bench = false` on the lib, and declares each test — leave that alone.

**Thin LTO making identical code 28% apart.** The one that nearly shipped. With
`lto = "thin"` the two crates are optimized in separate modules, and LLVM made
different vectorization choices for the same `Fp::sub`: **+28% and +29% on two
consecutive rounds**, present in the *minimum* per-iteration time, so not noise.
`lto = "fat"` merges everything before optimizing and the same case read +0.8%.
This is why `_control/*` exists and why the profile comment forbids reverting it
for build times. Generalise the lesson: *any* build setting that lets the two
crates be optimized differently is a correctness bug in the fitness function.

**Believing an estimator that describes the load.** Criterion's headline
`[lo mid hi]` is the regression **slope**; it and the mean describe the centre of
the sample distribution, which on a busy machine is mostly a description of the
other processes. A run at load average 7.75 was inflated 50–180% with narrow,
disjoint, confident intervals. Contention only ever makes code look slower, so
the report uses the 10th percentile of per-iteration times from `sample.json`.
The table therefore reads *lower* than the `cargo bench` output above it; that is
expected, not a bug.

**Measurement order looking like a speedup.** Criterion runs `now` to completion
before starting `genesis`, so a warming CPU biases the second one. That is part
of what `_control/*` measures. Never compare a margin against zero; compare it
against the printed threshold.

**Trusting an absolute time.** Measured here on byte-identical code, in a run
whose control read 0.03%: `univariate/add_untrimmed` reported 24.5 µs and
`multilinear/add_pointwise` 95.5 µs — 7–9× their true cost — printed next to
`univariate/add` (3.4 µs) and `multilinear/poly_add` (12.0 µs), which strictly
*contain* them. Same binary, same callee (checked by disassembly); correct on a
filtered rerun. It is machine/allocator state, it persists across whole
measurements, and no amount of sampling sees it — all 100 samples sat within 6%
of the wrong value. It also survived two consecutive repeats, which is why the
old `ROUNDS=n` median made it *worse*: the median selected the corrupted rounds.
Only `vs genesis` survives, because the artefact lands on both variants at once.
Never reason across rows, and never quote an absolute time as a result.

**Freezing an already-optimized function as "genesis".** Covered in §1. This is
the failure that cannot be detected later from the numbers alone — every gain
before the freeze silently becomes zero.

**Adding a bench file without declaring it.** `autobenches = false`, so a new
`benches/foo.rs` is simply not built until it has a `[[bench]]` entry in
`cpoly/Cargo.toml`. Silence, not an error.

**A dev-dependency's MSRV breaking `cargo test`.** Cargo resolves the whole
dependency graph before it builds anything, so a dev-dependency whose
`rust-version` exceeds the active toolchain fails `cargo test` even though the
tests never link it. criterion 0.8 declares 1.86 and did exactly that here; the
pin is **0.7** (declares 1.80) for that reason and no other. Before bumping it,
check `rust-version` against the oldest toolchain anyone runs `cargo test` with —
not against what the benchmarks need.

## Invariants to keep green

* `make bench-check` passes — genesis verified against git, coverage complete.
* `cargo clippy --all-targets` clean under `pedantic`, benches included.
* `make extract` still reports `unchanged` — dev-dependencies must never reach
  `lean/Generated.lean`. (`cargo build --lib` does not build them; this is
  checked, not assumed.)
* `_control/*` reads near 0%. If it does not, fix the harness or the machine —
  never the interpretation.
* No claim rests on an absolute time or on comparing two rows to each other.
* Every mirrored item is benched or excluded **by name, with a reason**.
* A new Makefile target is listed in `make help`, and in the right list. Under
  `Targets:` if someone who just cloned the repo would type it; under
  `Advanced targets:` if it exists so this loop can check or regenerate something
  mid-iteration — that is where `bench-check` and `bench-stamp` live, and where a
  new `bench-*` almost certainly belongs. One aligned line, ≤77 characters, and
  it must not promise more than the target delivers; the rest goes in the
  Makefile comment above the target. Leave it unlisted only if it is a
  prerequisite nobody invokes, like `bench-toolchain`.
* Nothing about a run is persisted by the harness. Do not add a store of past
  timings back without a consumer that can defend comparing across runs — the
  last one was removed for being unable to.
