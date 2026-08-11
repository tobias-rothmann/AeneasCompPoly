/-
The **optimized-variant layer**: home of the `Foo.opt` definitions and their
`Foo.opt_eq_spec` lemmas produced by the optimization loop (`lean-opt` and the
`opt-*` strategy skills; the loop itself is `perf-loop`).

Every definition here is a rewrite of a CompPoly definition `Foo`, written in
the trivially-translatable subset (the `lean-to-rust` skill's conventions), and
ships with its pure-Lean equivalence lemma

    theorem Foo.opt_eq_spec : ∀ …, Foo.opt … = Foo …

proved against the *pinned* CompPoly (`lake-manifest.json`).  The lemma is the
opt-contract: a variant without its lemma never lands here, and the Rust side
never mirrors an unlemma'd variant.  `Check.lean` §15 prints the axioms of
every lemma in this file — `sorryAx` appearing there is a landing violation,
not a style issue.

Names extend the original: the variant of `CPolynomial.Raw.mul` is declared
`CPolynomial.Raw.mul.opt`, so def, lemma, and reference stay one grep apart.
This module imports only CompPoly, never `Generated`/aeneas: the variants are
meaningful without extraction, and the equivalence proofs import this module,
not the other way around.

Upstream-first rule (owned by the `lean-opt` skill): before adding a variant
here, check whether the pinned CompPoly already ships one with its lemma
(`eval₂Horner` + `eval₂Horner_eq_eval₂` is the exemplar); if it does, the Rust
mirrors upstream directly and nothing lands in this file.
-/

-- CompPoly modules the variants below rewrite, plus the `toPoly` bridge their
-- proofs go through (`Raw.toPoly_mul`, `Raw.coeff_toPoly`).  The one Mathlib
-- import is a tactic: `noncomm_ring` discharges the ring algebra of the
-- Karatsuba identity, which has to hold in a *non*-commutative ring.
import CompPoly.Univariate.Raw.Ops
import CompPoly.Univariate.Raw.Proofs
import CompPoly.Univariate.ToPoly.Equiv
import Mathlib.Tactic.NoncommRing

namespace CompPoly.CPolynomial.Raw

variable {R : Type*}

/-! ## `CPolynomial.Raw.mul` — Karatsuba (`opt-algo-swap`)

`mul p q = (mulRaw p q).trim` is the `np · nq` schoolbook convolution
(`CompPoly/Univariate/Raw/Ops.lean:105,113`).  This variant splits both
operands at `X^m` and buys the middle product with one extra addition:

    p = p₀ + X^m·p₁,  q = q₀ + X^m·q₁
    p·q = p₀q₀ + X^m·((p₀+p₁)(q₀+q₁) − p₀q₀ − p₁q₁) + X^2m·p₁q₁

three half-size products instead of four.  Recursion stops at
`karatsubaCutoff`, below which `conv` — the fused presized convolution that the
Rust champion already implements — runs the schoolbook product.  Multiplication
count, the fitness proxy of the brief (an `Ext4` mul costs ~14 ns against ~4
wrapped `u64` adds): at `n = 64`, cutoff 32, `3 · 32² = 3072` versus `4096`
(−25%); at `n = 256`, `27 · 32² = 27 648` versus `65 536` (−58%).

The subtraction is why this asks `Ring R` where `mul` asks `Semiring R` — the
contract's pre-approved strengthening; `LawfulBEq R` is proof-side only, and
`F = Hachi.Ext4` is a field, so it satisfies both.  Commutativity is *not*
needed: `X` is central in `R[X]`, which is all the identity above uses.
-/

namespace mul.opt

/-- Size below which `karatsuba` falls back to the schoolbook `conv`.

  32 keeps the base case at `32² = 1024` multiplications, the size at which the
  fused convolution's linear overheads (one presized allocation, one trim scan)
  are already amortised, and is the value the accompanying candidate note
  quantifies. -/
def karatsubaCutoff : Nat := 32

/-- The coefficients of `p` below `X^m`, i.e. `p mod X^m` (untrimmed).

  Clamping is Lean's: `m ≥ p.size` returns all of `p`, which is what makes the
  splitting identity hold with no side condition on `m`. -/
def lowPart (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.extract 0 m

/-- The coefficients of `p` from `X^m` up, shifted down by `m`, i.e.
`p div X^m` (untrimmed).  Empty when `m ≥ p.size`. -/
def highPart (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.extract m p.size

/-- One row of the fused convolution: `out[off + j] += a * q[j]` for the `j`
  from `j` up.  The accumulator is written in place; `out` is presized by
  `conv`, so every write is in bounds (`convRow_getD` carries the bound). -/
def convRow [Semiring R] (a : R) (q : CPolynomial.Raw R) (off : Nat) (j : Nat)
    (out : Array R) : Array R :=
  if h : j < q.size then
    convRow a q off (j + 1) (out.setIfInBounds (off + j) (out.getD (off + j) 0 + a * q[j]))
  else
    out
  termination_by q.size - j
  decreasing_by omega

/-- The rows of the fused convolution: one `convRow` per coefficient of `p`. -/
def convOuter [Semiring R] (p q : CPolynomial.Raw R) (i : Nat) (out : Array R) : Array R :=
  if h : i < p.size then
    convOuter p q (i + 1) (convRow p[i] q i 0 out)
  else
    out
  termination_by p.size - i
  decreasing_by omega

/-- Schoolbook multiplication as one fused convolution into a presized buffer:
  `out[i+j] += p[i]*q[j]` into `np + nq - 1` zeros, no per-row allocation and
  no per-row trim.  This is the shape the Rust champion already has
  (`cpoly/src/univariate.rs`), and it is the base case of `karatsuba`.

  The result is untrimmed: `mul.opt` trims once, at the top. -/
def conv [Semiring R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let np := p.size
  let nq := q.size
  if np = 0 then mk #[]
  else if nq = 0 then mk #[]
  else mk (convOuter p q 0 (Array.replicate (np + nq - 1) 0))

/-- Karatsuba multiplication, untrimmed.

  `n` is the *working width* — the size the operands are known to fit in.  It
  drives the split point and the recursion, and it is what the termination
  measure decreases; correctness does not depend on it (the splitting identity
  holds for every `m`), which is why `toPoly_karatsuba` needs no hypothesis
  relating `n` to `p.size`, `q.size`.

  What `n` buys is the cost argument, which is *not* part of the proof:
  `mul.opt` starts it at `max p.size q.size`, and each recursive call keeps its
  operands inside its own budget (`lowPart` yields at most `m`, `highPart` at
  most `n - m`, `addRaw` the larger of the two, and `m ≤ n - m`), so the base
  case runs on operands of at most `karatsubaCutoff`. -/
def karatsuba [Ring R] (n : Nat) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if _h : n ≤ karatsubaCutoff then
    conv p q
  else
    let m := n / 2
    let p0 := lowPart m p
    let p1 := highPart m p
    let q0 := lowPart m q
    let q1 := highPart m q
    let z0 := karatsuba m p0 q0
    let z2 := karatsuba (n - m) p1 q1
    let z1 := karatsuba (n - m) (addRaw p0 p1) (addRaw q0 q1)
    let mid := addRaw (addRaw z1 (-z0)) (-z2)
    addRaw (addRaw z0 (mulPowX m mid)) (mulPowX (m + m) z2)
  termination_by n
  decreasing_by
    all_goals simp only [karatsubaCutoff, Nat.not_le] at _h
    all_goals omega

/-! ### Coefficients of the pieces

Everything below is stated at coefficient level or through `toPoly`, never as
array equality of intermediates: the intermediates are untrimmed, so they are
*not* canonical — two of them can agree as polynomials and differ as arrays by
trailing zeros. -/

section Semiring

variable [Semiring R]

lemma coeff_eq_zero_of_size_le {p : CPolynomial.Raw R} {i : Nat} (h : p.size ≤ i) :
    p.coeff i = 0 := by
  simp [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

lemma coeff_lowPart (m : Nat) (p : CPolynomial.Raw R) (k : Nat) :
    (lowPart m p).coeff k = if k < m then p.coeff k else 0 := by
  unfold lowPart
  by_cases hm : k < m
  · by_cases hs : k < p.size
    · simp [coeff, Array.getD_eq_getD_getElem?, hm, hs]
    · simp [coeff, Array.getD_eq_getD_getElem?, hm, hs]
  · simp [coeff, Array.getD_eq_getD_getElem?, hm]

lemma coeff_highPart (m : Nat) (p : CPolynomial.Raw R) (k : Nat) :
    (highPart m p).coeff k = p.coeff (m + k) := by
  unfold highPart
  by_cases h : k < p.size - m
  · have hlt : m + k < p.size := by omega
    simp [coeff, Array.getD_eq_getD_getElem?, h, hlt]
  · have h1 : p.size ≤ m + k := by omega
    rw [coeff_eq_zero_of_size_le h1]
    simp [coeff, Array.getD_eq_getD_getElem?, h]

/-- The splitting identity, in `Polynomial R`: `p = p₀ + p₁ · X^m`.  Holds for
every `m`, including `m ≥ p.size` (then `p₁ = 0`). -/
lemma toPoly_split (m : Nat) (p : CPolynomial.Raw R) :
    p.toPoly = (lowPart m p).toPoly + (highPart m p).toPoly * Polynomial.X ^ m := by
  ext k
  simp only [coeff_toPoly, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', coeff_lowPart,
    coeff_highPart]
  by_cases h : k < m
  · rw [if_pos h, if_neg (by omega), _root_.add_zero]
  · rw [if_neg h, if_pos (by omega), _root_.zero_add, show m + (k - m) = k from by omega]

/-! ### The fused convolution computes the convolution -/

@[simp] lemma convRow_size (a : R) (q : CPolynomial.Raw R) (off j : Nat) (out : Array R) :
    (convRow a q off j out).size = out.size := by
  fun_induction convRow with
  | case1 j out h ih => rw [ih]; exact Array.size_setIfInBounds
  | case2 => rfl

/-- A row adds `a * q[k - off]` at output index `k`, and changes nothing else.
  The hypothesis `off + q.size ≤ out.size` is what rules out a dropped write
  (`setIfInBounds` is silent out of bounds); `conv` presizes so that it holds. -/
lemma convRow_getD (a : R) (q : CPolynomial.Raw R) (off j : Nat) (out : Array R) (k : Nat) :
    off + q.size ≤ out.size →
      (convRow a q off j out).getD k 0
        = out.getD k 0 + (if off + j ≤ k ∧ k < off + q.size then a * q.coeff (k - off) else 0) := by
  fun_induction convRow with
  | case1 j out h ih =>
    intro hout
    rw [ih (by simpa using hout)]
    have hin : off + j < out.size := by omega
    have hset : ∀ (v : R) (l : Nat), (out.setIfInBounds (off + j) v).getD l 0
        = if l = off + j then v else out.getD l 0 := by
      intro v l
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      by_cases hl : l = off + j
      · subst hl; simp [hin]
      · have hl' : ¬ (off + j = l) := fun hh => hl hh.symm
        simp [hl, hl']
    rw [hset]
    have hq : q.coeff j = q[j] := by simp [coeff, h]
    by_cases hk : k = off + j
    · subst hk
      rw [if_pos rfl, if_neg (by omega), if_pos (And.intro (by omega) (by omega)),
        show off + j - off = j from by omega, hq, _root_.add_zero]
    · rw [if_neg hk]
      congr 1
      by_cases hle : off + j ≤ k
      · have h1 : off + (j + 1) ≤ k := by omega
        simp [h1, hle]
      · have h1 : ¬ (off + (j + 1) ≤ k) := by omega
        simp [h1, hle]
  | case2 j out h =>
    intro _
    rw [if_neg (by omega), _root_.add_zero]

/-- After the rows `i …` have run, output index `k` carries the partial
  convolution over those rows. -/
lemma convOuter_getD (p q : CPolynomial.Raw R) (i : Nat) (out : Array R) (k : Nat) :
    p.size + q.size ≤ out.size + 1 → 0 < q.size →
      (convOuter p q i out).getD k 0
        = out.getD k 0 + ∑ i' ∈ Finset.Ico i p.size,
            (if i' ≤ k ∧ k < i' + q.size then p.coeff i' * q.coeff (k - i') else 0) := by
  fun_induction convOuter with
  | case1 i out h ih =>
    intro hout hq
    rw [ih (by simpa using hout) hq,
      convRow_getD p[i] q i 0 out k (by omega),
      Finset.sum_eq_sum_Ico_succ_bot h]
    have hp : p.coeff i = p[i] := by simp [coeff, h]
    simp only [Nat.add_zero, hp]
    rw [_root_.add_assoc]
  | case2 i out h =>
    intro _ _
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, _root_.add_zero]

end Semiring

section Lawful

variable [Semiring R] [BEq R] [LawfulBEq R]

/-- The base case agrees with the spec coefficient-wise (both degenerate
  branches included: an empty operand makes the reference sum empty too). -/
lemma conv_coeff (p q : CPolynomial.Raw R) (k : Nat) :
    (conv p q).coeff k = (p * q).coeff k := by
  rw [mul_coeff_range_size]
  by_cases hp : p.size = 0
  · rw [show conv p q = mk #[] from by simp [conv, hp]]
    simp [hp, coeff]
  by_cases hq : q.size = 0
  · rw [show conv p q = mk #[] from by simp [conv, hp, hq]]
    have hz : ∀ i, q.coeff i = 0 := fun i => coeff_eq_zero_of_size_le (by omega)
    simp [coeff, hz]
  · have hconv : conv p q = mk (convOuter p q 0 (Array.replicate (p.size + q.size - 1) 0)) := by
      simp [conv, hp, hq]
    have hzero : ∀ l, (Array.replicate (p.size + q.size - 1) (0 : R)).getD l 0 = 0 := by
      intro l
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [hconv]
    show (convOuter p q 0 (Array.replicate (p.size + q.size - 1) 0)).getD k 0 = _
    rw [convOuter_getD p q 0 _ k (by simp; omega) (by omega), hzero, _root_.zero_add,
      ← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h1 : k < i
    · have h2 : ¬ (i ≤ k ∧ k < i + q.size) := by omega
      simp [h1, h2]
    · by_cases h2 : k < i + q.size
      · simp [h1, h2, Nat.not_lt.mp h1]
      · have hz : q.coeff (k - i) = 0 := coeff_eq_zero_of_size_le (by omega)
        simp [h1, h2, hz]

lemma toPoly_conv (p q : CPolynomial.Raw R) :
    (conv p q).toPoly = p.toPoly * q.toPoly := by
  ext k
  calc (conv p q).toPoly.coeff k = (conv p q).coeff k := coeff_toPoly
    _ = (p * q).coeff k := conv_coeff p q k
    _ = (p * q).toPoly.coeff k := coeff_toPoly.symm
    _ = (p.toPoly * q.toPoly).coeff k := by rw [toPoly_mul]

lemma toPoly_mulPowX (i : Nat) (p : CPolynomial.Raw R) :
    (p.mulPowX i).toPoly = p.toPoly * Polynomial.X ^ i := by
  ext k
  simp only [coeff_toPoly, coeff_mulPowX, Polynomial.coeff_mul_X_pow']
  split_ifs with h1 h2 <;> first | rfl | omega

end Lawful

/-- The Karatsuba identity itself, in any ring in which `x` is central — which
  is the case for `x = X^m` in `R[X]` for every `R`.  Commutativity of the
  coefficient ring is never used: the three products keep their operand order. -/
lemma karatsuba_identity {A : Type*} [Ring A] (a0 a1 b0 b1 x : A)
    (hx : ∀ c : A, x * c = c * x) :
    a0 * b0 + ((a0 + a1) * (b0 + b1) + -(a0 * b0) + -(a1 * b1)) * x + a1 * b1 * (x * x)
      = (a0 + a1 * x) * (b0 + b1 * x) := by
  have h1 : a1 * x * b0 = a1 * b0 * x := by
    rw [_root_.mul_assoc, hx b0, _root_.mul_assoc]
  have h2 : a1 * x * (b1 * x) = a1 * b1 * (x * x) := by
    rw [_root_.mul_assoc a1 x (b1 * x), ← _root_.mul_assoc x b1 x, hx b1,
      _root_.mul_assoc b1 x x, ← _root_.mul_assoc a1 b1 (x * x)]
  have key : (a0 + a1 * x) * (b0 + b1 * x)
      = a0 * b0 + (a0 * b1 + a1 * b0) * x + a1 * b1 * (x * x) := by
    calc (a0 + a1 * x) * (b0 + b1 * x)
        = a0 * b0 + a0 * (b1 * x) + (a1 * x * b0 + a1 * x * (b1 * x)) := by noncomm_ring
      _ = a0 * b0 + a0 * b1 * x + (a1 * b0 * x + a1 * b1 * (x * x)) := by
            rw [h1, h2, ← _root_.mul_assoc a0 b1 x]
      _ = a0 * b0 + (a0 * b1 + a1 * b0) * x + a1 * b1 * (x * x) := by noncomm_ring
  rw [key]
  noncomm_ring

section Main

variable [Ring R] [BEq R] [LawfulBEq R]

/-- Karatsuba computes the product, for every working width. -/
lemma toPoly_karatsuba : ∀ (n : Nat) (p q : CPolynomial.Raw R),
    (karatsuba n p q).toPoly = p.toPoly * q.toPoly := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p q
  rw [karatsuba]
  by_cases hn : n ≤ karatsubaCutoff
  · rw [dif_pos hn]
    exact toPoly_conv p q
  · rw [dif_neg hn]
    rw [show karatsubaCutoff = 32 from rfl] at hn
    have h1 : n / 2 < n := by omega
    have h2 : n - n / 2 < n := by omega
    simp only [toPoly_addRaw, toPoly_neg, toPoly_mulPowX, ih _ h1, ih _ h2]
    rw [toPoly_split (n / 2) p, toPoly_split (n / 2) q, _root_.pow_add]
    exact karatsuba_identity _ _ _ _ (Polynomial.X ^ (n / 2)) (fun c => Polynomial.X_pow_mul)

end Main

end mul.opt

/-- Karatsuba multiplication: the `opt-algo-swap` variant of
`CPolynomial.Raw.mul`, trimmed exactly once, at the end, like the spec. -/
def mul.opt [Ring R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (mul.opt.karatsuba (max p.size q.size) p q).trim

/-- The opt-contract lemma: the Karatsuba variant is the spec, on every input.

  No value-level hypothesis — the degenerate shapes (empty operands, odd
  lengths, a split point past the end of an operand) are handled inside the
  definition.  `Ring R` buys the subtraction in the middle term and `LawfulBEq
  R` the canonicalisation lemmas; both hold for `F = Hachi.Ext4`. -/
theorem mul.opt_eq_spec [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) :
    mul.opt p q = mul p q := by
  show (mul.opt.karatsuba (max p.size q.size) p q).trim = (mulRaw p q).trim
  refine Trim.eq_of_equiv ?_
  intro k
  calc (mul.opt.karatsuba (max p.size q.size) p q).coeff k
      = (mul.opt.karatsuba (max p.size q.size) p q).toPoly.coeff k := coeff_toPoly.symm
    _ = (p.toPoly * q.toPoly).coeff k := by rw [mul.opt.toPoly_karatsuba]
    _ = (p * q).toPoly.coeff k := by rw [toPoly_mul]
    _ = (p * q).coeff k := coeff_toPoly
    _ = (mulRaw p q).coeff k := Trim.coeff_eq_coeff (mulRaw p q) k

end CompPoly.CPolynomial.Raw
