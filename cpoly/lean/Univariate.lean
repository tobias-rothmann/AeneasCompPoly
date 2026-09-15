/-
The **univariate polynomial layer** of the equivalence between the
Aeneas-extracted Rust model (`cpoly.univariate.*`, see `Generated.lean`) and
CompPoly's reference univariate polynomials (`CompPoly.CPolynomial.Raw`, see
CompPoly/Univariate/Raw/Ops.lean).

The generated names carry the Rust module they come from, so `src/univariate.rs`
gives `cpoly.univariate.*`.  Operator impls are the exception: Aeneas mangles them
from the impl header, and for an `impl Trait for &T` the prefix it builds is *not*
module-qualified -- `impl Add<&Poly> for &Poly` becomes
`Poly.add`.  The field layer this
builds on is `Field.lean` (`src/field.rs`), and the multilinear sibling is
`Multilinear.lean` (`src/multilinear.rs`).

A `Vec Ext4` whose entries are all `Reduced` represents the
`CPolynomial.Raw Hachi.Ext4` obtained by mapping `toExt` over its coefficients
(`toRaw`); the multiplication helpers take `&[Ext4]`, whose twin is `toRawS`.
Each operation of `cpoly::univariate::UnivariatePoly` is shown to succeed, to
preserve the invariant, and to commute with the matching `CPolynomial.Raw`
operation: `constant`, `x`, `trim`, `eval`, `add_untrimmed`, and the `Add`, `Neg`,
`Sub`, `Mul<Ext4>` and `Mul` impls.

`Mul` is the deep one.  It is Karatsuba down to `KARATSUBA_CUTOFF = 16` over a
base case that accumulates the extension product in unreduced `u128` lanes and
reduces once per output coefficient, so its spec layer carries a `ℕ`-level lane
calculus (`lanePair`, `lanes`) with its overflow bound, a bridge for the
inlined `W = 2` (`toExt_mul_coeff`), and one spec per private helper —
`reduce_u128`, `conv_delayed`, `add_slices`, `mul_karatsuba` — each landing
directly on `CPolynomial.Raw.mul`.

One caveat: `mul_spec` needs the extra hypothesis
`v.val.length + w.val.length ≤ Usize.max`, because the generated code sizes its
accumulator with *checked* `Usize` additions.  See the docstring on `mul_spec`
for what those are and why the hypothesis is carried unchanged.

Specs are stated in Aeneas's triple form `m ⦃ r => post r ⦄` (see the header of
`Field.lean` for what that form means and how to compose it).
-/
import Field
import CompPoly.Univariate.Raw.Ops
import CompPoly.Univariate.Raw.Proofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial CompPoly.Extension

namespace CPolyEquiv

/-! ## Readable names for the operator impls

Aeneas builds the name of a trait impl from the impl header, and for an
`impl Trait for &T` the prefix it builds is `Shared<n><T>` — so
`impl Add<&UnivariatePoly> for &UnivariatePoly` comes out as
`cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add`.
That is unreadable in a statement, so each one gets an `abbrev` below.

An `abbrev` is `@[reducible]`, so a theorem stated about `Poly.add` *is* a theorem
about the extracted definition — this is an abbreviation, not a wrapper, and there
is nothing extra to trust.  `Check.lean` pins every alias to its generated name
with `rfl` so that a rename upstream cannot silently repoint one.  Each proof
opens by unfolding the alias and then the definition, which is also where a reader
can see which generated name is meant. -/

namespace Poly

/-- `impl Add<&UnivariatePoly> for &UnivariatePoly`. -/
abbrev add := cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add

/-- `impl Sub<&UnivariatePoly> for &UnivariatePoly`. -/
abbrev sub := cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithSubShared0UnivariatePolyUnivariatePoly.sub

/-- `impl Mul<&UnivariatePoly> for &UnivariatePoly`. -/
abbrev mul := cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul

/-! The multiplication helpers are free functions of `src/univariate.rs`, so
Aeneas does not mangle their names — but the loop names it derives from them
(`conv_delayed_loop0_loop0`, `mul_karatsuba_loop2`, …) say only *which* loop of
*which* function, never what the loop does.  Each gets an alias too, and each is
pinned in `Check.lean` §12 alongside the operator impls. -/

/-- `univariate::R64`, the residue of `2^64` used by `reduce_u128`. -/
abbrev r64 := cpoly.univariate.R64

/-- `univariate::KARATSUBA_CUTOFF`, the width at or below which `mul_karatsuba`
stops splitting. -/
abbrev karatsubaCutoff := cpoly.univariate.KARATSUBA_CUTOFF

/-- `univariate::reduce_u128`. -/
abbrev reduceU128 := cpoly.univariate.reduce_u128

/-- the lane loop of `conv_delayed`: the seven unreduced `u128` accumulators
for one output coefficient. -/
abbrev convDelayedLaneLoop := cpoly.univariate.conv_delayed_loop0_loop0

/-- the output loop of `conv_delayed`. -/
abbrev convDelayedLoop := cpoly.univariate.conv_delayed_loop0

/-- `univariate::conv_delayed`, the base case of the product. -/
abbrev convDelayed := cpoly.univariate.conv_delayed

/-- the loop of `add_slices`. -/
abbrev addSlicesLoop := cpoly.univariate.add_slices_loop

/-- `univariate::add_slices`. -/
abbrev addSlices := cpoly.univariate.add_slices

/-- `mul_karatsuba`'s in-place `z1 := zm - z0 - z2` loop. -/
abbrev karatsubaSubLoop := cpoly.univariate.mul_karatsuba_loop0

/-- `mul_karatsuba`'s `out[k] = z0[k]` loop. -/
abbrev karatsubaLowLoop := cpoly.univariate.mul_karatsuba_loop1

/-- `mul_karatsuba`'s `out[k + m] += z1[k]` loop. -/
abbrev karatsubaMidLoop := cpoly.univariate.mul_karatsuba_loop2

/-- `mul_karatsuba`'s `out[k + 2m] += z2[k]` loop. -/
abbrev karatsubaHighLoop := cpoly.univariate.mul_karatsuba_loop3

/-- `univariate::mul_karatsuba`, the untrimmed product. -/
abbrev karatsuba := cpoly.univariate.mul_karatsuba

/-- the loop of `Neg`. -/
abbrev negLoop := cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg_loop

/-- `impl Neg for &UnivariatePoly`. -/
abbrev neg := cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg

/-- the loop of `Mul<Ext4>`. -/
abbrev smulLoop := cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop

/-- `impl Mul<Ext4> for &UnivariatePoly`. -/
abbrev smul := cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul

end Poly

/-! ## The representation

Each statement below says: under the representation invariant, the generated
operation succeeds, preserves the invariant, and its `toRaw` equals the
CompPoly reference operation applied to the `toRaw` of the inputs. -/

/-- The reference `CPolynomial.Raw` represented by a `Vec Ext4`. -/
def toRaw (v : alloc.vec.Vec cpoly.field.Ext4) : CPolynomial.Raw F :=
  (v.val.map toExt).toArray

/-- The `k`-th coefficient of `toRaw v` is `toExt` of the `k`-th word (or `0`). -/
theorem toRaw_coeff (v : alloc.vec.Vec cpoly.field.Ext4) (k : ℕ) :
    (toRaw v).coeff k = (v.val.map toExt).getD k 0 := by
  unfold toRaw CPolynomial.Raw.coeff
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < v.val.length
  · simp [List.getElem?_eq_getElem h, dif_pos h]
  · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h), dif_neg h]

@[simp] theorem toRaw_size (v : alloc.vec.Vec cpoly.field.Ext4) :
    (toRaw v).size = v.val.length := by
  simp [toRaw]

/-- In-range coefficients of `toRaw v` are the `toExt`-images of the words. -/
theorem toRaw_coeff_of_lt (v : alloc.vec.Vec cpoly.field.Ext4) {k : ℕ} (hk : k < v.val.length) :
    (toRaw v).coeff k = toExt v.val[k] := by
  rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

/-- Out-of-range coefficients of `toRaw v` are zero. -/
theorem toRaw_coeff_of_ge (v : alloc.vec.Vec cpoly.field.Ext4) {k : ℕ} (hk : v.val.length ≤ k) :
    (toRaw v).coeff k = 0 := by
  rw [toRaw_coeff, List.getD_eq_default]; simpa using hk

/-! ### The same representation for a `&[Ext4]`

The three multiplication helpers (`conv_delayed`, `add_slices`, `mul_karatsuba`)
take slices rather than vectors — `Mul` derefs its operands, and the Karatsuba
splits are subslices — so they need `toRaw`'s twin on `Slice`.  It is the same
function on the same underlying list, and `toRawS_deref` is the bridge at the
one point where the two meet. -/

/-- The reference `CPolynomial.Raw` represented by a `&[Ext4]`. -/
def toRawS (s : Slice cpoly.field.Ext4) : CPolynomial.Raw F :=
  (s.val.map toExt).toArray

/-- `&*v` denotes what `v` denotes: `Vec::deref` is the identity on the list. -/
@[simp] theorem toRawS_deref (v : alloc.vec.Vec cpoly.field.Ext4) :
    toRawS (alloc.vec.Vec.deref v) = toRaw v := rfl

theorem toRawS_coeff (s : Slice cpoly.field.Ext4) (k : ℕ) :
    (toRawS s).coeff k = (s.val.map toExt).getD k 0 := by
  unfold toRawS CPolynomial.Raw.coeff
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < s.val.length
  · simp [List.getElem?_eq_getElem h, dif_pos h]
  · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h), dif_neg h]

@[simp] theorem toRawS_size (s : Slice cpoly.field.Ext4) :
    (toRawS s).size = s.val.length := by
  simp [toRawS]

theorem toRawS_coeff_of_lt (s : Slice cpoly.field.Ext4) {k : ℕ} (hk : k < s.val.length) :
    (toRawS s).coeff k = toExt s.val[k] := by
  rw [toRawS_coeff, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem toRawS_coeff_of_ge (s : Slice cpoly.field.Ext4) {k : ℕ} (hk : s.val.length ≤ k) :
    (toRawS s).coeff k = 0 := by
  rw [toRawS_coeff, List.getD_eq_default]; simpa using hk

/-- Reading coefficient `i` with zero-padding (`if i < len then v[i] else 0`)
returns the reduced word whose `toExt` is `(toRaw v).coeff i`. -/
theorem padded_read_spec (p : alloc.vec.Vec cpoly.field.Ext4) (np i : Std.Usize)
    (hnp : np.val = p.val.length) (hp : VecReduced p) :
    (if i < np
      then alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice cpoly.field.Ext4) p i
      else ok cpoly.field.Ext4.ZERO) ⦃ a => Reduced a ∧ toExt a = (toRaw p).coeff i.val ⦄ := by
  by_cases h : i < np
  · rw [if_pos h]
    have hb : i.val < p.val.length := by scalar_tac
    step as ⟨e, he⟩
    refine ⟨he ▸ hp _ (List.getElem_mem hb), ?_⟩
    rw [he, toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map]
  · rw [if_neg h]
    simp only [spec_ok]
    refine ⟨reduced_ZERO, ?_⟩
    rw [toRaw_coeff, List.getD_eq_default _ _ (by simp; scalar_tac)]
    simp

/-- The same zero-padded read on a `&[Ext4]`: this is the shape `add_slices`
uses for the two Karatsuba halves, which need not have equal length. -/
theorem padded_read_slice_spec (s : Slice cpoly.field.Ext4) (n i : Std.Usize)
    (hn : n.val = s.val.length) (hs : SliceReduced s) :
    (if i < n then Slice.index_usize s i else ok cpoly.field.Ext4.ZERO)
      ⦃ a => Reduced a ∧ toExt a = (toRawS s).coeff i.val ⦄ := by
  by_cases h : i < n
  · rw [if_pos h]
    have hb : i.val < s.val.length := by scalar_tac
    step as ⟨e, he⟩
    refine ⟨he ▸ hs _ (List.getElem_mem hb), ?_⟩
    rw [he, toRawS_coeff, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map]
  · rw [if_neg h]
    simp only [spec_ok]
    refine ⟨reduced_ZERO, ?_⟩
    rw [toRawS_coeff, List.getD_eq_default _ _ (by simp; scalar_tac)]
    simp

/-- `cpoly.univariate.UnivariatePoly.constant r` ↔ `CPolynomial.Raw.C`. -/
theorem c_spec (r : cpoly.field.Ext4) (hr : Reduced r) :
    cpoly.univariate.UnivariatePoly.constant r ⦃ v => VecReduced v ∧ toRaw v = CPolynomial.Raw.C (toExt r) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.constant]
  simp only [bind_ok_id]
  step as ⟨v, hv⟩
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hv] at hu; simp at hu; subst hu; exact hr
  · simp only [toRaw, hv, CPolynomial.Raw.C]
    simp

/-- `cpoly.univariate.UnivariatePoly.x` ↔ `CPolynomial.Raw.X`. -/
theorem x_spec :
    cpoly.univariate.UnivariatePoly.x ⦃ v => VecReduced v ∧ toRaw v = CPolynomial.Raw.X ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.x]
  simp only [bind_ok_id]
  step as ⟨p, hp⟩
  step as ⟨v, hv⟩
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hv, hp] at hu; simp at hu
    rcases hu with h | h
    · subst h; exact reduced_ZERO
    · subst h; exact reduced_ONE
  · simp only [toRaw, hv, hp, CPolynomial.Raw.X]
    simp

/-! ## Construction, observation and indexing

These are the items that only move the representation around or read it: they say
nothing new about `CPolynomial.Raw`, but they are public Rust API, so each gets a
triple. `Index` is the one with a precondition — it panics out of range, so its
spec is conditional on `i` being in bounds. -/

/-- `UnivariatePoly::zero` is the empty coefficient vector, i.e. the zero polynomial. -/
@[step]
theorem zero_spec :
    cpoly.univariate.UnivariatePoly.zero ⦃ z => VecReduced z ∧ toRaw z = (0 : CPolynomial.Raw F) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.zero]
  simp only [spec_ok]
  exact ⟨by intro u hu; simp at hu, by simp [toRaw]⟩

/-- `impl Default for UnivariatePoly` is `UnivariatePoly::zero`. -/
@[step]
theorem default_spec :
    cpoly.univariate.UnivariatePoly.Insts.CoreDefaultDefault.default
      ⦃ z => VecReduced z ∧ toRaw z = (0 : CPolynomial.Raw F) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.Insts.CoreDefaultDefault.default]; exact zero_spec

/-- `UnivariatePoly::from_coeffs` takes the vector as it stands: no trimming, so a trailing
zero survives.  This is what makes `Poly` a representation and not a normal form. -/
@[step]
theorem from_coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    cpoly.univariate.UnivariatePoly.from_coeffs v ⦃ z => VecReduced z ∧ toRaw z = toRaw v ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.from_coeffs]
  simp only [spec_ok]
  exact ⟨hv, trivial⟩

/-- `impl From<Vec<Ext4>> for Poly` is `UnivariatePoly::from_coeffs`. -/
@[step]
theorem from_vec_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    cpoly.univariate.UnivariatePoly.Insts.CoreConvertFromVecExt4.from v
      ⦃ z => VecReduced z ∧ toRaw z = toRaw v ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.Insts.CoreConvertFromVecExt4.from]; exact from_coeffs_spec v hv

/-- `UnivariatePoly::into_coeffs` gives the vector back unchanged. -/
@[step]
theorem into_coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.univariate.UnivariatePoly.into_coeffs v ⦃ z => z = v ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.into_coeffs]; simp only [spec_ok]

/-- `UnivariatePoly::coeffs` views the same words as a slice. -/
@[step]
theorem coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.univariate.UnivariatePoly.coeffs v ⦃ s => s.val = v.val ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.coeffs]; simp only [spec_ok]; rfl

/-- `UnivariatePoly::len` is the number of stored coefficients, which is the `size` of the
`CPolynomial.Raw` it denotes. -/
@[step]
theorem len_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.univariate.UnivariatePoly.len v ⦃ n => n.val = (toRaw v).size ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.len]; simp only [spec_ok, toRaw_size]; simp

/-- `UnivariatePoly::is_empty` decides whether there are no coefficients at all. -/
@[step]
theorem is_empty_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.univariate.UnivariatePoly.is_empty v ⦃ b => (b = true ↔ (toRaw v).size = 0) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.is_empty]
  apply spec_bind (len_spec v); intro n hn
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro h; rw [← hn, h]; rfl
  · intro h; rw [← hn] at h; scalar_tac

/-- `UnivariatePoly::degree` reads the *representation*: `none` when there are no
coefficients, else one less than their number.  It is the degree of the
polynomial exactly when the representation is trimmed. -/
@[step]
theorem degree_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.univariate.UnivariatePoly.degree v
      ⦃ d => match d with
             | none => (toRaw v).size = 0
             | some k => k.val + 1 = (toRaw v).size ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.degree]
  apply spec_bind (len_spec v); intro n hn
  by_cases h0 : n = 0#usize
  · rw [if_pos h0]
    simp only [spec_ok]
    rw [← hn, h0]; rfl
  · rw [if_neg h0]
    have hpos : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with h | h
      · exact absurd (by scalar_tac : n = 0#usize) h0
      · exact h
    step as ⟨i, hi⟩
    omega

/-- `impl Index<usize> for UnivariatePoly` reads coefficient `i`, which is
`(toRaw v).coeff i`.  Conditional on `i` being in range: out of range the Rust
panics, and the extracted model fails. -/
@[step]
theorem index_spec (v : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hv : VecReduced v) (hi : i.val < v.val.length) :
    cpoly.univariate.UnivariatePoly.Insts.CoreOpsIndexIndexUsizeExt4.index v i
      ⦃ a => Reduced a ∧ toExt a = (toRaw v).coeff i.val ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.Insts.CoreOpsIndexIndexUsizeExt4.index]
  step as ⟨e, he⟩
  exact ⟨he ▸ hv _ (List.getElem_mem hi), by rw [he, toRaw_coeff_of_lt v hi]⟩

/-- `UnivariatePoly::trim`'s scan loop runs from `m` downward and returns the canonical length `n1`:
all coefficients `≥ n1` are zero, and (if `n1 > 0`) coefficient `n1-1` is
nonzero. -/
theorem trim_loop_spec (p : alloc.vec.Vec cpoly.field.Ext4) (m : Std.Usize)
    (hp : VecReduced p) (hm : m.val ≤ p.val.length) :
    cpoly.univariate.UnivariatePoly.trim_loop p m ⦃ n1 => n1.val ≤ m.val ∧
      (∀ k, n1.val ≤ k → k < m.val → (toRaw p).coeff k = 0) ∧
      (n1.val = 0 ∨ (toRaw p).coeff (n1.val - 1) ≠ 0) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.trim_loop]
  apply loop.spec_decr_nat (fun s => s.val)
    (fun s => s.val ≤ m.val ∧ ∀ k, s.val ≤ k → k < m.val → (toRaw p).coeff k = 0)
  · intro m' ⟨hm'le, hm'z⟩
    simp only [cpoly.univariate.UnivariatePoly.trim_loop.body]
    by_cases hpos : m' > 0#usize
    · rw [if_pos hpos]
      have hb : m'.val - 1 < p.val.length := by scalar_tac
      step as ⟨i, hi⟩
      have hib : i.val < p.val.length := by rw [hi]; exact hb
      step as ⟨c, hc⟩
      have hRc : Reduced c := hc ▸ hp _ (List.getElem_mem hib)
      have hcoeff : (toRaw p).coeff i.val = toExt c := by
        rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hib),
          List.getElem_map, hc]
      apply spec_bind (ext_is_zero_spec c hRc)
      intro z hz
      cases z
      · -- the coefficient is nonzero: done with m'
        simp only [Bool.false_eq_true, if_false]
        refine ⟨hm'le, hm'z, Or.inr ?_⟩
        rw [show m'.val - 1 = i.val by rw [hi], hcoeff]
        exact fun hc0 => by simpa using hz.mpr hc0
      · -- the coefficient is zero: continue with i = m'-1
        simp only [if_true]
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk1 hk2
        rcases Nat.lt_or_ge k m'.val with hkm | hkm
        · have hki : k = i.val := by scalar_tac
          rw [hki, hcoeff]; exact hz.mp rfl
        · exact hm'z k hkm hk2
    · rw [if_neg hpos]
      exact ⟨hm'le, hm'z, Or.inl (by scalar_tac)⟩
  · exact ⟨le_refl _, fun k hk1 hk2 => absurd hk2 (by omega)⟩

/-- `cpoly.univariate.UnivariatePoly.trim` ↔ `CPolynomial.Raw.trim`. -/
theorem trim_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    cpoly.univariate.UnivariatePoly.trim v ⦃ w => VecReduced w ∧ toRaw w = (toRaw v).trim ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.trim]
  simp only [bind_ok_id]
  apply spec_bind (trim_loop_spec v (alloc.vec.Vec.len v) hv (by simp))
  rintro n1 ⟨hn1le, hn1zero, hn1bound⟩
  have hn1len : n1.val ≤ v.val.length := by simpa using hn1le
  -- `Vec::resize` down to `n1` truncates: `List.resize l n x = take n l ++ replicate (n - |l|) x`,
  -- and `n1 ≤ |v|` makes the padding empty.
  apply spec_mono (alloc.vec.Vec.resize_spec cpoly.field.Ext4.Insts.CoreCloneClone v n1
    cpoly.field.Ext4.ZERO (ext_clone_eq _))
  intro z hzres
  have hzval : z.val = v.val.take n1.val := by
    rw [hzres, List.resize, if_pos (Nat.zero_le _),
      Nat.sub_eq_zero_of_le (by simpa using hn1len), List.replicate_zero, List.append_nil]
  have hzred : VecReduced z := by
    intro u hu; rw [hzval] at hu; exact hv u (List.mem_of_mem_take hu)
  refine ⟨hzred, ?_⟩
  -- size and coefficient characterization of `toRaw z = toRaw (take n1)`
  have hsz : (toRaw z).size = n1.val := by
    simp only [toRaw, hzval]; simp [List.length_take]; omega
  have hzc : ∀ i, (toRaw z).coeff i = if i < n1.val then (toRaw v).coeff i else 0 := by
    intro i
    by_cases hi : i < n1.val
    · rw [if_pos hi, toRaw_coeff, hzval,
        List.getD_eq_getElem _ _ (by simp [List.length_take]; omega),
        List.getElem_map, List.getElem_take, toRaw_coeff,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
    · rw [if_neg hi, toRaw_coeff, hzval, List.getD_eq_default]
      simp only [List.length_map, List.length_take]; omega
  -- coefficient `i` of `toRaw v` is `0` once `i ≥ n1`
  have hvzero : ∀ i, n1.val ≤ i → (toRaw v).coeff i = 0 := by
    intro i hi
    rcases Nat.lt_or_ge i v.val.length with hil | hil
    · exact hn1zero i hi (by simpa using hil)
    · rw [toRaw_coeff, List.getD_eq_default]; simp only [List.length_map]; omega
  -- both sides are canonical and have equal coefficients
  apply CPolynomial.Raw.Trim.canonical_ext ?_ (CPolynomial.Raw.Trim.trim_twice _)
  · intro i
    rw [CPolynomial.Raw.Trim.coeff_eq_coeff, hzc i]
    by_cases hi : i < n1.val
    · rw [if_pos hi]
    · rw [if_neg hi]; exact (hvzero i (by omega)).symm
  · -- toRaw z is canonical (no trailing zero)
    rw [CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero]
    rcases hn1bound with h0 | hne
    · left; rw [hsz, h0]
    · right
      have hn1pos : 0 < n1.val := by
        rcases Nat.eq_zero_or_pos n1.val with h0 | hpos
        · exact absurd (by rw [h0] at hne ⊢; exact hvzero 0 (by omega)) hne
        · exact hpos
      have hgl : (toRaw z).getLastD 0 = (toRaw z).coeff (n1.val - 1) := by
        unfold Array.getLastD CPolynomial.Raw.coeff; rw [hsz]
      rw [hgl, hzc (n1.val - 1), if_pos (by omega)]; exact hne

theorem eval_loop_spec (p : alloc.vec.Vec cpoly.field.Ext4) (xv : cpoly.field.Ext4)
    (hp : VecReduced p) (hx : Reduced xv) :
    ∀ (acc : cpoly.field.Ext4) (i : Std.Usize), i.val ≤ p.val.length → Reduced acc →
      toExt acc = ((p.val.drop i.val).map toExt).foldr (fun a b => b * toExt xv + a) 0 →
      cpoly.univariate.UnivariatePoly.eval_loop p xv acc i ⦃ r => Reduced r ∧
        toExt r = ((p.val).map toExt).foldr (fun a b => b * toExt xv + a) 0 ⦄ := by
  intro acc i hi hacc hrel
  rw [cpoly.univariate.UnivariatePoly.eval_loop]
  apply loop.spec_decr_nat (fun s => s.2.val)
    (fun s => s.2.val ≤ p.val.length ∧ Reduced s.1 ∧
       toExt s.1 = ((p.val.drop s.2.val).map toExt).foldr (fun a b => b * toExt xv + a) 0)
  · rintro ⟨acc1, i1⟩ ⟨hi1, haccR, hrel1⟩
    simp only [cpoly.univariate.UnivariatePoly.eval_loop.body]
    by_cases hlt : i1 > 0#usize
    · rw [if_pos hlt]
      have hib : i1.val - 1 < p.val.length := by scalar_tac
      step as ⟨j, hj⟩
      have hjb : j.val < p.val.length := by rw [hj]; exact hib
      step as ⟨m, hmR, hmF⟩
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hp _ (List.getElem_mem hjb)
      step as ⟨acc2, hacc2R, hacc2F⟩
      refine ⟨by scalar_tac, hacc2R, ?_, by scalar_tac⟩
      have hdrop : p.val.drop j.val = p.val[j.val] :: p.val.drop i1.val := by
        rw [show i1.val = j.val + 1 from by scalar_tac]
        exact List.drop_eq_getElem_cons hjb
      rw [hacc2F, hmF, he, hdrop]
      simp only [List.map_cons, List.foldr_cons, hrel1]
    · rw [if_neg hlt]
      have hz : i1.val = 0 := by scalar_tac
      exact ⟨haccR, by rw [hrel1, hz]; simp⟩
  · exact ⟨hi, hacc, hrel⟩

/-- `cpoly.univariate.UnivariatePoly.eval` ↔ `CPolynomial.Raw.eval` (Horner). -/
theorem eval_spec (v : alloc.vec.Vec cpoly.field.Ext4) (xv : cpoly.field.Ext4)
    (hv : VecReduced v) (hx : Reduced xv) :
    cpoly.univariate.UnivariatePoly.eval v xv ⦃ r => Reduced r ∧ toExt r = (toRaw v).eval (toExt xv) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.eval]
  apply spec_mono (eval_loop_spec v xv hv hx cpoly.field.Ext4.ZERO (alloc.vec.Vec.len v)
    (by simp) reduced_ZERO (by simp))
  rintro r ⟨hrR, hrF⟩
  refine ⟨hrR, ?_⟩
  rw [hrF, CPolynomial.Raw.eval, ← CPolynomial.Raw.eval₂Horner_eq_eval₂,
    CPolynomial.Raw.eval₂Horner, Array.foldr_toList]
  simp [toRaw]

theorem add_raw_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (np nq n : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hnp : np.val = p.val.length) (hnq : nq.val = q.val.length)
    (hn : n.val = max p.val.length q.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt
        = (List.range i.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k) →
      cpoly.univariate.UnivariatePoly.add_untrimmed_loop p q np nq n r i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range n.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.univariate.UnivariatePoly.add_untrimmed_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt
        = (List.range s.2.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.univariate.UnivariatePoly.add_untrimmed_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hr1len : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      apply spec_bind (padded_read_spec p np i1 hnp hp); rintro a ⟨haR, haF⟩
      apply spec_bind (padded_read_spec q nq i1 hnq hq); rintro b ⟨hbR, hbF⟩
      step as ⟨s, hsR, hsF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact hsR
      · rw [hr2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hsF, haF, hbF]
      · have hlt2 : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      refine ⟨hr1, ?_⟩
      rw [← heq]; simpa using hrel1
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly.univariate.UnivariatePoly.add_untrimmed` ↔ `CPolynomial.Raw.addRaw` (untrimmed). -/
theorem add_raw_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w) :
    cpoly.univariate.UnivariatePoly.add_untrimmed v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.addRaw (toRaw v) (toRaw w) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.add_untrimmed]
  simp only [bind_ok_id]
  apply spec_bind (Pₘ := fun nn : Std.Usize => nn.val = max v.val.length w.val.length)
  · by_cases hc : alloc.vec.Vec.len v ≥ alloc.vec.Vec.len w
    · rw [if_pos hc]; simp only [spec_ok]; scalar_tac
    · rw [if_neg hc]; simp only [spec_ok]; scalar_tac
  · intro nn hnn
    apply spec_mono (add_raw_loop_spec v w (alloc.vec.Vec.len v) (alloc.vec.Vec.len w) nn
      hv hw (by simp) (by simp) hnn (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp)
      (by intro u hu; simp at hu) (by simp))
    rintro z ⟨hzred, hzmap⟩
    refine ⟨hzred, ?_⟩
    have hzlen : z.val.length = nn.val := by
      have := congrArg List.length hzmap; simpa using this
    apply Array.ext
    · rw [CPolynomial.Raw.add_size]
      simp only [toRaw]
      simp [hzlen, hnn]
    · intro i hi hi2
      rw [CPolynomial.Raw.add_coeff hi2]
      simp only [toRaw, List.getElem_toArray]
      rw [getElem_of_list_eq hzmap, List.getElem_map, List.getElem_range]
      simp only [toRaw]

/-- `Poly.add` ↔ `CPolynomial.Raw.add`. -/
theorem add_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w) :
    Poly.add v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.add (toRaw v) (toRaw w) ⦄ := by
  unfold Poly.add
  rw [cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add]
  apply spec_bind (add_raw_spec v w hv hw)
  rintro r ⟨hrred, hrmap⟩
  apply spec_mono (trim_spec r hrred)
  rintro z ⟨hzred, hztrim⟩
  exact ⟨hzred, by rw [hztrim, hrmap]; rfl⟩

/-- `Poly.neg` ↔ `CPolynomial.Raw.neg`.

The shared recipe for all the loop-based operations.  The generated `*_loop`
functions are `loop (fun s => body s) init`.  Reason about them with
`Aeneas.Std.loop.spec_decr_nat`, instantiated with:
  • measure  `fun s => n.val - s.2.val`   (counter approaches the length)
  • invariant tying the accumulator's field-image to the processed prefix, e.g.
      `s.1.val.map toExt = (p.val.take s.2.val).map (fun u => - toExt u)`
The body obligation steps with `step` through `Vec.index_usize_spec`,
`fp_neg_spec` (`@[step]`), and `Vec.push_spec`; the `List.take_succ` /
`List.map_append` lemmas extend the prefix by one.  The triple `m ⦃ r => P ⦄`
is `Aeneas.Std.spec m P` (a WP predicate, NOT a bare `∃`), so compose loop
specs into the top-level operation with `spec_mono` / `spec_bind`, then convert
the `List.map toExt` invariant to the `toRaw` (Array) equation via
`Array.map_toArray` + `List.map_map`.  `eval`/`smul`/`add_raw` follow the same
single-loop shape; `trim` adds a `lastNonzero`/`Array.extract` argument.

`mul` is the one operation that does not fit the prefix-append mould: its
Karatsuba recombination loops update single slots of a pre-sized buffer in
place, so their invariants are stated coefficient-wise (see
`karatsuba_low_loop_spec` and its neighbours) rather than as a `take`. -/
theorem neg_loop_spec (p : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (hp : VecReduced p) (hn : n.val = p.val.length) (r : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (hi : i.val ≤ n.val) (hr : VecReduced r)
    (hrel : r.val.map toExt = (p.val.take i.val).map (fun u => - toExt u)) :
    Poly.negLoop p n r i ⦃ z => VecReduced z ∧
      z.val.map toExt = p.val.map (fun u => - toExt u) ⦄ := by
  unfold Poly.negLoop
  rw [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
       s.1.val.map toExt = (p.val.take s.2.val).map (fun u => - toExt u))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlt' : i1.val < p.val.length := by scalar_tac
      have hr1len : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1
        simp only [List.length_map, List.length_take] at h
        omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hp _ (List.getElem_mem hlt')
      step as ⟨ne, hneR, hneF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · -- VecReduced r2
        intro u hu
        rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact hneR
      · -- field-image extends by one negated coefficient
        rw [hr2, hi2, ← List.take_concat_get' _ _ hlt']
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hneF, he]
      · -- measure decreases
        have hlt2 : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      refine ⟨hr1, ?_⟩
      rw [hrel1, heq, hn, List.take_length]
  · exact ⟨hi, hr, hrel⟩

theorem neg_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    Poly.neg v ⦃ z => VecReduced z ∧ toRaw z = CPolynomial.Raw.neg (toRaw v) ⦄ := by
  unfold Poly.neg
  rw [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg]
  simp only [bind_ok_id]
  apply spec_mono (neg_loop_spec v (alloc.vec.Vec.len v) hv (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzmap⟩
  refine ⟨hzred, ?_⟩
  simp only [toRaw, hzmap, CPolynomial.Raw.neg, List.map_toArray, List.map_map,
    Function.comp_def]

/-- `Poly.sub` ↔ `CPolynomial.Raw.sub`. -/
theorem sub_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w) :
    Poly.sub v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.sub (toRaw v) (toRaw w) ⦄ := by
  unfold Poly.sub
  rw [cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithSubShared0UnivariatePolyUnivariatePoly.sub]
  apply spec_bind (neg_spec w hw)
  rintro nq ⟨hnqred, hnqmap⟩
  apply spec_mono (add_spec v nq hv hnqred)
  rintro z ⟨hzred, hzmap⟩
  exact ⟨hzred, by rw [hzmap, hnqmap]; rfl⟩

theorem smul_loop_spec (rr : cpoly.field.Ext4) (p : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (hrr : Reduced rr) (hp : VecReduced p) (hn : n.val = p.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ n.val → VecReduced out →
      out.val.map toExt = (p.val.take i.val).map (fun u => toExt rr * toExt u) →
      Poly.smulLoop p rr n out i ⦃ z => VecReduced z ∧
        z.val.map toExt = p.val.map (fun u => toExt rr * toExt u) ⦄ := by
  intro out i hi hout hrel
  unfold Poly.smulLoop
  rw [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
       s.1.val.map toExt = (p.val.take s.2.val).map (fun u => toExt rr * toExt u))
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1, hrel1⟩
    simp only [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlt' : i1.val < p.val.length := by scalar_tac
      have hout1len : out1.val.length = i1.val := by
        have h := congrArg List.length hrel1
        simp only [List.length_map, List.length_take] at h; omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hp _ (List.getElem_mem hlt')
      step as ⟨pe, hpeR, hpeF⟩
      step as ⟨out2, hout2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hout2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hout1 u h
        · rw [List.mem_singleton.mp h]; exact hpeR
      · rw [hout2, hi2, ← List.take_concat_get' _ _ hlt']
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hpeF, he]
      · have hlt2 : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      refine ⟨hout1, ?_⟩
      rw [hrel1, heq, hn, List.take_length]
  · exact ⟨hi, hout, hrel⟩

/-- `Poly.smul` ↔ `CPolynomial.Raw.smul`. -/
theorem smul_spec (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) :
    Poly.smul v r ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.smul (toExt r) (toRaw v) ⦄ := by
  unfold Poly.smul
  rw [cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul]
  simp only [bind_ok_id]
  apply spec_mono (smul_loop_spec r v (alloc.vec.Vec.len v) hr hv (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzmap⟩
  refine ⟨hzred, ?_⟩
  simp only [toRaw, hzmap, CPolynomial.Raw.smul, List.map_toArray, List.map_map,
    Function.comp_def]

/-! ### Multiplication

`Poly.mul` is Karatsuba (`Poly.karatsuba`) down to `KARATSUBA_CUTOFF = 16`,
bottoming out in `Poly.convDelayed`: an *output-indexed* schoolbook convolution
that accumulates the seven unreduced coefficients of the extension product in
`u128` lanes and reduces once per output coefficient rather than once per
operation.  Neither layer changes the result: coefficient `k` of the product is
`Σ_{i+j=k} p_i q_j` either way, so every statement below lands on
`CPolynomial.Raw.mul` (or `CPolynomial.Raw.addRaw` for the recombination
helper) — never on a description of what the algorithm does.

Three things need machinery the schoolbook version did not:

* the helpers take `&[Ext4]`, so their representation is `toRawS`;
* the base case's inner loop carries seven *unreduced* `u128` lane sums instead
  of a field-valued accumulator, so its invariant is stated in `ℕ` over `lanes`
  and comes with the overflow bound (`lanes_le`, `lanes_fold_lt`) that is the
  whole reason the lanes are `u128` and not `u64`;
* the champion inlines `W = 2` — it doubles (`t + t`) where `Ext4`'s own `Mul`
  multiplies by `field::W` — so the `Y^4` wrap is bridged by `toExt_mul_coeff`,
  which is where `Hachi.ext4Params.W = 2` is used, rather than by
  `ext_mul_spec`.

The reference side is reached coefficient-wise throughout: `CPolynomial.Raw.mul`
is `mulRaw |> trim` and `Trim.coeff_eq_coeff` says trimming does not move a
coefficient, so `(toRaw z).coeff k = (CPolynomial.Raw.mul p q).coeff k` is the
right claim for the *untrimmed* helpers as well, and the headline `mul_spec`
turns the family of coefficient equations into the array equation with
`Trim.eq_of_equiv`. -/

/-! #### The unreduced lanes

`conv_delayed`'s inner loop is the one place in the crate where a value leaves
the field: seven `u128` accumulators hold the schoolbook coefficients of the
extension product before any reduction, before the `Y^4` wrap, and summed over
all the pairs `(i, k-i)` that feed output `k`.  The mathematics is stated in
`ℕ` on the raw `Fp` words and only meets `F` at `toExt_mul_coeff`. -/

/-- The seven unreduced lanes of one schoolbook `Ext4` product, in `ℕ`: lane `l`
is `Σ_{u+v=l} a_u b_v` over the raw words.  Zero for `l ≥ 7`, which keeps it
total and makes `toExt_mul_coeff`'s `l + 4` legal at `l = 3`. -/
def lanePair (a b : cpoly.field.Ext4) : ℕ → ℕ
  | 0 => a.c0.val * b.c0.val
  | 1 => a.c0.val * b.c1.val + a.c1.val * b.c0.val
  | 2 => a.c0.val * b.c2.val + a.c1.val * b.c1.val + a.c2.val * b.c0.val
  | 3 => a.c0.val * b.c3.val + a.c1.val * b.c2.val + a.c2.val * b.c1.val + a.c3.val * b.c0.val
  | 4 => a.c1.val * b.c3.val + a.c2.val * b.c2.val + a.c3.val * b.c1.val
  | 5 => a.c2.val * b.c3.val + a.c3.val * b.c2.val
  | 6 => a.c3.val * b.c3.val
  | _ => 0

/-- How many word products lane `l` takes: `1, 2, 3, 4, 3, 2, 1`.  The `u128`
headroom argument is stated against this rather than against a uniform `4`,
because the fold `c0 = t0 + 2 t4` is the widest combination (seven products per
pair) and a uniform bound would lose the factor that decides it. -/
def laneWidth : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | _ => 0

/-- Lane `l` of the base case's accumulator once the pairs `i ∈ [lo, m)` have
been folded in.  Out-of-range reads take `Ext4::ZERO`, which contributes
nothing: the loop never performs one, and the default keeps the definition total
so that no index proof travels with the invariant. -/
def lanes (p q : List cpoly.field.Ext4) (k lo m l : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico lo m,
    lanePair (p.getD i cpoly.field.Ext4.ZERO) (q.getD (k - i) cpoly.field.Ext4.ZERO) l

@[simp] theorem lanes_self (p q : List cpoly.field.Ext4) (k lo l : ℕ) :
    lanes p q k lo lo l = 0 := by
  simp [lanes]

/-- One more pair.  This is the step the inner loop body takes. -/
theorem lanes_succ (p q : List cpoly.field.Ext4) (k lo m l : ℕ) (h : lo ≤ m) :
    lanes p q k lo (m + 1) l
      = lanes p q k lo m l
        + lanePair (p.getD m cpoly.field.Ext4.ZERO)
            (q.getD (k - m) cpoly.field.Ext4.ZERO) l := by
  simp only [lanes]
  exact Finset.sum_Ico_succ_top h _

/-- Two reduced words multiply below `(P-1)^2`. -/
private theorem lanePair_le_aux {x y : ℕ} (hx : x < P) (hy : y < P) :
    x * y ≤ (P - 1) ^ 2 := by
  have hx' : x ≤ P - 1 := by omega
  have hy' : y ≤ P - 1 := by omega
  calc x * y ≤ (P - 1) * (P - 1) := Nat.mul_le_mul hx' hy'
    _ = (P - 1) ^ 2 := (sq (P - 1)).symm

/-- A single pair contributes at most `laneWidth l` products of two reduced
words, each below `(P-1)^2 < 2^64`.  This is the same bound `field::Fp`'s `Mul`
already relies on — which is why the *products* still fit a `u64` and only the
*sums* need `u128`. -/
theorem lanePair_le (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) (l : ℕ) :
    lanePair a b l ≤ laneWidth l * (P - 1) ^ 2 := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  simp only [Red] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have k00 := lanePair_le_aux ha0 hb0
  have k01 := lanePair_le_aux ha0 hb1
  have k02 := lanePair_le_aux ha0 hb2
  have k03 := lanePair_le_aux ha0 hb3
  have k10 := lanePair_le_aux ha1 hb0
  have k11 := lanePair_le_aux ha1 hb1
  have k12 := lanePair_le_aux ha1 hb2
  have k13 := lanePair_le_aux ha1 hb3
  have k20 := lanePair_le_aux ha2 hb0
  have k21 := lanePair_le_aux ha2 hb1
  have k22 := lanePair_le_aux ha2 hb2
  have k23 := lanePair_le_aux ha2 hb3
  have k30 := lanePair_le_aux ha3 hb0
  have k31 := lanePair_le_aux ha3 hb1
  have k32 := lanePair_le_aux ha3 hb2
  have k33 := lanePair_le_aux ha3 hb3
  generalize hc : (P - 1) ^ 2 = c at k00 k01 k02 k03 k10 k11 k12 k13 k20 k21 k22 k23 k30 k31 k32 k33 ⊢
  match l with
  | 0 => simp only [lanePair, laneWidth]; omega
  | 1 => simp only [lanePair, laneWidth]; omega
  | 2 => simp only [lanePair, laneWidth]; omega
  | 3 => simp only [lanePair, laneWidth]; omega
  | 4 => simp only [lanePair, laneWidth]; omega
  | 5 => simp only [lanePair, laneWidth]; omega
  | 6 => simp only [lanePair, laneWidth]; omega
  | (n + 7) => simp only [lanePair, laneWidth]; omega

/-- A zero-padded read out of an all-`Reduced` list is `Reduced`: in range it is
an element, out of range it is `Ext4::ZERO`. -/
private theorem lanes_le_aux (xs : List cpoly.field.Ext4)
    (h : ∀ a ∈ xs, Reduced a) (i : ℕ) :
    Reduced (xs.getD i cpoly.field.Ext4.ZERO) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact reduced_ZERO

/-- Hence a lane after `m - lo` pairs.  `Ext4::ZERO` is reduced, so the padding
reads cost nothing. -/
theorem lanes_le (p q : List cpoly.field.Ext4)
    (hp : ∀ a ∈ p, Reduced a) (hq : ∀ a ∈ q, Reduced a) (k lo m l : ℕ) :
    lanes p q k lo m l ≤ (m - lo) * (laneWidth l * (P - 1) ^ 2) := by
  unfold lanes
  calc ∑ i ∈ Finset.Ico lo m,
        lanePair (p.getD i cpoly.field.Ext4.ZERO) (q.getD (k - i) cpoly.field.Ext4.ZERO) l
      ≤ ∑ _i ∈ Finset.Ico lo m, laneWidth l * (P - 1) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          lanePair_le _ _ (lanes_le_aux p hp i) (lanes_le_aux q hq (k - i)) l
    _ = (m - lo) * (laneWidth l * (P - 1) ^ 2) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- The widest fold: `laneWidth l + 2 * laneWidth (l+4) ≤ 7`, attained at
`l = 0` (`1 + 2*3`).  Above `l = 2` the `l + 4` lane is out of range. -/
private theorem lanes_fold_lt_aux (l : ℕ) :
    laneWidth l + 2 * laneWidth (l + 4) ≤ 7 := by
  match l with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | (n + 7) =>
    have h1 : laneWidth (n + 7) = 0 := rfl
    have h2 : laneWidth (n + 7 + 4) = 0 := rfl
    omega

/-- The headroom that makes every `u128` operation of the base case succeed, at
the widest combination the code forms: `c_l = t_l + 2 t_{l+4}`, i.e. seven
products per pair for `l = 0`.

`7 * n * (P-1)^2 < 2^128` is the real condition, and with `P = 2^32 - 99` it
first fails between `2^61` and `2^62` pairs; `2^61` is the largest power of two
below the threshold, which is why `conv_delayed_spec` asks for
`min np nq ≤ 2^61` and not for something derivable from `Slice`'s own
`length ≤ Usize.max`.  `Poly.karatsuba` never comes close: it calls the base
case only at `min np nq ≤ KARATSUBA_CUTOFF = 16`. -/
theorem lanes_fold_lt (p q : List cpoly.field.Ext4)
    (hp : ∀ a ∈ p, Reduced a) (hq : ∀ a ∈ q, Reduced a) (k lo m : ℕ)
    (hm : m - lo ≤ 2 ^ 61) (l : ℕ) :
    lanes p q k lo m l + 2 * lanes p q k lo m (l + 4) < 2 ^ 128 := by
  have h1 := lanes_le p q hp hq k lo m l
  have h2 := lanes_le p q hp hq k lo m (l + 4)
  have hw := lanes_fold_lt_aux l
  calc lanes p q k lo m l + 2 * lanes p q k lo m (l + 4)
      ≤ (m - lo) * (laneWidth l * (P - 1) ^ 2)
          + 2 * ((m - lo) * (laneWidth (l + 4) * (P - 1) ^ 2)) := by omega
    _ = (m - lo) * ((laneWidth l + 2 * laneWidth (l + 4)) * (P - 1) ^ 2) := by ring
    _ ≤ 2 ^ 61 * (7 * (P - 1) ^ 2) :=
        Nat.mul_le_mul hm (Nat.mul_le_mul_right _ hw)
    _ < 2 ^ 128 := by norm_num [P, Hachi.fieldSize]

/-- **The `W = 2` bridge.**  `Hachi.ext4Params.W = 2`, and the champion inlines
that: it forms `t + t` where `Ext4`'s own `Mul` (and `ext_mul_spec`) multiplies
by `field::W`.  Coefficient `l < 3` of a product is therefore
`lane l + 2 * lane (l+4)` and coefficient `3` is `lane 3` alone — exactly the
`c0 / c1 / c2 / t3` the base case pushes.

No `Reduced` hypothesis: `toK` is the cast of the word and `lanePair` multiplies
the words in `ℕ`, so the identity is the ring-hom image of a `ℕ` identity
whatever the words are. -/
theorem toExt_mul_coeff (a b : cpoly.field.Ext4) (i : Fin Hachi.ext4Params.d) :
    Ext.coeff (toExt a * toExt b) i
      = if i.val < 3 then (lanePair a b i.val : K) + 2 * (lanePair a b (i.val + 4) : K)
        else (lanePair a b 3 : K) := by
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  rw [Ext.coeff_mul, sum_univ_four' Hachi.ext4Params_d]
  simp only [sum_univ_four' Hachi.ext4Params_d, coeff_toExt, Hachi.ext4Params_W, h4]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    norm_num [extCoeff, lanePair, toK] <;> ring

/-- The pair range the base case walks for output `k` — `i` from
`max 0 (k + 1 - nq)` up to `min k (np - 1)` — already carries the whole
convolution: below `lo` the `q` coefficient is out of range and above `hi` the
`p` coefficient is, so the discarded terms are zero.  This is what turns the
loop's `Finset.Ico` into `CPolynomial.Raw.mul_coeff`'s `Finset.range (k+1)`. -/
theorem sum_Ico_eq_mul_coeff (lhs rhs : Slice cpoly.field.Ext4) (k lo hi : ℕ)
    (hppos : 0 < lhs.val.length)
    (hlo : lo = if rhs.val.length ≤ k then k - rhs.val.length + 1 else 0)
    (hhi : hi = if k < lhs.val.length then k else lhs.val.length - 1) :
    ∑ i ∈ Finset.Ico lo (hi + 1), (toRawS lhs).coeff i * (toRawS rhs).coeff (k - i)
      = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k := by
  have hmul : (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k
      = ∑ i ∈ Finset.range (k + 1),
          (toRawS lhs).coeff i * (toRawS rhs).coeff (k - i) :=
    CPolynomial.Raw.mul_coeff (toRawS lhs) (toRawS rhs) k
  rw [hmul]
  apply Finset.sum_subset
  · -- `Ico lo (hi+1) ⊆ range (k+1)`: `hi ≤ k` in both branches
    intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [Finset.mem_range]
    rw [hhi] at hx
    split at hx <;> omega
  · -- the discarded terms vanish
    intro x hx hxn
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_Ico, not_and, not_lt] at hxn
    by_cases hlt : x < lo
    · -- below `lo`: the `q` coefficient is out of range
      have hq : rhs.val.length ≤ k - x := by
        rw [hlo] at hlt; split at hlt <;> omega
      rw [toRawS_coeff_of_ge rhs hq, mul_zero]
    · -- at or above `hi + 1`: the `p` coefficient is out of range
      have hge : hi + 1 ≤ x := hxn (Nat.le_of_not_lt hlt)
      have hp : lhs.val.length ≤ x := by
        rw [hhi] at hge; split at hge <;> omega
      rw [toRawS_coeff_of_ge lhs hp, zero_mul]

/-! #### `reduce_u128` -/

/-- `Poly.reduceU128` is the class of `x` in the base field, for *every* `x`.

Total, so no hypothesis.  The fail-point walk: the two `as` casts are the halves
of a `u128` and never fail; `hi % P` and `lo % P` are guarded by `P ≠ 0`;
`(hi % P) * R64 < 2^32 * 2^14 = 2^46` fits a `u64`; and the final
`(lo % P) + folded < 2P < 2^33` fits as well.  `Fp::new` reduces, which is what
re-establishes `Red` for the caller.

The one number-theoretic fact it rests on is `R64 = 9801 = 99^2 ≡ 2^64 (mod P)`,
from `P = 2^32 - 99`. -/
theorem reduce_u128_spec (x : Std.U128) :
    Poly.reduceU128 x ⦃ c => Red c ∧ toK c = (x.val : K) ⦄ := by
  unfold Poly.reduceU128
  rw [cpoly.univariate.reduce_u128]
  -- `lo = x as u64`
  step as ⟨lo, hlo⟩
  -- `i = x >> 64` (the shift amount `64 < 128` is discharged by `step`)
  step as ⟨i, hish, _⟩
  -- `hi = (x >> 64) as u64`
  step as ⟨hi, hhi⟩
  -- the two halves, as ℕ
  have hlov : lo.val = x.val % 2 ^ 64 := by
    rw [hlo, UScalar.cast_val_eq]; rfl
  have hhiv : hi.val = x.val / 2 ^ 64 := by
    rw [hhi, UScalar.cast_val_eq]
    have hiv : i.val = x.val / 2 ^ 64 := by
      rw [hish]; simp [Nat.shiftRight_eq_div_pow]
    rw [hiv]
    have hx : x.val < 2 ^ 128 := by scalar_tac
    have : x.val / 2 ^ 64 < 2 ^ 64 := by omega
    simp only [UScalarTy.numBits]
    omega
  -- `i1 = hi % P`
  step as ⟨i1, hi1v⟩
  have hPnum : P = 4294967197 := by norm_num
  have hR : (cpoly.univariate.R64).val = 9801 := by
    simp only [cpoly.univariate.R64]; decide
  have hi1lt : i1.val < P := by
    rw [hi1v, cpoly_P_val]; exact Nat.mod_lt _ (by omega)
  -- `(hi % P) * R64 < 2^32 * 2^14` fits a `u64`
  have hbound : i1.val * (cpoly.univariate.R64).val ≤ Std.U64.max := by
    rw [hR]
    have := Std.U64.max_eq
    omega
  step as ⟨i2, hi2v⟩
  -- `folded = ((hi % P) * R64) % P` and `i3 = lo % P`
  step as ⟨folded, hfv⟩
  step as ⟨i3, hi3v⟩
  have hfltP : folded.val < P := by
    rw [hfv, cpoly_P_val]; exact Nat.mod_lt _ (by omega)
  have hi3ltP : i3.val < P := by
    rw [hi3v, cpoly_P_val]; exact Nat.mod_lt _ (by omega)
  -- the final sum of two reduced words is below `2P < 2^33`
  have hsum : i3.val + folded.val ≤ Std.U64.max := by
    have := Std.U64.max_eq
    omega
  step as ⟨i4, hi4v⟩
  -- `Fp::new` reduces, which re-establishes `Red`
  step as ⟨c, hcred, hck⟩
  refine ⟨hcred, ?_⟩
  -- the one number-theoretic fact: `2^64 ≡ 9801 (mod P)`
  have key : (18446744073709551616 : ℕ) % P = 9801 := by rw [hPnum]
  have h2 : (18446744073709551616 : K) = (9801 : K) := by
    have h := ZMod.natCast_mod (18446744073709551616 : ℕ) P
    rw [key] at h
    simpa using h.symm
  have hx : x.val = lo.val + hi.val * 2 ^ 64 := by
    rw [hlov, hhiv]; omega
  rw [hck, hi4v, hi3v, hfv, hi2v, hi1v, cpoly_P_val, hR, hx]
  push_cast [ZMod.natCast_mod]
  rw [h2]

/-! #### The base case, `conv_delayed` -/

/-- The seven lanes read off the inner loop's result tuple.  The loop *state* is
an eight-tuple (the seven lanes and the index), so the invariant handed to
`loop.spec_decr_nat` is `LaneVal (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1,
s.2.2.2.2.2.1, s.2.2.2.2.2.2.1) (lanes …) ∧ …` with the index `s.2.2.2.2.2.2.2`
carrying the measure. -/
def LaneVal
    (u : Std.U128 × Std.U128 × Std.U128 × Std.U128 × Std.U128 × Std.U128 × Std.U128)
    (f : ℕ → ℕ) : Prop :=
  u.1.val = f 0 ∧ u.2.1.val = f 1 ∧ u.2.2.1.val = f 2 ∧ u.2.2.2.1.val = f 3 ∧
    u.2.2.2.2.1.val = f 4 ∧ u.2.2.2.2.2.1.val = f 5 ∧ u.2.2.2.2.2.2.val = f 6

/-- Every lane stays below `2^127` while at most `2^61` pairs have been folded
in: `laneWidth l ≤ 4` and `(P-1)^2 ≤ 2^64`, so `lanes ≤ 2^61 * (4 * 2^64)`.
This is the slack the *checked* `u128` accumulations of the body need — the
statement `lanes_fold_lt` makes about the final fold, one add earlier. -/
private theorem conv_delayed_lane_loop_spec_aux_lt
    (p q : List cpoly.field.Ext4)
    (hp : ∀ a ∈ p, Reduced a) (hq : ∀ a ∈ q, Reduced a)
    (k lo m l : ℕ) (hm : m - lo ≤ 2 ^ 61) :
    lanes p q k lo m l ≤ 2 ^ 127 := by
  have h := lanes_le p q hp hq k lo m l
  have hw : laneWidth l ≤ 4 := by
    rcases l with _|_|_|_|_|_|_|l <;> simp [laneWidth]
  have hP2 : (P - 1) ^ 2 ≤ 2 ^ 64 := by
    have hPv : P = 4294967197 := rfl
    rw [hPv]; norm_num
  calc lanes p q k lo m l ≤ (m - lo) * (laneWidth l * (P - 1) ^ 2) := h
    _ ≤ 2 ^ 61 * (4 * 2 ^ 64) := Nat.mul_le_mul hm (Nat.mul_le_mul hw hP2)
    _ = 2 ^ 127 := by norm_num

set_option maxHeartbeats 2000000 in
/-- The lane loop: for one output index `k` it folds the pairs `(i, k-i)` for
`i ∈ [i₀, hi]` into the seven `u128` accumulators, adding nothing else.

`lo` is a ghost parameter: the *entry* index of the whole loop, which the
invariant needs and the generated code does not carry.  `hhik : hi ≤ k` is what
makes the body's `if i <= k` guard vacuous — the call site establishes it,
since `hi` is `min k (np - 1)`.  The two index hypotheses are the in-bounds
conditions for `lhs[i]` and `rhs[k - i]`, and `hcap` is the `u128` headroom
(see `lanes_fold_lt`). -/
theorem conv_delayed_lane_loop_spec (lhs rhs : Slice cpoly.field.Ext4)
    (k hi : Std.Usize) (lo : ℕ)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs)
    (hhik : hi.val ≤ k.val)
    (hhi : hi.val < lhs.val.length)
    (hlo : k.val - lo < rhs.val.length)
    (hcap : hi.val + 1 - lo ≤ 2 ^ 61) :
    ∀ (t0 t1 t2 t3 t4 t5 t6 : Std.U128) (i : Std.Usize),
      lo ≤ i.val → i.val ≤ hi.val + 1 →
      LaneVal (t0, t1, t2, t3, t4, t5, t6) (lanes lhs.val rhs.val k.val lo i.val) →
      Poly.convDelayedLaneLoop lhs rhs k hi t0 t1 t2 t3 t4 t5 t6 i
        ⦃ u => LaneVal u (lanes lhs.val rhs.val k.val lo (hi.val + 1)) ⦄ := by
  intro t0 t1 t2 t3 t4 t5 t6 i hi0 hi1 hLV
  unfold Poly.convDelayedLaneLoop
  rw [cpoly.univariate.conv_delayed_loop0_loop0]
  apply loop.spec_decr_nat (fun s => hi.val + 1 - s.2.2.2.2.2.2.2.val)
    (fun s => lo ≤ s.2.2.2.2.2.2.2.val ∧ s.2.2.2.2.2.2.2.val ≤ hi.val + 1 ∧
      LaneVal (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)
        (lanes lhs.val rhs.val k.val lo s.2.2.2.2.2.2.2.val))
  · rintro ⟨a0, a1, a2, a3, a4, a5, a6, m⟩ hinv
    -- the projections out of an eight-tuple are opaque to `omega`: re-ascribe by defeq
    obtain ⟨hm0, hm1, hLV1⟩ :
        lo ≤ m.val ∧ m.val ≤ hi.val + 1 ∧
          LaneVal (a0, a1, a2, a3, a4, a5, a6) (lanes lhs.val rhs.val k.val lo m.val) := hinv
    simp only [cpoly.univariate.conv_delayed_loop0_loop0.body]
    by_cases hle : m ≤ hi
    · rw [if_pos hle]
      -- `hi ≤ k` makes the body's second guard vacuous
      rw [if_pos (show m ≤ k from by scalar_tac)]
      obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ :
          a0.val = lanes lhs.val rhs.val k.val lo m.val 0 ∧
          a1.val = lanes lhs.val rhs.val k.val lo m.val 1 ∧
          a2.val = lanes lhs.val rhs.val k.val lo m.val 2 ∧
          a3.val = lanes lhs.val rhs.val k.val lo m.val 3 ∧
          a4.val = lanes lhs.val rhs.val k.val lo m.val 4 ∧
          a5.val = lanes lhs.val rhs.val k.val lo m.val 5 ∧
          a6.val = lanes lhs.val rhs.val k.val lo m.val 6 := hLV1
      have hmlhs : m.val < lhs.val.length := by scalar_tac
      have hmcap : m.val - lo ≤ 2 ^ 61 := by omega
      -- the `u128` headroom, one lane at a time, before the adds that need it
      have ha0 : a0.val ≤ 2 ^ 127 := by
        rw [e0]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 0 hmcap
      have ha1 : a1.val ≤ 2 ^ 127 := by
        rw [e1]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 1 hmcap
      have ha2 : a2.val ≤ 2 ^ 127 := by
        rw [e2]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 2 hmcap
      have ha3 : a3.val ≤ 2 ^ 127 := by
        rw [e3]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 3 hmcap
      have ha4 : a4.val ≤ 2 ^ 127 := by
        rw [e4]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 4 hmcap
      have ha5 : a5.val ≤ 2 ^ 127 := by
        rw [e5]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 5 hmcap
      have ha6 : a6.val ≤ 2 ^ 127 := by
        rw [e6]; exact conv_delayed_lane_loop_spec_aux_lt _ _ hl hr _ _ _ 6 hmcap
      step as ⟨j, hj⟩
      have hjb : j.val < rhs.val.length := by omega
      step as ⟨pi, hpi⟩
      step as ⟨qj, hqj⟩
      have hpiR : Reduced pi := hpi ▸ hl _ (List.getElem_mem hmlhs)
      have hqjR : Reduced qj := hqj ▸ hr _ (List.getElem_mem hjb)
      obtain ⟨hp0, hp1, hp2, hp3⟩ :
          pi.c0.val < P ∧ pi.c1.val < P ∧ pi.c2.val < P ∧ pi.c3.val < P := hpiR
      obtain ⟨hq0, hq1, hq2, hq3⟩ :
          qj.c0.val < P ∧ qj.c1.val < P ∧ qj.c2.val < P ∧ qj.c3.val < P := hqjR
      step as ⟨x0, hx0⟩
      step as ⟨x1, hx1⟩
      step as ⟨x2, hx2⟩
      step as ⟨x3, hx3⟩
      step as ⟨y0, hy0⟩
      step as ⟨y1, hy1⟩
      step as ⟨y2, hy2⟩
      step as ⟨y3, hy3⟩
      have vx0 : x0.val = pi.c0.val := by rw [hx0]
      have vx1 : x1.val = pi.c1.val := by rw [hx1]
      have vx2 : x2.val = pi.c2.val := by rw [hx2]
      have vx3 : x3.val = pi.c3.val := by rw [hx3]
      have vy0 : y0.val = qj.c0.val := by rw [hy0]
      have vy1 : y1.val = qj.c1.val := by rw [hy1]
      have vy2 : y2.val = qj.c2.val := by rw [hy2]
      have vy3 : y3.val = qj.c3.val := by rw [hy3]
      -- each word product is below `(P-1)^2 < 2^64`, so the `u64` multiplies succeed
      have bx0 : x0.val < P := by omega
      have bx1 : x1.val < P := by omega
      have bx2 : x2.val < P := by omega
      have bx3 : x3.val < P := by omega
      have by0 : y0.val < P := by omega
      have by1 : y1.val < P := by omega
      have by2 : y2.val < P := by omega
      have by3 : y3.val < P := by omega
      -- lane 0: one product
      step as ⟨g1, hg1⟩; step as ⟨d1, hd1⟩
      have b1 : d1.val = g1.val := by simp [hd1]
      step as ⟨s1, hs1⟩
      -- lane 1: two products
      step as ⟨g2, hg2⟩; step as ⟨d2, hd2⟩
      have b2 : d2.val = g2.val := by simp [hd2]
      step as ⟨s2, hs2⟩
      step as ⟨g3, hg3⟩; step as ⟨d3, hd3⟩
      have b3 : d3.val = g3.val := by simp [hd3]
      step as ⟨s3, hs3⟩
      -- lane 2: three products
      step as ⟨g4, hg4⟩; step as ⟨d4, hd4⟩
      have b4 : d4.val = g4.val := by simp [hd4]
      step as ⟨s4, hs4⟩
      step as ⟨g5, hg5⟩; step as ⟨d5, hd5⟩
      have b5 : d5.val = g5.val := by simp [hd5]
      step as ⟨s5, hs5⟩
      step as ⟨g6, hg6⟩; step as ⟨d6, hd6⟩
      have b6 : d6.val = g6.val := by simp [hd6]
      step as ⟨s6, hs6⟩
      -- lane 3: four products, the widest
      step as ⟨g7, hg7⟩; step as ⟨d7, hd7⟩
      have b7 : d7.val = g7.val := by simp [hd7]
      step as ⟨s7, hs7⟩
      step as ⟨g8, hg8⟩; step as ⟨d8, hd8⟩
      have b8 : d8.val = g8.val := by simp [hd8]
      step as ⟨s8, hs8⟩
      step as ⟨g9, hg9⟩; step as ⟨d9, hd9⟩
      have b9 : d9.val = g9.val := by simp [hd9]
      step as ⟨s9, hs9⟩
      step as ⟨g10, hg10⟩; step as ⟨d10, hd10⟩
      have b10 : d10.val = g10.val := by simp [hd10]
      step as ⟨s10, hs10⟩
      -- lane 4: three products
      step as ⟨g11, hg11⟩; step as ⟨d11, hd11⟩
      have b11 : d11.val = g11.val := by simp [hd11]
      step as ⟨s11, hs11⟩
      step as ⟨g12, hg12⟩; step as ⟨d12, hd12⟩
      have b12 : d12.val = g12.val := by simp [hd12]
      step as ⟨s12, hs12⟩
      step as ⟨g13, hg13⟩; step as ⟨d13, hd13⟩
      have b13 : d13.val = g13.val := by simp [hd13]
      step as ⟨s13, hs13⟩
      -- lane 5: two products
      step as ⟨g14, hg14⟩; step as ⟨d14, hd14⟩
      have b14 : d14.val = g14.val := by simp [hd14]
      step as ⟨s14, hs14⟩
      step as ⟨g15, hg15⟩; step as ⟨d15, hd15⟩
      have b15 : d15.val = g15.val := by simp [hd15]
      step as ⟨s15, hs15⟩
      -- lane 6: one product
      step as ⟨g16, hg16⟩; step as ⟨d16, hd16⟩
      have b16 : d16.val = g16.val := by simp [hd16]
      step as ⟨s16, hs16⟩
      -- the index
      have hmlt : m.val + 1 ≤ Std.Usize.max := by scalar_tac
      step as ⟨mm, hmm⟩
      -- the pair just folded in is exactly the `lanes_succ` increment
      have hgetp : lhs.val.getD m.val cpoly.field.Ext4.ZERO = pi := by
        rw [List.getD_eq_getElem _ _ hmlhs]; exact hpi.symm
      have hgetq : rhs.val.getD (k.val - m.val) cpoly.field.Ext4.ZERO = qj := by
        rw [← hj, List.getD_eq_getElem _ _ hjb]; exact hqj.symm
      have hsucc : ∀ l, lanes lhs.val rhs.val k.val lo (m.val + 1) l
          = lanes lhs.val rhs.val k.val lo m.val l + lanePair pi qj l := by
        intro l
        rw [lanes_succ lhs.val rhs.val k.val lo m.val l hm0, hgetp, hgetq]
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      simp only [LaneVal, hmm, hsucc, lanePair]
      simp only [← vx0, ← vx1, ← vx2, ← vx3, ← vy0, ← vy1, ← vy2, ← vy3]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · rw [if_neg hle]
      simp only [spec_ok]
      have hmeq : m.val = hi.val + 1 := by scalar_tac
      rw [← hmeq]
      exact hLV1
  · exact ⟨hi0, hi1, hLV⟩

/-! Helpers for `conv_delayed_loop_spec`. -/

/-- `toRawS` read as a zero-padded word lookup — the shape `lanes`/`lanePair`
index with. -/
private theorem conv_delayed_loop_spec_aux_getD (s : Slice cpoly.field.Ext4) (k : ℕ) :
    (toRawS s).coeff k = toExt (s.val.getD k cpoly.field.Ext4.ZERO) := by
  by_cases h : k < s.val.length
  · rw [toRawS_coeff_of_lt s h, List.getD_eq_getElem _ _ h]
  · rw [toRawS_coeff_of_ge s (by omega), List.getD_eq_default _ _ (by omega), toExt_ZERO]

/-- `Ext.coeff` commutes with finite sums (it is `Ext.coeff_add`/`coeff_zero`
lifted over `Finset.sum`). -/
private theorem conv_delayed_loop_spec_aux_coeff_sum (S : Finset ℕ) (f : ℕ → F)
    (i : Fin Hachi.ext4Params.d) :
    Ext.coeff (∑ x ∈ S, f x) i = ∑ x ∈ S, Ext.coeff (f x) i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a S' ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.coeff_add, ih]

/-- Past `np + nq - 1` the pair range is empty, so the reference product has no
coefficient there. -/
private theorem conv_delayed_loop_spec_aux_zero (lhs rhs : Slice cpoly.field.Ext4)
    (hppos : 0 < lhs.val.length) (hqpos : 0 < rhs.val.length) (j : ℕ)
    (hj : lhs.val.length + rhs.val.length ≤ j + 1) :
    (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff j = 0 := by
  rw [← sum_Ico_eq_mul_coeff lhs rhs j _ _ hppos rfl rfl,
    if_pos (by omega : rhs.val.length ≤ j),
    if_neg (by omega : ¬ j < lhs.val.length),
    Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- The lane calculus meets the reference product: coefficient `i` of
`(p * q).coeff k` is what the base case's fold builds out of the lanes. -/
private theorem conv_delayed_loop_spec_aux_coeff (lhs rhs : Slice cpoly.field.Ext4)
    (k lo hi : ℕ) (hppos : 0 < lhs.val.length)
    (hlo : lo = if rhs.val.length ≤ k then k - rhs.val.length + 1 else 0)
    (hhi : hi = if k < lhs.val.length then k else lhs.val.length - 1)
    (i : Fin Hachi.ext4Params.d) :
    Ext.coeff ((CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k) i
      = if i.val < 3
        then ((lanes lhs.val rhs.val k lo (hi + 1) i.val : ℕ) : K)
             + 2 * ((lanes lhs.val rhs.val k lo (hi + 1) (i.val + 4) : ℕ) : K)
        else ((lanes lhs.val rhs.val k lo (hi + 1) 3 : ℕ) : K) := by
  rw [← sum_Ico_eq_mul_coeff lhs rhs k lo hi hppos hlo hhi,
    conv_delayed_loop_spec_aux_coeff_sum]
  simp only [conv_delayed_loop_spec_aux_getD, toExt_mul_coeff]
  by_cases h3 : i.val < 3
  · simp only [if_pos h3]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [lanes, Nat.cast_sum]
  · simp only [if_neg h3]
    simp only [lanes, Nat.cast_sum]

/-- A `Vec::push` moves no coefficient below the old length and puts the new
element at it. -/
private theorem conv_delayed_loop_spec_aux_push (v w : alloc.vec.Vec cpoly.field.Ext4)
    (e : cpoly.field.Ext4) (hw : w.val = v.val ++ [e]) (j : ℕ) (hj : j ≤ v.val.length) :
    (toRaw w).coeff j = if j < v.val.length then (toRaw v).coeff j else toExt e := by
  have hwlen : w.val.length = v.val.length + 1 := by rw [hw]; simp
  rw [toRaw_coeff_of_lt w (by omega)]
  rcases Nat.lt_or_ge j v.val.length with hc | hc
  · rw [if_pos hc, toRaw_coeff_of_lt v hc]
    congr 1
    rw [getElem_of_list_eq hw (hi := by omega)]
    exact List.getElem_append_left hc
  · have hje : j = v.val.length := by omega
    rw [if_neg (by omega)]
    congr 1
    rw [getElem_of_list_eq hw (hi := by omega)]
    rw [List.getElem_append_right (by omega)]
    simp [hje]

/-- The output loop: it pushes one finished coefficient per turn, so the
invariant is `out.val.length = k` together with the coefficients below `k`
already agreeing with the reference product.  Everything the lane loop computed
is consumed here — the `Y^4` fold, the four `reduce_u128`s and the `Ext4::new`
all live in this body. -/
theorem conv_delayed_loop_spec (lhs rhs : Slice cpoly.field.Ext4)
    (np nq np_last nout : Std.Usize)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs)
    (hnp : np.val = lhs.val.length) (hnq : nq.val = rhs.val.length)
    (hppos : 0 < lhs.val.length) (hqpos : 0 < rhs.val.length)
    (hlast : np_last.val + 1 = np.val) (hnout : nout.val = np_last.val + nq.val)
    (hcap : min lhs.val.length rhs.val.length ≤ 2 ^ 61) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (k : Std.Usize),
      VecReduced out → k.val ≤ nout.val → out.val.length = k.val →
      (∀ j < k.val,
        (toRaw out).coeff j = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff j) →
      Poly.convDelayedLoop lhs rhs np nq np_last nout out k ⦃ z => VecReduced z ∧
        z.val.length = nout.val ∧
        ∀ j, (toRaw z).coeff j
          = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff j ⦄ := by
  intro out k hout hk hlenk hcf
  unfold Poly.convDelayedLoop
  rw [cpoly.univariate.conv_delayed_loop0]
  apply loop.spec_decr_nat (fun s => nout.val - s.2.val)
    (fun s => s.2.val ≤ nout.val ∧ VecReduced s.1 ∧ s.1.val.length = s.2.val ∧
      ∀ j < s.2.val, (toRaw s.1).coeff j
        = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff j)
  · rintro ⟨out1, k1⟩ hinv
    obtain ⟨hk1, hout1, hlen1, hcf1⟩ :
        k1.val ≤ nout.val ∧ VecReduced out1 ∧ out1.val.length = k1.val ∧
        (∀ j < k1.val, (toRaw out1).coeff j
          = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff j) := hinv
    simp only [cpoly.univariate.conv_delayed_loop0.body]
    by_cases hlt : k1 < nout
    · rw [if_pos hlt]
      have hklt : k1.val < nout.val := by scalar_tac
      -- `lo = if k ≥ nq then k - nq + 1 else 0`
      apply spec_bind (Pₘ := fun (lo : Std.Usize) =>
        lo.val = if nq.val ≤ k1.val then k1.val - nq.val + 1 else 0)
      · by_cases hc : k1 ≥ nq
        · rw [if_pos hc]
          have hcv : nq.val ≤ k1.val := by scalar_tac
          step as ⟨a, ha⟩
          step as ⟨b, hb⟩
          rw [if_pos hcv]; scalar_tac
        · rw [if_neg hc]
          simp only [spec_ok]
          rw [if_neg (by scalar_tac : ¬ nq.val ≤ k1.val)]
          simp
      intro lo hlo
      -- `hi = if k < np then k else np_last`
      apply spec_bind (Pₘ := fun (hiv : Std.Usize) =>
        hiv.val = if k1.val < np.val then k1.val else np_last.val)
      · by_cases hc : k1 < np
        · rw [if_pos hc]; simp only [spec_ok]
          rw [if_pos (by scalar_tac : k1.val < np.val)]
        · rw [if_neg hc]; simp only [spec_ok]
          rw [if_neg (by scalar_tac : ¬ k1.val < np.val)]
      intro hiv hhiv
      have hhik : hiv.val ≤ k1.val := by rw [hhiv]; split_ifs <;> omega
      have hhib : hiv.val < lhs.val.length := by rw [hhiv]; split_ifs <;> omega
      have hlob : k1.val - lo.val < rhs.val.length := by
        rw [hlo]; split_ifs <;> omega
      have hcapb : hiv.val + 1 - lo.val ≤ 2 ^ 61 := by
        have h2 : (2 : ℕ) ^ 61 = 2305843009213693952 := by norm_num
        have hcapn : min lhs.val.length rhs.val.length ≤ 2305843009213693952 := by
          rw [← h2]; exact hcap
        rw [h2, hhiv, hlo]; split_ifs <;> omega
      -- the lane loop
      apply spec_bind (conv_delayed_lane_loop_spec lhs rhs k1 hiv lo.val hl hr
        hhik hhib hlob hcapb 0#u128 0#u128 0#u128 0#u128 0#u128 0#u128 0#u128 lo
        (le_refl _) (by rw [hhiv, hlo]; split_ifs <;> omega) (by simp [LaneVal]))
      rintro ⟨t0, t1, t2, t3, t4, t5, t6⟩ hlane
      obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6⟩ :
          t0.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 0 ∧
          t1.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 1 ∧
          t2.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 2 ∧
          t3.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 3 ∧
          t4.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 4 ∧
          t5.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 5 ∧
          t6.val = lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) 6 := hlane
      have hfold : ∀ l : ℕ, lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) l
          + 2 * lanes lhs.val rhs.val k1.val lo.val (hiv.val + 1) (l + 4) < 2 ^ 128 :=
        fun l => lanes_fold_lt lhs.val rhs.val hl hr k1.val lo.val (hiv.val + 1) hcapb l
      have hd0 : t0.val + 2 * t4.val < 2 ^ 128 := by
        rw [ht0, ht4]; simpa using hfold 0
      have hd1 : t1.val + 2 * t5.val < 2 ^ 128 := by
        rw [ht1, ht5]; simpa using hfold 1
      have hd2 : t2.val + 2 * t6.val < 2 ^ 128 := by
        rw [ht2, ht6]; simpa using hfold 2
      -- the `Y^4 = W = 2` fold, as three doublings
      step as ⟨u4, hu4⟩
      step as ⟨c0, hc0⟩
      step as ⟨u5, hu5⟩
      step as ⟨c1, hc1⟩
      step as ⟨u6, hu6⟩
      step as ⟨c2, hc2⟩
      apply spec_bind (reduce_u128_spec c0); rintro g0 ⟨hg0R, hg0K⟩
      apply spec_bind (reduce_u128_spec c1); rintro g1 ⟨hg1R, hg1K⟩
      apply spec_bind (reduce_u128_spec c2); rintro g2 ⟨hg2R, hg2K⟩
      apply spec_bind (reduce_u128_spec t3); rintro g3 ⟨hg3R, hg3K⟩
      have hlo' : lo.val
          = if rhs.val.length ≤ k1.val then k1.val - rhs.val.length + 1 else 0 := by
        rw [hlo, hnq]
      have hhi' : hiv.val
          = if k1.val < lhs.val.length then k1.val else lhs.val.length - 1 := by
        rw [hhiv, hnp, show np_last.val = lhs.val.length - 1 by omega]
      apply spec_bind (Pₘ := fun e => Reduced e ∧
        toExt e = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k1.val)
      · rw [cpoly.field.Ext4.new]
        simp only [spec_ok]
        refine ⟨⟨hg0R, hg1R, hg2R, hg3R⟩, ?_⟩
        apply Ext.ext
        intro i
        rw [conv_delayed_loop_spec_aux_coeff lhs rhs k1.val lo.val hiv.val hppos hlo' hhi' i,
          coeff_toExt]
        rcases fin_four_cases i with h | h | h | h <;> rw [h]
        · rw [if_pos (by omega : (0 : ℕ) < 3), show (0 : ℕ) + 4 = 4 by norm_num]
          show toK g0 = _
          rw [hg0K, hc0, hu4, ht0, ht4]
          push_cast; ring
        · rw [if_pos (by omega : (1 : ℕ) < 3), show (1 : ℕ) + 4 = 5 by norm_num]
          show toK g1 = _
          rw [hg1K, hc1, hu5, ht1, ht5]
          push_cast; ring
        · rw [if_pos (by omega : (2 : ℕ) < 3), show (2 : ℕ) + 4 = 6 by norm_num]
          show toK g2 = _
          rw [hg2K, hc2, hu6, ht2, ht6]
          push_cast; ring
        · rw [if_neg (by omega : ¬ (3 : ℕ) < 3)]
          show toK g3 = _
          rw [hg3K, ht3]
      rintro e ⟨heR, heC⟩
      step as ⟨out2, hout2⟩
      step as ⟨k2, hk2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro u hu
        rw [hout2] at hu
        rcases List.mem_append.mp hu with hh | hh
        · exact hout1 u hh
        · rw [List.mem_singleton.mp hh]; exact heR
      · rw [hout2]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro j hj
        rw [conv_delayed_loop_spec_aux_push out1 out2 e hout2 j (by omega)]
        by_cases hjc : j < out1.val.length
        · rw [if_pos hjc]; exact hcf1 j (by omega)
        · rw [if_neg hjc, show j = k1.val by omega]
          exact heC
      · omega
    · rw [if_neg hlt]
      have hkeq : k1.val = nout.val := by scalar_tac
      refine ⟨hout1, by omega, ?_⟩
      intro j
      rcases Nat.lt_or_ge j k1.val with hjc | hjc
      · exact hcf1 j hjc
      · rw [toRaw_coeff_of_ge out1 (by omega),
          conv_delayed_loop_spec_aux_zero lhs rhs hppos hqpos j (by omega)]
  · exact ⟨hk, hout, hlenk, hcf⟩

/-- `Poly.convDelayed` ↔ `CPolynomial.Raw.mul`, coefficient-wise and untrimmed.

Two hypotheses beyond the representation invariants, both earned:

* `hlen` is the checked `usize` `np_last + nq` that sizes the output.  It is
  what `mul_spec` propagates; the minimal form of the fail point is
  `np + nq - 1 ≤ Usize.max`, one less.
* `hcap` is the `u128` headroom of the lanes (`lanes_fold_lt`), and it is not
  derivable.  `Usize.max` is platform-dependent (`Usize.bounds_eq` leaves both
  branches open), and `Slice` bounds only `length ≤ Usize.max`.  On the 64-bit
  branch the model admits `min np nq = 2^62`, and with every word at `P - 1`
  the fold `c0 = t0 + 2 t4` reaches `7 * 2^62 * (P-1)^2 > 2^128` and the
  checked add fails — so the triple needs the hypothesis.  On a 32-bit `Usize`
  it follows from the slice length alone and is vacuous; it is stated
  unconditionally because it has to hold on both.  No `Vec<Ext4>` can be that
  long in reality — 32 bytes an element against an `isize::MAX`-byte capacity
  caps it near `2^59` — but the model does not know that, and
  `Poly.karatsuba` discharges it from `KARATSUBA_CUTOFF` rather than passing
  it on.

`hppos`/`hqpos` are not fail points: they pin the *length* clause, which the
early return makes `0` rather than `np + nq - 1` when either side is empty.
Every call site (`Poly.karatsuba`, itself called only under `Mul`'s two
emptiness guards) has them. -/
theorem conv_delayed_spec (lhs rhs : Slice cpoly.field.Ext4)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs)
    (hppos : 0 < lhs.val.length) (hqpos : 0 < rhs.val.length)
    (hlen : lhs.val.length + rhs.val.length ≤ Std.Usize.max)
    (hcap : min lhs.val.length rhs.val.length ≤ 2 ^ 61) :
    Poly.convDelayed lhs rhs ⦃ z => VecReduced z ∧
      z.val.length + 1 = lhs.val.length + rhs.val.length ∧
      ∀ k, (toRaw z).coeff k
        = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k ⦄ := by
  have hnpv : (Slice.len lhs).val = lhs.val.length := Slice.len_val lhs
  have hnqv : (Slice.len rhs).val = rhs.val.length := Slice.len_val rhs
  unfold Poly.convDelayed
  rw [cpoly.univariate.conv_delayed]
  -- `np`/`nq` are pure `let`s; zeta-reduce them so the two early-return guards
  -- become syntactic `if`s on `Slice.len`.
  simp only []
  -- `hppos`/`hqpos` kill both early returns, so the length clause is the real
  -- `np + nq - 1` and not the `0` the empty case would give.
  rw [if_neg (show ¬ (Slice.len lhs = 0#usize) by scalar_tac),
      if_neg (show ¬ (Slice.len rhs = 0#usize) by scalar_tac)]
  -- the two checked `usize` operations that size the output: `np - 1` (guarded
  -- by `hppos`) and `np_last + nq` (guarded by `hlen`).
  step as ⟨np_last, hnp_last⟩
  step as ⟨nout, hnout⟩
  -- the output loop, entered at `k = 0` with the empty accumulator
  -- (`Vec::with_capacity` is `Vec::new` in the model): the invariant's three
  -- entry conditions are `[] `'s reducedness, `0 ≤ nout` and `|[]| = 0`, and the
  -- coefficient family below `k = 0` is vacuous.
  apply spec_mono (conv_delayed_loop_spec lhs rhs (Slice.len lhs) (Slice.len rhs) np_last nout
    hl hr hnpv hnqv hppos hqpos (by omega) hnout hcap
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 nout) 0#usize
    (by intro u hu; simp [alloc.vec.Vec.with_capacity] at hu)
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro j hj; simp at hj))
  rintro z ⟨hzred, hzlen, hzc⟩
  -- `nout = (np - 1) + nq`, so the loop's `|z| = nout` is the stated
  -- `|z| + 1 = np + nq` once `hppos` rules out the truncating subtraction.
  exact ⟨hzred, by omega, hzc⟩

/-! #### `add_slices`

The `p0 + p1` halves of the Karatsuba split.  Structurally this is
`add_untrimmed` on slices, so the statement is `add_raw_spec`'s with `toRawS`
in place of `toRaw`, and the loop invariant is the same prefix `List.range`. -/

theorem add_slices_loop_spec (lhs rhs : Slice cpoly.field.Ext4) (na nb nout : Std.Usize)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs)
    (hna : na.val = lhs.val.length) (hnb : nb.val = rhs.val.length)
    (hnout : nout.val = max lhs.val.length rhs.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ nout.val → VecReduced out →
      out.val.map toExt
        = (List.range i.val).map (fun k => (toRawS lhs).coeff k + (toRawS rhs).coeff k) →
      Poly.addSlicesLoop lhs rhs na nb nout out i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range nout.val).map
              (fun k => (toRawS lhs).coeff k + (toRawS rhs).coeff k) ⦄ := by
  intro out i hi hout hrel
  rw [Poly.addSlicesLoop, cpoly.univariate.add_slices_loop]
  apply loop.spec_decr_nat (fun s => nout.val - s.2.val)
    (fun s => s.2.val ≤ nout.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt
        = (List.range s.2.val).map (fun k => (toRawS lhs).coeff k + (toRawS rhs).coeff k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.univariate.add_slices_loop.body]
    by_cases hlt : i1 < nout
    · rw [if_pos hlt]
      have hr1len : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      apply spec_bind (padded_read_slice_spec lhs na i1 hna hl); rintro a ⟨haR, haF⟩
      apply spec_bind (padded_read_slice_spec rhs nb i1 hnb hr); rintro b ⟨hbR, hbF⟩
      step as ⟨s, hsR, hsF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact hsR
      · rw [hr2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hsF, haF, hbF]
      · have hlt2 : i1.val < nout.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = nout.val := by scalar_tac
      refine ⟨hr1, ?_⟩
      rw [← heq]; simpa using hrel1
  · exact ⟨hi, hout, hrel⟩

/-- `Poly.addSlices` ↔ `CPolynomial.Raw.addRaw`.  The explicit length clause
earns its place: `addRaw`'s size is `max` of the two sizes, and the Karatsuba
recombination reasons about `|ps| = np - m` directly. -/
theorem add_slices_spec (lhs rhs : Slice cpoly.field.Ext4)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs) :
    Poly.addSlices lhs rhs ⦃ z => VecReduced z ∧
      z.val.length = max lhs.val.length rhs.val.length ∧
      toRaw z = CPolynomial.Raw.addRaw (toRawS lhs) (toRawS rhs) ⦄ := by
  unfold Poly.addSlices
  rw [cpoly.univariate.add_slices]
  apply spec_bind (Pₘ := fun nn : Std.Usize => nn.val = max lhs.val.length rhs.val.length)
  · by_cases hc : Slice.len lhs ≥ Slice.len rhs
    · rw [if_pos hc]; simp only [spec_ok]; scalar_tac
    · rw [if_neg hc]; simp only [spec_ok]; scalar_tac
  · intro nn hnn
    apply spec_mono (add_slices_loop_spec lhs rhs (Slice.len lhs) (Slice.len rhs) nn
      hl hr (by simp) (by simp) hnn
      (alloc.vec.Vec.with_capacity cpoly.field.Ext4 nn) 0#usize (by simp)
      (by intro u hu; simp [alloc.vec.Vec.with_capacity] at hu)
      (by simp [alloc.vec.Vec.with_capacity]))
    rintro z ⟨hzred, hzmap⟩
    have hzlen : z.val.length = nn.val := by
      have := congrArg List.length hzmap; simpa using this
    refine ⟨hzred, by rw [hzlen, hnn], ?_⟩
    apply Array.ext
    · rw [CPolynomial.Raw.add_size]
      simp only [toRaw]
      simp [hzlen, hnn]
    · intro i hi hi2
      rw [CPolynomial.Raw.add_coeff hi2]
      simp only [toRaw, List.getElem_toArray]
      rw [getElem_of_list_eq hzmap, List.getElem_map, List.getElem_range]

/-! #### The Karatsuba recombination loops

Four in-place loops over pre-sized buffers, so each is stated pointwise on
coefficients against the buffer it was handed — the `mul_inner_loop_spec` mould,
not the prefix-`take` one.  `Poly.karatsubaLowLoop` *assigns* and the other two
output loops *accumulate*, and they run in that order, which is what lets the
low loop write `[0, n0)` and the mid loop then add into `[m, m + n1)` across the
overlap `[m, n0)`. -/

/-- `toRaw` of a single-slot write: the written slot takes the new value, every
other coefficient is unchanged.  This is the only thing the three in-place
recombination loops need to know about `Vec.set`. -/
private theorem karatsuba_sub_loop_spec_aux (w : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (x : cpoly.field.Ext4) (hi : i.val < w.val.length) (j : ℕ) :
    (toRaw (alloc.vec.Vec.set w i x)).coeff j
      = if j = i.val then toExt x else (toRaw w).coeff j := by
  have hval : (alloc.vec.Vec.set w i x).val = w.val.set i.val x :=
    alloc.vec.Vec.set_val_eq w i x
  have hlen : (alloc.vec.Vec.set w i x).val.length = w.val.length := by
    rw [hval]; simp
  by_cases hj : j < w.val.length
  · have hjs : j < (alloc.vec.Vec.set w i x).val.length := by omega
    rw [toRaw_coeff_of_lt _ hjs]
    by_cases hji : j = i.val
    · rw [if_pos hji]
      congr 1
      rw [getElem_of_list_eq hval]
      subst hji
      simp
    · rw [if_neg hji, toRaw_coeff_of_lt _ hj]
      congr 1
      rw [getElem_of_list_eq hval, List.getElem_set_ne (by omega)]
  · rw [toRaw_coeff_of_ge _ (by omega), if_neg (by omega),
      toRaw_coeff_of_ge _ (by omega)]

/-- `z1 := zm - z0 - z2`, in place.  Stated relative to the vector the loop was
handed: below `k` the slots are already updated, at and above `k` they still
hold `zm`.  The `if k < n0` / `if k < n2` guards in the body are exactly
`(toRaw z0).coeff j = 0` / `(toRaw z2).coeff j = 0` past the ends, so the
subtraction can be written unconditionally on the reference side. -/
theorem karatsuba_sub_loop_spec (z0 z2 : alloc.vec.Vec cpoly.field.Ext4)
    (n0 n1 n2 : Std.Usize)
    (h0 : VecReduced z0) (h2 : VecReduced z2)
    (hn0 : n0.val = z0.val.length) (hn2 : n2.val = z2.val.length) :
    ∀ (z1 : alloc.vec.Vec cpoly.field.Ext4) (k : Std.Usize),
      VecReduced z1 → n1.val = z1.val.length → k.val ≤ n1.val →
      Poly.karatsubaSubLoop z0 z2 z1 n0 n1 n2 k ⦃ w => VecReduced w ∧
        w.val.length = z1.val.length ∧
        ∀ j, (toRaw w).coeff j
          = if k.val ≤ j ∧ j < n1.val
              then (toRaw z1).coeff j - (toRaw z0).coeff j - (toRaw z2).coeff j
              else (toRaw z1).coeff j ⦄ := by
  intro z1 k hz1 hn1 hk
  unfold Poly.karatsubaSubLoop
  rw [cpoly.univariate.mul_karatsuba_loop0]
  apply loop.spec_decr_nat (fun s => n1.val - s.2.val)
    (fun s => k.val ≤ s.2.val ∧ s.2.val ≤ n1.val ∧ VecReduced s.1 ∧
      s.1.val.length = z1.val.length ∧
      ∀ j, (toRaw s.1).coeff j
        = if k.val ≤ j ∧ j < s.2.val
            then (toRaw z1).coeff j - (toRaw z0).coeff j - (toRaw z2).coeff j
            else (toRaw z1).coeff j)
  · rintro ⟨w, k'⟩ hinv
    obtain ⟨hkk, hk'n, hwR, hwlen, hwc⟩ :
      k.val ≤ k'.val ∧ k'.val ≤ n1.val ∧ VecReduced w ∧
        w.val.length = z1.val.length ∧
        (∀ j, (toRaw w).coeff j
          = if k.val ≤ j ∧ j < k'.val
              then (toRaw z1).coeff j - (toRaw z0).coeff j - (toRaw z2).coeff j
              else (toRaw z1).coeff j) := hinv
    simp only [cpoly.univariate.mul_karatsuba_loop0.body]
    by_cases hlt : k' < n1
    · rw [if_pos hlt]
      have hkn : k'.val < n1.val := by scalar_tac
      have hkw : k'.val < w.val.length := by omega
      step as ⟨v, hv⟩
      have hvR : Reduced v := hv ▸ hwR _ (List.getElem_mem hkw)
      have hvc : toExt v = (toRaw z1).coeff k'.val := by
        rw [hv, ← toRaw_coeff_of_lt w hkw, hwc k'.val, if_neg (by omega)]
      apply spec_bind (Pₘ := fun a : cpoly.field.Ext4 =>
        Reduced a ∧ toExt a = (toRaw z1).coeff k'.val - (toRaw z0).coeff k'.val)
      · by_cases hc0 : k' < n0
        · rw [if_pos hc0]
          have hb0 : k'.val < z0.val.length := by scalar_tac
          step as ⟨e, he⟩
          have heR : Reduced e := he ▸ h0 _ (List.getElem_mem hb0)
          step as ⟨d, hdR, hdF⟩
          exact ⟨hdR, by rw [hdF, hvc, he, toRaw_coeff_of_lt z0 hb0]⟩
        · rw [if_neg hc0]
          simp only [spec_ok]
          refine ⟨hvR, ?_⟩
          rw [hvc, toRaw_coeff_of_ge z0 (by scalar_tac), sub_zero]
      · rintro v1 ⟨hv1R, hv1F⟩
        apply spec_bind (Pₘ := fun a : cpoly.field.Ext4 =>
          Reduced a ∧ toExt a = (toRaw z1).coeff k'.val - (toRaw z0).coeff k'.val
            - (toRaw z2).coeff k'.val)
        · by_cases hc2 : k' < n2
          · rw [if_pos hc2]
            have hb2 : k'.val < z2.val.length := by scalar_tac
            step as ⟨e, he⟩
            have heR : Reduced e := he ▸ h2 _ (List.getElem_mem hb2)
            step as ⟨d, hdR, hdF⟩
            exact ⟨hdR, by rw [hdF, hv1F, he, toRaw_coeff_of_lt z2 hb2]⟩
          · rw [if_neg hc2]
            simp only [spec_ok]
            refine ⟨hv1R, ?_⟩
            rw [hv1F, toRaw_coeff_of_ge z2 (by scalar_tac), sub_zero]
        · rintro v2 ⟨hv2R, hv2F⟩
          step as ⟨x, back, hx, hback⟩
          step as ⟨k2, hk2⟩
          subst hback
          refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_, ?_⟩
          · -- the write keeps every slot reduced
            intro u hu
            rw [alloc.vec.Vec.set_val_eq] at hu
            rcases List.mem_or_eq_of_mem_set hu with h | h
            · exact hwR u h
            · exact h ▸ hv2R
          · rw [alloc.vec.Vec.set_val_eq]; simpa using hwlen
          · -- the coefficient family extends by the slot just written
            intro j
            rw [karatsuba_sub_loop_spec_aux w k' v2 hkw j]
            by_cases hj : j = k'.val
            · rw [if_pos hj, hj, if_pos (by omega), hv2F]
            · rw [if_neg hj, hwc j]
              by_cases hjk : k.val ≤ j ∧ j < k'.val
              · rw [if_pos hjk, if_pos (by omega)]
              · rw [if_neg hjk, if_neg (by omega)]
          · omega
    · rw [if_neg hlt]
      simp only [spec_ok]
      have heq : k'.val = n1.val := by scalar_tac
      exact ⟨hwR, hwlen, by rw [← heq]; exact hwc⟩
  · have hinit : ∀ j, (toRaw z1).coeff j
        = if k.val ≤ j ∧ j < k.val
            then (toRaw z1).coeff j - (toRaw z0).coeff j - (toRaw z2).coeff j
            else (toRaw z1).coeff j := fun j => by rw [if_neg (by omega)]
    exact ⟨le_refl _, hk, hz1, rfl, hinit⟩

/-- Writing one slot of a `Vec Ext4` moves exactly one coefficient: this is the
`toRaw` image of `List.set`, and it is what every in-place recombination loop
needs at its `index_mut` write-back. -/
private theorem karatsuba_low_loop_spec_aux (v w : alloc.vec.Vec cpoly.field.Ext4)
    (i : ℕ) (x : cpoly.field.Ext4) (hw : w.val = v.val.set i x) (hi : i < v.val.length) (j : ℕ) :
    (toRaw w).coeff j = if j = i then toExt x else (toRaw v).coeff j := by
  have hlen : w.val.length = v.val.length := by rw [hw]; simp
  by_cases hj : j < v.val.length
  · rw [toRaw_coeff_of_lt w (by omega), toRaw_coeff_of_lt v hj]
    have hget : w.val[j]'(by omega) = if j = i then x else v.val[j]'hj := by
      simp only [hw, List.getElem_set]
      by_cases h : j = i
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hget]
    by_cases h : j = i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  · have hne : j ≠ i := by omega
    rw [if_neg hne, toRaw_coeff_of_ge w (by omega), toRaw_coeff_of_ge v (by omega)]

/-- Membership in a `List.set`: the entry is either one of the originals or the
written value.  Used to carry `VecReduced` across the write-back. -/
private theorem karatsuba_low_loop_spec_aux_mem {α : Type} (l : List α) (i : ℕ) (x u : α)
    (hu : u ∈ l.set i x) : u ∈ l ∨ u = x := by
  induction l generalizing i with
  | nil => simp at hu
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at hu
      rcases hu with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ n =>
      simp only [List.set_cons_succ, List.mem_cons] at hu
      rcases hu with h | h
      · exact Or.inl (h ▸ List.mem_cons_self ..)
      · rcases ih n h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

/-- `out[k] = z0[k]` for `k < n0`.  An assignment, not an accumulation, so the
slot's previous contents are irrelevant — which is only sound because this is
the first of the three output loops. -/
theorem karatsuba_low_loop_spec (z0 : alloc.vec.Vec cpoly.field.Ext4) (n0 : Std.Usize)
    (h0 : VecReduced z0) (hn0 : n0.val = z0.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (k0 : Std.Usize),
      VecReduced out → k0.val ≤ n0.val → n0.val ≤ out.val.length →
      Poly.karatsubaLowLoop z0 n0 out k0 ⦃ w => VecReduced w ∧
        w.val.length = out.val.length ∧
        ∀ j, (toRaw w).coeff j
          = if k0.val ≤ j ∧ j < n0.val then (toRaw z0).coeff j else (toRaw out).coeff j ⦄ := by
  intro out k0 hout hk0 hlen
  unfold Poly.karatsubaLowLoop
  rw [cpoly.univariate.mul_karatsuba_loop1]
  apply loop.spec_decr_nat (fun s => n0.val - s.2.val)
    (fun s => k0.val ≤ s.2.val ∧ s.2.val ≤ n0.val ∧ VecReduced s.1 ∧
      s.1.val.length = out.val.length ∧
      ∀ j, (toRaw s.1).coeff j
        = if k0.val ≤ j ∧ j < s.2.val then (toRaw z0).coeff j else (toRaw out).coeff j)
  · rintro ⟨out1, k1⟩ hinv
    obtain ⟨hk1lo, hk1hi, hout1, hlen1, hrel1⟩ :
      k0.val ≤ k1.val ∧ k1.val ≤ n0.val ∧ VecReduced out1 ∧
        out1.val.length = out.val.length ∧
        (∀ j, (toRaw out1).coeff j
          = if k0.val ≤ j ∧ j < k1.val then (toRaw z0).coeff j else (toRaw out).coeff j) := hinv
    simp only [cpoly.univariate.mul_karatsuba_loop1.body]
    by_cases hlt : k1 < n0
    · rw [if_pos hlt]
      have hltn : k1.val < n0.val := by scalar_tac
      have hb0 : k1.val < z0.val.length := by scalar_tac
      have hbout : k1.val < out1.val.length := by scalar_tac
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ h0 _ (List.getElem_mem hb0)
      have hez : toExt e = (toRaw z0).coeff k1.val := by
        rw [he, toRaw_coeff_of_lt z0 hb0]
      step as ⟨y, back, hy, hback⟩
      step as ⟨k2, hk2⟩
      have hset : (back e).val = out1.val.set k1.val e := by rw [hback]; simp
      refine ⟨by omega, by omega, ?_, ?_, ?_, by omega⟩
      · intro u hu
        rw [hset] at hu
        rcases karatsuba_low_loop_spec_aux_mem _ _ _ _ hu with h | h
        · exact hout1 u h
        · exact h ▸ hRe
      · rw [hset]; simp only [List.length_set]; exact hlen1
      · intro j
        rw [karatsuba_low_loop_spec_aux out1 (back e) k1.val e hset hbout j]
        by_cases hj : j = k1.val
        · rw [if_pos hj, hj, hez, if_pos (by omega)]
        · rw [if_neg hj, hrel1 j]
          by_cases hc : k0.val ≤ j ∧ j < k1.val
          · rw [if_pos hc, if_pos (by omega)]
          · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hlt]
      have heq : k1.val = n0.val := by scalar_tac
      exact ⟨hout1, hlen1, by rw [← heq]; exact hrel1⟩
  · show k0.val ≤ k0.val ∧ k0.val ≤ n0.val ∧ VecReduced out ∧
      out.val.length = out.val.length ∧
      ∀ j, (toRaw out).coeff j
        = if k0.val ≤ j ∧ j < k0.val then (toRaw z0).coeff j else (toRaw out).coeff j
    exact ⟨le_refl _, hk0, hout, rfl, fun j => by rw [if_neg (by omega)]⟩

/-- Writing one slot moves exactly one coefficient: `Vec.set` is `List.set` on
the words, and `toRaw` is a `map`, so the reference image changes at `i` and
nowhere else.  This is what the three recombination loops need at every step. -/
private theorem karatsuba_mid_loop_spec_aux (v : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (x : cpoly.field.Ext4) (hi : i.val < v.val.length) (j : ℕ) :
    (toRaw (alloc.vec.Vec.set v i x)).coeff j
      = if j = i.val then toExt x else (toRaw v).coeff j := by
  have hval : (alloc.vec.Vec.set v i x).val = v.val.set i.val x := rfl
  rw [toRaw_coeff, toRaw_coeff, hval, List.map_set,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hj : j = i.val
  · subst hj
    rw [if_pos rfl, List.getElem?_set_self (by simpa using hi)]
    simp
  · rw [if_neg hj, List.getElem?_set_ne (Ne.symm hj)]

/-- `out[k + m] += z1[k]` for `k < n1`.  `hbound` is the in-range condition for
the write, and it is also what discharges the checked `k1 + m`. -/
theorem karatsuba_mid_loop_spec (m : Std.Usize) (z1 : alloc.vec.Vec cpoly.field.Ext4)
    (n1 : Std.Usize) (h1 : VecReduced z1) (hn1 : n1.val = z1.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (k1 : Std.Usize),
      VecReduced out → k1.val ≤ n1.val → n1.val + m.val ≤ out.val.length →
      Poly.karatsubaMidLoop m z1 n1 out k1 ⦃ w => VecReduced w ∧
        w.val.length = out.val.length ∧
        ∀ j, (toRaw w).coeff j = (toRaw out).coeff j +
          (if k1.val + m.val ≤ j ∧ j < n1.val + m.val
            then (toRaw z1).coeff (j - m.val) else 0) ⦄ := by
  intro out k1 hout hk1 hbound
  unfold Poly.karatsubaMidLoop
  rw [cpoly.univariate.mul_karatsuba_loop2]
  apply loop.spec_decr_nat (fun s => n1.val - s.2.val)
    (fun s => k1.val ≤ s.2.val ∧ s.2.val ≤ n1.val ∧ VecReduced s.1 ∧
      s.1.val.length = out.val.length ∧
      ∀ j, (toRaw s.1).coeff j = (toRaw out).coeff j +
        (if k1.val + m.val ≤ j ∧ j < s.2.val + m.val
          then (toRaw z1).coeff (j - m.val) else 0))
  · rintro ⟨out1, i1⟩ hinv
    obtain ⟨hlo, hhi, hred, hlen, hrel⟩ :
        k1.val ≤ i1.val ∧ i1.val ≤ n1.val ∧ VecReduced out1 ∧
        out1.val.length = out.val.length ∧
        (∀ j, (toRaw out1).coeff j = (toRaw out).coeff j +
          (if k1.val + m.val ≤ j ∧ j < i1.val + m.val
            then (toRaw z1).coeff (j - m.val) else 0)) := hinv
    simp only [cpoly.univariate.mul_karatsuba_loop2.body]
    by_cases hlt : i1 < n1
    · rw [if_pos hlt]
      have hi1n : i1.val < n1.val := by scalar_tac
      have hom : out.val.length ≤ Std.Usize.max := out.property
      have hsum : i1.val + m.val < out.val.length := by omega
      -- the checked `t ← k1 + m`: `hbound` puts the slot it addresses inside
      -- `out`, and a `Vec`'s length is below `Usize.max`
      have ht0 : i1.val + m.val ≤ Std.Usize.max := by omega
      step as ⟨t, ht⟩
      have htb : t.val < out1.val.length := by omega
      have hzb : i1.val < z1.val.length := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hred _ (List.getElem_mem htb)
      have hEe : toExt e = (toRaw out1).coeff t.val := by
        rw [he, toRaw_coeff_of_lt out1 htb]
      step as ⟨e1, he1⟩
      have hRe1 : Reduced e1 := he1 ▸ h1 _ (List.getElem_mem hzb)
      have hEe1 : toExt e1 = (toRaw z1).coeff i1.val := by
        rw [he1, toRaw_coeff_of_lt z1 hzb]
      step as ⟨e2, hRe2, hEe2⟩
      step as ⟨u, back, hu, hback⟩
      step as ⟨k11, hk11⟩
      subst hback
      have hsv : (alloc.vec.Vec.set out1 t e2).val = out1.val.set t.val e2 := rfl
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · -- the invariant's `VecReduced`
        intro w hw
        rw [hsv] at hw
        rcases List.mem_or_eq_of_mem_set hw with h | h
        · exact hred w h
        · exact h ▸ hRe2
      · -- the length is untouched by a write
        rw [hsv, List.length_set]; exact hlen
      · -- one more coefficient of `z1` has landed, at offset `m`
        have hEe2' : toExt e2 = (toRaw out).coeff t.val + (toRaw z1).coeff i1.val := by
          rw [hEe2, hEe, hEe1, hrel t.val, if_neg (by omega), add_zero]
        intro j
        rw [karatsuba_mid_loop_spec_aux out1 t e2 htb j]
        by_cases hj : j = t.val
        · rw [if_pos hj, hEe2', hj,
            if_pos (show k1.val + m.val ≤ t.val ∧ t.val < k11.val + m.val by omega),
            show t.val - m.val = i1.val by omega]
        · rw [if_neg hj, hrel j]
          by_cases hc : k1.val + m.val ≤ j ∧ j < i1.val + m.val
          · rw [if_pos hc, if_pos (by omega)]
          · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hlt]
      have heq : i1.val = n1.val := by scalar_tac
      exact ⟨hred, hlen, by intro j; rw [hrel j, heq]⟩
  · refine ⟨le_refl _, hk1, hout, rfl, ?_⟩
    show ∀ j, (toRaw out).coeff j = (toRaw out).coeff j +
      (if k1.val + m.val ≤ j ∧ j < k1.val + m.val
        then (toRaw z1).coeff (j - m.val) else 0)
    intro j
    rw [if_neg (by omega), add_zero]

/-- Writing one slot moves exactly one coefficient: `toRaw` of `v.set t x`
agrees with `toRaw v` off `t` and is `toExt x` at `t`. -/
private theorem karatsuba_high_loop_spec_aux
    (o : alloc.vec.Vec cpoly.field.Ext4) (t : Std.Usize) (x : cpoly.field.Ext4)
    (ht : t.val < o.val.length) (j : ℕ) :
    (toRaw (alloc.vec.Vec.set o t x)).coeff j
      = if j = t.val then toExt x else (toRaw o).coeff j := by
  have hval : (alloc.vec.Vec.set o t x).val = o.val.set t.val x := rfl
  rw [toRaw_coeff, toRaw_coeff, hval, List.map_set]
  by_cases hj : j = t.val
  · subst hj
    rw [if_pos rfl, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_set_self (by simp; omega)]
  · rw [if_neg hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hj)]

/-- `out[k + 2m] += z2[k]` for `k < n2`.  The offset is built by two checked
adds (`i ← k2 + m`, `t ← i + m`), both covered by `hbound`. -/
theorem karatsuba_high_loop_spec (m : Std.Usize) (z2 : alloc.vec.Vec cpoly.field.Ext4)
    (n2 : Std.Usize) (h2 : VecReduced z2) (hn2 : n2.val = z2.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (k2 : Std.Usize),
      VecReduced out → k2.val ≤ n2.val → n2.val + m.val + m.val ≤ out.val.length →
      Poly.karatsubaHighLoop m z2 n2 out k2 ⦃ w => VecReduced w ∧
        w.val.length = out.val.length ∧
        ∀ j, (toRaw w).coeff j = (toRaw out).coeff j +
          (if k2.val + m.val + m.val ≤ j ∧ j < n2.val + m.val + m.val
            then (toRaw z2).coeff (j - m.val - m.val) else 0) ⦄ := by
  intro out k2 hout hk2 hbound
  have houtmax : out.val.length ≤ Std.Usize.max := alloc.vec.Vec.len_ineq out
  unfold Poly.karatsubaHighLoop
  rw [cpoly.univariate.mul_karatsuba_loop3]
  apply loop.spec_decr_nat (fun s => n2.val - s.2.val)
    (fun s => k2.val ≤ s.2.val ∧ s.2.val ≤ n2.val ∧ VecReduced s.1 ∧
      s.1.val.length = out.val.length ∧
      ∀ j, (toRaw s.1).coeff j = (toRaw out).coeff j +
        (if k2.val + m.val + m.val ≤ j ∧ j < s.2.val + m.val + m.val
          then (toRaw z2).coeff (j - m.val - m.val) else 0))
  · rintro ⟨o, k⟩ hinv
    obtain ⟨hk2k, hkn, hoR, hoLen, hoC⟩ :
        k2.val ≤ k.val ∧ k.val ≤ n2.val ∧ VecReduced o ∧
          o.val.length = out.val.length ∧
          (∀ j, (toRaw o).coeff j = (toRaw out).coeff j +
            (if k2.val + m.val + m.val ≤ j ∧ j < k.val + m.val + m.val
              then (toRaw z2).coeff (j - m.val - m.val) else 0)) := hinv
    simp only [cpoly.univariate.mul_karatsuba_loop3.body]
    by_cases hlt : k < n2
    · rw [if_pos hlt]
      have hkb : k.val < n2.val := by scalar_tac
      have hb1 : k.val + m.val ≤ Std.Usize.max := by omega
      step as ⟨i, hi⟩
      have hb2 : i.val + m.val ≤ Std.Usize.max := by omega
      step as ⟨t, ht⟩
      have htb : t.val < o.val.length := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hoR _ (List.getElem_mem htb)
      have hkz : k.val < z2.val.length := by omega
      step as ⟨e1, he1⟩
      have hRe1 : Reduced e1 := he1 ▸ h2 _ (List.getElem_mem hkz)
      step as ⟨e2, hRe2, hFe2⟩
      step as ⟨vv, back, hvv, hback⟩
      step as ⟨k1, hk1⟩
      subst hback
      have hcoe : toExt e = (toRaw o).coeff t.val := by
        rw [toRaw_coeff_of_lt o htb, he]
      have hcz : toExt e1 = (toRaw z2).coeff k.val := by
        rw [toRaw_coeff_of_lt z2 hkz, he1]
      refine ⟨by omega, by omega, ?_, ?_, ?_, by omega⟩
      · -- the written slot keeps the invariant
        intro u hu
        simp only [alloc.vec.Vec.set_val_eq] at hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact hoR u h
        · exact h ▸ hRe2
      · -- a write does not change the length
        simpa using hoLen
      · -- one more coefficient of `z2` has landed
        intro j
        by_cases hj : j = t.val
        · subst hj
          rw [karatsuba_high_loop_spec_aux o t e2 htb t.val, if_pos rfl,
            if_pos (show k2.val + m.val + m.val ≤ t.val ∧ t.val < k1.val + m.val + m.val by omega),
            hFe2, hcoe, hcz, hoC t.val,
            if_neg (show ¬(k2.val + m.val + m.val ≤ t.val ∧ t.val < k.val + m.val + m.val) by omega),
            add_zero, show t.val - m.val - m.val = k.val by omega]
        · rw [karatsuba_high_loop_spec_aux o t e2 htb j, if_neg hj, hoC j]
          by_cases hc : k2.val + m.val + m.val ≤ j ∧ j < k.val + m.val + m.val
          · rw [if_pos hc,
              if_pos (show k2.val + m.val + m.val ≤ j ∧ j < k1.val + m.val + m.val by omega)]
          · rw [if_neg hc,
              if_neg (show ¬(k2.val + m.val + m.val ≤ j ∧ j < k1.val + m.val + m.val) by omega)]
    · rw [if_neg hlt]
      have heq : k.val = n2.val := by scalar_tac
      refine ⟨hoR, hoLen, ?_⟩
      rw [← heq]; exact hoC
  · exact (show k2.val ≤ k2.val ∧ k2.val ≤ n2.val ∧ VecReduced out ∧
        out.val.length = out.val.length ∧
        (∀ j, (toRaw out).coeff j = (toRaw out).coeff j +
          (if k2.val + m.val + m.val ≤ j ∧ j < k2.val + m.val + m.val
            then (toRaw z2).coeff (j - m.val - m.val) else 0))
      from ⟨le_refl _, hk2, hout, rfl, by
        intro j; rw [if_neg (by omega), add_zero]⟩)

/-! #### `mul_karatsuba` -/

/-! The pure-arithmetic core of the Karatsuba recombination, stated on
coefficient families `ℕ → F` so that no `Result` plumbing travels with it. -/

/-- Convolution of two coefficient families: `(A * B).coeff j`. -/
private def karatsuba_spec_aux_conv (a b : ℕ → F) (j : ℕ) : F :=
  ∑ i ∈ Finset.range (j + 1), a i * b (j - i)

private theorem karatsuba_spec_aux_conv_comm (a b : ℕ → F) (j : ℕ) :
    karatsuba_spec_aux_conv a b j = karatsuba_spec_aux_conv b a j := by
  unfold karatsuba_spec_aux_conv
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h2 : j - (j + 1 - 1 - i) = i := by omega
  have h1 : j + 1 - 1 - i = j - i := by omega
  rw [h2, h1, mul_comm]

/-- Splitting the *left* factor of a convolution at `m`. -/
private theorem karatsuba_spec_aux_split_left (a b a0 a1 : ℕ → F) (m : ℕ)
    (ha0 : ∀ i, a0 i = if i < m then a i else 0)
    (ha1 : ∀ i, a1 i = a (i + m)) (j : ℕ) :
    karatsuba_spec_aux_conv a b j = karatsuba_spec_aux_conv a0 b j + (if m ≤ j then karatsuba_spec_aux_conv a1 b (j - m) else 0) := by
  unfold karatsuba_spec_aux_conv
  by_cases h : m ≤ j
  · rw [if_pos h]
    have e1 : ∑ i ∈ Finset.range (j + 1), a0 i * b (j - i)
        = ∑ i ∈ Finset.Ico 0 m, a i * b (j - i) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive
        (fun i => a0 i * b (j - i)) (Nat.zero_le m) (show m ≤ j + 1 by omega)]
      have hz : ∑ i ∈ Finset.Ico m (j + 1), a0 i * b (j - i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_Ico] at hi
        rw [ha0, if_neg (by omega), zero_mul]
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [ha0, if_pos (by omega)]
    have e2 : ∑ i ∈ Finset.range (j - m + 1), a1 i * b (j - m - i)
        = ∑ i ∈ Finset.Ico m (j + 1), a i * b (j - i) := by
      rw [Finset.sum_Ico_eq_sum_range, show j + 1 - m = j - m + 1 by omega]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [ha1, show j - (m + i) = j - m - i by omega, show i + m = m + i by omega]
    rw [e1, e2, Finset.sum_Ico_consecutive
      (fun i => a i * b (j - i)) (Nat.zero_le m) (show m ≤ j + 1 by omega),
      ← Finset.range_eq_Ico]
  · rw [if_neg h, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [ha0, if_pos (by omega)]

/-- Splitting the *right* factor of a convolution at `m`. -/
private theorem karatsuba_spec_aux_split_right (a b b0 b1 : ℕ → F) (m : ℕ)
    (hb0 : ∀ i, b0 i = if i < m then b i else 0)
    (hb1 : ∀ i, b1 i = b (i + m)) (j : ℕ) :
    karatsuba_spec_aux_conv a b j = karatsuba_spec_aux_conv a b0 j + (if m ≤ j then karatsuba_spec_aux_conv a b1 (j - m) else 0) := by
  rw [karatsuba_spec_aux_conv_comm a b,
    karatsuba_spec_aux_split_left b a b0 b1 m hb0 hb1 j,
    karatsuba_spec_aux_conv_comm b0 a]
  by_cases h : m ≤ j
  · rw [if_pos h, if_pos h, karatsuba_spec_aux_conv_comm b1 a]
  · rw [if_neg h, if_neg h]

/-- The full Karatsuba split of a convolution. -/
private theorem karatsuba_spec_aux_split (a b a0 a1 b0 b1 : ℕ → F) (m : ℕ)
    (ha0 : ∀ i, a0 i = if i < m then a i else 0)
    (ha1 : ∀ i, a1 i = a (i + m))
    (hb0 : ∀ i, b0 i = if i < m then b i else 0)
    (hb1 : ∀ i, b1 i = b (i + m)) (j : ℕ) :
    karatsuba_spec_aux_conv a b j = karatsuba_spec_aux_conv a0 b0 j
      + (if m ≤ j then karatsuba_spec_aux_conv a0 b1 (j - m) + karatsuba_spec_aux_conv a1 b0 (j - m) else 0)
      + (if m + m ≤ j then karatsuba_spec_aux_conv a1 b1 (j - m - m) else 0) := by
  rw [karatsuba_spec_aux_split_left a b a0 a1 m ha0 ha1 j,
    karatsuba_spec_aux_split_right a0 b b0 b1 m hb0 hb1 j]
  by_cases h : m ≤ j
  · simp only [if_pos h]
    rw [karatsuba_spec_aux_split_right a1 b b0 b1 m hb0 hb1 (j - m)]
    by_cases h2 : m + m ≤ j
    · rw [if_pos h2, if_pos (show m ≤ j - m by omega)]
      ring
    · rw [if_neg h2, if_neg (show ¬ m ≤ j - m by omega)]
      ring
  · simp only [if_neg h, if_neg (show ¬ m + m ≤ j by omega), add_zero]

/-- The Karatsuba middle term: `zm - z0 - z2 = a0*b1 + a1*b0`. -/
private theorem karatsuba_spec_aux_middle (a0 a1 b0 b1 asum bsum : ℕ → F) (j : ℕ)
    (has : ∀ i, asum i = a0 i + a1 i) (hbs : ∀ i, bsum i = b0 i + b1 i) :
    karatsuba_spec_aux_conv asum bsum j - karatsuba_spec_aux_conv a0 b0 j - karatsuba_spec_aux_conv a1 b1 j = karatsuba_spec_aux_conv a0 b1 j + karatsuba_spec_aux_conv a1 b0 j := by
  have h : karatsuba_spec_aux_conv asum bsum j = karatsuba_spec_aux_conv a0 b0 j + karatsuba_spec_aux_conv a0 b1 j + (karatsuba_spec_aux_conv a1 b0 j + karatsuba_spec_aux_conv a1 b1 j) := by
    unfold karatsuba_spec_aux_conv
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [has, hbs]
    ring
  rw [h]
  ring

/-- `CPolynomial.Raw.mul` *is* the convolution of the coefficient families. -/
private theorem karatsuba_spec_aux_mul_coeff (A B : CPolynomial.Raw F) (k : ℕ) :
    (CPolynomial.Raw.mul A B).coeff k = karatsuba_spec_aux_conv (fun i => A.coeff i) (fun i => B.coeff i) k := by
  have h : CPolynomial.Raw.mul A B = A * B := rfl
  rw [h, CPolynomial.Raw.mul_coeff]
  rfl

private theorem karatsuba_spec_aux_getD_take (l : List F) (n i : ℕ) :
    (l.take n).getD i (0 : F) = if i < n then l.getD i 0 else 0 := by
  by_cases h : i < n
  · rw [if_pos h]
    by_cases h2 : i < l.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h2]
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  · rw [if_neg h, List.getD_eq_default]
    simp; omega

private theorem karatsuba_spec_aux_getD_drop (l : List F) (n i : ℕ) :
    (l.drop n).getD i (0 : F) = l.getD (i + n) 0 := by
  by_cases h : i + n < l.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h]
    simp [Nat.add_comm]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- The low half of a split slice reads the low coefficients. -/
private theorem karatsuba_spec_aux_take_coeff (s t : Slice cpoly.field.Ext4) (m : ℕ)
    (ht : t.val = s.val.take m) (i : ℕ) :
    (toRawS t).coeff i = if i < m then (toRawS s).coeff i else 0 := by
  rw [toRawS_coeff, toRawS_coeff, ht, List.map_take, karatsuba_spec_aux_getD_take]

/-- The high half of a split slice reads the shifted coefficients. -/
private theorem karatsuba_spec_aux_drop_coeff (s t : Slice cpoly.field.Ext4) (m : ℕ)
    (ht : t.val = s.val.drop m) (i : ℕ) :
    (toRawS t).coeff i = (toRawS s).coeff (i + m) := by
  rw [toRawS_coeff, toRawS_coeff, ht, List.map_drop, karatsuba_spec_aux_getD_drop]

set_option maxHeartbeats 600000 in
/-- `Poly.karatsuba` ↔ `CPolynomial.Raw.mul`, coefficient-wise and untrimmed.

The recursion is on the *working width* `min np nq`, which strictly decreases:
`m = min np nq / 2`, so the three sub-products are taken at
`min m m = m` and `min (np - m) (nq - m) = min np nq - m`, both below `min np nq`
once it exceeds `KARATSUBA_CUTOFF = 16`.  That is also what discharges
`conv_delayed_spec`'s `hcap` at every leaf.

The length clause is exact, and — unlike the schoolbook champion's — it does
*not* pad to the working width: the output is sized `n2 + 2m`, and
`n2 = (np - m) + (nq - m) - 1` telescopes it to `np + nq - 1` at every level.
This is what keeps `mul_spec`'s hypothesis unchanged.

`hlen` is the checked `usize` arithmetic (`n2 + m`, `+ m`, and `np_last + nq` in
the base case); `hppos`/`hqpos` hold at every recursive call, since a split
under `nmin > 16` has `m ≥ 8` and `np - m ≥ m`.

`Poly.karatsuba` is self-recursive and extracts as a `partial_fixpoint`, so this
one is proved by strong induction on `lhs.val.length + rhs.val.length` (or on
`min`, which is what the code decreases) with the fixpoint's own unfolding
equation, not by `loop.spec_decr_nat`. -/
theorem karatsuba_spec (lhs rhs : Slice cpoly.field.Ext4)
    (hl : SliceReduced lhs) (hr : SliceReduced rhs)
    (hppos : 0 < lhs.val.length) (hqpos : 0 < rhs.val.length)
    (hlen : lhs.val.length + rhs.val.length ≤ Std.Usize.max) :
    Poly.karatsuba lhs rhs ⦃ z => VecReduced z ∧
      z.val.length + 1 = lhs.val.length + rhs.val.length ∧
      ∀ k, (toRaw z).coeff k
        = (CPolynomial.Raw.mul (toRawS lhs) (toRawS rhs)).coeff k ⦄ := by
  suffices h : ∀ (N : ℕ) (p q : Slice cpoly.field.Ext4),
      min p.val.length q.val.length ≤ N →
      SliceReduced p → SliceReduced q →
      0 < p.val.length → 0 < q.val.length →
      p.val.length + q.val.length ≤ Std.Usize.max →
      Poly.karatsuba p q ⦃ z => VecReduced z ∧
        z.val.length + 1 = p.val.length + q.val.length ∧
        ∀ k, (toRaw z).coeff k
          = (CPolynomial.Raw.mul (toRawS p) (toRawS q)).coeff k ⦄ by
    exact h _ lhs rhs (le_refl _) hl hr hppos hqpos hlen
  intro N
  induction N with
  | zero =>
    intro p q hmin _ _ hp hq _
    exfalso; omega
  | succ N ih =>
    intro p q hmin hp hq hppos' hqpos' hlen'
    unfold Poly.karatsuba
    rw [cpoly.univariate.mul_karatsuba.eq_def]
    apply spec_bind (Pₘ := fun nn : Std.Usize => nn.val = min p.val.length q.val.length)
    · by_cases hc : Slice.len p ≤ Slice.len q
      · rw [if_pos hc]; simp only [spec_ok]; scalar_tac
      · rw [if_neg hc]; simp only [spec_ok]; scalar_tac
    · intro nmin hnmin
      by_cases hcut : nmin ≤ Poly.karatsubaCutoff
      · rw [if_pos hcut]
        have hcap : min p.val.length q.val.length ≤ 2 ^ 61 := by
          have h16 : (cpoly.univariate.KARATSUBA_CUTOFF).val = 16 := by
            simp only [cpoly.univariate.KARATSUBA_CUTOFF]; decide
          have : nmin.val ≤ 16 := by
            unfold Poly.karatsubaCutoff at hcut
            have := hcut
            scalar_tac
          omega
        exact conv_delayed_spec p q hp hq hppos' hqpos' hlen' hcap
      · rw [if_neg hcut]
        have hcut16 : 16 < nmin.val := by
          have h16 : (cpoly.univariate.KARATSUBA_CUTOFF).val = 16 := by
            simp only [cpoly.univariate.KARATSUBA_CUTOFF]; decide
          unfold Poly.karatsubaCutoff at hcut
          scalar_tac
        step as ⟨half, hhalf⟩
        apply spec_bind (Pₘ := fun mm : Std.Usize => mm.val = nmin.val / 2)
        · rw [if_pos (show half ≤ nmin by scalar_tac)]
          simp only [spec_ok]; exact hhalf
        · intro m hm
          obtain ⟨hmpos, hmlt, hmp, hmq⟩ :
              0 < m.val ∧ m.val < nmin.val ∧
                m.val ≤ p.val.length ∧ m.val ≤ q.val.length := by omega
          step as ⟨p0, hp0val, hp0len⟩
          step as ⟨p1, hp1val, hp1len⟩
          step as ⟨q0, hq0val, hq0len⟩
          step as ⟨q1, hq1val, hq1len⟩
          have hp0take : p0.val = p.val.take m.val := by rw [hp0val, List.slice_zero_j]
          have hq0take : q0.val = q.val.take m.val := by rw [hq0val, List.slice_zero_j]
          have hp0L : p0.val.length = m.val := hp0len
          have hq0L : q0.val.length = m.val := hq0len
          have hp1L : p1.val.length = p.val.length - m.val := by rw [hp1val, List.length_drop]
          have hq1L : q1.val.length = q.val.length - m.val := by rw [hq1val, List.length_drop]
          have hp0red : SliceReduced p0 := by
            intro a ha; rw [hp0take] at ha; exact hp a (List.mem_of_mem_take ha)
          have hq0red : SliceReduced q0 := by
            intro a ha; rw [hq0take] at ha; exact hq a (List.mem_of_mem_take ha)
          have hp1red : SliceReduced p1 := by
            intro a ha; rw [hp1val] at ha; exact hp a (List.mem_of_mem_drop ha)
          have hq1red : SliceReduced q1 := by
            intro a ha; rw [hq1val] at ha; exact hq a (List.mem_of_mem_drop ha)
          obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8⟩ :
              min p0.val.length q0.val.length ≤ N ∧ 0 < p0.val.length ∧ 0 < q0.val.length ∧
              p0.val.length + q0.val.length ≤ Std.Usize.max ∧
              min p1.val.length q1.val.length ≤ N ∧ 0 < p1.val.length ∧ 0 < q1.val.length ∧
              p1.val.length + q1.val.length ≤ Std.Usize.max := by omega
          apply spec_bind (ih p0 q0 hk1 hp0red hq0red hk2 hk3 hk4)
          rintro z0 ⟨hz0red, hz0len, hz0coeff⟩
          apply spec_bind (ih p1 q1 hk5 hp1red hq1red hk6 hk7 hk8)
          rintro z2 ⟨hz2red, hz2len, hz2coeff⟩
          apply spec_bind (add_slices_spec p0 p1 hp0red hp1red)
          rintro ps ⟨hpsred, hpslen, hpsraw⟩
          apply spec_bind (add_slices_spec q0 q1 hq0red hq1red)
          rintro qs ⟨hqsred, hqslen, hqsraw⟩
          have hpsL : ps.val.length = p.val.length - m.val := by rw [hpslen, hp0L, hp1L]; omega
          have hqsL : qs.val.length = q.val.length - m.val := by rw [hqslen, hq0L, hq1L]; omega
          have hdpsL : (alloc.vec.Vec.deref ps).val.length = p.val.length - m.val := hpsL
          have hdqsL : (alloc.vec.Vec.deref qs).val.length = q.val.length - m.val := hqsL
          obtain ⟨hk9, hk10, hk11, hk12⟩ :
              min (alloc.vec.Vec.deref ps).val.length (alloc.vec.Vec.deref qs).val.length ≤ N ∧
              0 < (alloc.vec.Vec.deref ps).val.length ∧
              0 < (alloc.vec.Vec.deref qs).val.length ∧
              (alloc.vec.Vec.deref ps).val.length + (alloc.vec.Vec.deref qs).val.length
                ≤ Std.Usize.max := by omega
          apply spec_bind (ih (alloc.vec.Vec.deref ps) (alloc.vec.Vec.deref qs) hk9
            (sliceReduced_deref hpsred) (sliceReduced_deref hqsred) hk10 hk11 hk12)
          rintro z1 ⟨hz1red, hz1len, hz1coeff⟩
          rw [hp0L, hq0L] at hz0len
          rw [hp1L, hq1L] at hz2len
          rw [hdpsL, hdqsL] at hz1len
          have hmhalf : m.val + m.val ≤ nmin.val := by omega
          apply spec_bind (karatsuba_sub_loop_spec z0 z2 (alloc.vec.Vec.len z0)
            (alloc.vec.Vec.len z1) (alloc.vec.Vec.len z2) hz0red hz2red (by simp) (by simp)
            z1 0#usize hz1red (by simp) (by simp))
          rintro z11 ⟨hz11red, hz11len, hz11coeff⟩
          have hz2m : z2.val.length + m.val + m.val ≤ Std.Usize.max := by omega
          step as ⟨i, hi⟩
          step as ⟨i1, hi1⟩
          apply spec_bind (alloc.vec.from_elem_spec cpoly.field.Ext4.Insts.CoreCloneClone
            cpoly.field.Ext4.ZERO i1 (ext_clone_eq _))
          rintro out ⟨houtval, houtlen⟩
          have hlz0 : (alloc.vec.Vec.len z0).val = z0.val.length := by simp
          have hlz1 : (alloc.vec.Vec.len z1).val = z1.val.length := by simp
          have hlz2 : (alloc.vec.Vec.len z2).val = z2.val.length := by simp
          have houtL : out.val.length = z2.val.length + m.val + m.val := by
            have h : out.val.length = i1.val := houtlen
            omega
          have houtred : VecReduced out := by
            intro a ha; rw [houtval] at ha
            rw [List.eq_of_mem_replicate ha]; exact reduced_ZERO
          have houtzero : ∀ j, (toRaw out).coeff j = 0 := by
            intro j
            rw [toRaw_coeff, houtval, List.map_replicate, toExt_ZERO]
            by_cases hj : j < i1.val
            · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
            · rw [List.getD_eq_default _ _ (by simp; omega)]
          apply spec_bind (karatsuba_low_loop_spec z0 (alloc.vec.Vec.len z0) hz0red (by simp)
            out 0#usize houtred (by simp) (by omega))
          rintro out1 ⟨hout1red, hout1len, hout1coeff⟩
          apply spec_bind (karatsuba_mid_loop_spec m z11 (alloc.vec.Vec.len z1) hz11red
            (by simp [hz11len]) out1 0#usize hout1red (by simp) (by omega))
          rintro out2 ⟨hout2red, hout2len, hout2coeff⟩
          apply spec_mono (karatsuba_high_loop_spec m z2 (alloc.vec.Vec.len z2) hz2red (by simp)
            out2 0#usize hout2red (by simp) (by omega))
          rintro w ⟨hwred, hwlen, hwcoeff⟩
          have hzu : ((0#usize : Std.Usize)).val = 0 := rfl
          simp only [hzu, Nat.zero_le, true_and, Nat.zero_add, hlz0, hlz1, hlz2]
            at hz11coeff hout1coeff hout2coeff hwcoeff
          obtain ⟨hzlen0, hzlen2, hwfin⟩ :
              z0.val.length ≤ z1.val.length ∧ z2.val.length = z1.val.length ∧
              w.val.length + 1 = p.val.length + q.val.length := by omega
          refine ⟨hwred, hwfin, ?_⟩
          intro k
          -- the coefficient families of the four half-slices
          have hA0 : ∀ i, (toRawS p0).coeff i = if i < m.val then (toRawS p).coeff i else 0 :=
            karatsuba_spec_aux_take_coeff p p0 m.val hp0take
          have hA1 : ∀ i, (toRawS p1).coeff i = (toRawS p).coeff (i + m.val) :=
            karatsuba_spec_aux_drop_coeff p p1 m.val hp1val
          have hB0 : ∀ i, (toRawS q0).coeff i = if i < m.val then (toRawS q).coeff i else 0 :=
            karatsuba_spec_aux_take_coeff q q0 m.val hq0take
          have hB1 : ∀ i, (toRawS q1).coeff i = (toRawS q).coeff (i + m.val) :=
            karatsuba_spec_aux_drop_coeff q q1 m.val hq1val
          have hpsc : ∀ i, (toRaw ps).coeff i = (toRawS p0).coeff i + (toRawS p1).coeff i := by
            intro i; rw [hpsraw, CPolynomial.Raw.add_coeff?]
          have hqsc : ∀ i, (toRaw qs).coeff i = (toRawS q0).coeff i + (toRawS q1).coeff i := by
            intro i; rw [hqsraw, CPolynomial.Raw.add_coeff?]
          have hz0c : ∀ j, (toRaw z0).coeff j
              = karatsuba_spec_aux_conv (fun i => (toRawS p0).coeff i)
                  (fun i => (toRawS q0).coeff i) j := by
            intro j; rw [hz0coeff j, karatsuba_spec_aux_mul_coeff]
          have hz2c : ∀ j, (toRaw z2).coeff j
              = karatsuba_spec_aux_conv (fun i => (toRawS p1).coeff i)
                  (fun i => (toRawS q1).coeff i) j := by
            intro j; rw [hz2coeff j, karatsuba_spec_aux_mul_coeff]
          have hz1c : ∀ j, (toRaw z1).coeff j
              = karatsuba_spec_aux_conv (fun i => (toRaw ps).coeff i)
                  (fun i => (toRaw qs).coeff i) j := by
            intro j
            rw [hz1coeff j, toRawS_deref, toRawS_deref, karatsuba_spec_aux_mul_coeff]
          -- the three in-place loops, with their range guards discharged
          have hz11c : ∀ j, (toRaw z11).coeff j
              = (toRaw z1).coeff j - (toRaw z0).coeff j - (toRaw z2).coeff j := by
            intro j
            rw [hz11coeff j]
            split_ifs with hc
            · rfl
            · have hj : z1.val.length ≤ j := Nat.not_lt.mp hc
              rw [toRaw_coeff_of_ge z0 (Nat.le_trans hzlen0 hj),
                toRaw_coeff_of_ge z2 (show z2.val.length ≤ j by rw [hzlen2]; exact hj)]
              ring
          have hout1c : ∀ j, (toRaw out1).coeff j = (toRaw z0).coeff j := by
            intro j
            rw [hout1coeff j, houtzero j]
            split_ifs with hc
            · rfl
            · exact (toRaw_coeff_of_ge z0 (Nat.not_lt.mp hc)).symm
          have hout2c : ∀ j, (toRaw out2).coeff j
              = (toRaw z0).coeff j
                + (if m.val ≤ j then (toRaw z11).coeff (j - m.val) else 0) := by
            intro j
            rw [hout2coeff j, hout1c j]
            by_cases hmj : m.val ≤ j
            · rw [if_pos hmj]
              split_ifs with hcc
              · rfl
              · have hge : z1.val.length + m.val ≤ j := Nat.not_lt.mp (fun hx => hcc ⟨hmj, hx⟩)
                rw [toRaw_coeff_of_ge z11 (show z11.val.length ≤ j - m.val by
                  rw [hz11len]; exact Nat.le_sub_of_add_le hge)]
            · rw [if_neg hmj]
              split_ifs with hcc
              · exact absurd hcc.1 hmj
              · rfl
          have hwc : ∀ j, (toRaw w).coeff j
              = (toRaw out2).coeff j
                + (if m.val + m.val ≤ j then (toRaw z2).coeff (j - m.val - m.val) else 0) := by
            intro j
            rw [hwcoeff j]
            by_cases h1 : m.val + m.val ≤ j
            · rw [if_pos h1]
              split_ifs with hcc
              · rfl
              · have hge : z2.val.length + m.val + m.val ≤ j :=
                  Nat.not_lt.mp (fun hx => hcc ⟨h1, hx⟩)
                rw [toRaw_coeff_of_ge z2 (show z2.val.length ≤ j - m.val - m.val from
                  Nat.le_sub_of_add_le (Nat.le_sub_of_add_le hge))]
            · rw [if_neg h1]
              split_ifs with hcc
              · exact absurd hcc.1 h1
              · rfl
          rw [hwc k, hout2c k]
          have hmid : (if m.val ≤ k then (toRaw z11).coeff (k - m.val) else 0)
              = (if m.val ≤ k then (toRaw z1).coeff (k - m.val) - (toRaw z0).coeff (k - m.val)
                    - (toRaw z2).coeff (k - m.val) else 0) := by
            by_cases h : m.val ≤ k
            · rw [if_pos h, if_pos h, hz11c]
            · rw [if_neg h, if_neg h]
          rw [hmid]
          simp only [hz0c, hz1c, hz2c]
          rw [karatsuba_spec_aux_mul_coeff (toRawS p) (toRawS q) k,
            karatsuba_spec_aux_split (fun i => (toRawS p).coeff i) (fun i => (toRawS q).coeff i)
              (fun i => (toRawS p0).coeff i) (fun i => (toRawS p1).coeff i)
              (fun i => (toRawS q0).coeff i) (fun i => (toRawS q1).coeff i) m.val
              hA0 hA1 hB0 hB1 k]
          by_cases hmk : m.val ≤ k
          · rw [if_pos hmk, if_pos hmk,
              karatsuba_spec_aux_middle
                (fun i => (toRawS p0).coeff i) (fun i => (toRawS p1).coeff i)
                (fun i => (toRawS q0).coeff i) (fun i => (toRawS q1).coeff i)
                (fun i => (toRaw ps).coeff i) (fun i => (toRaw qs).coeff i) (k - m.val)
                hpsc hqsc]
          · rw [if_neg hmk, if_neg hmk]

/-- If either factor has all coefficients zero, the reference product is `0`.
Both emptiness guards of the `Mul` impl land here: the guard makes one operand's
vector empty, and `Trim.eq_of_equiv` against the canonical `0` closes the branch
without ever unfolding `mulRaw`'s fold. -/
private theorem mul_spec_aux (p q : CPolynomial.Raw F)
    (h : (∀ k, p.coeff k = 0) ∨ (∀ k, q.coeff k = 0)) :
    CPolynomial.Raw.mul p q = 0 := by
  have hequiv : CPolynomial.Raw.Trim.equiv (0 : CPolynomial.Raw F) (p * q) := by
    intro k
    rw [CPolynomial.Raw.coeff_zero, CPolynomial.Raw.mul_coeff]
    rcases h with h | h <;> simp [h]
  have h' := CPolynomial.Raw.Trim.eq_of_equiv hequiv
  rw [CPolynomial.Raw.zero_canonical, CPolynomial.Raw.mul_is_trimmed] at h'
  exact h'.symm

/-- `Poly.mul` ↔ `CPolynomial.Raw.mul`.

Unlike every other operation here, this one needs a length hypothesis, and it is
about a *checked* `Usize` addition rather than about the mathematics: the
untrimmed product is sized `np + nq - 1`, spelled `np_last + nq` in the base
case and `n2 + m + m` in the Karatsuba recombination, and each of those is a
checked add that returns `fail integerOverflow` once the sum passes
`Usize.max`.  `hlen` is one unit stronger than the weakest hypothesis that
makes the triple true (`np + nq - 1 ≤ Usize.max` is what the fail points
actually need, since no site computes `np + nq` itself); it is kept verbatim
because the headline statement is the trusted interface and does not move when a
champion does.  It cannot be derived, since `alloc.vec.Vec` records only
`length ≤ Usize.max` per vector.

Note this is an artifact of that over-approximation, not a bug in `cpoly::univariate::UnivariatePoly`'s `Mul`:
a real `Vec<Ext4>` is capacity-bounded by `isize::MAX` bytes, so `np + nq` cannot
overflow a `usize` in practice.  The same over-approximation is what makes
`conv_delayed_spec` carry a `u128` headroom bound — but that one never reaches
this statement, because the Karatsuba split hands the base case at most
`KARATSUBA_CUTOFF = 16` columns.

The length bound in the postcondition is what makes the spec composable with
itself (e.g. for `(v * w) * u`), since the caller then has a route to discharging
`hlen` for the outer product. -/
theorem mul_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    Poly.mul v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
        z.val.length ≤ v.val.length + w.val.length ⦄ := by
  unfold Poly.mul
  rw [cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul]
  by_cases h1 : alloc.vec.Vec.len v = 0#usize
  · -- `np = 0`: the impl returns `UnivariatePoly::zero`, and `toRaw v` is `0`.
    rw [if_pos h1]
    have hv0 : v.val.length = 0 := by scalar_tac
    apply spec_mono zero_spec
    rintro z ⟨hzred, hz0⟩
    have hzlen : z.val.length = 0 := by
      have := toRaw_size z; rw [hz0] at this; simpa using this.symm
    refine ⟨hzred, ?_, by omega⟩
    rw [hz0]
    exact (mul_spec_aux _ _ (Or.inl (fun k => toRaw_coeff_of_ge v (by omega)))).symm
  · rw [if_neg h1]
    by_cases h2 : alloc.vec.Vec.len w = 0#usize
    · -- `nq = 0`: symmetric.
      rw [if_pos h2]
      have hw0 : w.val.length = 0 := by scalar_tac
      apply spec_mono zero_spec
      rintro z ⟨hzred, hz0⟩
      have hzlen : z.val.length = 0 := by
        have := toRaw_size z; rw [hz0] at this; simpa using this.symm
      refine ⟨hzred, ?_, by omega⟩
      rw [hz0]
      exact (mul_spec_aux _ _ (Or.inr (fun k => toRaw_coeff_of_ge w (by omega)))).symm
    · -- both non-empty: deref, `mul_karatsuba`, then `trim`.
      rw [if_neg h2]
      have hvpos : 0 < v.val.length := by scalar_tac
      have hwpos : 0 < w.val.length := by scalar_tac
      apply spec_bind (karatsuba_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref w)
        (sliceReduced_deref hv) (sliceReduced_deref hw) hvpos hwpos hlen)
      rintro x ⟨hxred, hxlen, hxc⟩
      -- `Vec::deref` is the identity on the list, so the length clause is about `v`/`w`.
      have hd1 : (alloc.vec.Vec.deref v).val = v.val := rfl
      have hd2 : (alloc.vec.Vec.deref w).val = w.val := rfl
      rw [hd1, hd2] at hxlen
      apply spec_mono (trim_spec x hxred)
      rintro z ⟨hzred, hztrim⟩
      -- the coefficient family becomes the array equation: both sides are canonical.
      have heq : (toRaw x).trim = CPolynomial.Raw.mul (toRaw v) (toRaw w) := by
        have h := CPolynomial.Raw.Trim.eq_of_equiv
          (p := toRaw x) (q := CPolynomial.Raw.mul (toRaw v) (toRaw w))
          (by intro k; simpa using hxc k)
        rw [h]; exact CPolynomial.Raw.mul_is_trimmed _ _
      refine ⟨hzred, by rw [hztrim, heq], ?_⟩
      -- `trim` only shrinks, and `mul_karatsuba` returned `|v| + |w| - 1` words.
      have hzsz : (toRaw z).size = z.val.length := toRaw_size z
      rw [hztrim] at hzsz
      have hle := CPolynomial.Raw.Trim.size_le_size (toRaw x)
      rw [toRaw_size] at hle
      omega


end CPolyEquiv
