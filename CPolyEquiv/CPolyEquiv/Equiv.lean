/-
Equivalence between the Aeneas-extracted Rust model (`cpoly.*`, see
`CPolyEquiv/Generated.lean`) and CompPoly's reference univariate polynomials
(`CompPoly.CPolynomial.Raw`, see CompPoly/Univariate/Raw/Ops.lean).

The Rust crate fixes the concrete prime field `F_P` with
`P = 2013265921` (BabyBear).  On the CompPoly side we therefore instantiate the
generic ring `R` at `ZMod P`.

The bridge has two layers:

  1. Field layer.  A machine word `u : U64` represents the field element
     `toF u = (u.val : ZMod P)`.  Each `cpoly` field operation (`fadd`, `fsub`,
     `fmul`, `fneg`) is shown to never fail and to commute with the
     corresponding `ZMod P` operation, *under the representation invariant*
     `u.val < P` (which is also what discharges the no-overflow side conditions
     in the generated `Result`-monad code — see the `P < 2^31` comment in
     `lib.rs`).  These four lemmas are proved in full.

  2. Polynomial layer.  A `Vec U64` whose entries are all `< P` represents the
     `CPolynomial.Raw (ZMod P)` obtained by mapping `toF` over its coefficients
     (`toRaw`).  Each `cpoly` polynomial operation is shown to commute with the
     matching `CPolynomial.Raw` operation under this relation.  These are also
     proved in full: `c`, `x`, `trim`, `eval`, `add_raw`, `add`, `neg`, `sub`,
     `smul` and `mul`.

     One caveat: `mul_spec` needs the extra hypothesis
     `v.val.length + w.val.length ≤ Usize.max`, because the generated code sizes
     its accumulator with a *checked* `Usize` addition `np + nq`.  Without it the
     triple is false, not merely unprovable — see the docstring on `mul_spec`.

Specs are stated in Aeneas's triple form `m ⦃ r => post r ⦄`, which is the
shape the `step`/`progress` tactic consumes and is definitionally
`∃ r, m = ok r ∧ post r`.
-/
import CPolyEquiv.Generated
import CompPoly.Univariate.Raw.Ops
import CompPoly.Univariate.Raw.Proofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial

namespace CPolyEquiv

/-- The field modulus, as an `abbrev` so that `ZMod P` reduces to `Fin P` and
its `CommRing`/`BEq`/`DecidableEq` instances are found by synthesis. -/
abbrev P : ℕ := 2013265921

/-- The field the Rust code computes in. -/
abbrev F := ZMod P

/-- A machine word interpreted as a field element. -/
def toF (u : Std.U64) : F := (u.val : F)

/-- Representation invariant for a single field element: the word is reduced
mod `P`.  Maintained by every `cpoly` field operation and required to discharge
the no-overflow obligations in the generated code. -/
def Reduced (u : Std.U64) : Prop := u.val < P

/-- Representation invariant for a polynomial: every coefficient is reduced. -/
def VecReduced (v : alloc.vec.Vec Std.U64) : Prop := ∀ u ∈ v.val, Reduced u

/-- The reference `CPolynomial.Raw` represented by a `Vec U64`. -/
def toRaw (v : alloc.vec.Vec Std.U64) : CPolynomial.Raw F :=
  (v.val.map toF).toArray

/-! ## Field layer -/

/-- The generated modulus word `cpoly.P` has value `P` (it is `irreducible`). -/
@[simp, scalar_tac_simps]
theorem cpoly_P_val : (cpoly.P).val = P := by
  simp only [cpoly.P]; decide

theorem cpoly_P_val_ne_zero : (cpoly.P).val ≠ 0 := by simp

/-- `fadd` never fails, stays reduced, and computes field addition. -/
@[step]
theorem fadd_spec (a b : Std.U64) (ha : Reduced a) (hb : Reduced b) :
    cpoly.fadd a b ⦃ c => Reduced c ∧ toF c = toF a + toF b ⦄ := by
  unfold Reduced at ha hb
  rw [cpoly.fadd]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Reduced; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toF, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_add]

/-- `fmul` never fails, stays reduced, and computes field multiplication. -/
@[step]
theorem fmul_spec (a b : Std.U64) (ha : Reduced a) (hb : Reduced b) :
    cpoly.fmul a b ⦃ c => Reduced c ∧ toF c = toF a * toF b ⦄ := by
  unfold Reduced at ha hb
  rw [cpoly.fmul]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Reduced; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toF, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_mul]

/-- `fsub` never fails, stays reduced, and computes field subtraction. -/
theorem fsub_spec (a b : Std.U64) (ha : Reduced a) (hb : Reduced b) :
    cpoly.fsub a b ⦃ c => Reduced c ∧ toF c = toF a - toF b ⦄ := by
  unfold Reduced at ha hb
  have hPv : (cpoly.P).val = P := cpoly_P_val
  rw [cpoly.fsub]
  step as ⟨i, hi⟩          -- i = a + P
  step as ⟨j, hj⟩          -- j = i - b   (b.val ≤ i.val auto-discharged)
  step as ⟨c, hc⟩          -- c = j % P
  refine ⟨?_, ?_⟩
  · unfold Reduced; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · -- toF c = ↑(j % P) = ↑j = ↑(a + P - b) = ↑a + ↑P - ↑b = ↑a - ↑b   (↑P = 0)
    have hbi : b.val ≤ a.val + P := by scalar_tac
    simp only [toF, hc, cpoly_P_val, ZMod.natCast_mod, hj, hi]
    rw [Nat.cast_sub hbi, Nat.cast_add, ZMod.natCast_self]
    ring

/-- `fneg` never fails, stays reduced, and computes field negation. -/
@[step]
theorem fneg_spec (a : Std.U64) (ha : Reduced a) :
    cpoly.fneg a ⦃ c => Reduced c ∧ toF c = - toF a ⦄ := by
  unfold Reduced at ha
  have hPv : (cpoly.P).val = P := cpoly_P_val
  rw [cpoly.fneg]
  step as ⟨i, hi⟩          -- i = P - a   (a.val ≤ P.val auto-discharged)
  step as ⟨c, hc⟩          -- c = i % P
  refine ⟨?_, ?_⟩
  · unfold Reduced; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · have hai : a.val ≤ P := by scalar_tac
    simp only [toF, hc, cpoly_P_val, ZMod.natCast_mod, hi]
    rw [Nat.cast_sub hai, ZMod.natCast_self]
    ring

/-! ## Polynomial layer

Each statement says: under the representation invariant, the generated
operation succeeds, preserves the invariant, and its `toRaw` equals the
CompPoly reference operation applied to the `toRaw` of the inputs. -/

/-- A reduced word is the zero field element iff it is the zero word. -/
theorem toF_eq_zero_iff (u : Std.U64) (hu : Reduced u) : toF u = 0 ↔ u.val = 0 := by
  unfold toF; unfold Reduced at hu
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hu, fun h => h ▸ dvd_zero P⟩

/-- Rewrite `getElem` under a list equality (sidesteps the dependent-motive
issue that blocks `rw` on `l[i]`). -/
theorem getElem_of_list_eq {α} {l l' : List α} (h : l = l') {i : ℕ}
    {hi : i < l.length} : l[i] = l'[i]'(h ▸ hi) := by cases h; rfl

/-- The `k`-th coefficient of `toRaw v` is `toF` of the `k`-th word (or `0`). -/
theorem toRaw_coeff (v : alloc.vec.Vec Std.U64) (k : ℕ) :
    (toRaw v).coeff k = (v.val.map toF).getD k 0 := by
  unfold toRaw CPolynomial.Raw.coeff
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < v.val.length
  · simp [List.getElem?_eq_getElem h, dif_pos h]
  · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h), dif_neg h]

@[simp] theorem toRaw_size (v : alloc.vec.Vec Std.U64) : (toRaw v).size = v.val.length := by
  simp [toRaw]

/-- In-range coefficients of `toRaw v` are the `toF`-images of the words. -/
theorem toRaw_coeff_of_lt (v : alloc.vec.Vec Std.U64) {k : ℕ} (hk : k < v.val.length) :
    (toRaw v).coeff k = toF v.val[k] := by
  rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

/-- Out-of-range coefficients of `toRaw v` are zero. -/
theorem toRaw_coeff_of_ge (v : alloc.vec.Vec Std.U64) {k : ℕ} (hk : v.val.length ≤ k) :
    (toRaw v).coeff k = 0 := by
  rw [toRaw_coeff, List.getD_eq_default]; simpa using hk

/-- Reading coefficient `i` with zero-padding (`if i < len then v[i] else 0`)
returns the reduced word whose `toF` is `(toRaw v).coeff i`. -/
theorem padded_read_spec (p : alloc.vec.Vec Std.U64) (np i : Std.Usize)
    (hnp : np.val = p.val.length) (hp : VecReduced p) :
    (if i < np
      then alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U64) p i
      else ok 0#u64) ⦃ a => Reduced a ∧ toF a = (toRaw p).coeff i.val ⦄ := by
  by_cases h : i < np
  · rw [if_pos h]
    have hb : i.val < p.val.length := by scalar_tac
    step as ⟨e, he⟩
    refine ⟨he ▸ hp _ (List.getElem_mem hb), ?_⟩
    rw [he, toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map]
  · rw [if_neg h]
    simp only [spec_ok]
    refine ⟨by unfold Reduced; decide, ?_⟩
    rw [toRaw_coeff, List.getD_eq_default _ _ (by simp; scalar_tac)]
    simp [toF]

/-- `cpoly.c r` ↔ `CPolynomial.Raw.C`. -/
theorem c_spec (r : Std.U64) (hr : Reduced r) :
    cpoly.c r ⦃ v => VecReduced v ∧ toRaw v = CPolynomial.Raw.C (toF r) ⦄ := by
  rw [cpoly.c]
  step as ⟨v, hv⟩
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hv] at hu; simp at hu; subst hu; exact hr
  · simp only [toRaw, hv, CPolynomial.Raw.C]
    simp

/-- `cpoly.x` ↔ `CPolynomial.Raw.X`. -/
theorem x_spec :
    cpoly.x ⦃ v => VecReduced v ∧ toRaw v = CPolynomial.Raw.X ⦄ := by
  rw [cpoly.x]
  step as ⟨p, hp⟩
  step as ⟨v, hv⟩
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hv, hp] at hu; simp at hu
    rcases hu with h | h <;> (subst h; unfold Reduced; decide)
  · simp only [toRaw, hv, hp, CPolynomial.Raw.X]
    simp [toF]

/-- `trim_loop0` scans from `m` downward and returns the canonical length `n1`:
all coefficients `≥ n1` are zero, and (if `n1 > 0`) coefficient `n1-1` is
nonzero. -/
theorem trim_loop0_spec (p : alloc.vec.Vec Std.U64) (m : Std.Usize)
    (hp : VecReduced p) (hm : m.val ≤ p.val.length) :
    cpoly.trim_loop0 p m ⦃ n1 => n1.val ≤ m.val ∧
      (∀ k, n1.val ≤ k → k < m.val → (toRaw p).coeff k = 0) ∧
      (n1.val = 0 ∨ (toRaw p).coeff (n1.val - 1) ≠ 0) ⦄ := by
  rw [cpoly.trim_loop0]
  apply loop.spec_decr_nat (fun s => s.val)
    (fun s => s.val ≤ m.val ∧ ∀ k, s.val ≤ k → k < m.val → (toRaw p).coeff k = 0)
  · intro m' ⟨hm'le, hm'z⟩
    simp only [cpoly.trim_loop0.body]
    by_cases hpos : m' > 0#usize
    · rw [if_pos hpos]
      have hb : m'.val - 1 < p.val.length := by scalar_tac
      step as ⟨i, hi⟩
      have hib : i.val < p.val.length := by rw [hi]; exact hb
      step as ⟨c, hc⟩
      have hRc : Reduced c := hc ▸ hp _ (List.getElem_mem hib)
      have hcoeff : (toRaw p).coeff i.val = toF c := by
        rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hib),
          List.getElem_map, hc]
      cases hcz : (c != 0#u64)
      · -- c = 0 : continue with i = m'-1
        simp only [Bool.false_eq_true, if_false]
        have hc0 : c = 0#u64 := by simpa using hcz
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk1 hk2
        rcases Nat.lt_or_ge k m'.val with hkm | hkm
        · have hki : k = i.val := by scalar_tac
          rw [hki, hcoeff, hc0]; simp [toF]
        · exact hm'z k hkm hk2
      · -- c ≠ 0 : done with m'
        simp only [if_true]
        refine ⟨hm'le, hm'z, Or.inr ?_⟩
        rw [show m'.val - 1 = i.val by rw [hi], hcoeff, Ne, toF_eq_zero_iff c hRc]
        simp only [bne_iff_ne, ne_eq] at hcz
        scalar_tac
    · rw [if_neg hpos]
      exact ⟨hm'le, hm'z, Or.inl (by scalar_tac)⟩
  · exact ⟨le_refl _, fun k hk1 hk2 => absurd hk2 (by omega)⟩

/-- `trim_loop1` copies the first `n1` coefficients: the result is
`p.val.take n1`. -/
theorem trim_loop1_spec (p : alloc.vec.Vec Std.U64) (n1 : Std.Usize)
    (hp : VecReduced p) (hn1 : n1.val ≤ p.val.length) :
    ∀ (r : alloc.vec.Vec Std.U64) (i : Std.Usize),
      i.val ≤ n1.val → VecReduced r → r.val = p.val.take i.val →
      cpoly.trim_loop1 p n1 r i ⦃ z => VecReduced z ∧ z.val = p.val.take n1.val ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.trim_loop1]
  apply loop.spec_decr_nat (fun s => n1.val - s.2.val)
    (fun s => s.2.val ≤ n1.val ∧ VecReduced s.1 ∧ s.1.val = p.val.take s.2.val)
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.trim_loop1.body]
    by_cases hlt : i1 < n1
    · rw [if_pos hlt]
      have hib : i1.val < p.val.length := by scalar_tac
      have hr1len : r1.val.length = i1.val := by
        rw [hrel1, List.length_take]; scalar_tac
      step as ⟨e, he⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro u hu; rw [hr2] at hu; rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact he ▸ hp _ (List.getElem_mem hib)
      · rw [hr2, hi2, hrel1, he]; exact List.take_concat_get' _ _ hib
    · rw [if_neg hlt]
      have heq : i1.val = n1.val := by scalar_tac
      exact ⟨hr1, by rw [hrel1, heq]⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly.trim` ↔ `CPolynomial.Raw.trim`. -/
theorem trim_spec (v : alloc.vec.Vec Std.U64) (hv : VecReduced v) :
    cpoly.trim v ⦃ w => VecReduced w ∧ toRaw w = (toRaw v).trim ⦄ := by
  rw [cpoly.trim]
  apply spec_bind (trim_loop0_spec v (alloc.vec.Vec.len v) hv (by simp))
  rintro n1 ⟨hn1le, hn1zero, hn1bound⟩
  have hn1len : n1.val ≤ v.val.length := by simpa using hn1le
  apply spec_mono (trim_loop1_spec v n1 hv hn1len (alloc.vec.Vec.new Std.U64) 0#usize
    (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzval⟩
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

theorem eval_loop_spec (p : alloc.vec.Vec Std.U64) (xv : Std.U64)
    (hp : VecReduced p) (hx : Reduced xv) :
    ∀ (acc : Std.U64) (i : Std.Usize), i.val ≤ p.val.length → Reduced acc →
      toF acc = ((p.val.drop i.val).map toF).foldr (fun a b => b * toF xv + a) 0 →
      cpoly.eval_loop p xv acc i ⦃ r => Reduced r ∧
        toF r = ((p.val).map toF).foldr (fun a b => b * toF xv + a) 0 ⦄ := by
  intro acc i hi hacc hrel
  rw [cpoly.eval_loop]
  apply loop.spec_decr_nat (fun s => s.2.val)
    (fun s => s.2.val ≤ p.val.length ∧ Reduced s.1 ∧
       toF s.1 = ((p.val.drop s.2.val).map toF).foldr (fun a b => b * toF xv + a) 0)
  · rintro ⟨acc1, i1⟩ ⟨hi1, haccR, hrel1⟩
    simp only [cpoly.eval_loop.body]
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

/-- `cpoly.eval` ↔ `CPolynomial.Raw.eval` (Horner). -/
theorem eval_spec (v : alloc.vec.Vec Std.U64) (xv : Std.U64)
    (hv : VecReduced v) (hx : Reduced xv) :
    cpoly.eval v xv ⦃ r => Reduced r ∧ toF r = (toRaw v).eval (toF xv) ⦄ := by
  rw [cpoly.eval]
  apply spec_mono (eval_loop_spec v xv hv hx 0#u64 (alloc.vec.Vec.len v)
    (by simp) (by unfold Reduced; decide) (by simp [toF]))
  rintro r ⟨hrR, hrF⟩
  refine ⟨hrR, ?_⟩
  rw [hrF, CPolynomial.Raw.eval, ← CPolynomial.Raw.eval₂Horner_eq_eval₂,
    CPolynomial.Raw.eval₂Horner, Array.foldr_toList]
  simp [toRaw]

theorem add_raw_loop_spec (p q : alloc.vec.Vec Std.U64) (np nq n : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hnp : np.val = p.val.length) (hnq : nq.val = q.val.length)
    (hn : n.val = max p.val.length q.val.length) :
    ∀ (r : alloc.vec.Vec Std.U64) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toF
        = (List.range i.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k) →
      cpoly.add_raw_loop p q np nq n r i ⦃ z => VecReduced z ∧
        z.val.map toF
          = (List.range n.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.add_raw_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toF
        = (List.range s.2.val).map (fun k => (toRaw p).coeff k + (toRaw q).coeff k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.add_raw_loop.body]
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

/-- `cpoly.add_raw` ↔ `CPolynomial.Raw.addRaw` (untrimmed). -/
theorem add_raw_spec (v w : alloc.vec.Vec Std.U64)
    (hv : VecReduced v) (hw : VecReduced w) :
    cpoly.add_raw v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.addRaw (toRaw v) (toRaw w) ⦄ := by
  rw [cpoly.add_raw]
  apply spec_bind (Pₘ := fun nn : Std.Usize => nn.val = max v.val.length w.val.length)
  · by_cases hc : alloc.vec.Vec.len v ≥ alloc.vec.Vec.len w
    · rw [if_pos hc]; simp only [spec_ok]; scalar_tac
    · rw [if_neg hc]; simp only [spec_ok]; scalar_tac
  · intro nn hnn
    apply spec_mono (add_raw_loop_spec v w (alloc.vec.Vec.len v) (alloc.vec.Vec.len w) nn
      hv hw (by simp) (by simp) hnn (alloc.vec.Vec.new Std.U64) 0#usize (by simp)
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

/-- `cpoly.add` ↔ `CPolynomial.Raw.add`. -/
theorem add_spec (v w : alloc.vec.Vec Std.U64)
    (hv : VecReduced v) (hw : VecReduced w) :
    cpoly.add v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.add (toRaw v) (toRaw w) ⦄ := by
  rw [cpoly.add]
  apply spec_bind (add_raw_spec v w hv hw)
  rintro r ⟨hrred, hrmap⟩
  apply spec_mono (trim_spec r hrred)
  rintro z ⟨hzred, hztrim⟩
  exact ⟨hzred, by rw [hztrim, hrmap]; rfl⟩

/-- `cpoly.neg` ↔ `CPolynomial.Raw.neg`.

The shared recipe for all the loop-based operations.  The generated `*_loop`
functions are `loop (fun s => body s) init`.  Reason about them with
`Aeneas.Std.loop.spec_decr_nat`, instantiated with:
  • measure  `fun s => n.val - s.2.val`   (counter approaches the length)
  • invariant tying the accumulator's field-image to the processed prefix, e.g.
      `s.1.val.map toF = (p.val.take s.2.val).map (fun u => - toF u)`
The body obligation steps with `step` through `Vec.index_usize_spec`,
`fneg_spec` (now `@[step]`), and `Vec.push_spec`; the `List.take_succ` /
`List.map_append` lemmas extend the prefix by one.  The triple `m ⦃ r => P ⦄`
is `Aeneas.Std.spec m P` (a WP predicate, NOT a bare `∃`), so compose loop
specs into the top-level operation with `spec_mono` / `spec_bind`, then convert
the `List.map toF` invariant to the `toRaw` (Array) equation via
`Array.map_toArray` + `List.map_map`.  `eval`/`smul`/`add_raw` follow the same
single-loop shape; `trim` adds a `lastNonzero`/`Array.extract` argument.

`mul` is the one operation that does not fit the prefix-append mould: its inner
loop updates a single slot of the accumulator in place, so its invariant is
stated coefficient-wise (see `mul_loop1_loop0_spec`) rather than as a `take`. -/
theorem neg_loop_spec (p : alloc.vec.Vec Std.U64) (n : Std.Usize)
    (hp : VecReduced p) (hn : n.val = p.val.length) (r : alloc.vec.Vec Std.U64)
    (i : Std.Usize) (hi : i.val ≤ n.val) (hr : VecReduced r)
    (hrel : r.val.map toF = (p.val.take i.val).map (fun u => - toF u)) :
    cpoly.neg_loop p n r i ⦃ z => VecReduced z ∧
      z.val.map toF = p.val.map (fun u => - toF u) ⦄ := by
  rw [cpoly.neg_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
       s.1.val.map toF = (p.val.take s.2.val).map (fun u => - toF u))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.neg_loop.body]
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

theorem neg_spec (v : alloc.vec.Vec Std.U64) (hv : VecReduced v) :
    cpoly.neg v ⦃ z => VecReduced z ∧ toRaw z = CPolynomial.Raw.neg (toRaw v) ⦄ := by
  rw [cpoly.neg]
  apply spec_mono (neg_loop_spec v (alloc.vec.Vec.len v) hv (by simp)
    (alloc.vec.Vec.new Std.U64) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzmap⟩
  refine ⟨hzred, ?_⟩
  simp only [toRaw, hzmap, CPolynomial.Raw.neg, List.map_toArray, List.map_map,
    Function.comp_def]

/-- `cpoly.sub` ↔ `CPolynomial.Raw.sub`. -/
theorem sub_spec (v w : alloc.vec.Vec Std.U64)
    (hv : VecReduced v) (hw : VecReduced w) :
    cpoly.sub v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.sub (toRaw v) (toRaw w) ⦄ := by
  rw [cpoly.sub]
  apply spec_bind (neg_spec w hw)
  rintro nq ⟨hnqred, hnqmap⟩
  apply spec_mono (add_spec v nq hv hnqred)
  rintro z ⟨hzred, hzmap⟩
  exact ⟨hzred, by rw [hzmap, hnqmap]; rfl⟩

theorem smul_loop_spec (rr : Std.U64) (p : alloc.vec.Vec Std.U64) (n : Std.Usize)
    (hrr : Reduced rr) (hp : VecReduced p) (hn : n.val = p.val.length) :
    ∀ (out : alloc.vec.Vec Std.U64) (i : Std.Usize),
      i.val ≤ n.val → VecReduced out →
      out.val.map toF = (p.val.take i.val).map (fun u => toF rr * toF u) →
      cpoly.smul_loop rr p n out i ⦃ z => VecReduced z ∧
        z.val.map toF = p.val.map (fun u => toF rr * toF u) ⦄ := by
  intro out i hi hout hrel
  rw [cpoly.smul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
       s.1.val.map toF = (p.val.take s.2.val).map (fun u => toF rr * toF u))
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1, hrel1⟩
    simp only [cpoly.smul_loop.body]
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

/-- `cpoly.smul` ↔ `CPolynomial.Raw.smul`. -/
theorem smul_spec (r : Std.U64) (v : alloc.vec.Vec Std.U64)
    (hr : Reduced r) (hv : VecReduced v) :
    cpoly.smul r v ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.smul (toF r) (toRaw v) ⦄ := by
  rw [cpoly.smul]
  apply spec_mono (smul_loop_spec r v (alloc.vec.Vec.len v) hr hv (by simp)
    (alloc.vec.Vec.new Std.U64) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzmap⟩
  refine ⟨hzred, ?_⟩
  simp only [toRaw, hzmap, CPolynomial.Raw.smul, List.map_toArray, List.map_map,
    Function.comp_def]

/-! ### Multiplication

`cpoly.mul` is a schoolbook convolution: it zero-fills an accumulator of length
`np + nq - 1` (`mul_loop0`), then for each `i < np` and `j < nq` performs
`r[i+j] += p[i] * q[j]` (`mul_loop1` around `mul_loop1_loop0`), and finally
trims.  The reference `CPolynomial.Raw.mul` instead sums the shifted scalar
multiples `(a i • q) * X^i`; the two are reconciled at the level of
*coefficients* via `CPolynomial.Raw.mul_coeff`, so the bridge is the partial
convolution sum `convol` below. -/

/-- The contribution of the first `m` coefficients of `p` to coefficient `k` of
the product `p * q`.  This is the loop invariant of `mul_loop1`, and
`convol p q p.val.length` is the full convolution (`convol_eq_sum_range`). -/
def convol (p q : alloc.vec.Vec Std.U64) (m k : ℕ) : F :=
  ∑ i ∈ Finset.range m, if i ≤ k then (toRaw p).coeff i * (toRaw q).coeff (k - i) else 0

theorem convol_zero (p q : alloc.vec.Vec Std.U64) (k : ℕ) : convol p q 0 k = 0 := by
  simp [convol]

theorem convol_succ (p q : alloc.vec.Vec Std.U64) (m k : ℕ) :
    convol p q (m + 1) k
      = convol p q m k + (if m ≤ k then (toRaw p).coeff m * (toRaw q).coeff (k - m) else 0) := by
  simp [convol, Finset.sum_range_succ]

/-- `mul_loop0` zero-fills the accumulator up to length `n`. -/
theorem mul_loop0_spec (n : Std.Usize) :
    ∀ (r : alloc.vec.Vec Std.U64) (k : Std.Usize),
      k.val ≤ n.val → r.val = List.replicate k.val 0#u64 →
      cpoly.mul_loop0 r n k ⦃ z => z.val = List.replicate n.val 0#u64 ⦄ := by
  intro r k hk hrel
  rw [cpoly.mul_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = List.replicate s.2.val 0#u64)
  · rintro ⟨r1, k1⟩ ⟨hk1, hrel1⟩
    simp only [cpoly.mul_loop0.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      have hr1len : r1.val.length = k1.val := by
        rw [hrel1, List.length_replicate]
      have hpush : r1.val.length < Std.Usize.max := by
        rw [hr1len]; scalar_tac
      step as ⟨r2, hr2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · -- the zero prefix extends by one
        rw [hr2, hk2, hrel1, ← List.replicate_succ']
      · have hlt2 : k1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : k1.val = n.val := by scalar_tac
      have hrel1' : r1.val = List.replicate k1.val 0#u64 := hrel1
      exact hrel1'.trans (by rw [heq])
  · exact ⟨hk, hrel⟩

/-- `mul_loop1_loop0` is the inner convolution loop: for a fixed `i` it performs
`r[i+j] += p[i] * q[j]` for every `j ∈ [j₀, nq)`.  Since `i + j = k` has at most
one solution `j` for fixed `i` and `k`, the total effect on slot `k` is the
single guarded term below.  The hypothesis `i.val + nq.val ≤ r.val.length` is
what keeps every written index in bounds. -/
theorem mul_loop1_loop0_spec (p q : alloc.vec.Vec Std.U64) (nq i : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q) (hnq : nq.val = q.val.length)
    (hip : i.val < p.val.length) :
    ∀ (r : alloc.vec.Vec Std.U64) (j : Std.Usize),
      VecReduced r → j.val ≤ nq.val → i.val + nq.val ≤ r.val.length →
      cpoly.mul_loop1_loop0 p q nq r i j ⦃ z => VecReduced z ∧
        z.val.length = r.val.length ∧
        ∀ k, (toRaw z).coeff k = (toRaw r).coeff k +
          (if i.val + j.val ≤ k ∧ k < i.val + nq.val
            then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0) ⦄ := by
  intro r j hr hj hbound
  rw [cpoly.mul_loop1_loop0]
  apply loop.spec_decr_nat (fun s => nq.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ nq.val ∧ j.val ≤ s.2.val ∧
      s.1.val.length = r.val.length ∧
      ∀ k, (toRaw s.1).coeff k = (toRaw r).coeff k +
        (if i.val + j.val ≤ k ∧ k < i.val + s.2.val
          then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0))
  · rintro ⟨r1, j1⟩ hinv
    -- re-ascribe the invariant so `omega` sees `j1.val`, not `(r1, j1).2.val`
    obtain ⟨hr1, hj1, hjj1, hlen1, hcoeff1⟩ :
        VecReduced r1 ∧ j1.val ≤ nq.val ∧ j.val ≤ j1.val ∧
        r1.val.length = r.val.length ∧
        (∀ k, (toRaw r1).coeff k = (toRaw r).coeff k +
          (if i.val + j.val ≤ k ∧ k < i.val + j1.val
            then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0)) := hinv
    simp only [cpoly.mul_loop1_loop0.body]
    by_cases hlt : j1 < nq
    · rw [if_pos hlt]
      have hjb : j1.val < q.val.length := by scalar_tac
      have hidxb : i.val + j1.val < r1.val.length := by scalar_tac
      step as ⟨a, ha⟩                  -- a = p[i]
      step as ⟨b, hb⟩                  -- b = q[j1]
      have haR : Reduced a := ha ▸ hp _ (List.getElem_mem hip)
      have hbR : Reduced b := hb ▸ hq _ (List.getElem_mem hjb)
      step as ⟨prod, hprodR, hprodF⟩   -- prod = a * b
      step as ⟨idx, hidx⟩              -- idx = i + j1
      have hidxb2 : idx.val < r1.val.length := by scalar_tac
      step as ⟨c, hc⟩                  -- c = r1[idx]
      have hcR : Reduced c := hc ▸ hr1 _ (List.getElem_mem hidxb2)
      step as ⟨w, hwR, hwF⟩            -- w = c + prod
      step as ⟨_x, back, _hx, hback⟩   -- back = r1.set idx
      step as ⟨j2, hj2⟩
      subst hback
      have hset : (r1.set idx w).val = r1.val.set idx.val w := by simp
      have hsetlen : (r1.set idx w).val.length = r.val.length := by
        rw [hset, List.length_set, hlen1]
      have hpa : (toRaw p).coeff i.val = toF a := by rw [toRaw_coeff_of_lt p hip, ha]
      have hqb : (toRaw q).coeff j1.val = toF b := by rw [toRaw_coeff_of_lt q hjb, hb]
      have hrc : (toRaw r1).coeff idx.val = toF c := by
        rw [toRaw_coeff_of_lt r1 hidxb2, hc]
      -- pointwise description of the single-slot update
      have hcset : ∀ k, (toRaw (r1.set idx w)).coeff k =
          if idx.val = k then toF w else (toRaw r1).coeff k := by
        intro k
        by_cases hk : k < r1.val.length
        · rw [toRaw_coeff_of_lt _ (by rw [hsetlen]; omega), toRaw_coeff_of_lt r1 hk,
            getElem_of_list_eq hset, List.getElem_set]
          split <;> rfl
        · rw [toRaw_coeff_of_ge _ (by omega), toRaw_coeff_of_ge r1 (by omega),
            if_neg (by omega)]
      refine ⟨?_, by scalar_tac, by scalar_tac, hsetlen, ?_, by scalar_tac⟩
      · intro u hu
        rw [hset] at hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact hr1 u h
        · exact h ▸ hwR
      · intro k
        rw [hcset k]
        by_cases hke : idx.val = k
        · -- the slot just written: its new term is exactly `p[i] * q[j1]`
          rw [if_pos hke, if_pos (show i.val + j.val ≤ k ∧ k < i.val + j2.val by omega),
            hpa, show k - i.val = j1.val from by omega, hqb, hwF, hprodF]
          have hcr : toF c = (toRaw r).coeff idx.val := by
            rw [← hrc, hcoeff1 idx.val, if_neg (by omega), add_zero]
          rw [hcr, hke]
        · -- every other slot is untouched, and the two guards agree
          rw [if_neg hke, hcoeff1 k]
          congr 1
          by_cases hcond : i.val + j.val ≤ k ∧ k < i.val + j1.val
          · rw [if_pos hcond, if_pos (show i.val + j.val ≤ k ∧ k < i.val + j2.val by omega)]
          · rw [if_neg hcond, if_neg (show ¬(i.val + j.val ≤ k ∧ k < i.val + j2.val) by omega)]
    · rw [if_neg hlt]
      have heq : j1.val = nq.val := by scalar_tac
      refine ⟨hr1, hlen1, ?_⟩
      intro k
      rw [hcoeff1 k, heq]
  · refine ⟨hr, hj, le_refl _, rfl, fun k => ?_⟩
    have hfalse : ¬(i.val + j.val ≤ k ∧ k < i.val + j.val) := by omega
    simp [hfalse]

/-- `mul_loop1` is the outer convolution loop: it accumulates the inner loop's
contributions for `i ∈ [i₀, np)`, building up `convol p q np`. -/
theorem mul_loop1_spec (p q : alloc.vec.Vec Std.U64) (np nq : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hnp : np.val = p.val.length) (hnq : nq.val = q.val.length) :
    ∀ (r : alloc.vec.Vec Std.U64) (i : Std.Usize),
      VecReduced r → i.val ≤ np.val → np.val + nq.val ≤ r.val.length + 1 →
      (∀ k, (toRaw r).coeff k = convol p q i.val k) →
      cpoly.mul_loop1 p q np nq r i ⦃ z => VecReduced z ∧
        z.val.length = r.val.length ∧
        ∀ k, (toRaw z).coeff k = convol p q np.val k ⦄ := by
  intro r i hr hi hbound hcoeff
  rw [cpoly.mul_loop1]
  apply loop.spec_decr_nat (fun s => np.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ np.val ∧ s.1.val.length = r.val.length ∧
      ∀ k, (toRaw s.1).coeff k = convol p q s.2.val k)
  · rintro ⟨r1, i1⟩ hinv
    obtain ⟨hr1, hi1, hlen1, hcoeff1⟩ : VecReduced r1 ∧ i1.val ≤ np.val ∧
        r1.val.length = r.val.length ∧
        (∀ k, (toRaw r1).coeff k = convol p q i1.val k) := hinv
    simp only [cpoly.mul_loop1.body]
    by_cases hlt : i1 < np
    · rw [if_pos hlt]
      have h1 : i1.val < np.val := by scalar_tac
      have hip : i1.val < p.val.length := by omega
      have hib : i1.val + nq.val ≤ r1.val.length := by omega
      apply spec_bind (mul_loop1_loop0_spec p q nq i1 hp hq hnq hip
        r1 0#usize hr1 (by scalar_tac) hib)
      rintro r2 ⟨hr2, hlen2, hcoeff2⟩
      step as ⟨i2, hi2⟩
      have hz : (0#usize).val = 0 := by scalar_tac
      refine ⟨hr2, by scalar_tac, by omega, ?_, by scalar_tac⟩
      intro k
      rw [hcoeff2 k, hz, Nat.add_zero, hcoeff1 k,
        show i2.val = i1.val + 1 by scalar_tac, convol_succ]
      congr 1
      -- the inner loop's `k < i1 + nq` guard is redundant: past it, `q`'s
      -- coefficient is out of range and hence zero
      by_cases hk : i1.val ≤ k
      · by_cases hk2 : k < i1.val + nq.val
        · rw [if_pos ⟨hk, hk2⟩, if_pos hk]
        · rw [if_neg (by tauto), if_pos hk, toRaw_coeff_of_ge q (by omega), mul_zero]
      · rw [if_neg (by tauto), if_neg hk]
    · rw [if_neg hlt]
      have heq : i1.val = np.val := by scalar_tac
      exact ⟨hr1, hlen1, by rw [← heq]; exact hcoeff1⟩
  · exact ⟨hr, hi, rfl, hcoeff⟩

private theorem convol_eq_sum_range_aux (n k : ℕ) :
    (Finset.range n).filter (fun i => i ≤ k) = Finset.range (min n (k + 1)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The full convolution over all of `p` is the sum shape used by
`CPolynomial.Raw.mul_coeff`: the `i ≤ k` guard drops the terms above `k`, and
the terms with `i ≥ p.val.length` vanish because `(toRaw p).coeff i = 0` there. -/
theorem convol_eq_sum_range (p q : alloc.vec.Vec Std.U64) (k : ℕ) :
    convol p q p.val.length k
      = ∑ i ∈ Finset.range (k + 1), (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
  have hL : convol p q p.val.length k
      = ∑ i ∈ Finset.range (min p.val.length (k + 1)),
          (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
    rw [convol, ← Finset.sum_filter, convol_eq_sum_range_aux]
  have hR : ∑ i ∈ Finset.range (min p.val.length (k + 1)),
          (toRaw p).coeff i * (toRaw q).coeff (k - i)
      = ∑ i ∈ Finset.range (k + 1), (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      simp only [Finset.mem_range] at hx hnx
      rw [toRaw_coeff_of_ge p (by omega), zero_mul]
  rw [hL, hR]

/-- `cpoly.mul` ↔ `CPolynomial.Raw.mul`.

Unlike every other operation here, this one needs a length hypothesis, and it is
necessary rather than merely convenient: the generated code sizes its
accumulator with a *checked* `Usize` addition (`Generated.lean`, `let i ← np +
nq`, only then `n ← i - 1`), which returns `fail integerOverflow` whenever the
two lengths sum above `Usize.max` — lengths `(Usize.max, 1)` already suffice, it
is not only the both-maximal case.  So `hlen` is exactly the weakest hypothesis
that makes the triple true; in particular it cannot be relaxed to
`np + nq - 1 ≤ Usize.max`, which is all the *result* length needs, because the
intermediate sum overflows first.  And it cannot be derived, since
`alloc.vec.Vec` records only `length ≤ Usize.max` per vector.

Note this is an artifact of that over-approximation, not a bug in `cpoly::mul`:
a real `Vec<u64>` is capacity-bounded by `isize::MAX` bytes, so `np + nq` cannot
overflow a `usize` in practice.

The length bound in the postcondition is what makes the spec composable with
itself (e.g. for `(v * w) * u`), since the caller then has a route to discharging
`hlen` for the outer product. -/
theorem mul_spec (v w : alloc.vec.Vec Std.U64)
    (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    cpoly.mul v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
        z.val.length ≤ v.val.length + w.val.length ⦄ := by
  have hnewred : VecReduced (alloc.vec.Vec.new Std.U64) := by intro u hu; simp at hu
  have hnewraw : toRaw (alloc.vec.Vec.new Std.U64) = (0 : CPolynomial.Raw F) := by
    simp [toRaw]
  rw [cpoly.mul]
  by_cases hp0 : alloc.vec.Vec.len v = 0#usize
  · -- empty left factor
    rw [if_pos hp0]
    simp only [spec_ok]
    refine ⟨hnewred, ?_, by simp⟩
    have hvz : toRaw v = (0 : CPolynomial.Raw F) := by
      have hl : v.val.length = 0 := by scalar_tac
      simp [toRaw, List.length_eq_zero_iff.mp hl]
    rw [hnewraw, hvz]
    exact (CPolynomial.Raw.zero_mul (toRaw w)).symm
  · rw [if_neg hp0]
    by_cases hq0 : alloc.vec.Vec.len w = 0#usize
    · -- empty right factor
      rw [if_pos hq0]
      simp only [spec_ok]
      refine ⟨hnewred, ?_, by simp⟩
      have hwz : toRaw w = (0 : CPolynomial.Raw F) := by
        have hl : w.val.length = 0 := by scalar_tac
        simp [toRaw, List.length_eq_zero_iff.mp hl]
      rw [hnewraw, hwz]
      exact (CPolynomial.Raw.mul_zero (toRaw v)).symm
    · rw [if_neg hq0]
      have hvpos : 0 < v.val.length := by scalar_tac
      have hwpos : 0 < w.val.length := by scalar_tac
      step as ⟨i, hi⟩          -- i = np + nq   (needs `hlen`: this is a checked add)
      step as ⟨n, hn⟩          -- n = i - 1
      apply spec_bind (mul_loop0_spec n (alloc.vec.Vec.new Std.U64) 0#usize
        (by scalar_tac) (by simp))
      intro r hr
      have hrlen : r.val.length = n.val := by simp [hr]
      have hrred : VecReduced r := by
        intro u hu
        rw [hr] at hu
        rw [List.eq_of_mem_replicate hu]
        unfold Reduced; decide
      have hrcoeff : ∀ k, (toRaw r).coeff k = 0 := by
        intro k
        rcases Nat.lt_or_ge k r.val.length with h | h
        · rw [toRaw_coeff_of_lt r h]; simp [hr, toF]
        · exact toRaw_coeff_of_ge r h
      apply spec_bind (mul_loop1_spec v w (alloc.vec.Vec.len v) (alloc.vec.Vec.len w)
        hv hw (by simp) (by simp) r 0#usize hrred (by simp) (by scalar_tac)
        (by intro k; rw [hrcoeff k, show (0#usize).val = 0 from by scalar_tac, convol_zero]))
      rintro r1 ⟨hr1red, hr1len, hr1coeff⟩
      apply spec_mono (trim_spec r1 hr1red)
      rintro z ⟨hzred, hztrim⟩
      -- trimming only shortens, so the result fits in `np + nq - 1`
      have hzlen : z.val.length ≤ r1.val.length := by
        rw [← toRaw_size z, ← toRaw_size r1, hztrim]
        exact CPolynomial.Raw.Trim.size_le_size (toRaw r1)
      refine ⟨hzred, ?_, by scalar_tac⟩
      rw [hztrim]
      have hlenv : (alloc.vec.Vec.len v).val = v.val.length := by simp
      -- equal coefficients ⇒ equal trims, and the reference product is already trimmed
      have h2 : (toRaw r1).trim = ((toRaw v) * (toRaw w)).trim := by
        apply CPolynomial.Raw.Trim.eq_of_equiv
        intro k
        rw [hr1coeff k, CPolynomial.Raw.mul_coeff, hlenv, convol_eq_sum_range]
      rw [h2, CPolynomial.Raw.mul_is_trimmed]
      rfl

end CPolyEquiv
