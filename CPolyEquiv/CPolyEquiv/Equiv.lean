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
     matching `CPolynomial.Raw` operation under this relation.  (Statements are
     established and typecheck against both sides; proofs in progress.)

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
        simp only [hcz, Bool.false_eq_true, if_false]
        have hc0 : c = 0#u64 := by simpa using hcz
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk1 hk2
        rcases Nat.lt_or_ge k m'.val with hkm | hkm
        · have hki : k = i.val := by scalar_tac
          rw [hki, hcoeff, hc0]; simp [toF]
        · exact hm'z k hkm hk2
      · -- c ≠ 0 : done with m'
        simp only [hcz, if_true]
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

ROADMAP for this and the other loop-based operations.  The generated `*_loop`
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
single-loop shape; `trim` adds a `lastNonzero`/`Array.extract` argument; `mul`
needs a nested double-loop invariant plus `index_mut` reasoning. -/
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

/-- `cpoly.mul` ↔ `CPolynomial.Raw.mul`. -/
theorem mul_spec (v w : alloc.vec.Vec Std.U64)
    (hv : VecReduced v) (hw : VecReduced w) :
    cpoly.mul v w ⦃ z => VecReduced z ∧
        toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ⦄ := by
  -- ROADMAP (the one remaining obligation; everything it depends on is proved).
  --
  -- Target: after the convolution, the accumulator `r1` satisfies
  --   (toRaw r1).coeff k = ∑_{i ∈ range (k+1)} (toRaw v).coeff i * (toRaw w).coeff (k-i)
  -- which is exactly `CompPoly.CPolynomial.Raw.mul_coeff` for `(toRaw v * toRaw w)`.
  -- Then `toRaw (trim r1) = (toRaw r1).trim = (toRaw v * toRaw w)` by
  -- `eq_of_equiv` (equal coefficients ⇒ equal trims), and `mul = mulRaw |>.trim`.
  --
  -- Three loop lemmas (all via `loop.spec_decr_nat`, like the proofs above):
  --  1. `mul_loop0`  (zero-fill): result `z.val = List.replicate n 0#u64`
  --       (single loop; `List.replicate_succ'` extends by one each step).
  --  2. `mul_loop1_loop0` (inner): for fixed outer `i`, performs
  --       `r[i+j] += p[i]*q[j]` for `j ∈ [0,nq)`.  Each step reads `r[idx]`,
  --       `fadd`s `p[i]*q[j]`, and writes back via
  --       `Aeneas.Std.Vec.index_mut_usize_spec` (`back x = r.set idx x`, i.e.
  --       `r.val.set idx x`).  Invariant: `toF (r'.val[k])` equals the original
  --       plus `∑_{j'<j, i+j'=k} toF p[i] * toF q[j']`.
  --  3. `mul_loop1` (outer): accumulates 1.+2. into the full convolution
  --       `toF (r1.val[k]) = ∑_{i'<np} toF p[i'] * toF q[k-i']`.
  -- Compose with `spec_bind`/`spec_mono` + `trim_spec`, discharging the
  -- `np = 0` / `nq = 0` cases (empty product) up front.
  sorry

end CPolyEquiv
