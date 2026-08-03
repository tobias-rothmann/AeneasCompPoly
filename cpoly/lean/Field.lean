/-
The **field layer** of the equivalence between the Aeneas-extracted Rust model
(`cpoly.field.*`, see `Generated.lean`) and CompPoly's reference
field (`CompPoly.Extension.Ext Hachi.ext4Params`, see
CompPoly/Fields/Hachi/Ext4.lean).

This is the shared base of the two polynomial layers, `Univariate.lean` and
`Multilinear.lean`; the file split mirrors `cpoly`'s `src/field.rs` /
`src/univariate.rs` / `src/multilinear.rs`.

The Rust crate fixes a concrete *extension* field.  Its base field is `F_P`
with `P = 2^32 - 99`, the Hachi prime (`CompPoly/Fields/Hachi.lean`), and the
coefficient field is the quartic extension `Ext4 = F_P[Y] / (Y^4 - 2)`
(`CompPoly/Fields/Hachi/Ext4.lean`).  On the CompPoly side we therefore
instantiate the generic coefficient ring `R` at `Hachi.Ext4`, which is
`CompPoly.Extension.Ext Hachi.ext4Params`, i.e. `Vector Hachi.Field 4`.

There are two layers here:

  1. Base-field layer.  The Rust type is `Fp`, a newtype over `u64`; Aeneas
     extracts a single-field tuple struct as a `@[reducible]` abbreviation, so
     `cpoly.field.Fp` *is* `Std.U64` here and the two spellings are
     interchangeable.  A word `u : Fp` represents the base-field element
     `toK u = (u.val : Hachi.Field)`.  Each operator impl on `Fp` (`Add`, `Sub`,
     `Mul`, `Neg`, and the `*Assign` forms) is shown to never fail and to commute
     with the corresponding `ZMod P` operation, *under the representation
     invariant* `Red u : u.val < P`.  `Red` is also what discharges the
     no-overflow side conditions in the generated `Result`-monad code: `P < 2^32`,
     so for reduced `a, b` we have `a + b < 2^33` and `a * b < 2^64` — see the
     header of `field.rs`.  This is tighter than it was for BabyBear/KoalaBear,
     but it still holds with about `859 * 2^32` to spare on the multiplication.

     On the Rust side `Fp`'s `u64` is *private* and `Fp::new` reduces, so `Red`
     holds of every value a caller can construct.  Nothing here relies on that —
     `Red` is still carried as a hypothesis, because Aeneas cannot see a Rust
     privacy boundary — but it is why the hypothesis is discharged in practice.

  2. Extension layer.  A generated `cpoly.field.Ext4` struct represents the
     element of `Hachi.Ext4` whose four little-endian coefficients are the
     `toK`-images of its fields (`toExt`), under the componentwise invariant
     `Reduced`.  The extracted `Add`, `Sub`, `Neg` and `Mul` impls are shown total
     and to commute with `Ext`'s ring operations, as is the heterogeneous
     `Mul<Ext4> for Fp` that the polynomial layers use for scalar multiplication.
     `ext_mul_spec` is the load-bearing one: the Rust code is an unrolled
     schoolbook product with the `Y^4 = 2` wrap folded in by hand, and the
     reference `Ext.mul` is a double `Finset` sum over `Fin 4 × Fin 4` with a
     two-branch kernel; they are reconciled by expanding both (`sum_univ_four'`)
     and `ring`.  `ext_is_zero_spec` relates `Ext4::is_zero` to `toExt a = 0`,
     which is what `Univariate.lean`'s `trim` needs.

Naming: the Rust operators are trait impls, so the generated names are the ones
Aeneas mangles from the impl headers — `cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add`
for `impl Add for Ext4`, and so on.  They are mechanical, and each spec below
names the Rust item it is about in its docstring.

The extension specs are `@[step]`, which is what lets the polynomial layers
walk through the generated code without naming them.

Specs are stated in Aeneas's triple form `m ⦃ r => post r ⦄`, which is the shape
the `step`/`progress` tactic consumes.  It is `Aeneas.Std.spec m post`, a
weakest-precondition predicate rather than a bare existential; use
`Aeneas.Std.spec_imp_exists` to read a triple as the total-correctness statement
`∃ r, m = ok r ∧ post r`.  Compose triples with `spec_bind` / `spec_mono`.
-/
import Generated
import CompPoly.Fields.Hachi.Ext4

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension

namespace CPolyEquiv

/-! ## A generic `List` helper

Nothing to do with the field; it lives here because both polynomial layers need
it and this is the file they share. -/

/-- Rewrite `getElem` under a list equality (sidesteps the dependent-motive
issue that blocks `rw` on `l[i]`). -/
theorem getElem_of_list_eq {α} {l l' : List α} (h : l = l') {i : ℕ}
    {hi : i < l.length} : l[i] = l'[i]'(h ▸ hi) := by cases h; rfl

/-! ## A `Result`-monad helper

Aeneas ends a `do` block with `let x ← m; ok x` whenever the Rust function's tail
expression is a local it has just bound.  That shape is everywhere now that the
operations are methods and trait impls which name their result before returning
it, and it blocks `spec_mono` from seeing the last call as the whole body. -/

/-- `m >>= ok` is `m`. -/
@[simp] theorem bind_ok_id {α : Type} (m : Result α) : (do let x ← m; ok x) = m := by
  cases m <;> rfl

/-! ## The field on the CompPoly side -/

/-- The base-field modulus, `2^32 - 99`. An `abbrev` so that `ZMod P` reduces to
`Fin P` and its `CommRing`/`BEq`/`DecidableEq` instances are found by synthesis. -/
abbrev P : ℕ := Hachi.fieldSize

/-- The base field. -/
abbrev K := Hachi.Field

/-- The field the Rust code computes in: the quartic extension of `K`. -/
abbrev F := Hachi.Ext4

/-- `CPolynomial.Raw.trim` (and hence `add`/`sub`/`mul`) needs a *lawful* `BEq`
on the coefficient ring. `Ext.instBEq` is the `Vector` one, so this is the
`Vector` instance transported along `Ext P = Vector F P.d`; instance search will
not unfold `Ext` on its own. -/
instance : LawfulBEq F := inferInstanceAs (LawfulBEq (Vector K Hachi.ext4Params.d))

/-! ## Base-field layer -/

/-- An `Fp` word interpreted as a base-field element. -/
def toK (u : cpoly.field.Fp) : K := (u.val : K)

/-- Representation invariant for a single base-field element: the word is
reduced mod `P`. Maintained by every base operation and required to discharge
the no-overflow obligations in the generated code. -/
def Red (u : cpoly.field.Fp) : Prop := u.val < P

/-- The generated modulus word `cpoly.field.P` has value `P` (it is `irreducible`). -/
@[simp, scalar_tac_simps]
theorem cpoly_P_val : (cpoly.field.P).val = P := by simp only [cpoly.field.P]; decide

/-- The generated extension constant `cpoly.field.W` has value `2`. -/
@[simp, scalar_tac_simps]
theorem cpoly_W_val : (cpoly.field.W).val = 2 := by simp only [cpoly.field.W]; decide

theorem cpoly_P_val_ne_zero : (cpoly.field.P).val ≠ 0 := by simp

/-- `cpoly.field.Fp.ZERO` is the zero word. -/
@[simp, scalar_tac_simps]
theorem cpoly_Fp_ZERO_val : (cpoly.field.Fp.ZERO).val = 0 := by
  simp only [cpoly.field.Fp.ZERO]; decide

/-- `cpoly.field.Fp.ONE` is the one word. -/
@[simp, scalar_tac_simps]
theorem cpoly_Fp_ONE_val : (cpoly.field.Fp.ONE).val = 1 := by
  simp only [cpoly.field.Fp.ONE]; decide

/-! ### The base-field operator impls

`impl Add for Fp` and friends. Each never fails, stays reduced, and computes the
matching `ZMod P` operation. -/

/-- `impl Add for Fp`. -/
@[step]
theorem fp_add_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      ⦃ c => Red c ∧ toK c = toK a + toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_add]

/-- `impl Mul for Fp`.  The `a * b` in the generated code is a *checked* `U64`
product; it succeeds because `P < 2^32` forces `a * b ≤ (P-1)^2 < 2^64`. -/
@[step]
theorem fp_mul_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b
      ⦃ c => Red c ∧ toK c = toK a * toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_mul]

/-- `impl Sub for Fp`. -/
@[step]
theorem fp_sub_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub a b
      ⦃ c => Red c ∧ toK c = toK a - toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub]
  step as ⟨i, hi⟩          -- i = a + P
  step as ⟨j, hj⟩          -- j = i - b   (b.val ≤ i.val auto-discharged)
  step as ⟨c, hc⟩          -- c = j % P
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · -- toK c = ↑(j % P) = ↑j = ↑(a + P - b) = ↑a + ↑P - ↑b = ↑a - ↑b   (↑P = 0)
    have hbi : b.val ≤ a.val + P := by scalar_tac
    simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hj, hi]
    rw [Nat.cast_sub hbi, Nat.cast_add, ZMod.natCast_self]
    ring

/-- `impl Neg for Fp`. -/
@[step]
theorem fp_neg_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg a ⦃ c => Red c ∧ toK c = - toK a ⦄ := by
  unfold Red at ha
  rw [cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg]
  step as ⟨i, hi⟩          -- i = P - a   (a.val ≤ P.val auto-discharged)
  step as ⟨c, hc⟩          -- c = i % P
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · have hai : a.val ≤ P := by scalar_tac
    simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi]
    rw [Nat.cast_sub hai, ZMod.natCast_self]
    ring

/-! ### The compound-assignment impls

`impl AddAssign for Fp` and friends delegate to the corresponding binary
operator, so each spec is a one-line corollary.  They are `@[step]` so that the
`+=` in `multilinear::dot` and the `*=` in the basis loops go through without the
caller naming them. -/

/-- `impl AddAssign for Fp`. -/
@[step]
theorem fp_add_assign_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithAddAssignFp.add_assign a b
      ⦃ c => Red c ∧ toK c = toK a + toK b ⦄ := by
  rw [cpoly.field.Fp.Insts.CoreOpsArithAddAssignFp.add_assign]; exact fp_add_spec a b ha hb

/-- `impl SubAssign for Fp`. -/
@[step]
theorem fp_sub_assign_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithSubAssignFp.sub_assign a b
      ⦃ c => Red c ∧ toK c = toK a - toK b ⦄ := by
  rw [cpoly.field.Fp.Insts.CoreOpsArithSubAssignFp.sub_assign]; exact fp_sub_spec a b ha hb

/-- `impl MulAssign for Fp`. -/
@[step]
theorem fp_mul_assign_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithMulAssignFp.mul_assign a b
      ⦃ c => Red c ∧ toK c = toK a * toK b ⦄ := by
  rw [cpoly.field.Fp.Insts.CoreOpsArithMulAssignFp.mul_assign]; exact fp_mul_spec a b ha hb

/-! ### Construction and observation -/

/-- A reduced word is the zero base-field element iff it is the zero word. -/
theorem toK_eq_zero_iff (u : cpoly.field.Fp) (hu : Red u) : toK u = 0 ↔ u.val = 0 := by
  unfold toK; unfold Red at hu
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hu, fun h => h ▸ dvd_zero P⟩

@[simp] theorem toK_zero_word : toK 0#u64 = 0 := by simp [toK]
@[simp] theorem toK_one_word : toK 1#u64 = 1 := by simp [toK]

theorem red_zero_word : Red 0#u64 := by unfold Red; decide
theorem red_one_word : Red 1#u64 := by unfold Red; decide

@[simp] theorem toK_Fp_ZERO : toK cpoly.field.Fp.ZERO = 0 := by
  simp only [toK, cpoly_Fp_ZERO_val]; simp

@[simp] theorem toK_Fp_ONE : toK cpoly.field.Fp.ONE = 1 := by
  simp only [toK, cpoly_Fp_ONE_val]; simp

theorem red_Fp_ZERO : Red cpoly.field.Fp.ZERO := by
  unfold Red; rw [cpoly_Fp_ZERO_val]; decide

theorem red_Fp_ONE : Red cpoly.field.Fp.ONE := by
  unfold Red; rw [cpoly_Fp_ONE_val]; decide

/-- The extension constant `W = 2` is reduced, so `Fp`'s `Mul` spec applies to
`W * _`. -/
theorem red_W : Red cpoly.field.W := by unfold Red; rw [cpoly_W_val]; decide

/-- ... and denotes the `W` of `Hachi.ext4Params`. -/
@[simp] theorem toK_W : toK cpoly.field.W = 2 := by simp only [toK, cpoly_W_val]; norm_num

/-- `Fp::new` reduces an arbitrary word into the field.  This is the only public
Rust constructor from a `u64`, and it is what makes `Red` an invariant of the
type rather than a precondition. -/
@[step]
theorem fp_new_spec (v : Std.U64) :
    cpoly.field.Fp.new v ⦃ c => Red c ∧ toK c = (v.val : K) ⦄ := by
  rw [cpoly.field.Fp.new]
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod]

/-- `impl From<u64> for Fp` is `Fp::new`. -/
@[step]
theorem fp_from_u64_spec (v : Std.U64) :
    cpoly.field.Fp.Insts.CoreConvertFromU64.from v ⦃ c => Red c ∧ toK c = (v.val : K) ⦄ := by
  rw [cpoly.field.Fp.Insts.CoreConvertFromU64.from]; exact fp_new_spec v

/-- `Fp::to_u64` returns the canonical representative. -/
@[step]
theorem fp_to_u64_spec (a : cpoly.field.Fp) :
    cpoly.field.Fp.to_u64 a ⦃ v => v = a ⦄ := by
  rw [cpoly.field.Fp.to_u64]; simp only [spec_ok]

/-- `Fp::is_zero` decides `toK a = 0`.  Reducedness is needed in both directions:
without it a word congruent to `0` but not equal to it would make the test
unsound. -/
@[step]
theorem fp_is_zero_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.is_zero a ⦃ b => (b = true ↔ toK a = 0) ⦄ := by
  rw [cpoly.field.Fp.is_zero]
  simp only [spec_ok, decide_eq_true_eq]
  rw [toK_eq_zero_iff a ha]
  constructor
  · intro h; rw [h]; rfl
  · intro h; scalar_tac

/-- The derived `impl PartialEq for Fp` decides equality *in the field*, given
reduced representatives: `Fp`'s `==` is word equality, and on reduced words that
is the same as equality mod `P`. -/
@[step]
theorem fp_eq_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreCmpPartialEqFp.eq a b ⦃ r => (r = true ↔ toK a = toK b) ⦄ := by
  rw [cpoly.field.Fp.Insts.CoreCmpPartialEqFp.eq]
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro h; rw [h]
  · intro h
    unfold Red at ha hb
    unfold toK at h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
    scalar_tac

/-- `impl Default for Fp` is the zero element. -/
@[step]
theorem fp_default_spec :
    cpoly.field.Fp.Insts.CoreDefaultDefault.default ⦃ c => Red c ∧ toK c = 0 ⦄ := by
  have hz : (core.default.DefaultU64.default : Std.U64) = 0#u64 := by rfl
  rw [cpoly.field.Fp.Insts.CoreDefaultDefault.default]
  simp only [spec_ok, hz]
  exact ⟨red_zero_word, toK_zero_word⟩

/-! ## Extension layer

`Hachi.Ext4` is `CompPoly.Extension.Ext Hachi.ext4Params`, whose carrier is a
dense little-endian coefficient vector of length `ext4Params.d = 4`.  The
generated `cpoly.field.Ext4` struct is the same data with the coefficients
spelled as four named `Fp` fields. -/

/-- The `i`-th coefficient of the element denoted by an `Ext4` struct.  Total in
`i`; only `i < 4` is ever used. -/
def extCoeff (a : cpoly.field.Ext4) : ℕ → K
  | 0 => toK a.c0
  | 1 => toK a.c1
  | 2 => toK a.c2
  | _ => toK a.c3

/-- An extracted `Ext4` struct read as an element of `Hachi.Ext4`. -/
def toExt (a : cpoly.field.Ext4) : F := Ext.ofFn (fun i => extCoeff a i.val)

/-- Representation invariant for one extension element: all four coefficients
are reduced base-field words. -/
def Reduced (a : cpoly.field.Ext4) : Prop :=
  Red a.c0 ∧ Red a.c1 ∧ Red a.c2 ∧ Red a.c3

/-- Representation invariant for a polynomial: every coefficient is reduced.

Stated about `alloc.vec.Vec`, which is what `cpoly.univariate.UnivariatePoly`,
`cpoly.multilinear.MultilinearPoly` and `cpoly.multilinear.MultilinearEvals` all reduce to. -/
def VecReduced (v : alloc.vec.Vec cpoly.field.Ext4) : Prop := ∀ a ∈ v.val, Reduced a

/-- The same, for a `&[Ext4]` parameter — the evaluation points of the
multilinear layer are slices. -/
def SliceReduced (s : Slice cpoly.field.Ext4) : Prop := ∀ a ∈ s.val, Reduced a

/-- `Vec::deref` — the `&Vec<T>` to `&[T]` coercion — is the identity on the
underlying list, so it moves the invariant across for free.  The multilinear
layer needs this at every call that passes a table where a `&[Ext4]` is expected. -/
@[simp] theorem deref_val (v : alloc.vec.Vec cpoly.field.Ext4) :
    (alloc.vec.Vec.deref v).val = v.val := rfl

theorem sliceReduced_deref {v : alloc.vec.Vec cpoly.field.Ext4} (h : VecReduced v) :
    SliceReduced (alloc.vec.Vec.deref v) := h

theorem vecReduced_of_sliceReduced {v : alloc.vec.Vec cpoly.field.Ext4}
    (h : SliceReduced (alloc.vec.Vec.deref v)) : VecReduced v := h

@[simp] theorem deref_len (v : alloc.vec.Vec cpoly.field.Ext4) :
    Slice.len (alloc.vec.Vec.deref v) = alloc.vec.Vec.len v := rfl

@[simp] theorem coeff_toExt (a : cpoly.field.Ext4) (i : Fin Hachi.ext4Params.d) :
    Ext.coeff (toExt a) i = extCoeff a i.val := Ext.coeff_ofFn _ _

/-- Every coefficient index of `Ext4` is one of the four literals.  Together with
`sum_univ_four'` this is all the `Fin ext4Params.d` reasoning the file needs. -/
theorem fin_four_cases (i : Fin Hachi.ext4Params.d) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by
  have := i.isLt
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  omega

/-- `Fin.sum_univ_four` for an index type whose bound is only *provably* `4`.
Stating it with the equation as a hypothesis lets `subst` fix up the dependent
`Fin n`, which is what `simp only [Hachi.ext4Params_d]` cannot do. -/
theorem sum_univ_four' {M : Type*} [AddCommMonoid M] {n : ℕ} (h : n = 4) (f : Fin n → M) :
    ∑ i : Fin n, f i
      = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ := by
  subst h; exact Fin.sum_univ_four f

/-- `toExt` is injective on the four coefficients: this is what makes the
representation faithful. -/
theorem toExt_eq_iff (a b : cpoly.field.Ext4) :
    toExt a = toExt b ↔ (toK a.c0 = toK b.c0 ∧ toK a.c1 = toK b.c1 ∧
      toK a.c2 = toK b.c2 ∧ toK a.c3 = toK b.c3) := by
  constructor
  · intro h
    have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrArg (fun z => Ext.coeff z ⟨0, by omega⟩) h; simpa [extCoeff] using this
    · have := congrArg (fun z => Ext.coeff z ⟨1, by omega⟩) h; simpa [extCoeff] using this
    · have := congrArg (fun z => Ext.coeff z ⟨2, by omega⟩) h; simpa [extCoeff] using this
    · have := congrArg (fun z => Ext.coeff z ⟨3, by omega⟩) h; simpa [extCoeff] using this
  · rintro ⟨h0, h1, h2, h3⟩
    apply Ext.ext; intro i
    simp only [coeff_toExt]
    rcases fin_four_cases i with h | h | h | h <;> rw [h] <;> simpa [extCoeff]

/-! ### The distinguished constants -/

theorem reduced_ZERO : Reduced cpoly.field.Ext4.ZERO := by
  simp only [cpoly.field.Ext4.ZERO, Reduced]
  exact ⟨red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩

theorem reduced_ONE : Reduced cpoly.field.Ext4.ONE := by
  simp only [cpoly.field.Ext4.ONE, Reduced]
  exact ⟨red_Fp_ONE, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩

@[simp] theorem toExt_ZERO : toExt cpoly.field.Ext4.ZERO = 0 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_zero]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp [extCoeff, cpoly.field.Ext4.ZERO]

@[simp] theorem toExt_ONE : toExt cpoly.field.Ext4.ONE = 1 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_one]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp [extCoeff, cpoly.field.Ext4.ONE]

/-- `cpoly.field.Ext4.GEN` is the adjoined fourth root of `2`. Not needed by any
spec below, but it pins the basis convention: the Rust `c1` field really is the
coefficient of `Y`, not of some other basis vector. -/
theorem toExt_GEN : toExt cpoly.field.Ext4.GEN = Hachi.ext4Gen := by
  apply Ext.ext; intro i
  rw [Hachi.ext4Gen_eq_gen]
  simp only [coeff_toExt, Ext.coeff_gen]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp [extCoeff, cpoly.field.Ext4.GEN]

/-! ### The extension operator impls -/

/-- `impl Add for Ext4`, coefficient-wise. -/
@[step]
theorem ext_add_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add a b
      ⦃ c => Reduced c ∧ toExt c = toExt a + toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_add, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `impl Sub for Ext4`, coefficient-wise. -/
@[step]
theorem ext_sub_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithSubExt4Ext4.sub a b
      ⦃ c => Reduced c ∧ toExt c = toExt a - toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithSubExt4Ext4.sub]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_sub, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `impl Neg for Ext4`, coefficient-wise. -/
@[step]
theorem ext_neg_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.Ext4.Insts.CoreOpsArithNegExt4.neg a
      ⦃ c => Reduced c ∧ toExt c = - toExt a ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  rw [cpoly.field.Ext4.Insts.CoreOpsArithNegExt4.neg]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_neg, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `impl Mul for Ext4`.

The Rust code forms the seven schoolbook coefficients `t0 .. t6` and folds the
high half back with a factor of `W = 2` (`Y^4 = 2`); the reference `Ext.mul`
sums the two-branch kernel over all `(i, j) : Fin 4 × Fin 4`.  Expanding both
double sums with `sum_univ_four'` turns the identity into commutative-ring
algebra in the eight coefficients, which `ring` closes. -/
@[step]
theorem ext_mul_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  have hW : Red cpoly.field.W := red_W
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨t0, rt0, et0⟩
  step as ⟨m01, rm01, em01⟩
  step as ⟨m10, rm10, em10⟩
  step as ⟨t1, rt1, et1⟩
  step as ⟨m02, rm02, em02⟩
  step as ⟨m11, rm11, em11⟩
  step as ⟨s2, rs2, es2⟩
  step as ⟨m20, rm20, em20⟩
  step as ⟨t2, rt2, et2⟩
  step as ⟨m03, rm03, em03⟩
  step as ⟨m12, rm12, em12⟩
  step as ⟨s3a, rs3a, es3a⟩
  step as ⟨m21, rm21, em21⟩
  step as ⟨s3b, rs3b, es3b⟩
  step as ⟨m30, rm30, em30⟩
  step as ⟨t3, rt3, et3⟩
  step as ⟨m13, rm13, em13⟩
  step as ⟨m22, rm22, em22⟩
  step as ⟨s4, rs4, es4⟩
  step as ⟨m31, rm31, em31⟩
  step as ⟨t4, rt4, et4⟩
  step as ⟨m23, rm23, em23⟩
  step as ⟨m32, rm32, em32⟩
  step as ⟨t5, rt5, et5⟩
  step as ⟨t6, rt6, et6⟩
  step as ⟨w4, rw4, ew4⟩
  step as ⟨c0, rc0, ec0⟩
  step as ⟨w5, rw5, ew5⟩
  step as ⟨c1, rc1, ec1⟩
  step as ⟨w6, rw6, ew6⟩
  step as ⟨c2, rc2, ec2⟩
  refine ⟨⟨rc0, rc1, rc2, rt3⟩, ?_⟩
  apply Ext.ext; intro i
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  rw [Ext.coeff_mul, sum_univ_four' Hachi.ext4Params_d]
  simp only [sum_univ_four' Hachi.ext4Params_d, coeff_toExt, Hachi.ext4Params_W, h4]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, ec0, ec1, ec2, et3, ew4, ew5, ew6, et0, et1, et2, et4, et5, et6,
      es2, es3a, es3b, es4, em01, em10, em02, em11, em20, em03, em12, em21, em30,
      em13, em22, em31, em23, em32, toK_W] <;>
    norm_num <;>
    ring

/-- `impl Mul<Ext4> for Fp` — scaling an extension element by a base-field one.

This is the heterogeneous impl the polynomial layers use for scalar
multiplication.  Its reference is CompPoly's `SMul K F`: `Ext.coeff_smul` says
`coeff (c • x) i = c * coeff x i`, which is coefficient-for-coefficient what the
Rust does. -/
@[step]
theorem ext_smul_spec (a : cpoly.field.Fp) (b : cpoly.field.Ext4)
    (ha : Red a) (hb : Reduced b) :
    cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = toK a • toExt b ⦄ := by
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_smul, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-! ### The extension compound-assignment impls -/

/-- `impl AddAssign for Ext4`. -/
@[step]
theorem ext_add_assign_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithAddAssignExt4.add_assign a b
      ⦃ c => Reduced c ∧ toExt c = toExt a + toExt b ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreOpsArithAddAssignExt4.add_assign]
  exact ext_add_spec a b ha hb

/-- `impl SubAssign for Ext4`. -/
@[step]
theorem ext_sub_assign_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithSubAssignExt4.sub_assign a b
      ⦃ c => Reduced c ∧ toExt c = toExt a - toExt b ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreOpsArithSubAssignExt4.sub_assign]
  exact ext_sub_spec a b ha hb

/-- `impl MulAssign for Ext4`. -/
@[step]
theorem ext_mul_assign_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulAssignExt4.mul_assign a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulAssignExt4.mul_assign]
  exact ext_mul_spec a b ha hb

/-! ### Extension construction and comparison -/

/-- `Ext4::new` assembles the four coefficients. -/
@[step]
theorem ext_new_spec (c0 c1 c2 c3 : cpoly.field.Fp)
    (h0 : Red c0) (h1 : Red c1) (h2 : Red c2) (h3 : Red c3) :
    cpoly.field.Ext4.new c0 c1 c2 c3
      ⦃ a => Reduced a ∧ Ext.coeff (toExt a) ⟨0, by rw [Hachi.ext4Params_d]; omega⟩ = toK c0 ⦄ := by
  rw [cpoly.field.Ext4.new]
  simp only [spec_ok]
  exact ⟨⟨h0, h1, h2, h3⟩, by simp [extCoeff]⟩

/-- `Ext4::from_base` embeds a base-field element as the constant coefficient;
this is CompPoly's `Ext.ofBase`. -/
@[step]
theorem ext_from_base_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Ext4.from_base a ⦃ c => Reduced c ∧ toExt c = Ext.ofBase (toK a) ⦄ := by
  rw [cpoly.field.Ext4.from_base]
  simp only [spec_ok]
  refine ⟨⟨ha, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_ofBase]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;> simp [extCoeff]

/-- `impl From<Fp> for Ext4` is `Ext4::from_base`. -/
@[step]
theorem ext_from_fp_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Ext4.Insts.CoreConvertFromFp.from a
      ⦃ c => Reduced c ∧ toExt c = Ext.ofBase (toK a) ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreConvertFromFp.from]; exact ext_from_base_spec a ha

/-- `impl From<u64> for Ext4` reduces, then embeds. -/
@[step]
theorem ext_from_u64_spec (v : Std.U64) :
    cpoly.field.Ext4.Insts.CoreConvertFromU64.from v
      ⦃ c => Reduced c ∧ toExt c = Ext.ofBase ((v.val : K)) ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreConvertFromU64.from]
  apply spec_bind (fp_new_spec v); rintro a ⟨haR, haF⟩
  apply spec_mono (ext_from_base_spec a haR); rintro c ⟨hcR, hcF⟩
  exact ⟨hcR, by rw [hcF, haF]⟩

/-- `Ext4::is_zero` decides whether the represented element is `0`.  Reducedness
is needed in both directions: without it a word congruent to `0` but not equal to
it would make the test unsound. -/
@[step]
theorem ext_is_zero_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.Ext4.is_zero a ⦃ b => (b = true ↔ toExt a = 0) ⦄ := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  have hcoeffs : toExt a = 0 ↔ (toK a.c0 = 0 ∧ toK a.c1 = 0 ∧ toK a.c2 = 0 ∧ toK a.c3 = 0) := by
    rw [← toExt_ZERO, toExt_eq_iff]
    simp only [cpoly.field.Ext4.ZERO, toK_Fp_ZERO]
  rw [cpoly.field.Ext4.is_zero, hcoeffs]
  apply spec_bind (fp_is_zero_spec a.c0 h0); intro b0 hb0
  by_cases e0 : b0 = true
  · rw [if_pos e0]
    apply spec_bind (fp_is_zero_spec a.c1 h1); intro b1 hb1
    by_cases e1 : b1 = true
    · rw [if_pos e1]
      apply spec_bind (fp_is_zero_spec a.c2 h2); intro b2 hb2
      by_cases e2 : b2 = true
      · rw [if_pos e2]
        apply spec_mono (fp_is_zero_spec a.c3 h3); intro b3 hb3
        rw [hb3, hb0.mp e0, hb1.mp e1, hb2.mp e2]
        simp
      · rw [if_neg e2]
        simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
        intro _ _ hc
        exact absurd (hb2.mpr hc) e2
    · rw [if_neg e1]
      simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ hc
      exact absurd (hb1.mpr hc) e1
  · rw [if_neg e0]
    simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro hc
    exact absurd (hb0.mpr hc) e0

/-- The derived `impl PartialEq for Ext4` decides equality *in the field*, given
reduced representatives.  Nothing in this development uses it — `trim` goes
through `Ext4::is_zero` — but it is public Rust API, so it gets a spec. -/
@[step]
theorem ext_eq_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq a b
      ⦃ r => (r = true ↔ toExt a = toExt b) ⦄ := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq, toExt_eq_iff]
  apply spec_bind (fp_eq_spec a.c0 b.c0 ha0 hb0); intro r0 hr0
  by_cases e0 : r0 = true
  · rw [if_pos e0]
    apply spec_bind (fp_eq_spec a.c1 b.c1 ha1 hb1); intro r1 hr1
    by_cases e1 : r1 = true
    · rw [if_pos e1]
      apply spec_bind (fp_eq_spec a.c2 b.c2 ha2 hb2); intro r2 hr2
      by_cases e2 : r2 = true
      · rw [if_pos e2]
        apply spec_mono (fp_eq_spec a.c3 b.c3 ha3 hb3); intro r3 hr3
        rw [hr3, hr0.mp e0, hr1.mp e1, hr2.mp e2]
        simp
      · rw [if_neg e2]
        simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
        intro _ _ hc
        exact absurd (hr2.mpr hc) e2
    · rw [if_neg e1]
      simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ hc
      exact absurd (hr1.mpr hc) e1
  · rw [if_neg e0]
    simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro hc
    exact absurd (hr0.mpr hc) e0

/-- `impl Default for Ext4` is the zero element. -/
@[step]
theorem ext_default_spec :
    cpoly.field.Ext4.Insts.CoreDefaultDefault.default
      ⦃ c => Reduced c ∧ toExt c = 0 ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreDefaultDefault.default]
  -- the generated code binds `Fp::default` once and reuses it for all four fields
  step as ⟨f, rf, ef⟩
  refine ⟨⟨rf, rf, rf, rf⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_zero]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, ef]

/-- `Ext4::clone` is the identity, which is what `Slice.clone_spec` needs when
the multilinear evaluators copy their table. -/
theorem ext_clone_eq (a : cpoly.field.Ext4) :
    cpoly.field.Ext4.Insts.CoreCloneClone.clone a = ok a := by
  rw [cpoly.field.Ext4.Insts.CoreCloneClone.clone]

/-- Hence `Vec<Ext4>::clone` returns the very same vector.  The multilinear
evaluators use `self.0.clone()` to get a working copy of their table, where the
previous version of the crate copied it entry by entry in a loop. -/
@[step]
theorem vec_clone_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    alloc.vec.CloneVec.clone cpoly.field.Ext4.Insts.CoreCloneClone v ⦃ z => z = v ⦄ := by
  rw [alloc.vec.CloneVec.clone]
  apply spec_mono (Slice.clone_spec (fun x _ => ext_clone_eq x))
  intro z hz
  exact hz.symm

end CPolyEquiv
