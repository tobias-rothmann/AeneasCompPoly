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
     header of `field.rs`.  This is exactly where the Hachi prime is tighter than
     BabyBear/KoalaBear, and it still holds with about `859 * 2^32` to spare on
     the multiplication.

     On the Rust side `Fp`'s `u64` is *private* and `Fp::new` reduces, so `Red`
     holds of every value a caller can construct.  Nothing here relies on that —
     `Red` is still carried as a hypothesis, because Aeneas cannot see a Rust
     privacy boundary — but it is why the hypothesis is discharged in practice.

  2. Extension layer.  A generated `cpoly.field.Ext4` struct represents the
     element of `Hachi.Ext4` whose four little-endian coefficients are the
     `toK`-images of its fields (`toExt`), under the componentwise invariant
     `Reduced`.  The extracted `Add`, `Sub`, `Neg` and `Mul` impls are shown total
     and to commute with `Ext`'s ring operations, as is the heterogeneous
     `Mul<Ext4> for Fp`.  (That last one has no caller in the crate: every scalar
     in the polynomial layers is an `Ext4`, so those sites use `Ext4 * Ext4`.  It
     is public, so it carries a spec.)
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
expression is a local it has just bound.  That shape is everywhere, because the
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
  step as ⟨sum, hsum⟩
  have hsum_lt : sum.val < 2 * P := by
    rw [hsum]
    omega
  by_cases hP_le : P ≤ sum.val
  · have hif : sum ≥ cpoly.field.P := by
      simpa [cpoly_P_val] using hP_le
    rw [if_pos hif]
    step as ⟨out, hout⟩
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout, cpoly_P_val]
      omega
    · have hp_le : cpoly.field.P.val ≤ sum.val := by
        simpa [cpoly_P_val] using hP_le
      unfold toK
      rw [hout, Nat.cast_sub hp_le, cpoly_P_val, ZMod.natCast_self, hsum, Nat.cast_add]
      simp
  · have hif : ¬ sum ≥ cpoly.field.P := by
      intro h
      apply hP_le
      simpa [cpoly_P_val] using h
    rw [if_neg hif]
    refine ⟨?_, ?_⟩
    · unfold Red
      simpa [cpoly_P_val] using Nat.lt_of_not_ge hP_le
    · unfold toK
      rw [hsum, Nat.cast_add]

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
  by_cases hba : b.val ≤ a.val
  · have hif : a ≥ b := by simpa using hba
    rw [if_pos hif]
    step as ⟨out, hout⟩
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout]
      omega
    · unfold toK
      rw [hout, Nat.cast_sub hba]
  · have hif : ¬ a ≥ b := by
      intro h
      apply hba
      simpa using h
    rw [if_neg hif]
    step as ⟨sum, hsum⟩
    step as ⟨out, hout⟩
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout, hsum, cpoly_P_val]
      omega
    · have hbi : b.val ≤ a.val + P := by omega
      have hbs : b.val ≤ sum.val := by
        rw [hsum, cpoly_P_val]
        exact hbi
      unfold toK
      rw [hout, Nat.cast_sub hbs, hsum, Nat.cast_add,
        cpoly_P_val, ZMod.natCast_self]
      ring

/-- `impl Neg for Fp`. -/
@[step]
theorem fp_neg_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg a ⦃ c => Red c ∧ toK c = - toK a ⦄ := by
  unfold Red at ha
  rw [cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg]
  by_cases hzero : a = 0#u64
  · rw [if_pos hzero, hzero]
    refine ⟨?_, ?_⟩
    · unfold Red; decide
    · unfold toK; simp
  · rw [if_neg hzero]
    step as ⟨out, hout⟩
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout, cpoly_P_val]
      have ha_pos : 0 < a.val := by
        apply Nat.pos_of_ne_zero
        intro ha0
        apply hzero
        apply U64.bv_eq_imp_eq
        apply BitVec.eq_of_toNat_eq
        simpa using ha0
      omega
    · have hai : a.val ≤ cpoly.field.P.val := by
        simpa [cpoly_P_val] using Nat.le_of_lt ha
      unfold toK
      rw [hout, Nat.cast_sub hai, cpoly_P_val, ZMod.natCast_self]
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

/-- A product of two reduced Hachi representatives is a checked `u64` product.
The F2 accumulator deliberately uses this fact before preserving carries
separately. -/
theorem red_mul_fits_u64 (x y : cpoly.field.Fp) (hx : Red x) (hy : Red y) :
    x.val * y.val ≤ U64.max := by
  unfold Red at hx hy
  have hx' : x.val ≤ P - 1 := by omega
  have hy' : y.val ≤ P - 1 := by omega
  calc
    x.val * y.val ≤ (P - 1) * (P - 1) := Nat.mul_le_mul hx' hy'
    _ ≤ U64.max := by norm_num [U64.max_eq]

/-- The field image of one machine-word carry. -/
def carryK (b : Bool) : K := if b then 1 else 0

/-- The field image of the two-word integer represented by an F2 accumulator. -/
def wideK (acc : Std.U64 × Std.U64) : K :=
  (((acc.2 : Std.U64).val) : K) * 9801 + (((acc.1 : Std.U64).val) : K)

@[simp] theorem u64_size_toK : (U64.size : K) = 9801 := by
  rw [U64.size, U64.numBits]
  have hP : P = 4294967197 := by norm_num [P, Hachi.fieldSize]
  apply (ZMod.natCast_eq_natCast_iff' 18446744073709551616 9801 P).2
  rw [hP]

/-- `overflowing_add` preserves the represented integer, with its boolean
carry read as either zero or one. -/
theorem overflowing_add_toK (x y : Std.U64) :
    (((core.num.U64.overflowing_add x y).1).val : K) +
        carryK ((core.num.U64.overflowing_add x y).2) * 9801 =
      (x.val : K) + (y.val : K) := by
  have h := core.num.U64.overflowing_add_eq x y
  dsimp only at h
  by_cases overflow : x.val + y.val > U64.max
  · rw [if_pos (by simpa using overflow)] at h
    obtain ⟨hval, hcarry⟩ := h
    rw [hcarry]
    have hvalK := congrArg (fun n : Nat => (n : K)) hval
    simpa [carryK, u64_size_toK] using hvalK
  · rw [if_neg (by simpa using overflow)] at h
    obtain ⟨hval, hcarry⟩ := h
    rw [hcarry]
    have hvalK := congrArg (fun n : Nat => (n : K)) hval
    simpa [carryK] using hvalK

/-- Adding one raw reduced-coefficient product preserves the field image of
the two-word accumulator.  The `u64` low word is allowed to wrap; its carry is
recorded in the high word. -/
@[step]
theorem add_product_spec (acc : Std.U64 × Std.U64) (a b : cpoly.field.Fp)
    (ha : Red a) (hb : Red b) (hacc : acc.2.val ≤ 5) :
    cpoly.field.add_product acc a b ⦃ out =>
      out.2.val ≤ acc.2.val + 1 ∧ wideK out = wideK acc + toK a * toK b ⦄ := by
  rw [cpoly.field.add_product]
  apply spec_bind (U64.mul_spec (red_mul_fits_u64 a b ha hb))
  intro product hproduct
  simp only [lift]
  simp
  apply spec_bind (U64.add_spec (by
    change acc.2.val + (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val ≤ U64.max
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [U64.max_eq] at hacc ⊢ <;> omega))
  intro high hhigh
  simp only [spec_ok]
  simp only [wideK]
  change high.val = acc.2.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val at hhigh
  have hcarry :
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val =
        if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add acc.1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, UScalar.val]
  constructor
  · rw [hhigh, hcarry]
    split <;> omega
  ·
    change ((high.val : K) * 9801 +
      ((core.num.U64.overflowing_add acc.1 product).1.val : K)) = _
    rw [hhigh]
    rw [hcarry]
    have hcarryK :
        ((if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 : Nat) : K) =
          carryK (core.num.U64.overflowing_add acc.1 product).2 := by
      simp [carryK]
    have hproductK : (product.val : K) = toK a * toK b := by
      rw [hproduct]
      unfold toK
      norm_cast
    rw [Nat.cast_add, hcarryK, ← hproductK]
    have hoverflow := overflowing_add_toK acc.1 product
    linear_combination hoverflow

/-- Adding twice one raw reduced-coefficient product preserves the field image
of the accumulator.  This is the `2 * aᵢbⱼ` wrap contribution in `Ext4::mul`. -/
@[step]
theorem add_double_product_spec (acc : Std.U64 × Std.U64) (a b : cpoly.field.Fp)
    (ha : Red a) (hb : Red b) (hacc : acc.2.val ≤ 5) :
    cpoly.field.add_double_product acc a b ⦃ out =>
      out.2.val ≤ acc.2.val + 2 ∧ wideK out = wideK acc + 2 * toK a * toK b ⦄ := by
  rw [cpoly.field.add_double_product]
  apply spec_bind (U64.mul_spec (red_mul_fits_u64 a b ha hb))
  intro product hproduct
  simp only [lift]
  simp
  change (do
    let high0 ← acc.2 + core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2
    let high1 ← high0 + core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add (core.num.U64.overflowing_add acc.1 product).1 product).2
    ok ((core.num.U64.overflowing_add (core.num.U64.overflowing_add acc.1 product).1 product).1,
      high1)) ⦃ out => out.2.val ≤ acc.2.val + 2 ∧
        wideK out = wideK acc + 2 * toK a * toK b ⦄
  apply spec_bind (U64.add_spec (by
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [U64.max_eq] at hacc ⊢ <;> omega))
  intro high0 hhigh0
  apply spec_bind (U64.add_spec (by
    have hcarry0 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val ≤ 1 := by
      cases (core.num.U64.overflowing_add acc.1 product).2 <;>
        simp [core.convert.num.FromU64Bool.from, UScalar.val]
    have : high0.val ≤ acc.2.val + 1 := by
      rw [hhigh0]
      omega
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [U64.max_eq] at hacc ⊢ <;> omega))
  intro high1 hhigh1
  simp only [spec_ok]
  have hcarry0 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val =
      if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add acc.1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, UScalar.val]
  have hcarry1 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).2).val =
      if (core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add
      (core.num.U64.overflowing_add acc.1 product).1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, UScalar.val]
  constructor
  · rw [hhigh1, hhigh0, hcarry0, hcarry1]
    split <;> split <;> omega
  · simp only [wideK]
    change ((high1.val : K) * 9801 +
      ((core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).1.val : K)) = _
    change high0.val = acc.2.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val at hhigh0
    change high1.val = high0.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add
          (core.num.U64.overflowing_add acc.1 product).1 product).2).val at hhigh1
    rw [hhigh1, hhigh0, hcarry0, hcarry1]
    have hcarry0K :
        ((if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 : Nat) : K) =
          carryK (core.num.U64.overflowing_add acc.1 product).2 := by
      simp [carryK]
    have hcarry1K :
        ((if (core.num.U64.overflowing_add
          (core.num.U64.overflowing_add acc.1 product).1 product).2 then 1 else 0 : Nat) : K) =
          carryK (core.num.U64.overflowing_add
            (core.num.U64.overflowing_add acc.1 product).1 product).2 := by
      simp [carryK]
    have hproductK : (product.val : K) = toK a * toK b := by
      rw [hproduct]
      unfold toK
      norm_cast
    simp only [Nat.cast_add]
    rw [hcarry0K, hcarry1K]
    have hoverflow0 := overflowing_add_toK acc.1 product
    have hoverflow1 := overflowing_add_toK
      (core.num.U64.overflowing_add acc.1 product).1 product
    linear_combination hoverflow0 + hoverflow1 + 2 * hproductK

/-- Adding four copies of one raw reduced-coefficient product preserves the
field image of the accumulator.  Squaring uses this for its two `4 * aᵢaⱼ`
cross terms, while keeping the product unreduced. -/
@[step]
theorem add_quadruple_product_spec (acc : Std.U64 × Std.U64) (a b : cpoly.field.Fp)
    (ha : Red a) (hb : Red b) (hacc : acc.2.val ≤ 3) :
    cpoly.field.add_quadruple_product acc a b ⦃ out =>
      out.2.val ≤ acc.2.val + 4 ∧ wideK out = wideK acc + 4 * toK a * toK b ⦄ := by
  rw [cpoly.field.add_quadruple_product]
  apply spec_bind (U64.mul_spec (red_mul_fits_u64 a b ha hb))
  intro product hproduct
  simp only [lift]
  simp
  have carry_val (carry : Bool) :
      (core.convert.num.FromU64Bool.from carry).val = if carry then 1 else 0 := by
    cases carry <;> simp [core.convert.num.FromU64Bool.from, UScalar.val]
  have carry_le (carry : Bool) :
      (core.convert.num.FromU64Bool.from carry).val ≤ 1 := by
    rw [carry_val]
    split <;> omega
  let low0 := (core.num.U64.overflowing_add acc.1 product).1
  let carry0 := (core.num.U64.overflowing_add acc.1 product).2
  let low1 := (core.num.U64.overflowing_add low0 product).1
  let carry1 := (core.num.U64.overflowing_add low0 product).2
  let low2 := (core.num.U64.overflowing_add low1 product).1
  let carry2 := (core.num.U64.overflowing_add low1 product).2
  let low3 := (core.num.U64.overflowing_add low2 product).1
  let carry3 := (core.num.U64.overflowing_add low2 product).2
  change (do
    let high0 ← acc.2 + core.convert.num.FromU64Bool.from carry0
    let high1 ← high0 + core.convert.num.FromU64Bool.from carry1
    let high2 ← high1 + core.convert.num.FromU64Bool.from carry2
    let high3 ← high2 + core.convert.num.FromU64Bool.from carry3
    ok (low3, high3)) ⦃ out => out.2.val ≤ acc.2.val + 4 ∧
        wideK out = wideK acc + 4 * toK a * toK b ⦄
  apply spec_bind (U64.add_spec (by
    have hcarry := carry_le carry0
    norm_num [U64.max_eq] at hacc ⊢
    omega))
  intro high0 hhigh0
  apply spec_bind (U64.add_spec (by
    have hcarry := carry_le carry1
    have hcarry0 := carry_le carry0
    change high0.val = acc.2.val + (core.convert.num.FromU64Bool.from carry0).val at hhigh0
    have hhigh0' : high0.val ≤ acc.2.val + 1 := by omega
    norm_num [U64.max_eq] at hacc ⊢
    omega))
  intro high1 hhigh1
  apply spec_bind (U64.add_spec (by
    have hcarry := carry_le carry2
    have hcarry0 := carry_le carry0
    have hcarry1 := carry_le carry1
    change high0.val = acc.2.val + (core.convert.num.FromU64Bool.from carry0).val at hhigh0
    change high1.val = high0.val + (core.convert.num.FromU64Bool.from carry1).val at hhigh1
    have hhigh0' : high0.val ≤ acc.2.val + 1 := by
      have hcarry0 := carry_le carry0
      omega
    have hhigh1' : high1.val ≤ acc.2.val + 2 := by omega
    norm_num [U64.max_eq] at hacc ⊢
    omega))
  intro high2 hhigh2
  apply spec_bind (U64.add_spec (by
    have hcarry := carry_le carry3
    have hcarry0 := carry_le carry0
    have hcarry1 := carry_le carry1
    have hcarry2 := carry_le carry2
    change high0.val = acc.2.val + (core.convert.num.FromU64Bool.from carry0).val at hhigh0
    change high1.val = high0.val + (core.convert.num.FromU64Bool.from carry1).val at hhigh1
    change high2.val = high1.val + (core.convert.num.FromU64Bool.from carry2).val at hhigh2
    have hhigh0' : high0.val ≤ acc.2.val + 1 := by
      have hcarry0 := carry_le carry0
      omega
    have hhigh1' : high1.val ≤ acc.2.val + 2 := by
      have hcarry1 := carry_le carry1
      omega
    have hhigh2' : high2.val ≤ acc.2.val + 3 := by omega
    norm_num [U64.max_eq] at hacc ⊢
    omega))
  intro high3 hhigh3
  simp only [spec_ok]
  change high0.val = acc.2.val + (core.convert.num.FromU64Bool.from carry0).val at hhigh0
  change high1.val = high0.val + (core.convert.num.FromU64Bool.from carry1).val at hhigh1
  change high2.val = high1.val + (core.convert.num.FromU64Bool.from carry2).val at hhigh2
  change high3.val = high2.val + (core.convert.num.FromU64Bool.from carry3).val at hhigh3
  constructor
  · rw [hhigh3, hhigh2, hhigh1, hhigh0]
    rw [carry_val carry0, carry_val carry1, carry_val carry2, carry_val carry3]
    split <;> split <;> split <;> split <;> omega
  · simp only [wideK]
    change ((high3.val : K) * 9801 + (low3.val : K)) = _
    rw [hhigh3, hhigh2, hhigh1, hhigh0]
    have hcarry0K :
        ((if carry0 then 1 else 0 : Nat) : K) = carryK carry0 := by simp [carryK]
    have hcarry1K :
        ((if carry1 then 1 else 0 : Nat) : K) = carryK carry1 := by simp [carryK]
    have hcarry2K :
        ((if carry2 then 1 else 0 : Nat) : K) = carryK carry2 := by simp [carryK]
    have hcarry3K :
        ((if carry3 then 1 else 0 : Nat) : K) = carryK carry3 := by simp [carryK]
    have hproductK : (product.val : K) = toK a * toK b := by
      rw [hproduct]
      unfold toK
      norm_cast
    simp only [Nat.cast_add]
    rw [carry_val carry0, carry_val carry1, carry_val carry2, carry_val carry3,
      hcarry0K, hcarry1K, hcarry2K, hcarry3K]
    have hoverflow0 := overflowing_add_toK acc.1 product
    have hoverflow1 := overflowing_add_toK low0 product
    have hoverflow2 := overflowing_add_toK low1 product
    have hoverflow3 := overflowing_add_toK low2 product
    linear_combination hoverflow0 + hoverflow1 + hoverflow2 + hoverflow3 + 4 * hproductK

/-- F2's two-word reduction is a canonical base-field representative.  The
accumulator high word is at most seven in the only call sites below. -/
@[step]
theorem reduce_wide_spec (low high : Std.U64) (hhigh : high.val ≤ 7) :
    cpoly.field.reduce_wide low high ⦃ out =>
      Red out ∧ toK out = wideK (low, high) ⦄ := by
  rw [cpoly.field.reduce_wide]
  rw [cpoly.field.reduce_wide.LIMB]
  step as ⟨limb, hlimb⟩
  norm_num [U64.size, U64.numBits] at hlimb
  have hshift : ((1 <<< 32 : Nat) % 18446744073709551616) = 4294967296 := by
    decide
  rw [hshift] at hlimb
  step as ⟨r0, hr0⟩
  step as ⟨q0, hq0⟩
  step as ⟨x0, hx0⟩
  step as ⟨s0, hs0⟩
  step as ⟨x1, hx1⟩
  step as ⟨folded_once, hfolded_once⟩
  step as ⟨r1, hr1⟩
  step as ⟨q1, hq1⟩
  step as ⟨x2, hx2⟩
  step as ⟨folded_twice, hfolded_twice⟩
  have hdecomp0 : r0.val + 4294967296 * q0.val = low.val := by
    rw [hr0, hq0, hlimb]
    exact Nat.mod_add_div low.val 4294967296
  have hdecomp1 : r1.val + 4294967296 * q1.val = folded_once.val := by
    rw [hr1, hq1, hlimb]
    exact Nat.mod_add_div folded_once.val 4294967296
  have hL : ((4294967296 : Nat) : K) = (99 : K) := by
    have hP : P = 4294967197 := by norm_num [P, Hachi.fieldSize]
    apply (ZMod.natCast_eq_natCast_iff' 4294967296 99 P).2
    rw [hP]
  have hdecomp0K' := congrArg (fun n : Nat => (n : K)) hdecomp0
  have hdecomp0K : (r0.val : K) + ((4294967296 : Nat) : K) * (q0.val : K) = (low.val : K) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hdecomp0K'
  have hdecomp1K' := congrArg (fun n : Nat => (n : K)) hdecomp1
  have hdecomp1K : (r1.val : K) + ((4294967296 : Nat) : K) * (q1.val : K) = (folded_once.val : K) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hdecomp1K'
  have htwiceK' := congrArg (fun n : Nat => (n : K)) hfolded_twice
  have htwiceK : (folded_twice.val : K) = (r1.val : K) + (x2.val : K) := by
    simpa only [Nat.cast_add] using htwiceK'
  have honceK' := congrArg (fun n : Nat => (n : K)) hfolded_once
  have honceK : (folded_once.val : K) = (s0.val : K) + (x1.val : K) := by
    simpa only [Nat.cast_add] using honceK'
  have hs0K' := congrArg (fun n : Nat => (n : K)) hs0
  have hs0K : (s0.val : K) = (r0.val : K) + (x0.val : K) := by
    simpa only [Nat.cast_add] using hs0K'
  have hx0K' := congrArg (fun n : Nat => (n : K)) hx0
  have hx0K : (x0.val : K) = ((99 : Nat) : K) * (q0.val : K) := by
    simpa only [Nat.cast_mul] using hx0K'
  have hx1K' := congrArg (fun n : Nat => (n : K)) hx1
  have hx1K : (x1.val : K) = ((9801 : Nat) : K) * (high.val : K) := by
    simpa only [Nat.cast_mul] using hx1K'
  have hx2K' := congrArg (fun n : Nat => (n : K)) hx2
  have hx2K : (x2.val : K) = ((99 : Nat) : K) * (q1.val : K) := by
    simpa only [Nat.cast_mul] using hx2K'
  have hfoldedK : (folded_twice.val : K) = wideK (low, high) := by
    calc
      (folded_twice.val : K) = (r1.val : K) + ((99 : Nat) : K) * (q1.val : K) := by
        rw [htwiceK, hx2K]
      _ = (r1.val : K) + ((4294967296 : Nat) : K) * (q1.val : K) := by
        rw [hL]
        norm_num
      _ = (folded_once.val : K) := hdecomp1K
      _ = (r0.val : K) + ((99 : Nat) : K) * (q0.val : K) +
        ((9801 : Nat) : K) * (high.val : K) := by
        rw [honceK, hs0K, hx0K, hx1K]
      _ = (low.val : K) + ((9801 : Nat) : K) * (high.val : K) := by
        rw [hL] at hdecomp0K
        linear_combination hdecomp0K
      _ = wideK (low, high) := by
        simp only [wideK]
        ring
  have hlow : low.val < 18446744073709551616 := by
    have hlow' := low.hBounds
    norm_num [UScalarTy.U64_numBits_eq] at hlow'
    exact hlow'
  have hq0 : q0.val < 4294967296 := by
    rw [hq0, hlimb]
    apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
    norm_num
    exact hlow
  have hr0 : r0.val < 4294967296 := by
    rw [hr0, hlimb]
    exact Nat.mod_lt _ (by norm_num)
  have hs0 : s0.val < 429496729600 := by
    rw [hs0, hx0]
    omega
  have hx1 : x1.val ≤ 68607 := by
    rw [hx1]
    omega
  have hfolded_once : folded_once.val < 433791696896 := by
    rw [hfolded_once]
    omega
  have hq1 : q1.val < 101 := by
    rw [hq1, hlimb]
    apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
    norm_num
    exact hfolded_once
  have hr1 : r1.val < 4294967296 := by
    rw [hr1, hlimb]
    exact Nat.mod_lt _ (by norm_num)
  have hfolded_twice : folded_twice.val < 4294977196 := by
    rw [hfolded_twice, hx2]
    omega
  have hP : P = 4294967197 := by norm_num [P, Hachi.fieldSize]
  have htwice_twoP : folded_twice.val < 2 * P := by
    rw [hP]
    omega
  by_cases hP_le : P ≤ folded_twice.val
  · have hif : folded_twice ≥ cpoly.field.P := by
      simpa [cpoly_P_val] using hP_le
    rw [if_pos hif]
    step as ⟨out, hout⟩
    · simpa [cpoly_P_val] using hP_le
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout, cpoly_P_val, hP] at *
      omega
    · have hp_le : cpoly.field.P.val ≤ folded_twice.val := by
        simpa [cpoly_P_val] using hP_le
      unfold toK
      rw [hout, Nat.cast_sub hp_le, cpoly_P_val, ZMod.natCast_self]
      simpa using hfoldedK
  · have hif : ¬ folded_twice ≥ cpoly.field.P := by
      intro h
      apply hP_le
      simpa [cpoly_P_val] using h
    rw [if_neg hif]
    refine ⟨?_, hfoldedK⟩
    unfold Red
    simpa [cpoly_P_val] using Nat.lt_of_not_ge hP_le

/-- The private reduction helper is the direct field multiplication by the
extension constant. -/
@[step]
theorem mul_by_w_spec (t : cpoly.field.Fp) (ht : Red t) :
    cpoly.field.mul_by_w t ⦃ u => Red u ∧ toK u = toK cpoly.field.W * toK t ⦄ := by
  rw [cpoly.field.mul_by_w]
  step as ⟨u, ru, eu⟩
  refine ⟨ru, ?_⟩
  rw [eu]
  unfold toK
  rw [cpoly_W_val]
  ring

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

set_option maxRecDepth 16384 in
/-- `impl Mul for Ext4`.

The Rust code forms the seven schoolbook coefficients `t0 .. t6` and folds the
high half back with a factor of `W = 2` (`Y^4 = 2`); the reference `Ext.mul`
sums the two-branch kernel over all `(i, j) : Fin 4 × Fin 4`.  Expanding both
double sums with `sum_univ_four'` turns the identity into commutative-ring
algebra in the eight coefficients, which `ring` closes. -/
theorem ext_mul_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨c0, hc0bound, hc0⟩
  step as ⟨c1, hc1bound, hc1⟩
  step as ⟨c2, hc2bound, hc2⟩
  step as ⟨c3, hc3bound, hc3⟩
  step as ⟨c01, hc01bound, hc01⟩
  step as ⟨c11, hc11bound, hc11⟩
  step as ⟨c21, hc21bound, hc21⟩
  step as ⟨c31, hc31bound, hc31⟩
  step as ⟨c02, hc02bound, hc02⟩
  step as ⟨c12, hc12bound, hc12⟩
  step as ⟨c22, hc22bound, hc22⟩
  step as ⟨c32, hc32bound, hc32⟩
  step as ⟨c03, hc03bound, hc03⟩
  step as ⟨c13, hc13bound, hc13⟩
  step as ⟨c23, hc23bound, hc23⟩
  step as ⟨c33, hc33bound, hc33⟩
  change (do
    let f ← cpoly.field.reduce_wide c03.1 c03.2
    let f1 ← cpoly.field.reduce_wide c13.1 c13.2
    let f2 ← cpoly.field.reduce_wide c23.1 c23.2
    let f3 ← cpoly.field.reduce_wide c33.1 c33.2
    ok ({ c0 := f, c1 := f1, c2 := f2, c3 := f3 } : cpoly.field.Ext4)) ⦃ c =>
      Reduced c ∧ toExt c = toExt a * toExt b ⦄
  step as ⟨f0, rf0, ef0⟩
  step as ⟨f1, rf1, ef1⟩
  step as ⟨f2, rf2, ef2⟩
  step as ⟨f3, rf3, ef3⟩
  have ec0 : wideK c03 = toK a.c0 * toK b.c0 +
      2 * toK a.c1 * toK b.c3 + 2 * toK a.c2 * toK b.c2 + 2 * toK a.c3 * toK b.c1 := by
    rw [hc03, hc02, hc01, hc0]
    simp only [wideK]
    norm_num
  have ec1 : wideK c13 = toK a.c0 * toK b.c1 + toK a.c1 * toK b.c0 +
      2 * toK a.c2 * toK b.c3 + 2 * toK a.c3 * toK b.c2 := by
    rw [hc13, hc12, hc11, hc1]
    simp only [wideK]
    norm_num
  have ec2 : wideK c23 = toK a.c0 * toK b.c2 + toK a.c1 * toK b.c1 +
      toK a.c2 * toK b.c0 + 2 * toK a.c3 * toK b.c3 := by
    rw [hc23, hc22, hc21, hc2]
    simp only [wideK]
    norm_num
  have ec3 : wideK c33 = toK a.c0 * toK b.c3 + toK a.c1 * toK b.c2 +
      toK a.c2 * toK b.c1 + toK a.c3 * toK b.c0 := by
    rw [hc33, hc32, hc31, hc3]
    simp only [wideK]
    norm_num
  refine ⟨⟨rf0, rf1, rf2, rf3⟩, ?_⟩
  apply Ext.ext; intro i
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  rw [Ext.coeff_mul, sum_univ_four' Hachi.ext4Params_d]
  simp only [sum_univ_four' Hachi.ext4Params_d, coeff_toExt, Hachi.ext4Params_W, h4]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, ef0, ef1, ef2, ef3, ec0, ec1, ec2, ec3] <;>
    norm_num <;>
    ring

attribute [step] ext_mul_spec

/- The specialized `Ext4::square` uses the product symmetry: four diagonal
products and six off-diagonal products, rather than the general multiplier's
sixteen.  Its raw accumulators are discharged with the same two-word reduction
contract as `ext_mul_spec`. -/
@[step]
theorem ext_square_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.Ext4.square a
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt a ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  rw [cpoly.field.Ext4.square]
  step as ⟨c0, hc0bound, hc0⟩
  step as ⟨c01, hc01bound, hc01⟩
  step as ⟨c02, hc02bound, hc02⟩
  step as ⟨c1, hc1bound, hc1⟩
  step as ⟨c11, hc11bound, hc11⟩
  step as ⟨c2, hc2bound, hc2⟩
  step as ⟨c21, hc21bound, hc21⟩
  step as ⟨c22, hc22bound, hc22⟩
  step as ⟨c3, hc3bound, hc3⟩
  step as ⟨c31, hc31bound, hc31⟩
  change (do
    let f ← cpoly.field.reduce_wide c02.1 c02.2
    let f1 ← cpoly.field.reduce_wide c11.1 c11.2
    let f2 ← cpoly.field.reduce_wide c22.1 c22.2
    let f3 ← cpoly.field.reduce_wide c31.1 c31.2
    ok ({ c0 := f, c1 := f1, c2 := f2, c3 := f3 } : cpoly.field.Ext4)) ⦃ c =>
      Reduced c ∧ toExt c = toExt a * toExt a ⦄
  step as ⟨f0, rf0, ef0⟩
  step as ⟨f1, rf1, ef1⟩
  step as ⟨f2, rf2, ef2⟩
  step as ⟨f3, rf3, ef3⟩
  have ec0 : wideK c02 = toK a.c0 * toK a.c0 +
      4 * toK a.c1 * toK a.c3 + 2 * toK a.c2 * toK a.c2 := by
    rw [hc02, hc01, hc0]
    simp only [wideK]
    norm_num
  have ec1 : wideK c11 = 2 * toK a.c0 * toK a.c1 +
      4 * toK a.c2 * toK a.c3 := by
    rw [hc11, hc1]
    simp only [wideK]
    norm_num
  have ec2 : wideK c22 = 2 * toK a.c0 * toK a.c2 + toK a.c1 * toK a.c1 +
      2 * toK a.c3 * toK a.c3 := by
    rw [hc22, hc21, hc2]
    simp only [wideK]
    norm_num
  have ec3 : wideK c31 = 2 * toK a.c0 * toK a.c3 +
      2 * toK a.c1 * toK a.c2 := by
    rw [hc31, hc3]
    simp only [wideK]
    norm_num
  refine ⟨⟨rf0, rf1, rf2, rf3⟩, ?_⟩
  apply Ext.ext; intro i
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  rw [Ext.coeff_mul, sum_univ_four' Hachi.ext4Params_d]
  simp only [sum_univ_four' Hachi.ext4Params_d, coeff_toExt, Hachi.ext4Params_W, h4]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, ef0, ef1, ef2, ef3, ec0, ec1, ec2, ec3] <;>
    norm_num <;>
    ring

/-- `impl Mul<Ext4> for Fp` — scaling an extension element by a base-field one.

No caller in the crate reaches this impl — `univariate` and `multilinear` type
every scalar as an `Ext4`, so those sites resolve to `Ext4 * Ext4` — but it is
public, so it is proved.  Its reference is CompPoly's `SMul K F`:
`Ext.coeff_smul` says
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
evaluators use `self.0.clone()` to get a working copy of their table. -/
@[step]
theorem vec_clone_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    alloc.vec.CloneVec.clone cpoly.field.Ext4.Insts.CoreCloneClone v ⦃ z => z = v ⦄ := by
  rw [alloc.vec.CloneVec.clone]
  apply spec_mono (Slice.clone_spec (fun x _ => ext_clone_eq x))
  intro z hz
  exact hz.symm

end CPolyEquiv
