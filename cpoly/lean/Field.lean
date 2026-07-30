/-
The **field layer** of the equivalence between the Aeneas-extracted Rust model
(`cpoly.field.*`, see `Generated.lean`) and CompPoly's reference
field (`CompPoly.Extension.Ext Hachi.ext4Params`, see
CompPoly/Fields/Hachi/Ext4.lean).

This is the shared base of the two polynomial layers, `CPoly.lean`
(univariate) and `CMlPoly.lean` (multilinear); the file split mirrors
`cpoly`'s `src/field.rs` / `src/cpoly.rs` / `src/cmlpoly.rs`.

The Rust crate fixes a concrete *extension* field.  Its base field is `F_P`
with `P = 2^32 - 99`, the Hachi prime (`CompPoly/Fields/Hachi.lean`), and the
coefficient field is the quartic extension `Ext4 = F_P[Y] / (Y^4 - 2)`
(`CompPoly/Fields/Hachi/Ext4.lean`).  On the CompPoly side we therefore
instantiate the generic coefficient ring `R` at `Hachi.Ext4`, which is
`CompPoly.Extension.Ext Hachi.ext4Params`, i.e. `Vector Hachi.Field 4`.

There are two layers here:

  1. Base-field layer.  A machine word `u : U64` represents the base-field
     element `toK u = (u.val : Hachi.Field)`.  Each `cpoly.field` base operation
     (`fadd`, `fsub`, `fmul`, `fneg`) is shown to never fail and to commute with
     the corresponding `ZMod P` operation, *under the representation invariant*
     `Red u : u.val < P`.  `Red` is also what discharges the no-overflow side
     conditions in the generated `Result`-monad code: `P < 2^32`, so for reduced
     `a, b` we have `a + b < 2^33` and `a * b < 2^64` — see the header of
     `field.rs`.  This is tighter than it was for BabyBear/KoalaBear, but it
     still holds with about `859 * 2^32` to spare on the multiplication.

  2. Extension layer.  A generated `cpoly.field.Ext4` struct represents the
     element of `Hachi.Ext4` whose four little-endian coefficients are the
     `toK`-images of its fields (`toExt`), under the componentwise invariant
     `Reduced`.  The extracted `eadd`, `esub`, `eneg`, `emul` are shown total and
     to commute with `Ext`'s ring operations.  `emul_spec` is the load-bearing
     one: the Rust code is an unrolled schoolbook product with the `Y^4 = 2` wrap
     folded in by hand, and the reference `Ext.mul` is a double `Finset` sum over
     `Fin 4 × Fin 4` with a two-branch kernel; they are reconciled by expanding
     both (`sum_univ_four'`) and `ring`.  `is_ezero_spec` relates the hand-written
     zero test to `toExt a = 0`, which is what `CPoly.lean`'s `trim` needs.

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

/-- A machine word interpreted as a base-field element. -/
def toK (u : Std.U64) : K := (u.val : K)

/-- Representation invariant for a single base-field element: the word is
reduced mod `P`. Maintained by every base operation and required to discharge
the no-overflow obligations in the generated code. -/
def Red (u : Std.U64) : Prop := u.val < P

/-- The generated modulus word `cpoly.field.P` has value `P` (it is `irreducible`). -/
@[simp, scalar_tac_simps]
theorem cpoly_P_val : (cpoly.field.P).val = P := by simp only [cpoly.field.P]; decide

/-- The generated extension constant `cpoly.field.W` has value `2`. -/
@[simp, scalar_tac_simps]
theorem cpoly_W_val : (cpoly.field.W).val = 2 := by simp only [cpoly.field.W]; decide

theorem cpoly_P_val_ne_zero : (cpoly.field.P).val ≠ 0 := by simp

/-- `fadd` never fails, stays reduced, and computes base-field addition. -/
@[step]
theorem fadd_spec (a b : Std.U64) (ha : Red a) (hb : Red b) :
    cpoly.field.fadd a b ⦃ c => Red c ∧ toK c = toK a + toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.fadd]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_add]

/-- `fmul` never fails, stays reduced, and computes base-field multiplication.
The `a * b` in the generated code is a *checked* `U64` product; it succeeds
because `P < 2^32` forces `a * b ≤ (P-1)^2 < 2^64`. -/
@[step]
theorem fmul_spec (a b : Std.U64) (ha : Red a) (hb : Red b) :
    cpoly.field.fmul a b ⦃ c => Red c ∧ toK c = toK a * toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.fmul]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_mul]

/-- `fsub` never fails, stays reduced, and computes base-field subtraction. -/
@[step]
theorem fsub_spec (a b : Std.U64) (ha : Red a) (hb : Red b) :
    cpoly.field.fsub a b ⦃ c => Red c ∧ toK c = toK a - toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.fsub]
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

/-- `fneg` never fails, stays reduced, and computes base-field negation. -/
@[step]
theorem fneg_spec (a : Std.U64) (ha : Red a) :
    cpoly.field.fneg a ⦃ c => Red c ∧ toK c = - toK a ⦄ := by
  unfold Red at ha
  rw [cpoly.field.fneg]
  step as ⟨i, hi⟩          -- i = P - a   (a.val ≤ P.val auto-discharged)
  step as ⟨c, hc⟩          -- c = i % P
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · have hai : a.val ≤ P := by scalar_tac
    simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi]
    rw [Nat.cast_sub hai, ZMod.natCast_self]
    ring

/-- A reduced word is the zero base-field element iff it is the zero word. -/
theorem toK_eq_zero_iff (u : Std.U64) (hu : Red u) : toK u = 0 ↔ u.val = 0 := by
  unfold toK; unfold Red at hu
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hu, fun h => h ▸ dvd_zero P⟩

@[simp] theorem toK_zero_word : toK 0#u64 = 0 := by simp [toK]
@[simp] theorem toK_one_word : toK 1#u64 = 1 := by simp [toK]

theorem red_zero_word : Red 0#u64 := by unfold Red; decide
theorem red_one_word : Red 1#u64 := by unfold Red; decide

/-- The extension constant `W = 2` is reduced, so `fmul W _` is in scope of
`fmul_spec`. -/
theorem red_W : Red cpoly.field.W := by unfold Red; rw [cpoly_W_val]; decide

/-- ... and denotes the `W` of `Hachi.ext4Params`. -/
@[simp] theorem toK_W : toK cpoly.field.W = 2 := by simp only [toK, cpoly_W_val]; norm_num

/-! ## Extension layer

`Hachi.Ext4` is `CompPoly.Extension.Ext Hachi.ext4Params`, whose carrier is a
dense little-endian coefficient vector of length `ext4Params.d = 4`.  The
generated `cpoly.field.Ext4` struct is the same data with the coefficients spelled as
four named `U64` fields. -/

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

/-- Representation invariant for a polynomial: every coefficient is reduced. -/
def VecReduced (v : alloc.vec.Vec cpoly.field.Ext4) : Prop := ∀ a ∈ v.val, Reduced a

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

theorem reduced_EZERO : Reduced cpoly.field.EZERO := by
  simp only [cpoly.field.EZERO, Reduced]
  exact ⟨red_zero_word, red_zero_word, red_zero_word, red_zero_word⟩

theorem reduced_EONE : Reduced cpoly.field.EONE := by
  simp only [cpoly.field.EONE, Reduced]
  exact ⟨red_one_word, red_zero_word, red_zero_word, red_zero_word⟩

@[simp] theorem toExt_EZERO : toExt cpoly.field.EZERO = 0 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_zero]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;> simp [extCoeff, cpoly.field.EZERO]

@[simp] theorem toExt_EONE : toExt cpoly.field.EONE = 1 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt, Ext.coeff_one]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;> simp [extCoeff, cpoly.field.EONE]

/-- `cpoly.field.EGEN` is the adjoined fourth root of `2`. Not needed by any spec
below, but it pins the basis convention: the Rust `c1` field really is the
coefficient of `Y`, not of some other basis vector. -/
theorem toExt_EGEN : toExt cpoly.field.EGEN = Hachi.ext4Gen := by
  apply Ext.ext; intro i
  rw [Hachi.ext4Gen_eq_gen]
  simp only [coeff_toExt, Ext.coeff_gen]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;> simp [extCoeff, cpoly.field.EGEN]

/-! ### The extension operations -/

/-- `eadd` never fails, stays reduced, and computes `Ext` addition. -/
@[step]
theorem eadd_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.eadd a b ⦃ c => Reduced c ∧ toExt c = toExt a + toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.eadd]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_add, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `esub` never fails, stays reduced, and computes `Ext` subtraction. -/
@[step]
theorem esub_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.esub a b ⦃ c => Reduced c ∧ toExt c = toExt a - toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.esub]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_sub, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `eneg` never fails, stays reduced, and computes `Ext` negation. -/
@[step]
theorem eneg_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.eneg a ⦃ c => Reduced c ∧ toExt c = - toExt a ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  rw [cpoly.field.eneg]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_neg, coeff_toExt]
  rcases fin_four_cases i with h | h | h | h <;> rw [h] <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `emul` never fails, stays reduced, and computes `Ext` multiplication.

The Rust code forms the seven schoolbook coefficients `t0 .. t6` and folds the
high half back with a factor of `W = 2` (`Y^4 = 2`); the reference `Ext.mul`
sums the two-branch kernel over all `(i, j) : Fin 4 × Fin 4`.  Expanding both
double sums with `sum_univ_four'` turns the identity into commutative-ring
algebra in the eight coefficients, which `ring` closes. -/
@[step]
theorem emul_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.emul a b ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  have hW : Red cpoly.field.W := red_W
  rw [cpoly.field.emul]
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

/-- `is_ezero` decides whether the represented element is `0`.  Reducedness is
needed in both directions: without it a word congruent to `0` but not equal to
it would make the test unsound. -/
@[step]
theorem is_ezero_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.is_ezero a ⦃ b => (b = true ↔ toExt a = 0) ⦄ := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  have hcoeffs : toExt a = 0 ↔ (toK a.c0 = 0 ∧ toK a.c1 = 0 ∧ toK a.c2 = 0 ∧ toK a.c3 = 0) := by
    rw [← toExt_EZERO, toExt_eq_iff]
    simp only [cpoly.field.EZERO, toK_zero_word]
  have hz : ∀ (u : Std.U64), Red u → (u = 0#u64 ↔ toK u = 0) := by
    intro u hu
    rw [toK_eq_zero_iff u hu]
    constructor
    · intro h; rw [h]; decide
    · intro h; scalar_tac
  rw [cpoly.field.is_ezero, hcoeffs]
  by_cases e0 : a.c0 = 0#u64
  · rw [if_pos e0]
    by_cases e1 : a.c1 = 0#u64
    · rw [if_pos e1]
      by_cases e2 : a.c2 = 0#u64
      · rw [if_pos e2]
        simp only [spec_ok, decide_eq_true_eq]
        rw [(hz _ h0).mp e0, (hz _ h1).mp e1, (hz _ h2).mp e2]
        simpa using (hz a.c3 h3)
      · rw [if_neg e2]
        simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
        exact fun _ _ hc => absurd ((hz _ h2).mpr hc) e2
    · rw [if_neg e1]
      simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
      exact fun _ hc => absurd ((hz _ h1).mpr hc) e1
  · rw [if_neg e0]
    simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
    exact fun hc => absurd ((hz _ h0).mpr hc) e0

end CPolyEquiv
