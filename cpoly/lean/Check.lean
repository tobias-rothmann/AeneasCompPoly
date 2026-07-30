import CPoly
import CMlPoly

/-!
Audit file: not part of the development, only a machine-checked review of what
the specs in `Field.lean` / `CPoly.lean` / `CMlPoly.lean` actually claim.

Nothing imports this file and nothing here is used by a proof; it is a root of
the library in its own right (see `lakefile.lean`), which is what gets it
checked by `lake build`.  It exists to catch the failure mode that a `_spec`
theorem is *true but vacuous*: that the field is degenerate, that `toExt`
collapses distinct words, that `Reduced` is secretly `True`, or that a triple is
weaker than total correctness.  It also prints the axiom dependencies of the
headline specs, which is how a reader confirms there is no `sorryAx` hiding
under a `_spec`.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial CompPoly.Extension

namespace CPolyEquiv.Check

-- 1. The field is the one we think it is, and it is not degenerate.
example : P = 4294967197 := by norm_num
example : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
example : Hachi.ext4Params.W = 2 := Hachi.ext4Params_W
example : Nat.Prime P := Hachi.is_prime
example : Fintype.card F = P ^ 4 := Hachi.card_ext4
example : Field F := inferInstance
example : Irreducible Hachi.ext4Params.poly := Hachi.ext4Params_poly_irreducible

-- 2. `toExt` is injective, so the representation cannot collapse.
example : ∀ a b : cpoly.field.Ext4, Reduced a → Reduced b → toExt a = toExt b → a = b := by
  have key : ∀ u v : Std.U64, Red u → Red v → toK u = toK v → u = v := by
    intro u v hu hv huv
    unfold Red at hu hv
    have h : (u.val : K) = (v.val : K) := huv
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h
    scalar_tac
  rintro ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩ ⟨ha0, ha1, ha2, ha3⟩ ⟨hb0, hb1, hb2, hb3⟩ h
  rw [toExt_eq_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [cpoly.field.Ext4.mk.injEq]
  exact ⟨key _ _ ha0 hb0 h0, key _ _ ha1 hb1 h1, key _ _ ha2 hb2 h2, key _ _ ha3 hb3 h3⟩

-- 3. `toExt` really does hit non-base-field elements: the basis is faithful.
example : toExt cpoly.field.EGEN = Hachi.ext4Gen := toExt_EGEN
example : Hachi.ext4Gen ^ 4 = Ext.ofBase (2 : K) := Hachi.ext4Gen_pow_four
example : Hachi.ext4Gen ≠ 0 := by
  intro h
  have h4 : (0 : F) = Ext.ofBase (2 : K) := by rw [← Hachi.ext4Gen_pow_four, h]; ring
  have := congrArg (fun z => Ext.coeff z ⟨0, by rw [Hachi.ext4Params_d]; omega⟩) h4
  simp only [Ext.coeff_zero, Ext.coeff_ofBase, if_pos] at this
  exact absurd this.symm (by decide)

-- 4. `Reduced` is a real constraint (not `True`) and `toExt` is not constant.
example : ¬ Reduced ⟨4294967197#u64, 0#u64, 0#u64, 0#u64⟩ := by
  rintro ⟨h, -, -, -⟩; unfold Red at h; exact absurd h (by decide)
example : toExt cpoly.field.EZERO ≠ toExt cpoly.field.EONE := by
  rw [toExt_EZERO, toExt_EONE]; exact zero_ne_one

-- 5. The triples are total-correctness statements: `spec m Q` gives `m = ok r`.
example (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    ∃ c, cpoly.field.emul a b = ok c ∧ Reduced c ∧ toExt c = toExt a * toExt b :=
  spec_imp_exists (emul_spec a b ha hb)

example (v w : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    ∃ z, cpoly.cpoly.mul v w = ok z ∧ VecReduced z ∧
      toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
      z.val.length ≤ v.val.length + w.val.length :=
  spec_imp_exists (mul_spec v w hv hw hlen)

-- 6. The reference operations on the right-hand sides are CompPoly's, at `F`.
example : CPolynomial.Raw F = _root_.Array F := rfl
example : CMlPolynomial F 3 = Vector F 8 := by norm_num [CMlPolynomial]

-- 7. Print the headline statements for review.
#print axioms CPolyEquiv.emul_spec
#print axioms CPolyEquiv.mul_spec
#print axioms CPolyEquiv.eval_spec
#print axioms CPolyEquiv.trim_spec
#print axioms CPolyEquiv.Ml.eval_horner_spec
#print axioms CPolyEquiv.Ml.eval_mle_spec
#print axioms CPolyEquiv.Ml.mono_to_lagrange_spec
#print axioms CPolyEquiv.Ml.lagrange_to_mono_spec
#print axioms CPolyEquiv.Ml.eq_tilde_spec

end CPolyEquiv.Check
