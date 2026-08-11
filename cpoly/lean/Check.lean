import Univariate
import Multilinear
import Opt

/-!
Audit file: not part of the development, only a machine-checked review of what
the specs in `Field.lean` / `Univariate.lean` / `Multilinear.lean` actually claim.

Nothing imports this file and nothing here is used by a proof; it is a root of
the library in its own right (see `lakefile.lean`), which is what gets it
checked by `lake build`.  It exists to catch the failure mode that a `_spec`
theorem is *true but vacuous*: that the field is degenerate, that `toExt`
collapses distinct words, that `Reduced` is secretly `True`, or that a triple is
weaker than total correctness.  It also prints the axiom dependencies of the
headline specs, which is how a reader confirms there is no `sorryAx` hiding
under a `_spec`.

Sections 7-11 are about the Rust newtypes: that they cost these proofs nothing,
and -- section 8 -- that the price of that is a real limitation, namely that
`MultilinearPoly` and `MultilinearEvals` are indistinguishable here.
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
example : toExt cpoly.field.Ext4.GEN = Hachi.ext4Gen := toExt_GEN
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
example : toExt cpoly.field.Ext4.ZERO ≠ toExt cpoly.field.Ext4.ONE := by
  rw [toExt_ZERO, toExt_ONE]; exact zero_ne_one

-- 5. The triples are total-correctness statements: `spec m Q` gives `m = ok r`.
example (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    ∃ c, cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul a b = ok c ∧ Reduced c ∧ toExt c = toExt a * toExt b :=
  spec_imp_exists (ext_mul_spec a b ha hb)

example (v w : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    ∃ z, cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul v w = ok z ∧ VecReduced z ∧
      toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
      z.val.length ≤ v.val.length + w.val.length :=
  spec_imp_exists (mul_spec v w hv hw hlen)

-- 6. The reference operations on the right-hand sides are CompPoly's, at `F`.
example : CPolynomial.Raw F = _root_.Array F := rfl
example : CMlPolynomial F 3 = Vector F 8 := by norm_num [CMlPolynomial]

-- 7. The Rust newtypes really are free on this side: Aeneas extracts a
--    single-field tuple struct as a `@[reducible]` abbreviation, so each wrapper
--    *is* its content here and no spec had to change domain to accommodate one.
example : cpoly.field.Fp = Std.U64 := rfl
example : cpoly.univariate.UnivariatePoly = alloc.vec.Vec cpoly.field.Ext4 := rfl
example : cpoly.multilinear.MultilinearPoly = alloc.vec.Vec cpoly.field.Ext4 := rfl
example : cpoly.multilinear.MultilinearEvals = alloc.vec.Vec cpoly.field.Ext4 := rfl

-- 8. ... and the flip side of that, stated plainly because it is a limitation:
--    `MultilinearPoly` and `MultilinearEvals` are the *same* type here, so the separation between the
--    monomial and the Lagrange reading is enforced by rustc and not by these
--    proofs.  What the proofs do give is that each Rust operation computes the
--    CompPoly operation for the reading its Rust type names -- `add_spec` is
--    about `CMlPolynomial.add` and `add_evals_spec` about
--    `CMlPolynomialEval.add` -- so a Rust caller who mixes the two gets a
--    compile error, and a caller who does not gets the operation it asked for.
example : cpoly.multilinear.MultilinearPoly = cpoly.multilinear.MultilinearEvals := rfl

-- 9. `Fp`'s reducedness is a real constraint, and `Fp::new` establishes it for
--    an arbitrary word -- which is what makes `Red` an invariant of the Rust type
--    rather than a precondition callers must respect.
example : ¬ Red 4294967197#u64 := by
  intro h; unfold Red at h; exact absurd h (by decide)
example (v : Std.U64) : ∃ c, cpoly.field.Fp.new v = ok c ∧ Red c ∧ toK c = (v.val : K) :=
  spec_imp_exists (fp_new_spec v)

-- 10. The operator impls are total-correctness statements too, including the
--     heterogeneous scalar multiplication and the two `Add` impls of the
--     multilinear layer.
example (a : cpoly.field.Fp) (b : cpoly.field.Ext4) (ha : Red a) (hb : Reduced b) :
    ∃ c, cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul a b = ok c ∧
      Reduced c ∧ toExt c = toK a • toExt b :=
  spec_imp_exists (ext_smul_spec a b ha hb)

example (n : ℕ) (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hvl : v.val.length = 2 ^ n) (hwl : w.val.length = 2 ^ n) :
    ∃ z, cpoly.Shared1MultilinearEvals.Insts.CoreOpsArithAddShared0MultilinearEvalsMultilinearEvals.add v w = ok z ∧
      VecReduced z ∧ z.val.length = 2 ^ n ∧
      Ml.toMlEval n z = CMlPolynomialEval.add (Ml.toMlEval n v) (Ml.toMlEval n w) :=
  spec_imp_exists (Ml.add_evals_spec n v w hv hw hvl hwl)

-- 11. `table_len` is `1usize << vars`, and its side condition is exact: the
--     shift fails exactly when `2 ^ vars` does not fit.  Sanity-check the spec
--     at a concrete arity.
example : ∃ z, cpoly.multilinear.table_len 10#usize = ok z ∧ z.val = 1024 := by
  have h := Ml.pow2_spec 10#usize (by scalar_tac)
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists h
  exact ⟨z, hz, by simpa using hzv⟩

-- 12. The readable aliases in `Univariate.lean` / `Multilinear.lean` really are
--     the generated operator impls.  They are `abbrev`s, so this is `rfl` — the
--     point is that a rename in `Generated.lean` cannot silently repoint one
--     without this file failing to compile.
example : Poly.add = cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add := rfl
example : Poly.sub = cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithSubShared0UnivariatePolyUnivariatePoly.sub := rfl
example : Poly.mul = cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul := rfl
example : Poly.neg = cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithNegUnivariatePoly.neg := rfl
example : Poly.smul = cpoly.Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul := rfl
example : Ml.polyAdd = cpoly.Shared1MultilinearPoly.Insts.CoreOpsArithAddShared0MultilinearPolyMultilinearPoly.add := rfl
example : Ml.evalsAdd = cpoly.Shared1MultilinearEvals.Insts.CoreOpsArithAddShared0MultilinearEvalsMultilinearEvals.add := rfl
example : Ml.polyNeg = cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithNegMultilinearPoly.neg := rfl
example : Ml.evalsNeg = cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithNegMultilinearEvals.neg := rfl
example : Ml.polySmul = cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithMulExt4MultilinearPoly.mul := rfl
example : Ml.evalsSmul = cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithMulExt4MultilinearEvals.mul := rfl

-- 13. The multilinear layer has its own negation and scaling.
example (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v)
    (hvl : v.val.length = 2 ^ n) :
    ∃ z, Ml.polyNeg v = ok z ∧ VecReduced z ∧ z.val.length = 2 ^ n ∧
      Ml.toMl n z = CMlPolynomial.neg (Ml.toMl n v) :=
  spec_imp_exists (Ml.neg_spec n v hv hvl)

example (n : ℕ) (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) :
    ∃ z, Ml.evalsSmul v r = ok z ∧ VecReduced z ∧ z.val.length = 2 ^ n ∧
      Ml.toMlEval n z = CMlPolynomialEval.smul (toExt r) (Ml.toMlEval n v) :=
  spec_imp_exists (Ml.smul_evals_spec n r v hr hv hvl)

-- 14. Print the headline statements for review.
#print axioms CPolyEquiv.ext_mul_spec
#print axioms CPolyEquiv.mul_spec
#print axioms CPolyEquiv.eval_spec
#print axioms CPolyEquiv.trim_spec
#print axioms CPolyEquiv.Ml.eval_horner_spec
#print axioms CPolyEquiv.Ml.eval_mle_spec
#print axioms CPolyEquiv.Ml.mono_to_lagrange_spec
#print axioms CPolyEquiv.Ml.lagrange_to_mono_spec
#print axioms CPolyEquiv.Ml.eq_tilde_spec
#print axioms CPolyEquiv.Ml.add_spec
#print axioms CPolyEquiv.Ml.add_evals_spec
#print axioms CPolyEquiv.ext_smul_spec
#print axioms CPolyEquiv.fp_new_spec
#print axioms CPolyEquiv.Ml.neg_spec
#print axioms CPolyEquiv.Ml.smul_evals_spec
#print axioms CPolyEquiv.Ml.zero_evals_spec

-- 15. Every `Foo.opt_eq_spec` lemma in `Opt.lean` is axiom-clean.  The
--     opt-contract (see `Opt.lean`'s header and the `lean-opt` skill) admits a
--     variant only together with its proved equivalence lemma; this section is
--     what makes a `sorry` in one of them a build-visible event instead of a
--     silent debt.  The loop appends one `#print axioms` line per accepted
--     variant, next to this comment.

#print axioms CompPoly.CPolynomial.Raw.mul.opt_eq_spec

end CPolyEquiv.Check
