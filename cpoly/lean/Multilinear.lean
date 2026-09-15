/-
Equivalence between the Aeneas-extracted Rust model (`cpoly.multilinear.*`, see
`Generated.lean`) and CompPoly's reference **multilinear**
polynomials (`CompPoly.CMlPolynomial` / `CompPoly.CMlPolynomialEval`, see
CompPoly/Multilinear/Basic.lean).

This is the multilinear counterpart of `Univariate.lean`, and it reuses
`Field.lean` verbatim: a generated `cpoly.field.Ext4` struct denotes
the element `toExt a` of `F = Hachi.Ext4`, the quartic extension
`F_P[Y]/(Y^4 - 2)` of the Hachi prime field `P = 2^32 - 99`, and the four
extension operators `Add`/`Sub`/`Neg`/`Mul` are already known to be total
and to commute with `Ext`'s ring operations under the reducedness invariant
`Reduced`/`VecReduced`.  Nothing below depends on which field it is: the
arguments only use that `F` is a commutative ring and that the field layer is
`@[step]`-available.

## Representation

`CMlPolynomial F n` and `CMlPolynomialEval F n` are both `Vector F (2 ^ n)`:
the coefficient table in the monomial basis, respectively the value table on the
Boolean hypercube, indexed **little-endian** (bit `j` of the index belongs to
variable `j`).  A `Vec Ext4` of length `2 ^ n` represents such a table via
`toMl`, which pads out-of-range indices with `0` so that the bridge is total;
every spec below carries the length hypothesis that makes it faithful.

An evaluation point of `F^n` is likewise a `Vec Ext4` of length `n`, read by
`toPoint`.  Both readers are built from the two total index functions `coeffFn`
and `pointFn`, and `pointFn` carries an offset so that "drop the
least-significant variable" is just `o + 1` — this is what keeps the layered
evaluation algorithms free of `Vector.head`/`Vector.tail` reasoning.

## Layering of the development

1. **Explicit-value layer** (`monoProd`, `lagProd`, `mlVal`, `mlValL`).  The
   value of a multilinear polynomial written out as a `Finset.range` sum over
   plain index functions `ℕ → F`.  All the *mathematical* content of the
   layered algorithms lives here, where it is pure `Finset` algebra:
   `mlVal_layer` / `mlValL_layer` say that one Horner (resp. multilinear
   extension) layer preserves the value, and `mlVal_zero` / `mlValL_zero` are
   the base cases.

2. **CompPoly bridge** (`mlVal_eq_eval`, `mlValL_eq_eval`,
   `monomialBasis_getElem'`, `lagrangeBasis_getElem'`).  Identifies that layer
   with `CMlPolynomial.eval` / `CMlPolynomialEval.eval`, which are
   `Vector.dotProduct` against `monomialBasis` / `lagrangeBasis`.

3. **Aeneas layer** (everything named `*_spec`).  Each generated `cpoly.multilinear`
   function is shown to succeed, to preserve `VecReduced` and the length
   `2 ^ n`, and to compute the corresponding CompPoly operation.  Loop bodies
   are handled with `Aeneas.Std.loop.spec_decr_nat` exactly as in
   `Univariate.lean`; the top-level specs are composed with `spec_bind`/`spec_mono`.

## Size side conditions

`cpoly::multilinear::table_len` is `1usize << vars`, and Aeneas's model of `<<<`
fails once the shift amount reaches the word width -- so it fails on exactly the
inputs for which `2 ^ vars` does not fit in a `usize`.  Specs whose inputs
already include a vector of length `2 ^ n` get `2 ^ n ≤ Usize.max` for free from
the `alloc.vec.Vec` invariant (`Vec α = { l : List α // l.length ≤ Usize.max }`);
the others (`zero_spec`, `zero_evals_spec`, `of_array_spec`, and the two bases)
take it as a hypothesis, which is exactly the weakest condition making those
triples true.  The direct `eq_tilde` loop has no table allocation or shift, so
its specification no longer needs a size side condition.
-/
import Field
import Univariate
import CompPoly.Multilinear.Basic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly

namespace CPolyEquiv.Ml

/-! ## Readable names for the operator impls

As in `Univariate.lean`: Aeneas builds an `impl Trait for &T` name from the impl
header with a `Shared<n><T>` prefix, which is unreadable in a statement, so each
gets an `abbrev`.  These are `@[reducible]`, so a theorem about `polyAdd` *is* a
theorem about the extracted definition; `Check.lean` pins each to its generated
name with `rfl`. -/

/-- `impl Add<&MultilinearPoly> for &MultilinearPoly`. -/
abbrev polyAdd := cpoly.Shared1MultilinearPoly.Insts.CoreOpsArithAddShared0MultilinearPolyMultilinearPoly.add

/-- `impl Add<&MultilinearEvals> for &MultilinearEvals`. -/
abbrev evalsAdd := cpoly.Shared1MultilinearEvals.Insts.CoreOpsArithAddShared0MultilinearEvalsMultilinearEvals.add

/-- `impl Neg for &MultilinearPoly`. -/
abbrev polyNeg := cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithNegMultilinearPoly.neg

/-- `impl Neg for &MultilinearEvals`. -/
abbrev evalsNeg := cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithNegMultilinearEvals.neg

/-- `impl Mul<Ext4> for &MultilinearPoly`. -/
abbrev polySmul := cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithMulExt4MultilinearPoly.mul

/-- `impl Mul<Ext4> for &MultilinearEvals`. -/
abbrev evalsSmul := cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithMulExt4MultilinearEvals.mul

/-! ## Word-level helpers

The `0`/`1` of the coefficient field are the extracted constants `cpoly.field.Ext4.ZERO`
and `cpoly.field.Ext4.ONE`; `Field.lean` supplies `toExt_ZERO`/`toExt_ONE` and
`reduced_ZERO`/`reduced_ONE` for them, and tags every extension operation
`@[step]`. -/

theorem usize_eq_of_val_eq {a b : Std.Usize} (h : a.val = b.val) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      congr
      exact BitVec.eq_of_toNat_eq h

/-! ## Bit arithmetic

The extracted code never uses `>>` or `&`: a bit test is `(i / 2 ^ j) % 2 == 1`,
and the inner loops carry the running quotient `m = i / 2 ^ j`.  These lemmas
are the dictionary between that form and `Nat.testBit`. -/

theorem testBit_eq_div_pow_mod (i j : ℕ) : Nat.testBit i j = decide (i / 2 ^ j % 2 = 1) := by
  induction j generalizing i with
  | zero => simp [Nat.testBit_zero]
  | succ j ih =>
    rw [Nat.testBit_add_one, ih]
    congr 2
    rw [Nat.div_div_eq_div_mul]
    ring_nf

/-- The running quotient `m = i / 2 ^ j`: its low bit is bit `j` of `i`. -/
theorem testBit_zero_div (i j : ℕ) : Nat.testBit (i / 2 ^ j) 0 = Nat.testBit i j := by
  rw [Nat.testBit_zero, testBit_eq_div_pow_mod]

@[simp] theorem testBit_two_mul_zero (j : ℕ) : Nat.testBit (2 * j) 0 = false := by
  rw [Nat.testBit_zero]; simp

@[simp] theorem testBit_two_mul_add_one_zero (j : ℕ) : Nat.testBit (2 * j + 1) 0 = true := by
  rw [Nat.testBit_zero]; simp

@[simp] theorem testBit_two_mul_succ (j k : ℕ) :
    Nat.testBit (2 * j) (k + 1) = Nat.testBit j k := by
  rw [Nat.testBit_add_one]; congr 1; omega

@[simp] theorem testBit_two_mul_add_one_succ (j k : ℕ) :
    Nat.testBit (2 * j + 1) (k + 1) = Nat.testBit j k := by
  rw [Nat.testBit_add_one]; congr 1; omega

/-- Bit `j` set forces the index to be at least the stride `2 ^ j`.  This is what
makes the checked subtraction `i - stride` in the zeta/Möbius levels succeed. -/
theorem le_of_testBit (i j : ℕ) (h : Nat.testBit i j = true) : 2 ^ j ≤ i := by
  rw [testBit_eq_div_pow_mod] at h
  simp only [decide_eq_true_eq] at h
  by_contra hc
  rw [Nat.div_eq_of_lt (by omega)] at h
  simp at h

/-- Even/odd split of a sum over `range (2 * m)`: the shape of every
halving-layer argument below. -/
theorem sum_range_two_mul (m : ℕ) (f : ℕ → F) :
    ∑ i ∈ Finset.range (2 * m), f i
      = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Prefix step for the `foldl` in `monoToLagrange`. -/
theorem finRange_take_succ (n m : ℕ) (hm : m < n) :
    (List.finRange n).take (m + 1) = (List.finRange n).take m ++ [(⟨m, hm⟩ : Fin n)] := by
  have hlen : m < (List.finRange n).length := by simpa using hm
  rw [← List.take_concat_get' _ _ hlen]
  congr 2
  simp

/-- Suffix step for the `foldr` in `lagrangeToMono`. -/
theorem finRange_drop_succ (n m : ℕ) (hm : m < n) :
    (List.finRange n).drop m = (⟨m, hm⟩ : Fin n) :: (List.finRange n).drop (m + 1) := by
  have hlen : m < (List.finRange n).length := by simpa using hm
  rw [List.drop_eq_getElem_cons hlen]
  congr 2
  simp

/-- The stride of level `j` is a legal `usize` whenever the whole table is. -/
theorem pow_le_of_lt {j n : ℕ} (h : j < n) (hn : 2 ^ n ≤ Std.Usize.max) :
    2 ^ j ≤ Std.Usize.max :=
  le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hn

/-! ## Bridge: words ↔ multilinear tables and points -/

/-- Coefficient reader: entry `i` of `v` as a field element, `0` past the end. -/
def coeffFn (v : alloc.vec.Vec cpoly.field.Ext4) : ℕ → F :=
  fun i => (v.val.map toExt).getD i 0

/-- Point reader: coordinate `k` of the point stored in `v` starting at offset
`o`.  The offset is what makes "eliminate the least-significant variable"
into `o + 1`. -/
def pointFn (v : Slice cpoly.field.Ext4) (o : ℕ) : ℕ → F :=
  fun k => (v.val.map toExt).getD (o + k) 0

theorem coeffFn_of_lt (v : alloc.vec.Vec cpoly.field.Ext4) {i : ℕ} (hi : i < v.val.length) :
    coeffFn v i = toExt v.val[i] := by
  unfold coeffFn
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem coeffFn_of_ge (v : alloc.vec.Vec cpoly.field.Ext4) {i : ℕ} (hi : v.val.length ≤ i) :
    coeffFn v i = 0 := by
  unfold coeffFn
  rw [List.getD_eq_default]; simpa using hi

theorem pointFn_of_lt (v : Slice cpoly.field.Ext4) (o : ℕ) {k : ℕ}
    (hk : o + k < v.val.length) : pointFn v o k = toExt v.val[o + k] := by
  unfold pointFn
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem pointFn_succ (v : Slice cpoly.field.Ext4) (o k : ℕ) :
    pointFn v o (k + 1) = pointFn v (o + 1) k := by
  unfold pointFn; rw [show o + (k + 1) = o + 1 + k by omega]

/-- The two ways the iterative basis proof writes a coordinate agree: the
builder indexes it as `point[j]`, while the mathematical basis uses an offset
of zero and coordinate `j`. -/
theorem pointFn_offset_zero (v : Slice cpoly.field.Ext4) (j : ℕ) :
    pointFn v j 0 = pointFn v 0 j := by
  unfold pointFn
  rw [show j + 0 = 0 + j by omega]

/-- `coeffFn` for a table that arrives as a `&[Ext4]` rather than a `&Vec<Ext4>`.
Since `Vec::deref` is the identity on the underlying list, the two agree on every
table that is passed across that coercion (`sliceCoeffFn_deref`). -/
def sliceCoeffFn (s : Slice cpoly.field.Ext4) : ℕ → F :=
  fun i => (s.val.map toExt).getD i 0

@[simp] theorem sliceCoeffFn_deref (v : alloc.vec.Vec cpoly.field.Ext4) :
    sliceCoeffFn (alloc.vec.Vec.deref v) = coeffFn v := rfl

@[simp] theorem coeffFn_deref (v : alloc.vec.Vec cpoly.field.Ext4) :
    coeffFn (alloc.vec.Vec.deref v) = coeffFn v := rfl

theorem sliceCoeffFn_of_lt (s : Slice cpoly.field.Ext4) {i : ℕ} (hi : i < s.val.length) :
    sliceCoeffFn s i = toExt s.val[i] := by
  unfold sliceCoeffFn
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

/-- The multilinear table (in either basis) represented by a `Vec Ext4`. -/
def toMl (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) : CMlPolynomial F n :=
  Vector.ofFn (fun i : Fin (2 ^ n) => coeffFn v i.val)

/-- The same words read as a Boolean-hypercube value table. -/
abbrev toMlEval (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) : CMlPolynomialEval F n := toMl n v

/-- The point of `F^n` stored in `v` starting at offset `o`. -/
def toPointFrom (n : ℕ) (v : Slice cpoly.field.Ext4) (o : ℕ) : Vector F n :=
  Vector.ofFn (fun k : Fin n => pointFn v o k.val)

/-- The point of `F^n` stored in `v`. -/
abbrev toPoint (n : ℕ) (v : Slice cpoly.field.Ext4) : Vector F n := toPointFrom n v 0

@[simp] theorem toMl_getElem (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (i : ℕ)
    (hi : i < 2 ^ n) :
    (toMl n v)[i] = coeffFn v i := by
  simp [toMl]

@[simp] theorem toPointFrom_getElem (n : ℕ) (v : Slice cpoly.field.Ext4) (o k : ℕ)
    (hk : k < n) : (toPointFrom n v o)[k] = pointFn v o k := by
  simp [toPointFrom]

/-- Two `Vec`s that agree coefficient-wise below `2 ^ n` give the same table. -/
theorem toMl_congr (n : ℕ) (v w : alloc.vec.Vec cpoly.field.Ext4)
    (h : ∀ i, i < 2 ^ n → coeffFn v i = coeffFn w i) : toMl n v = toMl n w := by
  unfold toMl
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  exact h i hi

/-- A vector of length `2 ^ n` witnesses that `2 ^ n` is a legal `usize`. -/
theorem pow2_le_usize_max {n : ℕ} {v : alloc.vec.Vec cpoly.field.Ext4}
    (hv : v.val.length = 2 ^ n) :
    2 ^ n ≤ Std.Usize.max := hv ▸ v.property

/-! ## Explicit-value layer

`mlVal n c x` is the value at `x` of the coefficient table `c`, and
`mlValL n c x` the value at `x` of the hypercube value table `c`, both written
out as `Finset.range` sums over plain index functions.  Working with functions
`ℕ → F` rather than `Vector`s turns the layer recursions of the fast evaluation
algorithms into pure `Finset` algebra. -/

/-- Monomial-basis weight of index `i`: `∏_{bit k of i set} x k`. -/
def monoProd (n i : ℕ) (x : ℕ → F) : F :=
  ∏ k ∈ Finset.range n, (if Nat.testBit i k then x k else 1)

/-- Lagrange-basis weight of index `i`: `∏_k (bit k of i ? x k : 1 - x k)`. -/
def lagProd (n i : ℕ) (x : ℕ → F) : F :=
  ∏ k ∈ Finset.range n, (if Nat.testBit i k then x k else 1 - x k)

/-- Value of a coefficient table, written out. -/
def mlVal (n : ℕ) (c x : ℕ → F) : F :=
  ∑ i ∈ Finset.range (2 ^ n), c i * monoProd n i x

/-- Value of a Boolean-hypercube value table, written out. -/
def mlValL (n : ℕ) (c x : ℕ → F) : F :=
  ∑ i ∈ Finset.range (2 ^ n), c i * lagProd n i x

@[simp] theorem monoProd_zero (i : ℕ) (x : ℕ → F) : monoProd 0 i x = 1 := by
  simp [monoProd]

@[simp] theorem lagProd_zero (i : ℕ) (x : ℕ → F) : lagProd 0 i x = 1 := by
  simp [lagProd]

/-- Splitting off the least-significant bit of the index. -/
theorem monoProd_succ_even (n j : ℕ) (x : ℕ → F) :
    monoProd (n + 1) (2 * j) x = monoProd n j (fun k => x (k + 1)) := by
  unfold monoProd
  rw [Finset.prod_range_succ']
  have h0 : Nat.testBit (2 * j) 0 = false := by simp [testBit_eq_div_pow_mod]
  simp only [h0, Bool.false_eq_true, if_false, mul_one]
  apply Finset.prod_congr rfl
  intro k hk
  have hb : Nat.testBit (2 * j) (k + 1) = Nat.testBit j k := by
    rw [show 2 * j = j * 2 ^ 1 by ring, Nat.testBit_mul_two_pow]
    simp
  rw [hb]

theorem monoProd_succ_odd (n j : ℕ) (x : ℕ → F) :
    monoProd (n + 1) (2 * j + 1) x = x 0 * monoProd n j (fun k => x (k + 1)) := by
  unfold monoProd
  rw [Finset.prod_range_succ']
  have h0 : Nat.testBit (2 * j + 1) 0 = true := by simp [testBit_eq_div_pow_mod]
  simp only [h0, if_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hb : Nat.testBit (2 * j + 1) (k + 1) = Nat.testBit j k := by
    rw [Nat.testBit_add_one]
    congr 1
    omega
  rw [hb]

theorem lagProd_succ_even (n j : ℕ) (x : ℕ → F) :
    lagProd (n + 1) (2 * j) x = (1 - x 0) * lagProd n j (fun k => x (k + 1)) := by
  unfold lagProd
  rw [Finset.prod_range_succ']
  have h0 : Nat.testBit (2 * j) 0 = false := by simp [testBit_eq_div_pow_mod]
  simp only [h0, Bool.false_eq_true, if_false]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hb : Nat.testBit (2 * j) (k + 1) = Nat.testBit j k := by
    rw [show 2 * j = j * 2 ^ 1 by ring, Nat.testBit_mul_two_pow]
    simp
  rw [hb]

theorem lagProd_succ_odd (n j : ℕ) (x : ℕ → F) :
    lagProd (n + 1) (2 * j + 1) x = x 0 * lagProd n j (fun k => x (k + 1)) := by
  unfold lagProd
  rw [Finset.prod_range_succ']
  have h0 : Nat.testBit (2 * j + 1) 0 = true := by simp [testBit_eq_div_pow_mod]
  simp only [h0, if_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hb : Nat.testBit (2 * j + 1) (k + 1) = Nat.testBit j k := by
    rw [Nat.testBit_add_one]
    congr 1
    omega
  rw [hb]

@[simp] theorem mlVal_zero (c x : ℕ → F) : mlVal 0 c x = c 0 := by
  simp [mlVal]

@[simp] theorem mlValL_zero (c x : ℕ → F) : mlValL 0 c x = c 0 := by
  simp [mlValL]

/-- **One Horner layer preserves the value.**  Eliminating the
least-significant variable of a *coefficient* table at `x 0` and evaluating the
half-size table at the remaining coordinates gives the original value.  This is
the mathematical heart of `cpoly::multilinear::MultilinearPoly::eval_horner`. -/
theorem mlVal_layer (n : ℕ) (c x : ℕ → F) :
    mlVal n (fun j => c (2 * j) + x 0 * c (2 * j + 1)) (fun k => x (k + 1))
      = mlVal (n + 1) c x := by
  unfold mlVal
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring, sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [monoProd_succ_even, monoProd_succ_odd]
  ring

/-- **One multilinear-extension layer preserves the value.**  The
`CMlPolynomialEval` analogue of `mlVal_layer`, and the heart of
`cpoly::multilinear::MultilinearEvals::eval_mle`. -/
theorem mlValL_layer (n : ℕ) (c x : ℕ → F) :
    mlValL n (fun j => (1 - x 0) * c (2 * j) + x 0 * c (2 * j + 1)) (fun k => x (k + 1))
      = mlValL (n + 1) c x := by
  unfold mlValL
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring, sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lagProd_succ_even, lagProd_succ_odd]
  ring

/-! ## Bridge to the CompPoly reference definitions -/

/-- `BitVec.ofFin`'s bits are `Nat.testBit` of the underlying value. -/
theorem getLsb_ofFin {m : ℕ} (i : Fin (2 ^ m)) (j : Fin m) :
    (BitVec.ofFin i).getLsb j = Nat.testBit i.val j.val := by
  rfl

/-- The monomial basis at a `Vec`-represented point, coefficient-wise. -/
theorem monomialBasis_getElem' (n : ℕ) (w : Slice cpoly.field.Ext4) (o i : ℕ)
    (hi : i < 2 ^ n) :
    (CMlPolynomial.monomialBasis (toPointFrom n w o))[i] = monoProd n i (pointFn w o) := by
  simp [CMlPolynomial.monomialBasis, monoProd, toPointFrom]
  exact Fin.prod_univ_eq_prod_range
    (f := fun k => if Nat.testBit i k then pointFn w o k else 1) n

/-- The Lagrange basis at a `Vec`-represented point, coefficient-wise. -/
theorem lagrangeBasis_getElem' (n : ℕ) (w : Slice cpoly.field.Ext4) (o i : ℕ)
    (hi : i < 2 ^ n) :
    (CMlPolynomialEval.lagrangeBasis (toPointFrom n w o))[i] = lagProd n i (pointFn w o) := by
  simp [CMlPolynomialEval.lagrangeBasis, lagProd, toPointFrom]
  exact Fin.prod_univ_eq_prod_range
    (f := fun k => if Nat.testBit i k then pointFn w o k else 1 - pointFn w o k) n

/-- `Vector.dotProduct` as a plain `Finset.univ` sum. -/
theorem dotProduct_eq_sum_univ {m : ℕ} (a b : Vector F m) :
    Vector.dotProduct a b = ∑ i : Fin m, a.get i * b.get i := by
  rw [Vector.dotProduct_eq_root_dotProduct]
  rfl

/-- The explicit value equals `CMlPolynomial.eval`. -/
theorem mlVal_eq_eval (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4) (o : ℕ) :
    mlVal n (coeffFn p) (pointFn w o)
      = CMlPolynomial.eval (toMl n p) (toPointFrom n w o) := by
  rw [CMlPolynomial.eval, dotProduct_eq_sum_univ]
  unfold mlVal
  have h : (∑ i : Fin (2 ^ n), (toMl n p).get i *
      (CMlPolynomial.monomialBasis (toPointFrom n w o)).get i) =
      ∑ i : Fin (2 ^ n), coeffFn p i.val * monoProd n i.val (pointFn w o) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Vector.get_eq_getElem, Vector.get_eq_getElem, toMl_getElem,
      monomialBasis_getElem']
  rw [h]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun i => coeffFn p i * monoProd n i (pointFn w o)) (2 ^ n)

/-- The explicit value equals `CMlPolynomialEval.eval`. -/
theorem mlValL_eq_eval (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4) (o : ℕ) :
    mlValL n (coeffFn p) (pointFn w o)
      = CMlPolynomialEval.eval (toMlEval n p) (toPointFrom n w o) := by
  rw [CMlPolynomialEval.eval, dotProduct_eq_sum_univ]
  unfold mlValL
  have h : (∑ i : Fin (2 ^ n), (toMlEval n p).get i *
      (CMlPolynomialEval.lagrangeBasis (toPointFrom n w o)).get i) =
      ∑ i : Fin (2 ^ n), coeffFn p i.val * lagProd n i.val (pointFn w o) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Vector.get_eq_getElem, Vector.get_eq_getElem, toMl_getElem,
      lagrangeBasis_getElem']
  rw [h]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun i => coeffFn p i * lagProd n i (pointFn w o)) (2 ^ n)

/-! ## Direct equality-kernel product -/

/-- One coordinate's contribution to the multilinear equality kernel. -/
def eqFactor (w x : ℕ → F) (j : ℕ) : F :=
  (1 - x j) * (1 - w j) + x j * w j

/-- The direct product form of `CMlPolynomialEval.eqTilde`. -/
def eqProd (n : ℕ) (w x : ℕ → F) : F :=
  ∏ j ∈ Finset.range n, eqFactor w x j

/-- Split a range product at its least-significant coordinate. -/
theorem prod_range_succ_head (n : ℕ) (f : ℕ → F) :
    (∏ j ∈ Finset.range (n + 1), f j) = f 0 * ∏ j ∈ Finset.range n, f (j + 1) := by
  calc
    (∏ j ∈ Finset.range (n + 1), f j) = ∏ j : Fin (n + 1), f j.val :=
      (Fin.prod_univ_eq_prod_range (f := f) (n + 1)).symm
    _ = f 0 * ∏ j : Fin n, f (j.val + 1) := by
      rw [Fin.prod_univ_succ]
      rfl
    _ = f 0 * ∏ j ∈ Finset.range n, f (j + 1) := by
      congr 1
      exact Fin.prod_univ_eq_prod_range (f := fun j => f (j + 1)) n

/-- Summing the two Lagrange weights at every Boolean point factors coordinatewise. -/
theorem lagProd_pair_sum (n : ℕ) (w x : ℕ → F) :
    (∑ i ∈ Finset.range (2 ^ n), lagProd n i w * lagProd n i x) = eqProd n w x := by
  induction n generalizing w x with
  | zero => simp [lagProd, eqProd, eqFactor]
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring, sum_range_two_mul]
    calc
      (∑ j ∈ Finset.range (2 ^ n),
          (lagProd (n + 1) (2 * j) w * lagProd (n + 1) (2 * j) x +
            lagProd (n + 1) (2 * j + 1) w * lagProd (n + 1) (2 * j + 1) x)) =
          ∑ j ∈ Finset.range (2 ^ n), eqFactor w x 0 *
            (lagProd n j (fun k => w (k + 1)) * lagProd n j (fun k => x (k + 1))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [lagProd_succ_even, lagProd_succ_even, lagProd_succ_odd, lagProd_succ_odd]
            unfold eqFactor
            ring
      _ = eqFactor w x 0 *
            (∑ j ∈ Finset.range (2 ^ n),
              lagProd n j (fun k => w (k + 1)) * lagProd n j (fun k => x (k + 1))) := by
            rw [Finset.mul_sum]
      _ = eqFactor w x 0 * eqProd n (fun k => w (k + 1)) (fun k => x (k + 1)) := by
            rw [ih]
      _ = eqProd (n + 1) w x := by
            unfold eqProd
            rw [prod_range_succ_head]
            unfold eqFactor
            congr 2

/-- CompPoly's equality kernel is the direct coordinatewise product. -/
theorem eqTilde_eq_eqProd (n : ℕ) (w x : Slice cpoly.field.Ext4) :
    CMlPolynomialEval.eqTilde (toPoint n w) (toPoint n x) =
      eqProd n (pointFn w 0) (pointFn x 0) := by
  rw [CMlPolynomialEval.eqTilde, CMlPolynomialEval.eval, dotProduct_eq_sum_univ]
  have h : (∑ i : Fin (2 ^ n),
      (CMlPolynomialEval.lagrangeBasis (toPoint n w)).get i *
        (CMlPolynomialEval.lagrangeBasis (toPoint n x)).get i) =
      ∑ i : Fin (2 ^ n),
        lagProd n i.val (pointFn w 0) * lagProd n i.val (pointFn x 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Vector.get_eq_getElem, Vector.get_eq_getElem,
      lagrangeBasis_getElem', lagrangeBasis_getElem']
  rw [h]
  calc
    (∑ i : Fin (2 ^ n),
        lagProd n i.val (pointFn w 0) * lagProd n i.val (pointFn x 0)) =
        ∑ i ∈ Finset.range (2 ^ n),
          lagProd n i (pointFn w 0) * lagProd n i (pointFn x 0) := by
            exact Fin.sum_univ_eq_sum_range
              (fun i => lagProd n i (pointFn w 0) * lagProd n i (pointFn x 0)) (2 ^ n)
    _ = eqProd n (pointFn w 0) (pointFn x 0) := lagProd_pair_sum n _ _

/-! ## `table_len`

`multilinear::table_len` is `1usize << vars`.  The Aeneas model of `<<<` fails
when the shift amount reaches the word width and otherwise reduces modulo
`2 ^ 64`, so the function succeeds exactly when `vars < 64` — which, since
`2 ^ vars ≤ Usize.max = 2 ^ 64 - 1` iff `vars < 64`, is the side condition the
spec below carries. -/

/-- `2 ^ n ≤ Usize.max` forces `n` below the word width: the shift's own
precondition.  Stated in terms of `System.Platform.numBits` rather than `64`, so
it does not assume the platform Aeneas's `Usize` is modelling. -/
theorem lt_numBits_of_pow2_le_max {n : ℕ} (hn : 2 ^ n ≤ Std.Usize.max) :
    n < System.Platform.numBits := by
  by_contra hc
  have h1 : (2 : ℕ) ^ System.Platform.numBits ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    rw [Std.Usize.max_def]; simp [Std.Usize.numBits]
  have h3 : 0 < (2 : ℕ) ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

/-- `cpoly::multilinear::table_len` computes `2 ^ n`, provided that fits in a
`usize`. -/
theorem pow2_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.multilinear.table_len n ⦃ z => z.val = 2 ^ n.val ⦄ := by
  have hnb : n.val < System.Platform.numBits := lt_numBits_of_pow2_le_max hn
  have hsize : Std.Usize.size = 2 ^ System.Platform.numBits := by
    rw [Std.Usize.size_def]; simp [Std.Usize.numBits]
  have hlt : (2 : ℕ) ^ n.val < Std.Usize.size := by
    have h2 : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
      rw [Std.Usize.max_def]; simp [Std.Usize.numBits]
    have h3 : 0 < (2 : ℕ) ^ System.Platform.numBits := Nat.two_pow_pos _
    omega
  rw [cpoly.multilinear.table_len]
  apply spec_mono (Std.Usize.ShiftLeft_spec 1#usize n hnb)
  rintro z ⟨hzval, -⟩
  rw [hzval]
  have hone : (1#usize : Std.Usize).val = 1 := by simp
  rw [hone, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hlt]

/-! ## `zeros` -/

/-- `cpoly::multilinear::MultilinearPoly::zeros` ↔ `CMlPolynomial.zero`.

`vec![Ext4::ZERO; table_len(vars)]` is a single `alloc::vec::from_elem`, so there
is no fill loop to reason about. -/
theorem zero_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.multilinear.MultilinearPoly.zeros n ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n.val ∧
      toMl n.val z = (CMlPolynomial.zero : CMlPolynomial F n.val) ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.zeros]
  simp only [bind_ok_id]
  apply spec_bind (pow2_spec n hn)
  intro sz hsz
  apply spec_mono (alloc.vec.from_elem_spec cpoly.field.Ext4.Insts.CoreCloneClone
    cpoly.field.Ext4.ZERO sz (ext_clone_eq _))
  rintro z ⟨hz, -⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [hz] at hu
    rw [List.eq_of_mem_replicate hu]
    exact reduced_ZERO
  · simp [hz, hsz]
  · apply Vector.ext
    intro i hi
    simp [toMl, coeffFn, hz, CMlPolynomial.zero]

/-- `cpoly::multilinear::MultilinearEvals::zeros` ↔ `CMlPolynomialEval.zero`.

The same all-zero table as `MultilinearPoly::zeros`, read on the hypercube
instead — which is the same statement, since the zero polynomial vanishes
everywhere.  It gets its own spec because it is its own Rust function. -/
theorem zero_evals_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.multilinear.MultilinearEvals.zeros n ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n.val ∧
      toMlEval n.val z = (CMlPolynomialEval.zero : CMlPolynomialEval F n.val) ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.zeros]
  simp only [bind_ok_id]
  apply spec_bind (pow2_spec n hn)
  intro sz hsz
  apply spec_mono (alloc.vec.from_elem_spec cpoly.field.Ext4.Insts.CoreCloneClone
    cpoly.field.Ext4.ZERO sz (ext_clone_eq _))
  rintro z ⟨hz, -⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [hz] at hu
    rw [List.eq_of_mem_replicate hu]
    exact reduced_ZERO
  · simp [hz, hsz]
  · apply Vector.ext
    intro i hi
    simp [toMl, coeffFn, hz, CMlPolynomialEval.zero]

/-! ## `from_coeffs` -/

/-- `Vec::resize` pads with the fill value and truncates, which is exactly the
zero-padding-or-dropping that `CMlPolynomial.ofArray` describes: entry `i` of the
resized list reads as `coeffFn` of the original, because `coeffFn` is itself
`0` out of range. -/
theorem map_resize_eq_range_map (l : List cpoly.field.Ext4) (n : ℕ) :
    (l.resize n cpoly.field.Ext4.ZERO).map toExt
      = (List.range n).map (fun i => (l.map toExt).getD i 0) := by
  have hlen : (l.resize n cpoly.field.Ext4.ZERO).length = n := by
    simp only [List.resize, if_pos (Nat.zero_le _), List.length_append, List.length_take,
      List.length_replicate]
    omega
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi : i < n := by simpa [hlen] using h1
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.resize, if_pos (Nat.zero_le _)]
    by_cases hil : i < l.length
    · rw [List.getElem_append_left (by simp [List.length_take]; omega)]
      rw [List.getElem_take]
      rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_map]
    · have hge : l.length ≤ i := by omega
      have htk : (l.take n).length = l.length := by simp [List.length_take]; omega
      rw [List.getElem_append_right (by omega)]
      rw [List.getElem_replicate]
      rw [List.getD_eq_default _ _ (by simpa using hge)]
      simp

/-- `cpoly::multilinear::MultilinearPoly::from_coeffs` ↔ `CMlPolynomial.ofArray`. -/
theorem of_array_spec (coeffs : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (hc : VecReduced coeffs) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.multilinear.MultilinearPoly.from_coeffs coeffs n ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n.val ∧
      toMl n.val z
        = CMlPolynomial.ofArray (coeffs.val.map toExt).toArray n.val ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.from_coeffs]
  simp only [bind_ok_id]
  apply spec_bind (pow2_spec n hn)
  intro sz hsz
  apply spec_mono (alloc.vec.Vec.resize_spec cpoly.field.Ext4.Insts.CoreCloneClone coeffs sz
    cpoly.field.Ext4.ZERO (ext_clone_eq _))
  intro z hzres
  have hmap : z.val.map toExt = (List.range sz.val).map (coeffFn coeffs) := by
    rw [hzres, map_resize_eq_range_map]
    rfl
  have hz : VecReduced z := by
    intro u hu
    rw [hzres] at hu
    simp only [List.resize, if_pos (Nat.zero_le _)] at hu
    rcases List.mem_append.mp hu with h | h
    · exact hc u (List.mem_of_mem_take h)
    · rw [List.eq_of_mem_replicate h]; exact reduced_ZERO
  have hlen : z.val.length = 2 ^ n.val := by
    have h := congrArg List.length hmap
    simpa [hsz] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  unfold CMlPolynomial.ofArray
  simp only [Vector.getElem_ofFn, List.size_toArray]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm]
  by_cases hic : i < coeffs.val.length
  · have him : i < (coeffs.val.map toExt).length := by simpa using hic
    simp [coeffFn_of_lt, hic]
  · have hge : coeffs.val.length ≤ i := by omega
    have hnim : ¬ i < (coeffs.val.map toExt).length := by simpa using hic
    rw [dif_neg hnim, coeffFn_of_ge coeffs hge]

/-! ## Construction, observation and indexing

The items that only move a table around or read it.  They say nothing new about
`CMlPolynomial`, but they are public Rust API, so each gets a triple.  There is one
pair per reading, because there is one Rust function per reading — and `Index` is
the only one with a precondition, since it panics out of range. -/

/-- `MultilinearPoly::coeffs` views the same words as a slice. -/
@[step]
theorem coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearPoly.coeffs v ⦃ s => s.val = v.val ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.coeffs]; simp only [spec_ok]; rfl

/-- `MultilinearEvals::values` likewise. -/
@[step]
theorem values_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearEvals.values v ⦃ s => s.val = v.val ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.values]; simp only [spec_ok]; rfl

/-- `MultilinearPoly::into_coeffs` gives the table back unchanged. -/
@[step]
theorem into_coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearPoly.into_coeffs v ⦃ z => z = v ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.into_coeffs]; simp only [spec_ok]

/-- `MultilinearEvals::into_values` likewise. -/
@[step]
theorem into_values_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearEvals.into_values v ⦃ z => z = v ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.into_values]; simp only [spec_ok]

/-- `MultilinearEvals::from_values` takes the table as it stands: unlike
`MultilinearPoly::from_coeffs` it does not conform the length, so the denoted
`CMlPolynomialEval n` is only faithful when the caller supplies `2 ^ n` values. -/
@[step]
theorem from_values_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) :
    cpoly.multilinear.MultilinearEvals.from_values v
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧ toMlEval n z = toMlEval n v ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.from_values]
  simp only [spec_ok]
  exact ⟨hv, hvl, trivial⟩

/-- `MultilinearPoly::len` is the table size, `2 ^ n` for a well-formed table. -/
@[step]
theorem len_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearPoly.len v ⦃ m => m.val = v.val.length ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.len]; simp only [spec_ok]; simp

/-- `MultilinearEvals::len` likewise. -/
@[step]
theorem evals_len_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearEvals.len v ⦃ m => m.val = v.val.length ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.len]; simp only [spec_ok]; simp

/-- `MultilinearPoly::is_empty` is always `false` on a well-formed table, since
`2 ^ n ≥ 1`.  Stated as the length test it performs, so it stays true of the
malformed tables the type does not rule out. -/
@[step]
theorem is_empty_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearPoly.is_empty v ⦃ b => (b = true ↔ v.val.length = 0) ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.is_empty]
  apply spec_bind (len_spec v); intro m hm
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro h; rw [← hm, h]; rfl
  · intro h; rw [← hm] at h; scalar_tac

/-- `MultilinearEvals::is_empty` likewise. -/
@[step]
theorem evals_is_empty_spec (v : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearEvals.is_empty v ⦃ b => (b = true ↔ v.val.length = 0) ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.is_empty]
  apply spec_bind (evals_len_spec v); intro m hm
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro h; rw [← hm, h]; rfl
  · intro h; rw [← hm] at h; scalar_tac

/-- `impl Index<usize> for MultilinearPoly` reads coefficient `i`, i.e. entry `i`
of the table `toMl` denotes.  Conditional on `i` being in range: out of range the
Rust panics and the extracted model fails. -/
@[step]
theorem index_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hi : i.val < 2 ^ n) :
    cpoly.multilinear.MultilinearPoly.Insts.CoreOpsIndexIndexUsizeExt4.index v i
      ⦃ a => Reduced a ∧ toExt a = (toMl n v)[i.val] ⦄ := by
  have hib : i.val < v.val.length := by omega
  rw [cpoly.multilinear.MultilinearPoly.Insts.CoreOpsIndexIndexUsizeExt4.index]
  step as ⟨e, he⟩
  refine ⟨he ▸ hv _ (List.getElem_mem hib), ?_⟩
  rw [he, toMl_getElem n v i.val hi, coeffFn_of_lt v hib]

/-- `impl Index<usize> for MultilinearEvals` reads the hypercube value at the
point index `i`. -/
@[step]
theorem evals_index_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hi : i.val < 2 ^ n) :
    cpoly.multilinear.MultilinearEvals.Insts.CoreOpsIndexIndexUsizeExt4.index v i
      ⦃ a => Reduced a ∧ toExt a = (toMlEval n v)[i.val] ⦄ := by
  have hib : i.val < v.val.length := by omega
  rw [cpoly.multilinear.MultilinearEvals.Insts.CoreOpsIndexIndexUsizeExt4.index]
  step as ⟨e, he⟩
  refine ⟨he ▸ hv _ (List.getElem_mem hib), ?_⟩
  rw [he, toMl_getElem n v i.val hi, coeffFn_of_lt v hib]

/-! ## `add`

Both `MultilinearPoly` and `MultilinearEvals` add entry by entry, and neither cares how the index is
read, so the Rust factors the loop into one `multilinear::add_pointwise` over two
slices and both `Add` impls call it.  There is correspondingly one loop spec here,
and two one-screen corollaries — one per reading. -/

theorem add_pointwise_loop_spec (a b : Slice cpoly.field.Ext4) (n : Std.Usize)
    (ha : SliceReduced a) (hb : SliceReduced b)
    (hn : n.val = a.val.length) (hlen : a.val.length ≤ b.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt
        = (List.range i.val).map (fun k => sliceCoeffFn a k + sliceCoeffFn b k) →
      cpoly.multilinear.add_pointwise_loop a b n r i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range n.val).map (fun k => sliceCoeffFn a k + sliceCoeffFn b k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.multilinear.add_pointwise_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt =
        (List.range s.2.val).map (fun k => sliceCoeffFn a k + sliceCoeffFn b k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.multilinear.add_pointwise_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a.val.length := by scalar_tac
      have hib : i1.val < b.val.length := by scalar_tac
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxR : Reduced x := hx ▸ ha _ (List.getElem_mem hia)
      have hyR : Reduced y := hy ▸ hb _ (List.getElem_mem hib)
      step as ⟨t, htR, htF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact htR
      · rw [hr2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, htF]
        rw [hx, hy, sliceCoeffFn_of_lt a hia, sliceCoeffFn_of_lt b hib]
      · have : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::multilinear::add_pointwise` on two `2 ^ n`-entry tables. -/
theorem add_pointwise_spec (n : ℕ) (a b : Slice cpoly.field.Ext4)
    (ha : SliceReduced a) (hb : SliceReduced b)
    (hal : a.val.length = 2 ^ n) (hbl : b.val.length = 2 ^ n) :
    cpoly.multilinear.add_pointwise a b ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      z.val.map toExt
        = (List.range (2 ^ n)).map (fun k => sliceCoeffFn a k + sliceCoeffFn b k) ⦄ := by
  rw [cpoly.multilinear.add_pointwise]
  apply spec_mono (add_pointwise_loop_spec a b (Slice.len a) ha hb (by simp)
    (by omega) (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp)
    (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hslen : (Slice.len a).val = 2 ^ n := by simp [hal]
  rw [hslen] at hmap
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa using h
  exact ⟨hz, hlen, hmap⟩

/-- The shared tail of the two `Add` corollaries: an entrywise-sum table denotes
the `Vector.zipWith (· + ·)` of the two tables it came from. -/
theorem toMl_of_add_map {n : ℕ} {v w z : alloc.vec.Vec cpoly.field.Ext4}
    (hzlen : z.val.length = 2 ^ n)
    (hmap : z.val.map toExt
      = (List.range (2 ^ n)).map (fun k =>
          sliceCoeffFn (alloc.vec.Vec.deref v) k + sliceCoeffFn (alloc.vec.Vec.deref w) k)) :
    toMl n z = Vector.zipWith (· + ·) (toMl n v) (toMl n w) := by
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm]
  simp [toMl]

/-- `cpoly::multilinear::MultilinearPoly`'s `Add` impl ↔ `CMlPolynomial.add`. -/
theorem add_spec (n : ℕ) (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hvl : v.val.length = 2 ^ n) (hwl : w.val.length = 2 ^ n) :
    polyAdd v w
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMl n z = CMlPolynomial.add (toMl n v) (toMl n w) ⦄ := by
  unfold polyAdd
  rw [cpoly.Shared1MultilinearPoly.Insts.CoreOpsArithAddShared0MultilinearPolyMultilinearPoly.add]
  simp only [bind_ok_id]
  apply spec_mono (add_pointwise_spec n (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref w)
    (sliceReduced_deref hv) (sliceReduced_deref hw) (by simpa using hvl) (by simpa using hwl))
  rintro z ⟨hz, hlen, hmap⟩
  exact ⟨hz, hlen, by rw [CMlPolynomial.add]; exact toMl_of_add_map hlen hmap⟩

/-- `cpoly::multilinear::MultilinearEvals`'s `Add` impl ↔ `CMlPolynomialEval.add`.  Same
function underneath, different reading of the index. -/
theorem add_evals_spec (n : ℕ) (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hvl : v.val.length = 2 ^ n) (hwl : w.val.length = 2 ^ n) :
    evalsAdd v w
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMlEval n z = CMlPolynomialEval.add (toMlEval n v) (toMlEval n w) ⦄ := by
  unfold evalsAdd
  rw [cpoly.Shared1MultilinearEvals.Insts.CoreOpsArithAddShared0MultilinearEvalsMultilinearEvals.add]
  simp only [bind_ok_id]
  apply spec_mono (add_pointwise_spec n (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref w)
    (sliceReduced_deref hv) (sliceReduced_deref hw) (by simpa using hvl) (by simpa using hwl))
  rintro z ⟨hz, hlen, hmap⟩
  exact ⟨hz, hlen, by rw [CMlPolynomialEval.add]; exact toMl_of_add_map hlen hmap⟩

/-! ## Negation and scalar multiplication

Negating or scaling an entry does not care how the index is read, so the Rust
factors each into one loop over a slice — `multilinear::neg_pointwise` and
`multilinear::scale_pointwise` — and the `Neg` and `Mul<Ext4>` impls of both
readings call them.

`toMl_eq_ofFn` is the shared tail: a table whose `toExt`-image is a `range` map
denotes the `Vector` of that map, which is what `Vector.map` unfolds to on the
CompPoly side. -/

/-- A table whose `toExt`-image is `(range (2^n)).map f` denotes `Vector.ofFn f`. -/
theorem toMl_eq_ofFn {n : ℕ} {z : alloc.vec.Vec cpoly.field.Ext4} {f : ℕ → F}
    (hzlen : z.val.length = 2 ^ n)
    (hmap : z.val.map toExt = (List.range (2 ^ n)).map f) :
    toMl n z = Vector.ofFn (fun i : Fin (2 ^ n) => f i.val) := by
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm]
  simp

theorem neg_pointwise_loop_spec (a : Slice cpoly.field.Ext4) (n : Std.Usize)
    (ha : VecReduced a) (hn : n.val = a.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map (fun k => - sliceCoeffFn a k) →
      cpoly.multilinear.neg_pointwise_loop a n r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map (fun k => - sliceCoeffFn a k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.multilinear.neg_pointwise_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map (fun k => - sliceCoeffFn a k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.multilinear.neg_pointwise_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a.val.length := by scalar_tac
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ ha _ (List.getElem_mem hia)
      step as ⟨t, htR, htF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact htR
      · rw [hr2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, htF]
        rw [hx, sliceCoeffFn_of_lt a hia]
      · have : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::multilinear::neg_pointwise` on a `2 ^ n`-entry table. -/
theorem neg_pointwise_spec (n : ℕ) (a : Slice cpoly.field.Ext4)
    (ha : VecReduced a) (hal : a.val.length = 2 ^ n) :
    cpoly.multilinear.neg_pointwise a ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      z.val.map toExt = (List.range (2 ^ n)).map (fun k => - sliceCoeffFn a k) ⦄ := by
  rw [cpoly.multilinear.neg_pointwise]
  apply spec_mono (neg_pointwise_loop_spec a (Slice.len a) ha (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp)
    (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hslen : (Slice.len a).val = 2 ^ n := by simp [hal]
  rw [hslen] at hmap
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap; simpa using h
  exact ⟨hz, hlen, hmap⟩

theorem scale_pointwise_loop_spec (a : Slice cpoly.field.Ext4) (r : cpoly.field.Ext4)
    (n : Std.Usize) (ha : VecReduced a) (hr : Reduced r) (hn : n.val = a.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced out →
      out.val.map toExt = (List.range i.val).map (fun k => toExt r * sliceCoeffFn a k) →
      cpoly.multilinear.scale_pointwise_loop a r n out i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map (fun k => toExt r * sliceCoeffFn a k) ⦄ := by
  intro out i hi hout hrel
  rw [cpoly.multilinear.scale_pointwise_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map (fun k => toExt r * sliceCoeffFn a k))
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1, hrel1⟩
    simp only [cpoly.multilinear.scale_pointwise_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a.val.length := by scalar_tac
      have holen : o1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ ha _ (List.getElem_mem hia)
      step as ⟨t, htR, htF⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact ho1 u h
        · rw [List.mem_singleton.mp h]; exact htR
      · rw [ho2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, htF]
        rw [hx, sliceCoeffFn_of_lt a hia]
      · have : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨ho1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hout, hrel⟩

/-- `cpoly::multilinear::scale_pointwise` on a `2 ^ n`-entry table. -/
theorem scale_pointwise_spec (n : ℕ) (a : Slice cpoly.field.Ext4) (r : cpoly.field.Ext4)
    (ha : VecReduced a) (hr : Reduced r) (hal : a.val.length = 2 ^ n) :
    cpoly.multilinear.scale_pointwise a r ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      z.val.map toExt = (List.range (2 ^ n)).map (fun k => toExt r * sliceCoeffFn a k) ⦄ := by
  rw [cpoly.multilinear.scale_pointwise]
  apply spec_mono (scale_pointwise_loop_spec a r (Slice.len a) ha hr (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp)
    (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hslen : (Slice.len a).val = 2 ^ n := by simp [hal]
  rw [hslen] at hmap
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap; simpa using h
  exact ⟨hz, hlen, hmap⟩

/-- `cpoly::multilinear::MultilinearPoly`'s `Neg` ↔ `CMlPolynomial.neg`. -/
theorem neg_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v)
    (hvl : v.val.length = 2 ^ n) :
    polyNeg v
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMl n z = CMlPolynomial.neg (toMl n v) ⦄ := by
  unfold polyNeg
  rw [cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithNegMultilinearPoly.neg]
  simp only [bind_ok_id]
  apply spec_mono (neg_pointwise_spec n (alloc.vec.Vec.deref v) hv (by simpa using hvl))
  rintro z ⟨hz, hlen, hmap⟩
  refine ⟨hz, hlen, ?_⟩
  rw [toMl_eq_ofFn hlen hmap]
  apply Vector.ext
  intro i hi
  simp [CMlPolynomial.neg, toMl]

/-- `cpoly::multilinear::MultilinearEvals`'s `Neg` ↔ `CMlPolynomialEval.neg`. -/
theorem neg_evals_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v)
    (hvl : v.val.length = 2 ^ n) :
    evalsNeg v
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMlEval n z = CMlPolynomialEval.neg (toMlEval n v) ⦄ := by
  unfold evalsNeg
  rw [cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithNegMultilinearEvals.neg]
  simp only [bind_ok_id]
  apply spec_mono (neg_pointwise_spec n (alloc.vec.Vec.deref v) hv (by simpa using hvl))
  rintro z ⟨hz, hlen, hmap⟩
  refine ⟨hz, hlen, ?_⟩
  show toMl n z = _
  rw [toMl_eq_ofFn hlen hmap]
  apply Vector.ext
  intro i hi
  simp [CMlPolynomialEval.neg, toMl]

/-- `cpoly::multilinear::MultilinearPoly`'s `Mul<Ext4>` ↔ `CMlPolynomial.smul`. -/
theorem smul_spec (n : ℕ) (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) :
    polySmul v r
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMl n z = CMlPolynomial.smul (toExt r) (toMl n v) ⦄ := by
  unfold polySmul
  rw [cpoly.Shared0MultilinearPoly.Insts.CoreOpsArithMulExt4MultilinearPoly.mul]
  simp only [bind_ok_id]
  apply spec_mono (scale_pointwise_spec n (alloc.vec.Vec.deref v) r hv hr (by simpa using hvl))
  rintro z ⟨hz, hlen, hmap⟩
  refine ⟨hz, hlen, ?_⟩
  rw [toMl_eq_ofFn hlen hmap]
  apply Vector.ext
  intro i hi
  simp [CMlPolynomial.smul, toMl]

/-- `cpoly::multilinear::MultilinearEvals`'s `Mul<Ext4>` ↔ `CMlPolynomialEval.smul`. -/
theorem smul_evals_spec (n : ℕ) (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) :
    evalsSmul v r
      ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
        toMlEval n z = CMlPolynomialEval.smul (toExt r) (toMlEval n v) ⦄ := by
  unfold evalsSmul
  rw [cpoly.Shared0MultilinearEvals.Insts.CoreOpsArithMulExt4MultilinearEvals.mul]
  simp only [bind_ok_id]
  apply spec_mono (scale_pointwise_spec n (alloc.vec.Vec.deref v) r hv hr (by simpa using hvl))
  rintro z ⟨hz, hlen, hmap⟩
  refine ⟨hz, hlen, ?_⟩
  show toMl n z = _
  rw [toMl_eq_ofFn hlen hmap]
  apply Vector.ext
  intro i hi
  simp [CMlPolynomialEval.smul, toMl]

/-! ## Iterative basis construction -/

/-- Adding the `j`-th binary place leaves every lower bit of an index below
`2^j` unchanged. -/
theorem testBit_add_pow_of_lt (j i k : ℕ) (hi : i < 2 ^ j) (hk : k < j) :
    Nat.testBit (2 ^ j + i) k = Nat.testBit i k := by
  have h := Nat.testBit_mod_two_pow (2 ^ j + i) j k
  simp only [hk, decide_true, Bool.true_and] at h
  rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hi] at h
  rw [Nat.mod_eq_of_lt hi] at h
  exact h.symm

/-- The newly added place is set. -/
theorem testBit_add_pow_self (j i : ℕ) (hi : i < 2 ^ j) :
    Nat.testBit (2 ^ j + i) j = true := by
  rw [testBit_eq_div_pow_mod, Nat.add_div (Nat.pow_pos (by omega))]
  rw [Nat.div_self (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hi]
  simp only [Nat.mod_self, Nat.mod_eq_of_lt hi, zero_add]
  rw [if_neg (by omega)]
  rfl

theorem monoProd_extend_low (j i : ℕ) (x : ℕ → F) (hi : i < 2 ^ j) :
    monoProd (j + 1) i x = monoProd j i x := by
  unfold monoProd
  rw [Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hi]
  simp

theorem monoProd_extend_high (j i : ℕ) (x : ℕ → F) (hi : i < 2 ^ j) :
    monoProd (j + 1) (2 ^ j + i) x = monoProd j i x * x j := by
  unfold monoProd
  rw [Finset.prod_range_succ, testBit_add_pow_self j i hi]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [testBit_add_pow_of_lt j i k hi (Finset.mem_range.mp hk)]

theorem lagProd_extend_low (j i : ℕ) (x : ℕ → F) (hi : i < 2 ^ j) :
    lagProd (j + 1) i x = lagProd j i x * (1 - x j) := by
  unfold lagProd
  rw [Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hi]
  simp

theorem lagProd_extend_high (j i : ℕ) (x : ℕ → F) (hi : i < 2 ^ j) :
    lagProd (j + 1) (2 ^ j + i) x = lagProd j i x * x j := by
  unfold lagProd
  rw [Finset.prod_range_succ, testBit_add_pow_self j i hi]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [testBit_add_pow_of_lt j i k hi (Finset.mem_range.mp hk)]

theorem range_pow_succ_append (j : ℕ) :
    List.range (2 ^ (j + 1)) =
      List.range (2 ^ j) ++ (List.range (2 ^ j)).map (fun i => 2 ^ j + i) := by
  apply List.ext_getElem
  · simp only [List.length_range, List.length_append, List.length_map]
    rw [pow_succ]
    omega
  · intro k hk1 _
    simp only [List.getElem_range]
    by_cases hk : k < 2 ^ j
    · rw [List.getElem_append_left (by simp; exact hk)]
      simp
    · have hlow : 2 ^ j ≤ k := by omega
      have hkfull : k < 2 ^ (j + 1) := by simpa using hk1
      have hsub : k - 2 ^ j < 2 ^ j := by
        rw [pow_succ] at hkfull
        omega
      rw [List.getElem_append_right (by simp; exact hlow)]
      simp only [List.getElem_map, List.getElem_range, List.length_range]
      exact (Nat.add_sub_of_le hlow).symm

theorem mono_extend_map (j : ℕ) (x : ℕ → F) :
    (List.range (2 ^ j)).map (fun i => monoProd j i x) ++
      (List.range (2 ^ j)).map (fun i => monoProd j i x * x j) =
    (List.range (2 ^ (j + 1))).map (fun i => monoProd (j + 1) i x) := by
  rw [range_pow_succ_append]
  simp only [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [monoProd_extend_low _ _ _ (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    rw [monoProd_extend_high _ _ _ (List.mem_range.mp hi)]

theorem lag_extend_map (j : ℕ) (x : ℕ → F) :
    (List.range (2 ^ j)).map (fun i => lagProd j i x * (1 - x j)) ++
      (List.range (2 ^ j)).map (fun i => lagProd j i x * x j) =
    (List.range (2 ^ (j + 1))).map (fun i => lagProd (j + 1) i x) := by
  rw [range_pow_succ_append]
  simp only [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [lagProd_extend_low _ _ _ (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    rw [lagProd_extend_high _ _ _ (List.mem_range.mp hi)]

/-! ## `monomial_basis` -/

set_option maxHeartbeats 1000000 in
theorem monomial_basis_inner_spec (w : Slice cpoly.field.Ext4) (basis : alloc.vec.Vec cpoly.field.Ext4)
    (j half : Std.Usize) (hw : VecReduced w) (hb : VecReduced basis)
    (hjw : j.val < w.val.length) (hblen : basis.val.length = half.val)
    (hbound : basis.val.length + half.val ≤ Std.Usize.max) :
    cpoly.multilinear.monomial_basis_loop0_loop0 w basis j half 0#usize ⦃ z =>
      VecReduced z ∧ z.val.map toExt = basis.val.map toExt ++
        (List.range half.val).map (fun k => coeffFn basis k * pointFn w 0 j.val) ⦄ := by
  rw [cpoly.multilinear.monomial_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = basis.val.map toExt ++
        (List.range s.2.val).map (fun k => coeffFn basis k * pointFn w 0 j.val))
  · rintro ⟨cur, i⟩ ⟨hi, hcur, hrel⟩
    simp only [Prod.fst, Prod.snd] at hi hcur hrel
    simp only [cpoly.multilinear.monomial_basis_loop0_loop0.body]
    by_cases hlt : i < half
    · rw [if_pos hlt]
      have hcurlen : cur.val.length = basis.val.length + i.val := by
        have h := congrArg List.length hrel
        simpa using h
      have hib : i.val < basis.val.length := by scalar_tac
      have hic : i.val < cur.val.length := by scalar_tac
      step as ⟨old, hold⟩
      have holdR : Reduced old := hold ▸ hcur _ (List.getElem_mem hic)
      have holdF : toExt old = coeffFn basis i.val := by
        have hm := getElem_of_list_eq hrel (i := i.val) (hi := by simpa [hcurlen] using hic)
        rw [List.getElem_append_left (by simpa using hib)] at hm
        rw [hold, coeffFn_of_lt basis hib]
        simpa only [List.getElem_map] using hm
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ hw _ (List.getElem_mem hjw)
      have hxF0 : toExt x = pointFn w j.val 0 := by
        calc
          toExt x = toExt w.val[j.val] := by rw [hx]
          _ = pointFn w j.val 0 := (pointFn_of_lt w j.val (k := 0) hjw).symm
      have hxF : toExt x = pointFn w 0 j.val := hxF0.trans (pointFn_offset_zero w j.val)
      apply spec_bind (ext_mul_spec old x holdR hxR)
      rintro product ⟨hproductR, hproductF⟩
      have hpushbound : cur.val.length < Std.Usize.max := by scalar_tac
      apply spec_bind (alloc.vec.Vec.push_spec cur product hpushbound)
      rintro cur2 hpush
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu
        rw [hpush] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hcur u hu
        · rw [List.mem_singleton.mp hu]
          exact hproductR
      · rw [hi2, List.range_succ, hpush, List.map_append, hrel, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hproductF, holdF, hxF]
        simp [List.append_assoc]
      · scalar_tac
    · rw [if_neg hlt]
      have heq : i.val = half.val := by scalar_tac
      exact ⟨hcur, by simpa [heq] using hrel⟩
  · exact ⟨by simp, hb, by simp⟩

set_option maxHeartbeats 1000000 in
theorem monomial_basis_loop_spec (w : Slice cpoly.field.Ext4) (nn : Std.Usize)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) (hmax : 2 ^ nn.val ≤ Std.Usize.max) :
    ∀ (basis : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ nn.val → VecReduced basis →
      basis.val.map toExt
        = (List.range (2 ^ j.val)).map (fun k => monoProd j.val k (pointFn w 0)) →
      basis.val.length = 2 ^ j.val →
      cpoly.multilinear.monomial_basis_loop0 w nn basis j ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range (2 ^ nn.val)).map (fun k => monoProd nn.val k (pointFn w 0)) ⦄ := by
  intro basis j hj hb hrel hblen
  rw [cpoly.multilinear.monomial_basis_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.val)
    (fun s => s.2.val ≤ nn.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range (2 ^ s.2.val)).map
        (fun k => monoProd s.2.val k (pointFn w 0)) ∧ s.1.val.length = 2 ^ s.2.val)
  · rintro ⟨b, k⟩ ⟨hk, hb1, hrel1, hblen1⟩
    have hrelk : b.val.map toExt = (List.range (2 ^ k.val)).map
        (fun q => monoProd k.val q (pointFn w 0)) := by
      simpa only [Prod.fst, Prod.snd] using hrel1
    have hblenk : b.val.length = 2 ^ k.val := by
      simpa only [Prod.fst, Prod.snd] using hblen1
    simp only [cpoly.multilinear.monomial_basis_loop0.body]
    by_cases hlt : k < nn
    · rw [if_pos hlt]
      have hkw : k.val < w.val.length := by scalar_tac
      have hbound : b.val.length + b.len.val ≤ Std.Usize.max := by
        change b.val.length + b.val.length ≤ Std.Usize.max
        calc
          b.val.length + b.val.length = 2 ^ (k.val + 1) := by rw [hblenk, pow_succ]; omega
          _ ≤ 2 ^ nn.val := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ Std.Usize.max := hmax
      apply spec_bind (monomial_basis_inner_spec w b k b.len hw hb1 hkw (by rfl) hbound)
      rintro b2 ⟨hb2, hmap2⟩
      step as ⟨k2, hk2⟩
      have hcoeff : ∀ q, q < 2 ^ k.val → coeffFn b q = monoProd k.val q (pointFn w 0) := by
        intro q hq
        rw [coeffFn_of_lt b (by rw [hblenk]; exact hq)]
        have hm := getElem_of_list_eq hrelk (i := q) (hi := by simp [hblenk, hq])
        simpa only [List.getElem_map, List.getElem_range] using hm
      have hhigh : (List.range b.len.val).map (fun q => coeffFn b q * pointFn w 0 k.val) =
          (List.range (2 ^ k.val)).map (fun q => monoProd k.val q (pointFn w 0) * pointFn w 0 k.val) := by
        change (List.range b.val.length).map _ = _
        rw [hblenk]
        apply List.map_congr_left
        intro q hq
        rw [hcoeff q (List.mem_range.mp hq)]
      have hmapnext : b2.val.map toExt = (List.range (2 ^ (k.val + 1))).map
          (fun q => monoProd (k.val + 1) q (pointFn w 0)) := by
        calc
          b2.val.map toExt = b.val.map toExt ++
              (List.range b.len.val).map (fun q => coeffFn b q * pointFn w 0 k.val) := hmap2
          _ = (List.range (2 ^ k.val)).map (fun q => monoProd k.val q (pointFn w 0)) ++
              (List.range (2 ^ k.val)).map
                (fun q => monoProd k.val q (pointFn w 0) * pointFn w 0 k.val) := by
                rw [hrelk, hhigh]
          _ = _ := mono_extend_map k.val (pointFn w 0)
      have hlen2 : b2.val.length = 2 ^ (k.val + 1) := by
        have h := congrArg List.length hmapnext
        simpa using h
      refine ⟨by scalar_tac, hb2, ?_, ?_, ?_⟩
      · simpa [hk2] using hmapnext
      · simpa [hk2] using hlen2
      · scalar_tac
    · rw [if_neg hlt]
      have heq : k.val = nn.val := by scalar_tac
      exact ⟨hb1, by simpa [heq] using hrel1⟩
  · exact ⟨hj, hb, hrel, hblen⟩

/-- `cpoly::multilinear::monomial_basis` ↔ `CMlPolynomial.monomialBasis`. -/
theorem monomial_basis_spec (n : ℕ) (w : Slice cpoly.field.Ext4)
    (hw : VecReduced w) (hwl : w.val.length = n) (hsz : 2 ^ n ≤ Std.Usize.max) :
    cpoly.multilinear.monomial_basis w ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.monomialBasis (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.monomial_basis]
  apply spec_bind (pow2_spec (alloc.vec.Vec.len w) (by simpa [hwl] using hsz))
  intro sz hsz'
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new cpoly.field.Ext4)
    cpoly.field.Ext4.ONE (by scalar_tac))
  rintro basis hpush
  apply spec_mono (monomial_basis_loop_spec w w.len hw (by simp) (by simpa [hwl] using hsz)
    basis 0#usize (by simp)
    (by intro u hu; rw [hpush] at hu; simp at hu; exact hu ▸ reduced_ONE)
    (by rw [hpush]; simp [monoProd_zero, toExt_ONE]) (by simp [hpush]))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hwl] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm, monomialBasis_getElem']
  congr 2

/-! ## `lagrange_basis` -/

set_option maxHeartbeats 1000000 in
theorem lagrange_basis_low_spec (basis next : alloc.vec.Vec cpoly.field.Ext4)
    (one_minus : cpoly.field.Ext4) (half : Std.Usize) (hb : VecReduced basis)
    (hn : VecReduced next) (hblen : basis.val.length = half.val)
    (hbound : next.val.length + half.val ≤ Std.Usize.max) (hr : Reduced one_minus) :
    cpoly.multilinear.lagrange_basis_loop0_loop0 basis one_minus half next 0#usize ⦃ z =>
      VecReduced z ∧ z.val.map toExt = next.val.map toExt ++
        (List.range half.val).map (fun k => coeffFn basis k * toExt one_minus) ⦄ := by
  rw [cpoly.multilinear.lagrange_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = next.val.map toExt ++
        (List.range s.2.val).map (fun k => coeffFn basis k * toExt one_minus))
  · rintro ⟨cur, i⟩ ⟨hi, hcur, hrel⟩
    simp only [Prod.fst, Prod.snd] at hi hcur hrel
    simp only [cpoly.multilinear.lagrange_basis_loop0_loop0.body]
    by_cases hlt : i < half
    · rw [if_pos hlt]
      have hcurlen : cur.val.length = next.val.length + i.val := by
        have h := congrArg List.length hrel
        simpa using h
      have hib : i.val < basis.val.length := by scalar_tac
      step as ⟨old, hold⟩
      have holdR : Reduced old := hold ▸ hb _ (List.getElem_mem hib)
      have holdF : toExt old = coeffFn basis i.val := by
        rw [hold, coeffFn_of_lt basis hib]
      apply spec_bind (ext_mul_spec old one_minus holdR hr)
      rintro product ⟨hproductR, hproductF⟩
      have hpushbound : cur.val.length < Std.Usize.max := by scalar_tac
      apply spec_bind (alloc.vec.Vec.push_spec cur product hpushbound)
      rintro cur2 hpush
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu
        rw [hpush] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hcur u hu
        · rw [List.mem_singleton.mp hu]
          exact hproductR
      · rw [hi2, List.range_succ, hpush, List.map_append, hrel, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hproductF, holdF]
        simp [List.append_assoc]
      · scalar_tac
    · rw [if_neg hlt]
      have heq : i.val = half.val := by scalar_tac
      exact ⟨hcur, by simpa [heq] using hrel⟩
  · exact ⟨by simp, hn, by simp⟩

set_option maxHeartbeats 1000000 in
theorem lagrange_basis_high_spec (w : Slice cpoly.field.Ext4)
    (basis next : alloc.vec.Vec cpoly.field.Ext4) (j half : Std.Usize)
    (hw : VecReduced w) (hb : VecReduced basis) (hn : VecReduced next)
    (hjw : j.val < w.val.length) (hblen : basis.val.length = half.val)
    (hbound : next.val.length + half.val ≤ Std.Usize.max) :
    cpoly.multilinear.lagrange_basis_loop0_loop1 w basis j half next 0#usize ⦃ z =>
      VecReduced z ∧ z.val.map toExt = next.val.map toExt ++
        (List.range half.val).map (fun k => coeffFn basis k * pointFn w 0 j.val) ⦄ := by
  rw [cpoly.multilinear.lagrange_basis_loop0_loop1]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = next.val.map toExt ++
        (List.range s.2.val).map (fun k => coeffFn basis k * pointFn w 0 j.val))
  · rintro ⟨cur, i⟩ ⟨hi, hcur, hrel⟩
    simp only [Prod.fst, Prod.snd] at hi hcur hrel
    simp only [cpoly.multilinear.lagrange_basis_loop0_loop1.body]
    by_cases hlt : i < half
    · rw [if_pos hlt]
      have hcurlen : cur.val.length = next.val.length + i.val := by
        have h := congrArg List.length hrel
        simpa using h
      have hib : i.val < basis.val.length := by scalar_tac
      step as ⟨old, hold⟩
      have holdR : Reduced old := hold ▸ hb _ (List.getElem_mem hib)
      have holdF : toExt old = coeffFn basis i.val := by
        rw [hold, coeffFn_of_lt basis hib]
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ hw _ (List.getElem_mem hjw)
      have hxF0 : toExt x = pointFn w j.val 0 := by
        calc
          toExt x = toExt w.val[j.val] := by rw [hx]
          _ = pointFn w j.val 0 := (pointFn_of_lt w j.val (k := 0) hjw).symm
      have hxF : toExt x = pointFn w 0 j.val := hxF0.trans (pointFn_offset_zero w j.val)
      apply spec_bind (ext_mul_spec old x holdR hxR)
      rintro product ⟨hproductR, hproductF⟩
      have hpushbound : cur.val.length < Std.Usize.max := by scalar_tac
      apply spec_bind (alloc.vec.Vec.push_spec cur product hpushbound)
      rintro cur2 hpush
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu
        rw [hpush] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hcur u hu
        · rw [List.mem_singleton.mp hu]
          exact hproductR
      · rw [hi2, List.range_succ, hpush, List.map_append, hrel, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hproductF, holdF, hxF]
        simp [List.append_assoc]
      · scalar_tac
    · rw [if_neg hlt]
      have heq : i.val = half.val := by scalar_tac
      exact ⟨hcur, by simpa [heq] using hrel⟩
  · exact ⟨by simp, hn, by simp⟩

set_option maxHeartbeats 1000000 in
theorem lagrange_basis_loop_spec (w : Slice cpoly.field.Ext4) (nn : Std.Usize)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) (hmax : 2 ^ nn.val ≤ Std.Usize.max) :
    ∀ (basis : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ nn.val → VecReduced basis →
      basis.val.map toExt = (List.range (2 ^ j.val)).map
        (fun k => lagProd j.val k (pointFn w 0)) →
      basis.val.length = 2 ^ j.val →
      cpoly.multilinear.lagrange_basis_loop0 w nn basis j ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range (2 ^ nn.val)).map
          (fun k => lagProd nn.val k (pointFn w 0)) ⦄ := by
  intro basis j hj hb hrel hblen
  rw [cpoly.multilinear.lagrange_basis_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.val)
    (fun s => s.2.val ≤ nn.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range (2 ^ s.2.val)).map
        (fun k => lagProd s.2.val k (pointFn w 0)) ∧ s.1.val.length = 2 ^ s.2.val)
  · rintro ⟨b, k⟩ ⟨hk, hb1, hrel1, hblen1⟩
    have hrelk : b.val.map toExt = (List.range (2 ^ k.val)).map
        (fun q => lagProd k.val q (pointFn w 0)) := by
      simpa only [Prod.fst, Prod.snd] using hrel1
    have hblenk : b.val.length = 2 ^ k.val := by
      simpa only [Prod.fst, Prod.snd] using hblen1
    simp only [cpoly.multilinear.lagrange_basis_loop0.body]
    by_cases hlt : k < nn
    · rw [if_pos hlt]
      have hkw : k.val < w.val.length := by scalar_tac
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ hw _ (List.getElem_mem hkw)
      have hxF0 : toExt x = pointFn w k.val 0 := by
        calc
          toExt x = toExt w.val[k.val] := by rw [hx]
          _ = pointFn w k.val 0 := (pointFn_of_lt w k.val (k := 0) hkw).symm
      have hxF : toExt x = pointFn w 0 k.val := hxF0.trans (pointFn_offset_zero w k.val)
      apply spec_bind (ext_sub_spec cpoly.field.Ext4.ONE x reduced_ONE hxR)
      rintro one_minus ⟨homR, homF⟩
      have hOneF : toExt one_minus = 1 - pointFn w 0 k.val := by
        rw [homF, hxF, toExt_ONE]
      have hcap : 2 * b.len.val ≤ Std.Usize.max := by
        change 2 * b.val.length ≤ Std.Usize.max
        calc
          2 * b.val.length = 2 ^ (k.val + 1) := by rw [hblenk, pow_succ]; omega
          _ ≤ 2 ^ nn.val := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ Std.Usize.max := hmax
      step as ⟨capacity, hcapacity⟩
      simp only [alloc.vec.Vec.with_capacity]
      apply spec_bind (lagrange_basis_low_spec b (alloc.vec.Vec.new cpoly.field.Ext4) one_minus b.len
        hb1 (by intro u hu; simp at hu) (by rfl) (by scalar_tac) homR)
      rintro low ⟨hlow, hlowmap⟩
      have hlowlen : low.val.length = 2 ^ k.val := by
        have h := congrArg List.length hlowmap
        simp only [List.length_map, List.length_append, List.length_range] at h
        calc
          low.val.length = [].length + b.len.val := h
          _ = b.val.length := by simp
          _ = 2 ^ k.val := hblenk
      have hhighbound : low.val.length + b.len.val ≤ Std.Usize.max := by
        change low.val.length + b.val.length ≤ Std.Usize.max
        calc
          low.val.length + b.val.length = 2 ^ (k.val + 1) := by rw [hlowlen, hblenk, pow_succ]; omega
          _ ≤ 2 ^ nn.val := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ Std.Usize.max := hmax
      apply spec_bind (lagrange_basis_high_spec w b low k b.len hw hb1 hlow hkw (by rfl) hhighbound)
      rintro b2 ⟨hb2, hmap2⟩
      step as ⟨k2, hk2⟩
      have hlowmap' : low.val.map toExt = (List.range (2 ^ k.val)).map
          (fun q => lagProd k.val q (pointFn w 0) * (1 - pointFn w 0 k.val)) := by
        rw [hlowmap]
        change [] ++ (List.range b.val.length).map
          (fun q => coeffFn b q * toExt one_minus) = _
        simp only [List.nil_append]
        rw [hblenk]
        apply List.map_congr_left
        intro q hq
        rw [coeffFn_of_lt b (by rw [hblenk]; exact List.mem_range.mp hq)]
        have hm := getElem_of_list_eq hrelk (i := q)
          (hi := by simp [hblenk, List.mem_range.mp hq])
        simp only [List.getElem_map, List.getElem_range] at hm
        rw [hm, hOneF]
      have hhigh : (List.range b.len.val).map (fun q => coeffFn b q * pointFn w 0 k.val) =
          (List.range (2 ^ k.val)).map (fun q => lagProd k.val q (pointFn w 0) * pointFn w 0 k.val) := by
        change (List.range b.val.length).map _ = _
        rw [hblenk]
        apply List.map_congr_left
        intro q hq
        rw [coeffFn_of_lt b (by rw [hblenk]; exact List.mem_range.mp hq)]
        have hm := getElem_of_list_eq hrelk (i := q) (hi := by simp [hblenk, List.mem_range.mp hq])
        simp only [List.getElem_map, List.getElem_range] at hm
        rw [hm]
      have hmapnext : b2.val.map toExt = (List.range (2 ^ (k.val + 1))).map
          (fun q => lagProd (k.val + 1) q (pointFn w 0)) := by
        calc
          b2.val.map toExt = low.val.map toExt ++
              (List.range b.len.val).map (fun q => coeffFn b q * pointFn w 0 k.val) := hmap2
          _ = (List.range (2 ^ k.val)).map
                (fun q => lagProd k.val q (pointFn w 0) * (1 - pointFn w 0 k.val)) ++
              (List.range (2 ^ k.val)).map
                (fun q => lagProd k.val q (pointFn w 0) * pointFn w 0 k.val) := by rw [hlowmap', hhigh]
          _ = _ := lag_extend_map k.val (pointFn w 0)
      have hlen2 : b2.val.length = 2 ^ (k.val + 1) := by
        have h := congrArg List.length hmapnext
        simpa using h
      refine ⟨by scalar_tac, hb2, ?_, ?_, ?_⟩
      · simpa [hk2] using hmapnext
      · simpa [hk2] using hlen2
      · scalar_tac
    · rw [if_neg hlt]
      have heq : k.val = nn.val := by scalar_tac
      exact ⟨hb1, by simpa [heq] using hrel1⟩
  · exact ⟨hj, hb, hrel, hblen⟩

/-- `cpoly::multilinear::lagrange_basis` ↔ `CMlPolynomialEval.lagrangeBasis`. -/
theorem lagrange_basis_spec (n : ℕ) (w : Slice cpoly.field.Ext4)
    (hw : VecReduced w) (hwl : w.val.length = n) (hsz : 2 ^ n ≤ Std.Usize.max) :
    cpoly.multilinear.lagrange_basis w ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMlEval n z = CMlPolynomialEval.lagrangeBasis (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.lagrange_basis]
  simp only [bind_ok_id]
  apply spec_bind (pow2_spec (alloc.vec.Vec.len w) (by simpa [hwl] using hsz))
  intro sz hsz'
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new cpoly.field.Ext4)
    cpoly.field.Ext4.ONE (by scalar_tac))
  rintro basis hpush
  apply spec_mono (lagrange_basis_loop_spec w w.len hw (by simp) (by simpa [hwl] using hsz)
    basis 0#usize (by simp)
    (by intro u hu; rw [hpush] at hu; simp at hu; exact hu ▸ reduced_ONE)
    (by rw [hpush]; simp [lagProd_zero, toExt_ONE]) (by simp [hpush]))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hwl] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm, lagrangeBasis_getElem']
  congr 2

/-! ## `dot` -/

theorem dot_loop_spec (a b : Slice cpoly.field.Ext4) (n : Std.Usize)
    (ha : VecReduced a) (hb : VecReduced b) :
    ∀ (acc : cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → Reduced acc →
      n.val ≤ a.val.length → n.val ≤ b.val.length →
      toExt acc = ∑ k ∈ Finset.range i.val, coeffFn a k * coeffFn b k →
      cpoly.multilinear.dot_loop a b n acc i ⦃ z => Reduced z ∧
        toExt z = ∑ k ∈ Finset.range n.val, coeffFn a k * coeffFn b k ⦄ := by
  intro acc i hi hacc han hbn heq
  rw [cpoly.multilinear.dot_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ Reduced s.1 ∧
      toExt s.1 = ∑ k ∈ Finset.range s.2.val, coeffFn a k * coeffFn b k)
  · rintro ⟨acc1, i1⟩ ⟨hi1, ha1, heq1⟩
    simp only [cpoly.multilinear.dot_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a.val.length := by scalar_tac
      have hib : i1.val < b.val.length := by scalar_tac
      step as ⟨av, hav⟩
      step as ⟨bv, hbv⟩
      have havr : Reduced av := hav ▸ ha _ (List.getElem_mem hia)
      have hbvr : Reduced bv := hbv ▸ hb _ (List.getElem_mem hib)
      step as ⟨p, hpr, hpf⟩
      step as ⟨acc2, hacc2, hacc2f⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, hacc2, ?_, ?_⟩
      · rw [hi2, hacc2f, heq1, Finset.sum_range_succ, hpf, hav, hbv,
          coeffFn_of_lt a hia, coeffFn_of_lt b hib]
      · have : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      simp only [spec_ok]
      have : i1.val = n.val := by scalar_tac
      refine ⟨ha1, ?_⟩
      rw [heq1, this]
  · exact ⟨hi, hacc, heq⟩

/-- `cpoly::multilinear::dot` ↔ `Vector.dotProduct`, as a `Finset.range` sum.

The Rust takes two slices and runs over `a.len()`, so `n` is pinned to that. -/
theorem dot_spec (a b : Slice cpoly.field.Ext4) (n : Std.Usize)
    (ha : VecReduced a) (hb : VecReduced b)
    (han : n = Slice.len a) (hbn : n.val ≤ b.val.length) :
    cpoly.multilinear.dot a b ⦃ z => Reduced z ∧
      toExt z = ∑ k ∈ Finset.range n.val, coeffFn a k * coeffFn b k ⦄ := by
  rw [cpoly.multilinear.dot, ← han]
  apply dot_loop_spec a b n ha hb cpoly.field.Ext4.ZERO 0#usize
  · simp
  · exact reduced_ZERO
  · rw [han]; simp
  · exact hbn
  · simp

/-! ## `eval`, `eval_lagrange`, `eq_tilde` -/

/-- `cpoly::multilinear::MultilinearPoly::eval` ↔ `CMlPolynomial.eval`. -/
theorem eval_spec (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.multilinear.MultilinearPoly.eval p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomial.eval (toMl n p) (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.eval]
  apply spec_bind (monomial_basis_spec n w hw hwl (pow2_le_usize_max hpl))
  intro basis hb
  apply spec_mono (dot_spec (alloc.vec.Vec.deref p) (alloc.vec.Vec.deref basis)
    (alloc.vec.Vec.len p) hp hb.1 (by simp) (by simp [hb.2.1, hpl]))
  intro z hz
  simp only [coeffFn_deref] at hz
  refine ⟨hz.1, ?_⟩
  rw [hz.2, ← mlVal_eq_eval n p w 0]
  unfold mlVal
  rw [show (alloc.vec.Vec.len p).val = 2 ^ n by simp [hpl]]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 1
  rw [← toMl_getElem n basis k hk, hb.2.2, monomialBasis_getElem']

/-- `cpoly::multilinear::MultilinearEvals::eval` ↔ `CMlPolynomialEval.eval`. -/
theorem eval_lagrange_spec (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.multilinear.MultilinearEvals.eval p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.eval (toMlEval n p) (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.eval]
  apply spec_bind (lagrange_basis_spec n w hw hwl (pow2_le_usize_max hpl))
  intro basis hb
  apply spec_mono (dot_spec (alloc.vec.Vec.deref p) (alloc.vec.Vec.deref basis)
    (alloc.vec.Vec.len p) hp hb.1 (by simp) (by simp [hb.2.1, hpl]))
  intro z hz
  simp only [coeffFn_deref] at hz
  refine ⟨hz.1, ?_⟩
  rw [hz.2, ← mlValL_eq_eval n p w 0]
  unfold mlValL
  rw [show (alloc.vec.Vec.len p).val = 2 ^ n by simp [hpl]]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 1
  rw [← toMl_getElem n basis k hk]
  change (toMlEval n basis)[k] = _
  rw [hb.2.2, lagrangeBasis_getElem']

/-- The first direct-product loop reaches the common arity and accumulates every factor. -/
theorem eq_tilde_loop0_spec (w x : Slice cpoly.field.Ext4) (n : Std.Usize)
    (hw : VecReduced w) (hx : VecReduced x)
    (hn : n.val = w.val.length) (hxl : x.val.length = n.val) :
    ∀ (acc : cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → Reduced acc →
      toExt acc = eqProd i.val (pointFn w 0) (pointFn x 0) →
      cpoly.multilinear.eq_tilde_loop0 w x n acc i ⦃ z =>
        Reduced z.1 ∧ z.2.val = n.val ∧
          toExt z.1 = eqProd n.val (pointFn w 0) (pointFn x 0) ⦄ := by
  intro acc i hi hacc hval
  rw [cpoly.multilinear.eq_tilde_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ Reduced s.1 ∧
      toExt s.1 = eqProd s.2.val (pointFn w 0) (pointFn x 0))
  · rintro ⟨a, k⟩ ⟨hk, ha, hv⟩
    simp only [Prod.fst, Prod.snd] at hk ha hv
    simp only [cpoly.multilinear.eq_tilde_loop0.body]
    by_cases hlt : k < n
    · rw [if_pos hlt]
      have hkx : k.val < x.val.length := by scalar_tac
      have hkw : k.val < w.val.length := by scalar_tac
      step as ⟨xe, hxe⟩
      have hxeR : Reduced xe := hxe ▸ hx _ (List.getElem_mem hkx)
      step as ⟨we, hwe⟩
      have hweR : Reduced we := hwe ▸ hw _ (List.getElem_mem hkw)
      apply spec_bind (ext_mul_spec xe we hxeR hweR)
      rintro product ⟨hproductR, hproductF⟩
      apply spec_bind (ext_sub_spec cpoly.field.Ext4.ONE xe reduced_ONE hxeR)
      rintro oneMinusX ⟨honeMinusXR, honeMinusXF⟩
      apply spec_bind (ext_sub_spec oneMinusX we honeMinusXR hweR)
      rintro oneMinusXMinusW ⟨honeMinusXMinusWR, honeMinusXMinusWF⟩
      apply spec_bind (ext_add_spec oneMinusXMinusW product honeMinusXMinusWR hproductR)
      rintro withProduct ⟨hwithProductR, hwithProductF⟩
      apply spec_bind (ext_add_spec withProduct product hwithProductR hproductR)
      rintro factor ⟨hfactorR, hfactorF⟩
      apply spec_bind (ext_mul_assign_spec a factor ha hfactorR)
      rintro a2 ⟨ha2R, ha2F⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ha2R, ?_, ?_⟩
      · calc
          toExt a2 = toExt a * toExt factor := ha2F
          _ = eqProd k.val (pointFn w 0) (pointFn x 0) * toExt factor := by rw [hv]
          _ = eqProd (k.val + 1) (pointFn w 0) (pointFn x 0) := by
            unfold eqProd
            rw [Finset.prod_range_succ]
            unfold eqFactor
            rw [hfactorF, hwithProductF, honeMinusXMinusWF, honeMinusXF, hproductF]
            rw [hxe, hwe, pointFn_of_lt x 0 (by simpa using hkx),
              pointFn_of_lt w 0 (by simpa using hkw), toExt_ONE]
            ring
          _ = eqProd k2.val (pointFn w 0) (pointFn x 0) := by
            congr 2
            exact hk2.symm
      · scalar_tac
    · rw [if_neg hlt]
      have heq : k.val = n.val := by scalar_tac
      exact ⟨ha, by simpa [heq], by simpa [heq] using hv⟩
  · exact ⟨hi, hacc, hval⟩

/-- The compatibility tail is empty when the points have the same arity. -/
theorem eq_tilde_loop1_done_spec (x : Slice cpoly.field.Ext4)
    (acc : cpoly.field.Ext4) (i : Std.Usize) (hi : x.val.length ≤ i.val) :
    cpoly.multilinear.eq_tilde_loop1 x acc i ⦃ z => z = acc ⦄ := by
  rw [cpoly.multilinear.eq_tilde_loop1]
  apply loop.spec_decr_nat (fun _ => 0)
    (fun s => s.1 = acc ∧ x.val.length ≤ s.2.val)
  · rintro ⟨a, k⟩ ⟨ha, hk⟩
    simp only [cpoly.multilinear.eq_tilde_loop1.body]
    have hlt : ¬ k < Slice.len x := by scalar_tac
    rw [if_neg hlt]
    simp only [spec_ok]
    exact ha
  · exact ⟨rfl, hi⟩

/-- `cpoly::multilinear::eq_tilde` ↔ `CMlPolynomialEval.eqTilde`. -/
theorem eq_tilde_spec (n : ℕ) (w x : Slice cpoly.field.Ext4)
    (hw : VecReduced w) (hx : VecReduced x)
    (hwl : w.val.length = n) (hxl : x.val.length = n) :
    cpoly.multilinear.eq_tilde w x ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.eqTilde (toPoint n w) (toPoint n x) ⦄ := by
  rw [cpoly.multilinear.eq_tilde]
  apply spec_bind (eq_tilde_loop0_spec w x (Slice.len w) hw hx (by simp)
    (by simpa [hwl] using hxl) cpoly.field.Ext4.ONE 0#usize (by simp) reduced_ONE (by simp [eqProd]))
  rintro ⟨acc, i⟩ ⟨hacc, hi, hval⟩
  have hilen : i.val = w.val.length := by simpa using hi
  have hxwlen : x.val.length = w.val.length := hxl.trans hwl.symm
  apply spec_mono (eq_tilde_loop1_done_spec x acc i
    (le_of_eq (hxwlen.trans hilen.symm)))
  intro z hz
  rw [hz]
  refine ⟨hacc, ?_⟩
  rw [hval, eqTilde_eq_eqProd]
  simp [hwl]

/-! ## `eval_horner` -/

theorem eval_horner_layer_loop_spec (c : Slice cpoly.field.Ext4) (x0 : cpoly.field.Ext4)
    (half : Std.Usize) (hc : VecReduced c) (hx : Reduced x0)
    (hhalf : 2 * half.val ≤ c.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ half.val → VecReduced out →
      out.val.map toExt = (List.range j.val).map
        (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) →
      cpoly.multilinear.eval_horner_layer_loop c x0 half out j ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range half.val).map
          (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) ⦄ := by
  intro out j hj hout hrel
  rw [cpoly.multilinear.eval_horner_layer_loop]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)))
  · rintro ⟨out1, j1⟩ ⟨hj1, hout1, hrel1⟩
    simp only [cpoly.multilinear.eval_horner_layer_loop.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hlo : 2 * j1.val < c.val.length := by scalar_tac
      have hhi : 2 * j1.val + 1 < c.val.length := by scalar_tac
      have houtlen : out1.val.length = j1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨i, hi⟩
      step as ⟨lo, hloeq⟩
      step as ⟨i1, hi1⟩
      step as ⟨hiw, hhiweq⟩
      have hlo' : i.val < c.val.length := by scalar_tac
      have hhi' : i1.val < c.val.length := by scalar_tac
      have hloR : Reduced lo := hloeq ▸ hc _ (List.getElem_mem hlo')
      have hhiR : Reduced hiw := hhiweq ▸ hc _ (List.getElem_mem hhi')
      step as ⟨t, htR, htF⟩
      step as ⟨v, hvR, hvF⟩
      step as ⟨out2, hout2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hout2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hout1 u h
        · rw [List.mem_singleton.mp h]; exact hvR
      · rw [hout2, hj2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hvF, htF]
        simp [coeffFn, hlo, hhi, hi, hi1, hloeq, hhiweq]
      · have : j1.val < half.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : j1.val = half.val := by scalar_tac
      exact ⟨hout1, by simpa [heq] using hrel1⟩
  · exact ⟨hj, hout, hrel⟩

/-- One extracted Horner layer halves the table and folds in `x0`. -/
theorem eval_horner_layer_spec (n : ℕ) (c : Slice cpoly.field.Ext4)
    (x0 : cpoly.field.Ext4)
    (hc : VecReduced c) (hx : Reduced x0) (hcl : c.val.length = 2 ^ (n + 1)) :
    cpoly.multilinear.eval_horner_layer c x0 ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      ∀ k, coeffFn z k
        = if k < 2 ^ n then coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1) else 0 ⦄ := by
  rw [cpoly.multilinear.eval_horner_layer]
  step as ⟨half, hhalf⟩
  have hclen : c.len.val = 2 ^ (n + 1) := by simpa using hcl
  have hhalfval : half.val = 2 ^ n := by
    calc
      half.val = c.len.val / 2 := hhalf
      _ = 2 ^ (n + 1) / 2 := by rw [hclen]
      _ = 2 ^ n := by rw [pow_succ]; omega
  apply spec_mono (eval_horner_layer_loop_spec c x0 half hc hx
    (by rw [hhalfval, hcl, pow_succ]; omega)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hhalfval] using h
  refine ⟨hz, hlen, ?_⟩
  intro k
  by_cases hk : k < 2 ^ n
  · rw [if_pos hk, coeffFn_of_lt z (by omega)]
    have hm := getElem_of_list_eq hmap (i := k) (hi := by simpa [hlen] using hk)
    simp only [List.getElem_map, List.getElem_range] at hm
    exact hm
  · rw [if_neg hk, coeffFn_of_ge z (by omega)]

theorem eval_horner_loop1_spec (n : ℕ) (w : Slice cpoly.field.Ext4) (nn : Std.Usize)
    (t : F) (hw : VecReduced w) (hwl : w.val.length = n) (hnn : nn.val = n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ (n - j.val) →
      mlVal (n - j.val) (coeffFn cur) (pointFn w j.val) = t →
      cpoly.multilinear.MultilinearPoly.eval_horner_loop w nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 1 ∧ coeffFn z 0 = t ⦄ := by
  intro cur j hj hcur hcurlen hval
  rw [cpoly.multilinear.MultilinearPoly.eval_horner_loop]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧
      s.1.val.length = 2 ^ (n - s.2.val) ∧
      mlVal (n - s.2.val) (coeffFn s.1) (pointFn w s.2.val) = t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.multilinear.MultilinearPoly.eval_horner_loop.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjn : j1.val < n := by scalar_tac
      have hjw : j1.val < w.val.length := by omega
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ hw _ (List.getElem_mem hjw)
      have hpow : cur1.val.length = 2 ^ ((n - (j1.val + 1)) + 1) := by
        rw [hlen1]
        congr 2
        omega
      apply spec_bind (eval_horner_layer_spec (n - (j1.val + 1)) cur1 x hcur1 hxR hpow)
      rintro cur2 ⟨hcur2, hlen2, hfn2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hcur2, ?_, ?_, ?_⟩
      · simpa [hj2] using hlen2
      · rw [show n - j2.val = n - (j1.val + 1) by omega]
        have hpoint : pointFn w j2.val = fun k => pointFn w j1.val (k + 1) := by
          funext k
          unfold pointFn
          rw [hj2]
          have harith : j1.val + 1 + k = j1.val + (k + 1) := by omega
          rw [harith]
        rw [hpoint]
        calc
          mlVal (n - (j1.val + 1)) (coeffFn cur2) (fun k => pointFn w j1.val (k + 1)) =
              mlVal (n - (j1.val + 1))
                (fun k => coeffFn cur1 (2 * k) + pointFn w j1.val 0 * coeffFn cur1 (2 * k + 1))
                (fun k => pointFn w j1.val (k + 1)) := by
                  unfold mlVal
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hfn2, if_pos (Finset.mem_range.mp hk)]
                  have hxpoint : toExt x = pointFn w j1.val 0 := by
                    simp [pointFn, hx, hjw]
                  rw [hxpoint]
          _ = mlVal ((n - (j1.val + 1)) + 1) (coeffFn cur1) (pointFn w j1.val) :=
                mlVal_layer _ _ _
          _ = t := by
                rw [show (n - (j1.val + 1)) + 1 = n - j1.val by omega]
                exact hval1
      · omega
    · rw [if_neg hlt]
      have heq : j1.val = n := by scalar_tac
      refine ⟨hcur1, ?_, ?_⟩
      · simpa [heq] using hlen1
      · simpa [heq] using hval1
  · exact ⟨hj, hcur, hcurlen, hval⟩

/-- `cpoly::multilinear::MultilinearPoly::eval_horner` ↔ `CMlPolynomial.evalHorner`.

The extracted code is the `O(2^n)` layered algorithm; the reference
`CMlPolynomial.evalHorner` is CompPoly's structurally-recursive version of the
same, and `CompPoly.CMlPolynomial.eval_horner_eq_eval` identifies both with the
`O(n · 2^n)` dot-product semantics. -/
theorem eval_horner_spec (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.multilinear.MultilinearPoly.eval_horner p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomial.evalHorner (toMl n p) (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.eval_horner]
  have hlen : w.len.val = n := by simpa using hwl
  -- `self.0.clone()` seeds the layers.
  apply spec_bind (vec_clone_spec p)
  intro cur hcur
  rw [hcur]
  apply spec_bind (eval_horner_loop1_spec n w w.len
    (mlVal n (coeffFn p) (pointFn w 0)) hw hwl hlen p 0#usize
    (by simp) hp (by simpa using hpl) (by simp))
  intro z hz
  step as ⟨e, he⟩
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hz.1 _ (List.getElem_mem (by omega))
  · rw [he, ← coeffFn_of_lt z (by omega), hz.2.2, mlVal_eq_eval,
      CMlPolynomial.eval_horner_eq_eval]

/-! ## `eval_mle` -/

theorem eval_mle_layer_loop_spec (c : Slice cpoly.field.Ext4)
    (x0 : cpoly.field.Ext4)
    (half : Std.Usize) (hc : VecReduced c) (hx : Reduced x0)
    (hhalf : 2 * half.val ≤ c.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ half.val → VecReduced out →
      out.val.map toExt = (List.range j.val).map
        (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) →
      cpoly.multilinear.eval_mle_layer_loop c x0 half out j ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range half.val).map
          (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) ⦄ := by
  intro out j hj hout hrel
  rw [cpoly.multilinear.eval_mle_layer_loop]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)))
  · rintro ⟨out1, j1⟩ ⟨hj1, hout1, hrel1⟩
    simp only [cpoly.multilinear.eval_mle_layer_loop.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hlo : 2 * j1.val < c.val.length := by scalar_tac
      have hhi : 2 * j1.val + 1 < c.val.length := by scalar_tac
      have houtlen : out1.val.length = j1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨i, hi⟩
      step as ⟨lo, hloeq⟩
      step as ⟨i1, hi1⟩
      step as ⟨hiw, hhiweq⟩
      have hlo' : i.val < c.val.length := by scalar_tac
      have hhi' : i1.val < c.val.length := by scalar_tac
      have hloR : Reduced lo := hloeq ▸ hc _ (List.getElem_mem hlo')
      have hhiR : Reduced hiw := hhiweq ▸ hc _ (List.getElem_mem hhi')
      step as ⟨d, hdR, hdF⟩
      step as ⟨m, hmR, hmF⟩
      step as ⟨v, hvR, hvF⟩
      step as ⟨out2, hout2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hout2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hout1 u h
        · rw [List.mem_singleton.mp h]; exact hvR
      · rw [hout2, hj2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hvF, hmF, hdF]
        simp [coeffFn, hlo, hhi, hi, hi1, hloeq, hhiweq]
        ring
      · have : j1.val < half.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : j1.val = half.val := by scalar_tac
      exact ⟨hout1, by simpa [heq] using hrel1⟩
  · exact ⟨hj, hout, hrel⟩

/-- One extracted multilinear-extension layer halves the table and folds in `x0`. -/
theorem eval_mle_layer_spec (n : ℕ) (c : Slice cpoly.field.Ext4) (x0 : cpoly.field.Ext4)
    (hc : VecReduced c) (hx : Reduced x0) (hcl : c.val.length = 2 ^ (n + 1)) :
    cpoly.multilinear.eval_mle_layer c x0 ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      ∀ k, coeffFn z k
        = if k < 2 ^ n
            then (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)
            else 0 ⦄ := by
  rw [cpoly.multilinear.eval_mle_layer]
  step as ⟨half, hhalf⟩
  have hclen : c.len.val = 2 ^ (n + 1) := by simpa using hcl
  have hhalfval : half.val = 2 ^ n := by
    calc
      half.val = c.len.val / 2 := hhalf
      _ = 2 ^ (n + 1) / 2 := by rw [hclen]
      _ = 2 ^ n := by rw [pow_succ]; omega
  apply spec_mono (eval_mle_layer_loop_spec c x0 half hc hx
    (by rw [hhalfval, hcl, pow_succ]; omega)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hhalfval] using h
  refine ⟨hz, hlen, ?_⟩
  intro k
  by_cases hk : k < 2 ^ n
  · rw [if_pos hk, coeffFn_of_lt z (by omega)]
    have hm := getElem_of_list_eq hmap (i := k) (hi := by simpa [hlen] using hk)
    simp only [List.getElem_map, List.getElem_range] at hm
    exact hm
  · rw [if_neg hk, coeffFn_of_ge z (by omega)]

/- The storage-aware MLE path overwrites the low half of its owned table before
   shrinking it.  The inner invariant records both the completed prefix and the
   still-live source suffix, so reading `2*i` and `2*i+1` can never observe an
   earlier write. -/
theorem eval_mle_in_place_loop_spec (w : Slice cpoly.field.Ext4) (j half : Std.Usize)
    (c : alloc.vec.Vec cpoly.field.Ext4) (hw : VecReduced w) (hc : VecReduced c)
    (hjw : j.val < w.val.length) (hhalf : 2 * half.val ≤ c.val.length) :
    cpoly.multilinear.MultilinearEvals.eval_mle_loop0_loop0 w c j half 0#usize
      ⦃ z => VecReduced z ∧ z.val.length = c.val.length ∧ ∀ k, coeffFn z k =
        if k < half.val then
          coeffFn c (2 * k) + pointFn w j.val 0 *
            (coeffFn c (2 * k + 1) - coeffFn c (2 * k))
        else coeffFn c k ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.eval_mle_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.1.val.length = c.val.length ∧ s.2.val ≤ half.val ∧
      ∀ k, coeffFn s.1 k = if k < s.2.val then
        coeffFn c (2 * k) + pointFn w j.val 0 *
          (coeffFn c (2 * k + 1) - coeffFn c (2 * k))
        else coeffFn c k)
  · rintro ⟨cur, i⟩ ⟨hcur, hlen, hi, hfn⟩
    simp only [Prod.fst, Prod.snd] at hcur hlen hi hfn
    simp only [cpoly.multilinear.MultilinearEvals.eval_mle_loop0_loop0.body]
    by_cases hlt : i < half
    · rw [if_pos hlt]
      step as ⟨i1, hi1⟩
      have hi1val : i1.val = 2 * i.val := by scalar_tac
      have hlow : i1.val < cur.val.length := by scalar_tac
      step as ⟨lo, hlo⟩
      step as ⟨i2, hi2⟩
      have hi2val : i2.val = 2 * i.val + 1 := by scalar_tac
      have hhigh : i2.val < cur.val.length := by scalar_tac
      step as ⟨hiw, hhiw⟩
      step as ⟨x, hx⟩
      have hxR : Reduced x := hx ▸ hw _ (List.getElem_mem hjw)
      have hloR : Reduced lo := hlo ▸ hcur _ (List.getElem_mem hlow)
      have hhiR : Reduced hiw := hhiw ▸ hcur _ (List.getElem_mem hhigh)
      have hloF : toExt lo = coeffFn c (2 * i.val) := by
        calc
          toExt lo = coeffFn cur i1.val := by rw [coeffFn_of_lt cur hlow, hlo]
          _ = coeffFn c (2 * i.val) := by rw [hfn, if_neg (by omega), hi1val]
      have hhiF : toExt hiw = coeffFn c (2 * i.val + 1) := by
        calc
          toExt hiw = coeffFn cur i2.val := by rw [coeffFn_of_lt cur hhigh, hhiw]
          _ = coeffFn c (2 * i.val + 1) := by rw [hfn, if_neg (by omega), hi2val]
      have hxF : toExt x = pointFn w j.val 0 := by
        calc
          toExt x = toExt w.val[j.val] := by rw [hx]
          _ = pointFn w j.val 0 := (pointFn_of_lt w j.val (k := 0) (by omega)).symm
      step as ⟨d, hdR, hdF⟩
      step as ⟨m, hmR, hmF⟩
      step as ⟨v, hvR, hvF⟩
      step as ⟨_x, back, _hx, hback⟩
      step as ⟨i3, hi3⟩
      subst hback
      have hset : (cur.set i v).val = cur.val.set i.val v := by simp
      have hsetlen : (cur.set i v).val.length = c.val.length := by
        rw [hset, List.length_set, hlen]
      have hcoeff : ∀ k, coeffFn (cur.set i v) k =
          if i.val = k then toExt v else coeffFn cur k := by
        intro k
        by_cases hk : k < cur.val.length
        · rw [coeffFn_of_lt _ (by rw [hsetlen]; omega), coeffFn_of_lt cur hk,
            getElem_of_list_eq hset, List.getElem_set]
          split <;> rfl
        · rw [coeffFn_of_ge _ (by omega), coeffFn_of_ge cur (by omega),
            if_neg (by omega)]
      refine ⟨?_, hsetlen, by scalar_tac, ?_⟩
      · intro u hu
        rw [hset] at hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact hcur u h
        · exact h ▸ hvR
      · refine ⟨?_, by scalar_tac⟩
        intro k
        rw [hcoeff k]
        by_cases hki : i.val = k
        · subst k
          rw [if_pos rfl, if_pos (by scalar_tac), hvF, hmF, hdF, hxF, hloF, hhiF]
        · rw [if_neg hki, hfn k]
          by_cases hki' : k < i.val
          · rw [if_pos hki', if_pos (by scalar_tac)]
          · rw [if_neg hki', if_neg (by omega)]
    · rw [if_neg hlt]
      have heq : i.val = half.val := by scalar_tac
      refine ⟨hcur, hlen, ?_⟩
      intro k
      simpa [heq] using hfn k
  · exact ⟨hc, rfl, by simp, fun k => by simp⟩

theorem eval_mle_loop0_spec (n : ℕ) (w : Slice cpoly.field.Ext4) (nn : Std.Usize)
    (t : F) (hw : VecReduced w) (hwl : w.val.length = n) (hnn : nn.val = n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ (n - j.val) →
      mlValL (n - j.val) (coeffFn cur) (pointFn w j.val) = t →
      cpoly.multilinear.MultilinearEvals.eval_mle_loop0 w nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 1 ∧ coeffFn z 0 = t ⦄ := by
  intro cur j hj hcur hcurlen hval
  rw [cpoly.multilinear.MultilinearEvals.eval_mle_loop0]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧
      s.1.val.length = 2 ^ (n - s.2.val) ∧
      mlValL (n - s.2.val) (coeffFn s.1) (pointFn w s.2.val) = t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [cpoly.multilinear.MultilinearEvals.eval_mle_loop0.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjn : j1.val < n := by scalar_tac
      have hjw : j1.val < w.val.length := by omega
      step as ⟨half, hhalf⟩
      have hhalfval : half.val = 2 ^ (n - (j1.val + 1)) := by
        calc
          half.val = cur1.val.length / 2 := hhalf
          _ = 2 ^ (n - j1.val) / 2 := by rw [hlen1]
          _ = 2 ^ (n - (j1.val + 1)) := by
            rw [show n - j1.val = (n - (j1.val + 1)) + 1 by omega, pow_succ]
            omega
      have hhalf_eq : 2 * half.val = cur1.val.length := by
        calc
          2 * half.val = 2 * 2 ^ (n - (j1.val + 1)) := by rw [hhalfval]
          _ = 2 ^ (n - (j1.val + 1)) * 2 := by ring
          _ = cur1.val.length := by
            rw [hlen1, show n - j1.val = (n - (j1.val + 1)) + 1 by omega, pow_succ]
      have hhalfbound : 2 * half.val ≤ cur1.val.length := le_of_eq hhalf_eq
      apply spec_bind (eval_mle_in_place_loop_spec w j1 half cur1 hw hcur1 hjw hhalfbound)
      rintro cur2 ⟨hcur2, hlen2, hfn2⟩
      have hhalf_le : half.val ≤ cur2.val.length := by
        calc
          half.val = 2 ^ (n - (j1.val + 1)) := hhalfval
          _ ≤ 2 ^ (n - (j1.val + 1)) * 2 := by omega
          _ = cur2.val.length := by
            rw [hlen2, hlen1, show n - j1.val = (n - (j1.val + 1)) + 1 by omega,
              pow_succ]
      apply spec_bind (alloc.vec.Vec.resize_spec cpoly.field.Ext4.Insts.CoreCloneClone cur2 half
        cpoly.field.Ext4.ZERO (ext_clone_eq _))
      intro cur3 hresize
      have htake : cur3.val = cur2.val.take half.val := by
        rw [hresize, List.resize, if_pos (Nat.zero_le _),
          Nat.sub_eq_zero_of_le hhalf_le, List.replicate_zero,
          List.append_nil]
      have hcur3 : VecReduced cur3 := by
        intro u hu
        rw [htake] at hu
        exact hcur2 u (List.mem_of_mem_take hu)
      have hlen3 : cur3.val.length = half.val := by
        rw [htake, List.length_take, Nat.min_eq_left hhalf_le]
      have hmap3 : cur3.val.map toExt = (List.range half.val).map (coeffFn cur2) := by
        rw [hresize, map_resize_eq_range_map]
        rfl
      have hfn3 : ∀ k, k < half.val → coeffFn cur3 k =
          coeffFn cur1 (2 * k) + pointFn w j1.val 0 *
            (coeffFn cur1 (2 * k + 1) - coeffFn cur1 (2 * k)) := by
        intro k hk
        have hk3 : k < cur3.val.length := by rw [hlen3]; exact hk
        have hkmap3 : k < (cur3.val.map toExt).length := by simp [hk3]
        rw [coeffFn_of_lt cur3 hk3]
        have hm := getElem_of_list_eq hmap3 (i := k) (hi := hkmap3)
        simp only [List.getElem_map, List.getElem_range] at hm
        rw [hm, hfn2, if_pos hk]
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hcur3, ?_, ?_, ?_⟩
      · rw [hlen3, hhalfval, hj2]
      · rw [show n - j2.val = n - (j1.val + 1) by omega]
        have hpoint : pointFn w j2.val = fun k => pointFn w j1.val (k + 1) := by
          funext k
          unfold pointFn
          rw [hj2]
          have harith : j1.val + 1 + k = j1.val + (k + 1) := by omega
          rw [harith]
        rw [hpoint]
        calc
          mlValL (n - (j1.val + 1)) (coeffFn cur3) (fun k => pointFn w j1.val (k + 1)) =
              mlValL (n - (j1.val + 1))
                (fun k => coeffFn cur1 (2 * k) + pointFn w j1.val 0 *
                  (coeffFn cur1 (2 * k + 1) - coeffFn cur1 (2 * k)))
                (fun k => pointFn w j1.val (k + 1)) := by
                  unfold mlValL
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hfn3 k (by simpa [hhalfval] using Finset.mem_range.mp hk)]
          _ = mlValL (n - (j1.val + 1))
                (fun k => (1 - pointFn w j1.val 0) * coeffFn cur1 (2 * k) +
                  pointFn w j1.val 0 * coeffFn cur1 (2 * k + 1))
                (fun k => pointFn w j1.val (k + 1)) := by
                  unfold mlValL
                  apply Finset.sum_congr rfl
                  intro k _
                  ring
          _ = mlValL ((n - (j1.val + 1)) + 1) (coeffFn cur1) (pointFn w j1.val) :=
                mlValL_layer _ _ _
          _ = t := by
                rw [show (n - (j1.val + 1)) + 1 = n - j1.val by omega]
                exact hval1
      · omega
    · rw [if_neg hlt]
      have heq : j1.val = n := by scalar_tac
      refine ⟨hcur1, ?_, ?_⟩
      · simpa [heq] using hlen1
      · simpa [heq] using hval1
  · exact ⟨hj, hcur, hcurlen, hval⟩

/-- `cpoly::multilinear::MultilinearEvals::eval_mle` ↔ `CMlPolynomialEval.evalMle`. -/
theorem eval_mle_spec (n : ℕ) (p : alloc.vec.Vec cpoly.field.Ext4) (w : Slice cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.multilinear.MultilinearEvals.eval_mle p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.evalMle (toMlEval n p) (toPoint n w) ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.eval_mle]
  have hlen : w.len.val = n := by simpa using hwl
  -- `self.0.clone()` seeds the layers.
  apply spec_bind (vec_clone_spec p)
  intro cur hcur
  rw [hcur]
  apply spec_bind (eval_mle_loop0_spec n w w.len
    (mlValL n (coeffFn p) (pointFn w 0)) hw hwl hlen p 0#usize
    (by simp) hp (by simpa using hpl) (by simp))
  intro z hz
  step as ⟨e, he⟩
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hz.1 _ (List.getElem_mem (by omega))
  · rw [he, ← coeffFn_of_lt z (by omega), hz.2.2, mlValL_eq_eval,
      CMlPolynomialEval.eval_mle_eq_eval]

/-! ## Zeta and Möbius transforms

`monoToLagrange` / `lagrangeToMono` are a `foldl` / `foldr` of the per-variable
levels over `List.finRange n`.  `zetaUpTo n m` and `mobiusFrom n m` name the
partial folds that the extracted loops actually maintain. -/

/-- The first `m` levels of the zeta transform. -/
def zetaUpTo (n m : ℕ) (v : CMlPolynomial F n) : CMlPolynomial F n :=
  ((List.finRange n).take m).foldl
    (fun acc level => CMlPolynomial.monoToLagrangeLevel level acc) v

/-- The levels `n-1, …, m` of the Möbius transform (the tail of the `foldr`). -/
def mobiusFrom (n m : ℕ) (v : CMlPolynomial F n) : CMlPolynomial F n :=
  ((List.finRange n).drop m).foldr
    (fun level acc => CMlPolynomial.lagrangeToMonoLevel level acc) v

@[simp] theorem zetaUpTo_zero (n : ℕ) (v : CMlPolynomial F n) : zetaUpTo n 0 v = v := by
  simp [zetaUpTo]

theorem zetaUpTo_succ (n m : ℕ) (hm : m < n) (v : CMlPolynomial F n) :
    zetaUpTo n (m + 1) v
      = CMlPolynomial.monoToLagrangeLevel ⟨m, hm⟩ (zetaUpTo n m v) := by
  unfold zetaUpTo
  rw [finRange_take_succ n m hm]
  simp

theorem zetaUpTo_full (n : ℕ) (v : CMlPolynomial F n) :
    zetaUpTo n n v = CMlPolynomial.monoToLagrange n v := by
  unfold zetaUpTo CMlPolynomial.monoToLagrange
  rw [List.take_of_length_le (by simp)]

theorem mobiusFrom_full (n : ℕ) (v : CMlPolynomial F n) : mobiusFrom n n v = v := by
  simp [mobiusFrom]

theorem mobiusFrom_succ (n m : ℕ) (hm : m < n) (v : CMlPolynomial F n) :
    mobiusFrom n m v
      = CMlPolynomial.lagrangeToMonoLevel ⟨m, hm⟩ (mobiusFrom n (m + 1) v) := by
  unfold mobiusFrom
  rw [finRange_drop_succ n m hm]
  simp

theorem mobiusFrom_zero (n : ℕ) (v : CMlPolynomial F n) :
    mobiusFrom n 0 v = CMlPolynomial.lagrangeToMono n v := by
  rfl

/-- Coefficient-wise description of one zeta level. -/
theorem monoToLagrangeLevel_getElem (n : ℕ) (j : Fin n) (v : CMlPolynomial F n)
    (i : ℕ) (hi : i < 2 ^ n) :
    (CMlPolynomial.monoToLagrangeLevel j v)[i]
      = if Nat.testBit i j.val
          then v[i]'hi + v[i - 2 ^ j.val]'(lt_of_le_of_lt (Nat.sub_le i (2 ^ j.val)) hi)
          else v[i]'hi := by
  unfold CMlPolynomial.monoToLagrangeLevel
  simp

/-- Coefficient-wise description of one Möbius level. -/
theorem lagrangeToMonoLevel_getElem (n : ℕ) (j : Fin n) (v : CMlPolynomial F n)
    (i : ℕ) (hi : i < 2 ^ n) :
    (CMlPolynomial.lagrangeToMonoLevel j v)[i]
      = if Nat.testBit i j.val
          then v[i]'hi - v[i - 2 ^ j.val]'(lt_of_le_of_lt (Nat.sub_le i (2 ^ j.val)) hi)
          else v[i]'hi := by
  unfold CMlPolynomial.lagrangeToMonoLevel
  simp

/-! ### `mono_to_lagrange` -/

theorem mono_to_lagrange_level_loop_spec (v : Slice cpoly.field.Ext4)
    (n stride : Std.Usize) (jv : ℕ) (hv : VecReduced v) (hn : n.val = v.val.length)
    (hstride : stride.val = 2 ^ jv) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                  else coeffFn v k) →
      cpoly.multilinear.mono_to_lagrange_level_loop v n stride r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map
          (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                    else coeffFn v k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.multilinear.mono_to_lagrange_level_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                  else coeffFn v k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [Prod.fst, Prod.snd] at hi1 hr1 hrel1
    simp only [cpoly.multilinear.mono_to_lagrange_level_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1
        simpa using h
      have hcap : r1.val.length < Std.Usize.max :=
        lt_of_lt_of_le (hrlen ▸ hiv) v.property
      have hstridepos : 0 < stride.val := by rw [hstride]; positivity
      step as ⟨q, hq⟩
      step as ⟨bit, hbit⟩
      have hbitval : bit.val = i1.val / 2 ^ jv % 2 := by scalar_tac
      have htest : Nat.testBit i1.val jv = decide (i1.val / 2 ^ jv % 2 = 1) :=
        testBit_eq_div_pow_mod _ _
      have hbitiff : bit = 1#usize ↔ Nat.testBit i1.val jv = true := by
        constructor
        · intro hb
          rw [htest, decide_eq_true_eq]
          scalar_tac
        · intro ht
          rw [htest, decide_eq_true_eq] at ht
          apply usize_eq_of_val_eq
          scalar_tac
      by_cases hb : bit = 1#usize
      · rw [if_pos hb]
        step as ⟨a, ha⟩
        have haR : Reduced a := ha ▸ hv _ (List.getElem_mem hiv)
        have hle : stride.val ≤ i1.val := by
          rw [hstride]
          exact le_of_testBit _ _ (hbitiff.mp hb)
        step as ⟨idx, hidx⟩
        have hidv : idx.val < v.val.length := by scalar_tac
        have hsubv : i1.val - 2 ^ jv < v.val.length := by omega
        step as ⟨b, hbval⟩
        have hbR : Reduced b := hbval ▸ hv _ (List.getElem_mem hidv)
        step as ⟨c, hcR, hcF⟩
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hr1 u hu
          · rw [List.mem_singleton.mp hu]; exact hcR
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hcF]
          rw [if_pos (hbitiff.mp hb)]
          simp [coeffFn, ha, hbval, hidx, hstride, hiv, hsubv]
        · have : i1.val < n.val := by scalar_tac
          omega
      · rw [if_neg hb]
        step as ⟨a, ha⟩
        have haR : Reduced a := ha ▸ hv _ (List.getElem_mem hiv)
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hr1 u hu
          · rw [List.mem_singleton.mp hu]; exact haR
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1]
          have ht : Nat.testBit i1.val jv = false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            exact hb (hbitiff.mpr ht)
          simp [ht, coeffFn, ha, hiv]
        · have : i1.val < n.val := by scalar_tac
          omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::multilinear::mono_to_lagrange_level` ↔ `CMlPolynomial.monoToLagrangeLevel`. -/
theorem mono_to_lagrange_level_spec (n : ℕ) (v : Slice cpoly.field.Ext4) (j : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hj : j.val < n) :
    cpoly.multilinear.mono_to_lagrange_level v j ⦃ z => VecReduced z ∧
      z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.monoToLagrangeLevel ⟨j.val, hj⟩ (toMl n v) ⦄ := by
  rw [cpoly.multilinear.mono_to_lagrange_level]
  have hpw : 2 ^ j.val ≤ Std.Usize.max := pow_le_of_lt hj (pow2_le_usize_max hvl)
  apply spec_bind (pow2_spec j hpw)
  intro stride hstride
  apply spec_mono (mono_to_lagrange_level_loop_spec v v.len stride j.val hv (by simp) hstride
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hvl] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [monoToLagrangeLevel_getElem]
  simp only [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa [hlen] using hi)
  simp only [List.getElem_map, List.getElem_range] at hm
  exact hm

/-- The zeta loop, `j` levels in.  `toMl`/`toMlEval` mark which reading each side
has: `t` is the coefficient table going in and `z` the hypercube table coming out.
The loop's own `cur` is `j` levels through and so is neither, which is why the
invariant states it with the unmarked `toMl` against `zetaUpTo`.  (The two readers
are the same function — `toMlEval` is an `abbrev` for `toMl` — so this is a note to
the reader, not something the typechecker enforces.) -/
theorem mono_to_lagrange_loop_spec (n : ℕ) (nn : Std.Usize) (hnn : nn.val = n)
    (t : CMlPolynomial F n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ n →
      toMl n cur = zetaUpTo n j.val t →
      cpoly.multilinear.MultilinearPoly.to_evals_loop nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 2 ^ n ∧ toMlEval n z = CMlPolynomial.monoToLagrange n t ⦄ := by
  intro cur j hj hcur hlen hval
  rw [cpoly.multilinear.MultilinearPoly.to_evals_loop]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧ s.1.val.length = 2 ^ n ∧
      toMl n s.1 = zetaUpTo n s.2.val t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.multilinear.MultilinearPoly.to_evals_loop.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjn : j1.val < n := by scalar_tac
      apply spec_bind (mono_to_lagrange_level_spec n cur1 j1 hcur1 hlen1 hjn)
      rintro cur2 ⟨hcur2, hlen2, hlevel⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hcur2, hlen2, ?_, ?_⟩
      · rw [hj2, zetaUpTo_succ n j1.val hjn, ← hval1]
        exact hlevel
      · omega
    · rw [if_neg hlt]
      have heq : j1.val = n := by scalar_tac
      -- `toMlEval` is an `abbrev` for `toMl`, so the goal has to be shown in the
      -- unmarked form before the invariant rewrites into it
      refine ⟨hcur1, hlen1, ?_⟩
      show toMl n cur1 = CMlPolynomial.monoToLagrange n t
      rw [hval1, heq, zetaUpTo_full]
  · exact ⟨hj, hcur, hlen, hval⟩

/-- `cpoly::multilinear::MultilinearPoly::to_evals` ↔ `CMlPolynomial.monoToLagrange`. -/
theorem mono_to_lagrange_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hnn : nn.val = n) :
    cpoly.multilinear.MultilinearPoly.to_evals v nn ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMlEval n z = CMlPolynomial.monoToLagrange n (toMl n v) ⦄ := by
  rw [cpoly.multilinear.MultilinearPoly.to_evals]
  simp only [bind_ok_id]
  apply mono_to_lagrange_loop_spec n nn hnn (toMl n v) v 0#usize
  · simp
  · exact hv
  · exact hvl
  · simp

/-! ### `lagrange_to_mono` -/

theorem lagrange_to_mono_level_loop_spec (v : Slice cpoly.field.Ext4)
    (n stride : Std.Usize) (jv : ℕ) (hv : VecReduced v) (hn : n.val = v.val.length)
    (hstride : stride.val = 2 ^ jv) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                  else coeffFn v k) →
      cpoly.multilinear.lagrange_to_mono_level_loop v n stride r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map
          (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                    else coeffFn v k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.multilinear.lagrange_to_mono_level_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                  else coeffFn v k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [Prod.fst, Prod.snd] at hi1 hr1 hrel1
    simp only [cpoly.multilinear.lagrange_to_mono_level_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1
        simpa using h
      have hcap : r1.val.length < Std.Usize.max :=
        lt_of_lt_of_le (hrlen ▸ hiv) v.property
      have hstridepos : 0 < stride.val := by rw [hstride]; positivity
      step as ⟨q, hq⟩
      step as ⟨bit, hbit⟩
      have hbitval : bit.val = i1.val / 2 ^ jv % 2 := by scalar_tac
      have htest : Nat.testBit i1.val jv = decide (i1.val / 2 ^ jv % 2 = 1) :=
        testBit_eq_div_pow_mod _ _
      have hbitiff : bit = 1#usize ↔ Nat.testBit i1.val jv = true := by
        constructor
        · intro hb
          rw [htest, decide_eq_true_eq]
          scalar_tac
        · intro ht
          rw [htest, decide_eq_true_eq] at ht
          apply usize_eq_of_val_eq
          scalar_tac
      by_cases hb : bit = 1#usize
      · rw [if_pos hb]
        step as ⟨a, ha⟩
        have haR : Reduced a := ha ▸ hv _ (List.getElem_mem hiv)
        have hle : stride.val ≤ i1.val := by
          rw [hstride]
          exact le_of_testBit _ _ (hbitiff.mp hb)
        step as ⟨idx, hidx⟩
        have hidv : idx.val < v.val.length := by scalar_tac
        have hsubv : i1.val - 2 ^ jv < v.val.length := by omega
        step as ⟨b, hbval⟩
        have hbR : Reduced b := hbval ▸ hv _ (List.getElem_mem hidv)
        step as ⟨c, hcR, hcF⟩
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hr1 u hu
          · rw [List.mem_singleton.mp hu]; exact hcR
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hcF]
          rw [if_pos (hbitiff.mp hb)]
          simp [coeffFn, ha, hbval, hidx, hstride, hiv, hsubv]
        · have : i1.val < n.val := by scalar_tac
          omega
      · rw [if_neg hb]
        step as ⟨a, ha⟩
        have haR : Reduced a := ha ▸ hv _ (List.getElem_mem hiv)
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hr1 u hu
          · rw [List.mem_singleton.mp hu]; exact haR
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1]
          have ht : Nat.testBit i1.val jv = false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            exact hb (hbitiff.mpr ht)
          simp [ht, coeffFn, ha, hiv]
        · have : i1.val < n.val := by scalar_tac
          omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::multilinear::lagrange_to_mono_level` ↔ `CMlPolynomial.lagrangeToMonoLevel`. -/
theorem lagrange_to_mono_level_spec (n : ℕ) (v : Slice cpoly.field.Ext4) (j : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hj : j.val < n) :
    cpoly.multilinear.lagrange_to_mono_level v j ⦃ z => VecReduced z ∧
      z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.lagrangeToMonoLevel ⟨j.val, hj⟩ (toMl n v) ⦄ := by
  rw [cpoly.multilinear.lagrange_to_mono_level]
  have hpw : 2 ^ j.val ≤ Std.Usize.max := pow_le_of_lt hj (pow2_le_usize_max hvl)
  apply spec_bind (pow2_spec j hpw)
  intro stride hstride
  apply spec_mono (lagrange_to_mono_level_loop_spec v v.len stride j.val hv (by simp) hstride
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hvl] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [lagrangeToMonoLevel_getElem]
  simp only [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa [hlen] using hi)
  simp only [List.getElem_map, List.getElem_range] at hm
  exact hm

theorem lagrange_to_mono_loop_spec (n : ℕ) (t : CMlPolynomialEval F n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ n →
      toMl n cur = mobiusFrom n j.val t →
      cpoly.multilinear.MultilinearEvals.to_coeffs_loop cur j ⦃ z => VecReduced z ∧
        z.val.length = 2 ^ n ∧ toMl n z = CMlPolynomial.lagrangeToMono n t ⦄ := by
  intro cur j hj hcur hlen hval
  rw [cpoly.multilinear.MultilinearEvals.to_coeffs_loop]
  apply loop.spec_decr_nat (fun s => s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧ s.1.val.length = 2 ^ n ∧
      toMl n s.1 = mobiusFrom n s.2.val t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.multilinear.MultilinearEvals.to_coeffs_loop.body]
    by_cases hpos : j1 > 0#usize
    · rw [if_pos hpos]
      step as ⟨j2, hj2⟩
      have hj2n : j2.val < n := by scalar_tac
      apply spec_bind (lagrange_to_mono_level_spec n cur1 j2 hcur1 hlen1 hj2n)
      rintro cur2 ⟨hcur2, hlen2, hlevel⟩
      refine ⟨by scalar_tac, hcur2, hlen2, ?_, ?_⟩
      · rw [mobiusFrom_succ n j2.val hj2n]
        have hs : j2.val + 1 = j1.val := by scalar_tac
        rw [hs, ← hval1]
        exact hlevel
      · scalar_tac
    · rw [if_neg hpos]
      have heq : j1.val = 0 := by scalar_tac
      exact ⟨hcur1, hlen1, by rw [hval1, heq, mobiusFrom_zero]⟩
  · exact ⟨hj, hcur, hlen, hval⟩

/-- `cpoly::multilinear::MultilinearEvals::to_coeffs` ↔ `CMlPolynomial.lagrangeToMono`. -/
theorem lagrange_to_mono_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hnn : nn.val = n) :
    cpoly.multilinear.MultilinearEvals.to_coeffs v nn ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.lagrangeToMono n (toMlEval n v) ⦄ := by
  rw [cpoly.multilinear.MultilinearEvals.to_coeffs]
  simp only [bind_ok_id]
  apply lagrange_to_mono_loop_spec n (toMlEval n v) v nn
  · simp [hnn]
  · exact hv
  · exact hvl
  · rw [hnn, mobiusFrom_full]

end CPolyEquiv.Ml
