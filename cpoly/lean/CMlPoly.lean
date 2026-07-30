/-
Equivalence between the Aeneas-extracted Rust model (`cpoly.cmlpoly.*`, see
`Generated.lean`) and CompPoly's reference **multilinear**
polynomials (`CompPoly.CMlPolynomial` / `CompPoly.CMlPolynomialEval`, see
CompPoly/Multilinear/Basic.lean).

This is the multilinear counterpart of `CPoly.lean`, and it reuses
`Field.lean` verbatim: a generated `cpoly.field.Ext4` struct denotes
the element `toExt a` of `F = Hachi.Ext4`, the quartic extension
`F_P[Y]/(Y^4 - 2)` of the Hachi prime field `P = 2^32 - 99`, and the four
extension operations `eadd`/`esub`/`eneg`/`emul` are already known to be total
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

3. **Aeneas layer** (everything named `*_spec`).  Each generated `cpoly.cmlpoly`
   function is shown to succeed, to preserve `VecReduced` and the length
   `2 ^ n`, and to compute the corresponding CompPoly operation.  Loop bodies
   are handled with `Aeneas.Std.loop.spec_decr_nat` exactly as in
   `CPoly.lean`; the top-level specs are composed with `spec_bind`/`spec_mono`.

## Size side conditions

`cpoly::cmlpoly::pow2` builds `2 ^ n` by repeated *checked* doubling, so it fails
once `2 ^ n` exceeds `Usize.max`.  Specs whose inputs already include a vector
of length `2 ^ n` get `2 ^ n ≤ Usize.max` for free from the `alloc.vec.Vec`
invariant (`Vec α = { l : List α // l.length ≤ Usize.max }`); the others
(`zero`, `of_array`, the two bases, `eq_tilde`) take it as a hypothesis, which
is exactly the weakest condition making the triple true.
-/
import Field
import CPoly
import CompPoly.Multilinear.Basic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly

namespace CPolyEquiv.Ml

/-! ## Word-level helpers

The `0`/`1` of the coefficient field are the extracted constants `cpoly.field.EZERO`
and `cpoly.field.EONE`; `Field.lean` supplies `toExt_EZERO`/`toExt_EONE` and
`reduced_EZERO`/`reduced_EONE` for them, and tags every extension operation
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
def pointFn (v : alloc.vec.Vec cpoly.field.Ext4) (o : ℕ) : ℕ → F :=
  fun k => (v.val.map toExt).getD (o + k) 0

theorem coeffFn_of_lt (v : alloc.vec.Vec cpoly.field.Ext4) {i : ℕ} (hi : i < v.val.length) :
    coeffFn v i = toExt v.val[i] := by
  unfold coeffFn
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem coeffFn_of_ge (v : alloc.vec.Vec cpoly.field.Ext4) {i : ℕ} (hi : v.val.length ≤ i) :
    coeffFn v i = 0 := by
  unfold coeffFn
  rw [List.getD_eq_default]; simpa using hi

theorem pointFn_of_lt (v : alloc.vec.Vec cpoly.field.Ext4) (o : ℕ) {k : ℕ}
    (hk : o + k < v.val.length) : pointFn v o k = toExt v.val[o + k] := by
  unfold pointFn
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem pointFn_succ (v : alloc.vec.Vec cpoly.field.Ext4) (o k : ℕ) :
    pointFn v o (k + 1) = pointFn v (o + 1) k := by
  unfold pointFn; rw [show o + (k + 1) = o + 1 + k by omega]

/-- The multilinear table (in either basis) represented by a `Vec Ext4`. -/
def toMl (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) : CMlPolynomial F n :=
  Vector.ofFn (fun i : Fin (2 ^ n) => coeffFn v i.val)

/-- The same words read as a Boolean-hypercube value table. -/
abbrev toMlEval (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) : CMlPolynomialEval F n := toMl n v

/-- The point of `F^n` stored in `v` starting at offset `o`. -/
def toPointFrom (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (o : ℕ) : Vector F n :=
  Vector.ofFn (fun k : Fin n => pointFn v o k.val)

/-- The point of `F^n` stored in `v`. -/
abbrev toPoint (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) : Vector F n := toPointFrom n v 0

@[simp] theorem toMl_getElem (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (i : ℕ)
    (hi : i < 2 ^ n) :
    (toMl n v)[i] = coeffFn v i := by
  simp [toMl]

@[simp] theorem toPointFrom_getElem (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (o k : ℕ)
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
the mathematical heart of `cpoly::cmlpoly::eval_horner`. -/
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
`cpoly::cmlpoly::eval_mle`. -/
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
theorem monomialBasis_getElem' (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4) (o i : ℕ)
    (hi : i < 2 ^ n) :
    (CMlPolynomial.monomialBasis (toPointFrom n w o))[i] = monoProd n i (pointFn w o) := by
  simp [CMlPolynomial.monomialBasis, monoProd, toPointFrom]
  exact Fin.prod_univ_eq_prod_range
    (f := fun k => if Nat.testBit i k then pointFn w o k else 1) n

/-- The Lagrange basis at a `Vec`-represented point, coefficient-wise. -/
theorem lagrangeBasis_getElem' (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4) (o i : ℕ)
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
theorem mlVal_eq_eval (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4) (o : ℕ) :
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
theorem mlValL_eq_eval (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4) (o : ℕ) :
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

/-! ## `pow2` -/

theorem pow2_loop_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    ∀ (m k : Std.Usize), k.val ≤ n.val → m.val = 2 ^ k.val →
      cpoly.cmlpoly.pow2_loop n m k ⦃ z => z.val = 2 ^ n.val ⦄ := by
  intro m k hk hm
  rw [cpoly.cmlpoly.pow2_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = 2 ^ s.2.val)
  · rintro ⟨m1, k1⟩ ⟨hk1, hm1⟩
    simp only [cpoly.cmlpoly.pow2_loop.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      have hklt : k1.val < n.val := by scalar_tac
      have hpow : 2 ^ (k1.val + 1) ≤ 2 ^ n.val :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hb : m1.val * 2 ≤ Std.Usize.max := by
        rw [hm1, ← pow_succ]
        exact le_trans hpow hn
      step as ⟨m2, hm2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hm2, hk2, hm1]
        simp [pow_succ]
      · omega
    · rw [if_neg hlt]
      have heq : k1.val = n.val := by scalar_tac
      simp only [spec_ok]
      rw [hm1, heq]
  · exact ⟨hk, hm⟩

/-- `cpoly::cmlpoly::pow2` computes `2 ^ n`, provided that fits in a `usize`. -/
theorem pow2_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.cmlpoly.pow2 n ⦃ z => z.val = 2 ^ n.val ⦄ := by
  rw [cpoly.cmlpoly.pow2]
  exact pow2_loop_spec n hn 1#usize 0#usize (by simp) (by simp)

/-! ## `zero` -/

theorem zero_loop_spec (sz : Std.Usize) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ sz.val →
      r.val = List.replicate i.val cpoly.field.EZERO →
      cpoly.cmlpoly.zero_loop sz r i
        ⦃ z => z.val = List.replicate sz.val cpoly.field.EZERO ⦄ := by
  intro r i hi hr
  rw [cpoly.cmlpoly.zero_loop]
  apply loop.spec_decr_nat (fun s => sz.val - s.2.val)
    (fun s => s.2.val ≤ sz.val ∧ s.1.val = List.replicate s.2.val cpoly.field.EZERO)
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1⟩
    simp only [cpoly.cmlpoly.zero_loop.body]
    by_cases hlt : i1 < sz
    · rw [if_pos hlt]
      have hlen : r1.val.length < Std.Usize.max := by
        rw [hr1, List.length_replicate]
        scalar_tac
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hr2, hi2, hr1, ← List.replicate_succ']
      · have : i1.val < sz.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      simp only [spec_ok]
      have : i1.val = sz.val := by scalar_tac
      rw [hr1, this]
  · exact ⟨hi, hr⟩

/-- `cpoly::cmlpoly::zero` ↔ `CMlPolynomial.zero`. -/
theorem zero_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.cmlpoly.zero n ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n.val ∧
      toMl n.val z = (CMlPolynomial.zero : CMlPolynomial F n.val) ⦄ := by
  rw [cpoly.cmlpoly.zero]
  apply spec_bind (pow2_spec n hn)
  intro sz hsz
  apply spec_mono (zero_loop_spec sz (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize
    (by simp) (by simp))
  intro z hz
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [hz] at hu
    have : u = cpoly.field.EZERO := List.eq_of_mem_replicate hu
    rw [this]
    exact reduced_EZERO
  · simp [hz, hsz]
  · apply Vector.ext
    intro i hi
    simp [toMl, coeffFn, hz, CMlPolynomial.zero]

/-! ## `of_array` -/

theorem of_array_loop_spec (coeffs : alloc.vec.Vec cpoly.field.Ext4) (sz m : Std.Usize)
    (hc : VecReduced coeffs) (hm : m.val = coeffs.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ sz.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map (coeffFn coeffs) →
      cpoly.cmlpoly.of_array_loop coeffs sz m r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range sz.val).map (coeffFn coeffs) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.cmlpoly.of_array_loop]
  apply loop.spec_decr_nat (fun s => sz.val - s.2.val)
    (fun s => s.2.val ≤ sz.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map (coeffFn coeffs))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.cmlpoly.of_array_loop.body]
    by_cases hlt : i1 < sz
    · rw [if_pos hlt]
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      by_cases him : i1 < m
      · rw [if_pos him]
        have hic : i1.val < coeffs.val.length := by scalar_tac
        step as ⟨e, he⟩
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hr1 u h
          · rw [List.mem_singleton.mp h, he]
            exact hc _ (List.getElem_mem hic)
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1, he]
          simp [coeffFn, hic]
        · have : i1.val < sz.val := by scalar_tac
          omega
      · rw [if_neg him]
        step as ⟨r2, hr2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_⟩
        · intro u hu; rw [hr2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hr1 u h
          · rw [List.mem_singleton.mp h]
            exact reduced_EZERO
        · rw [hr2, hi2, List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, hrel1]
          have hic : coeffs.val.length ≤ i1.val := by scalar_tac
          simp [coeffFn, hic]
        · have : i1.val < sz.val := by scalar_tac
          omega
    · rw [if_neg hlt]
      have heq : i1.val = sz.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::cmlpoly::of_array` ↔ `CMlPolynomial.ofArray`. -/
theorem of_array_spec (coeffs : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (hc : VecReduced coeffs) (hn : 2 ^ n.val ≤ Std.Usize.max) :
    cpoly.cmlpoly.of_array coeffs n ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n.val ∧
      toMl n.val z
        = CMlPolynomial.ofArray (coeffs.val.map toExt).toArray n.val ⦄ := by
  rw [cpoly.cmlpoly.of_array]
  apply spec_bind (pow2_spec n hn)
  intro sz hsz
  apply spec_mono (of_array_loop_spec coeffs sz (alloc.vec.Vec.len coeffs) hc (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n.val := by
    have h := congrArg List.length hmap
    simpa [hsz] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  unfold CMlPolynomial.ofArray
  simp only [Vector.getElem_ofFn, List.size_toArray, List.getElem_toArray]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm]
  by_cases hic : i < coeffs.val.length
  · have him : i < (coeffs.val.map toExt).length := by simpa using hic
    simp [him, coeffFn_of_lt, hic]
  · have hge : coeffs.val.length ≤ i := by omega
    have hnim : ¬ i < (coeffs.val.map toExt).length := by simpa using hic
    rw [dif_neg hnim, coeffFn_of_ge coeffs hge]

/-! ## `add` -/

theorem add_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hn : n.val = p.val.length) (hlen : p.val.length ≤ q.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt
        = (List.range i.val).map (fun k => coeffFn p k + coeffFn q k) →
      cpoly.cmlpoly.add_loop p q n r i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range n.val).map (fun k => coeffFn p k + coeffFn q k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.cmlpoly.add_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt =
        (List.range s.2.val).map (fun k => coeffFn p k + coeffFn q k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [cpoly.cmlpoly.add_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < p.val.length := by scalar_tac
      have hiq : i1.val < q.val.length := by scalar_tac
      have hrlen : r1.val.length = i1.val := by
        have h := congrArg List.length hrel1; simpa using h
      step as ⟨a, ha⟩
      step as ⟨b, hb⟩
      have haR : Reduced a := ha ▸ hp _ (List.getElem_mem hip)
      have hbR : Reduced b := hb ▸ hq _ (List.getElem_mem hiq)
      step as ⟨s, hsR, hsF⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hr2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact hsR
      · rw [hr2, hi2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hsF]
        simp [coeffFn, hip, hiq, ha, hb]
      · have : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hr1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hr, hrel⟩

/-- `cpoly::cmlpoly::add` ↔ `CMlPolynomial.add` (equivalently
`CMlPolynomialEval.add`; both are `Vector.zipWith (· + ·)`). -/
theorem add_spec (n : ℕ) (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hvl : v.val.length = 2 ^ n) (hwl : w.val.length = 2 ^ n) :
    cpoly.cmlpoly.add v w ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.add (toMl n v) (toMl n w) ⦄ := by
  rw [cpoly.cmlpoly.add]
  apply spec_mono (add_loop_spec v w (alloc.vec.Vec.len v) hv hw (by simp)
    (by omega) (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp)
    (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hvl] using h
  refine ⟨hz, hlen, ?_⟩
  apply Vector.ext
  intro i hi
  rw [toMl_getElem]
  have hiz : i < z.val.length := by omega
  rw [coeffFn_of_lt z hiz]
  have hm := getElem_of_list_eq hmap (i := i) (hi := by simpa using hiz)
  simp only [List.getElem_map, List.getElem_range] at hm
  rw [hm]
  unfold CMlPolynomial.add
  simp [toMl]

/-! ## Negation and scalar multiplication

Coefficient-wise negation and scaling do not depend on how the index is read,
so the multilinear layer reuses the univariate `cpoly::cpoly::neg` / `cpoly::cpoly::smul`
unchanged; only the *statement* changes basis. -/

/-- `cpoly::cpoly::neg` ↔ `CMlPolynomial.neg`. -/
theorem neg_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v)
    (hvl : v.val.length = 2 ^ n) :
    cpoly.cpoly.neg v ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.neg (toMl n v) ⦄ := by
  apply spec_mono (CPolyEquiv.neg_spec v hv)
  rintro z ⟨hz, heq⟩
  have hs : z.val.length = v.val.length := by
    have h := congrArg Array.size heq
    simpa [CPolyEquiv.toRaw, CPolynomial.Raw.neg] using h
  refine ⟨hz, hs.trans hvl, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [toMl, Vector.getElem_ofFn, CMlPolynomial.neg, Vector.getElem_map]
  unfold coeffFn
  rw [← CPolyEquiv.toRaw_coeff, ← CPolyEquiv.toRaw_coeff,
    show toRaw z = CPolynomial.Raw.neg (toRaw v) from heq,
    CPolynomial.Raw.neg_coeff]

/-- `cpoly::cpoly::smul` ↔ `CMlPolynomial.smul`. -/
theorem smul_spec (n : ℕ) (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) :
    cpoly.cpoly.smul r v ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.smul (toExt r) (toMl n v) ⦄ := by
  apply spec_mono (CPolyEquiv.smul_spec r v hr hv)
  rintro z ⟨hz, heq⟩
  have hs : z.val.length = v.val.length := by
    have h := congrArg Array.size heq
    simpa [CPolyEquiv.toRaw, CPolynomial.Raw.smul] using h
  refine ⟨hz, hs.trans hvl, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [toMl, Vector.getElem_ofFn, CMlPolynomial.smul, Vector.getElem_map]
  unfold coeffFn
  rw [← CPolyEquiv.toRaw_coeff, ← CPolyEquiv.toRaw_coeff, heq,
    CPolynomial.Raw.smul_coeff]

/-! ## `monomial_basis` -/

theorem monomial_basis_inner_spec (w : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize) (idx : ℕ)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) :
    ∀ (acc : cpoly.field.Ext4) (m j : Std.Usize),
      j.val ≤ nn.val → Reduced acc → m.val = idx / 2 ^ j.val →
      toExt acc = monoProd j.val idx (pointFn w 0) →
      cpoly.cmlpoly.monomial_basis_loop0_loop0 w nn acc m j ⦃ z => Reduced z ∧
        toExt z = monoProd nn.val idx (pointFn w 0) ⦄ := by
  intro acc m j hj hacc hm hval
  rw [cpoly.cmlpoly.monomial_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.2.val)
    (fun s => s.2.2.val ≤ nn.val ∧ Reduced s.1 ∧ s.2.1.val = idx / 2 ^ s.2.2.val ∧
      toExt s.1 = monoProd s.2.2.val idx (pointFn w 0))
  · rintro ⟨a, q, k⟩ ⟨hk, ha, hq, hv⟩
    simp only [Prod.fst, Prod.snd] at hk ha hq hv
    simp only [cpoly.cmlpoly.monomial_basis_loop0_loop0.body]
    by_cases hlt : k < nn
    · rw [if_pos hlt]
      step as ⟨bit, hbit⟩
      have hbitiff : bit = 1#usize ↔ Nat.testBit idx k.val = true := by
        constructor
        · intro hb
          rw [testBit_eq_div_pow_mod, decide_eq_true_eq]
          scalar_tac
        · intro ht
          apply usize_eq_of_val_eq
          rw [testBit_eq_div_pow_mod, decide_eq_true_eq] at ht
          scalar_tac
      by_cases hb : bit = 1#usize
      · rw [if_pos hb]
        have hkw : k.val < w.val.length := by scalar_tac
        step as ⟨x, hxw⟩
        have hxR : Reduced x := hxw ▸ hw _ (List.getElem_mem hkw)
        step as ⟨a2, ha2R, ha2F⟩
        step as ⟨q2, hq2⟩
        step as ⟨k2, hk2⟩
        refine ⟨by scalar_tac, ha2R, ?_, ?_, ?_⟩
        · rw [hq2, hq, Nat.div_div_eq_div_mul]
          congr 2
          scalar_tac
        · apply Eq.trans (b := monoProd (k.val + 1) idx (pointFn w 0))
          · unfold monoProd at hv ⊢
            calc
              toExt a2 = toExt a * toExt x := ha2F
              _ = (∏ l ∈ Finset.range k.val,
                    if Nat.testBit idx l then pointFn w 0 l else 1) * toExt x := by rw [hv]
              _ = ∏ l ∈ Finset.range (k.val + 1),
                    (if Nat.testBit idx l then pointFn w 0 l else 1) := by
                    rw [Finset.prod_range_succ]
                    have ht := hbitiff.mp hb
                    rw [if_pos ht]
                    simp [hxw, pointFn_of_lt w 0 (by simpa using hkw)]
          · congr 2
            exact hk2.symm
        · have : k.val < nn.val := by scalar_tac
          omega
      · rw [if_neg hb]
        step as ⟨q2, hq2⟩
        step as ⟨k2, hk2⟩
        refine ⟨by scalar_tac, ha, ?_, ?_, ?_⟩
        · rw [hq2, hq, Nat.div_div_eq_div_mul]
          congr 2
          scalar_tac
        · apply Eq.trans (b := monoProd (k.val + 1) idx (pointFn w 0))
          · unfold monoProd at hv ⊢
            calc
              toExt a = ∏ l ∈ Finset.range k.val,
                    (if Nat.testBit idx l then pointFn w 0 l else 1) := hv
              _ = ∏ l ∈ Finset.range (k.val + 1),
                    (if Nat.testBit idx l then pointFn w 0 l else 1) := by
                    rw [Finset.prod_range_succ]
                    have ht : Nat.testBit idx k.val = false := by
                      apply Bool.eq_false_iff.mpr
                      intro ht
                      exact hb (hbitiff.mpr ht)
                    simp [ht]
          · congr 2
            exact hk2.symm
        · have : k.val < nn.val := by scalar_tac
          omega
    · rw [if_neg hlt]
      have heq : k.val = nn.val := by scalar_tac
      exact ⟨ha, by simpa [heq] using hv⟩
  · exact ⟨hj, hacc, hm, hval⟩

theorem monomial_basis_loop_spec (w : alloc.vec.Vec cpoly.field.Ext4) (nn sz : Std.Usize)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) :
    ∀ (basis : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ sz.val → VecReduced basis →
      basis.val.map toExt
        = (List.range i.val).map (fun k => monoProd nn.val k (pointFn w 0)) →
      cpoly.cmlpoly.monomial_basis_loop0 w nn sz basis i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range sz.val).map (fun k => monoProd nn.val k (pointFn w 0)) ⦄ := by
  intro basis i hi hb hrel
  rw [cpoly.cmlpoly.monomial_basis_loop0]
  apply loop.spec_decr_nat (fun s => sz.val - s.2.val)
    (fun s => s.2.val ≤ sz.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map (fun k => monoProd nn.val k (pointFn w 0)))
  · rintro ⟨b, k⟩ ⟨hk, hb1, hrel1⟩
    simp only [cpoly.cmlpoly.monomial_basis_loop0.body]
    by_cases hlt : k < sz
    · rw [if_pos hlt]
      have hblen : b.val.length = k.val := by
        have h := congrArg List.length hrel1; simpa using h
      apply spec_bind (monomial_basis_inner_spec w nn k.val hw hnn cpoly.field.EONE k 0#usize
        (by simp) reduced_EONE (by simp) (by simp))
      rintro acc ⟨haccR, haccF⟩
      step as ⟨b2, hb2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hb2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hb1 u h
        · rw [List.mem_singleton.mp h]; exact haccR
      · rw [hb2, hk2, List.range_succ]
        simp [hrel1, haccF]
      · have : k.val < sz.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : k.val = sz.val := by scalar_tac
      exact ⟨hb1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hb, hrel⟩

/-- `cpoly::cmlpoly::monomial_basis` ↔ `CMlPolynomial.monomialBasis`. -/
theorem monomial_basis_spec (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4)
    (hw : VecReduced w) (hwl : w.val.length = n) (hsz : 2 ^ n ≤ Std.Usize.max) :
    cpoly.cmlpoly.monomial_basis w ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.monomialBasis (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.monomial_basis]
  apply spec_bind (pow2_spec (alloc.vec.Vec.len w) (by simpa [hwl] using hsz))
  intro sz hsz'
  apply spec_mono (monomial_basis_loop_spec w w.len sz hw (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hszn : sz.val = 2 ^ n := by simpa [hwl] using hsz'
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hszn] using h
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

theorem lagrange_basis_inner_spec (w : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize) (idx : ℕ)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) :
    ∀ (acc : cpoly.field.Ext4) (m j : Std.Usize),
      j.val ≤ nn.val → Reduced acc → m.val = idx / 2 ^ j.val →
      toExt acc = lagProd j.val idx (pointFn w 0) →
      cpoly.cmlpoly.lagrange_basis_loop0_loop0 w nn acc m j ⦃ z => Reduced z ∧
        toExt z = lagProd nn.val idx (pointFn w 0) ⦄ := by
  intro acc m j hj hacc hm hval
  rw [cpoly.cmlpoly.lagrange_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.2.val)
    (fun s => s.2.2.val ≤ nn.val ∧ Reduced s.1 ∧ s.2.1.val = idx / 2 ^ s.2.2.val ∧
      toExt s.1 = lagProd s.2.2.val idx (pointFn w 0))
  · rintro ⟨a, q, k⟩ ⟨hk, ha, hq, hv⟩
    simp only [Prod.fst, Prod.snd] at hk ha hq hv
    simp only [cpoly.cmlpoly.lagrange_basis_loop0_loop0.body]
    by_cases hlt : k < nn
    · rw [if_pos hlt]
      step as ⟨bit, hbit⟩
      have hbitiff : bit = 1#usize ↔ Nat.testBit idx k.val = true := by
        constructor
        · intro hb
          rw [testBit_eq_div_pow_mod, decide_eq_true_eq]
          scalar_tac
        · intro ht
          apply usize_eq_of_val_eq
          rw [testBit_eq_div_pow_mod, decide_eq_true_eq] at ht
          scalar_tac
      have hkw : k.val < w.val.length := by scalar_tac
      by_cases hb : bit = 1#usize
      · rw [if_pos hb]
        step as ⟨x, hxw⟩
        have hxR : Reduced x := hxw ▸ hw _ (List.getElem_mem hkw)
        step as ⟨a2, ha2R, ha2F⟩
        step as ⟨q2, hq2⟩
        step as ⟨k2, hk2⟩
        refine ⟨by scalar_tac, ha2R, ?_, ?_, ?_⟩
        · rw [hq2, hq, Nat.div_div_eq_div_mul]
          congr 2
          scalar_tac
        · apply Eq.trans (b := lagProd (k.val + 1) idx (pointFn w 0))
          · unfold lagProd at hv ⊢
            calc
              toExt a2 = toExt a * toExt x := ha2F
              _ = (∏ l ∈ Finset.range k.val,
                    if Nat.testBit idx l then pointFn w 0 l else 1 - pointFn w 0 l) * toExt x := by rw [hv]
              _ = ∏ l ∈ Finset.range (k.val + 1),
                    (if Nat.testBit idx l then pointFn w 0 l else 1 - pointFn w 0 l) := by
                    rw [Finset.prod_range_succ]
                    have ht := hbitiff.mp hb
                    rw [if_pos ht]
                    simp [hxw, pointFn_of_lt w 0 (by simpa using hkw)]
          · congr 2
            exact hk2.symm
        · have : k.val < nn.val := by scalar_tac
          omega
      · rw [if_neg hb]
        step as ⟨x, hxw⟩
        have hxR : Reduced x := hxw ▸ hw _ (List.getElem_mem hkw)
        have hone : Reduced cpoly.field.EONE := reduced_EONE
        step as ⟨oneMinus, homR, homF⟩
        step as ⟨a2, ha2R, ha2F⟩
        step as ⟨q2, hq2⟩
        step as ⟨k2, hk2⟩
        refine ⟨by scalar_tac, ha2R, ?_, ?_, ?_⟩
        · rw [hq2, hq, Nat.div_div_eq_div_mul]
          congr 2
          scalar_tac
        · apply Eq.trans (b := lagProd (k.val + 1) idx (pointFn w 0))
          · unfold lagProd at hv ⊢
            calc
              toExt a2 = toExt a * toExt oneMinus := ha2F
              _ = (∏ l ∈ Finset.range k.val,
                    if Nat.testBit idx l then pointFn w 0 l else 1 - pointFn w 0 l) *
                    (1 - toExt x) := by simp [hv, homF]
              _ = ∏ l ∈ Finset.range (k.val + 1),
                    (if Nat.testBit idx l then pointFn w 0 l else 1 - pointFn w 0 l) := by
                    rw [Finset.prod_range_succ]
                    have ht : Nat.testBit idx k.val = false := by
                      apply Bool.eq_false_iff.mpr
                      intro ht
                      exact hb (hbitiff.mpr ht)
                    simp [ht, hxw, pointFn_of_lt w 0 (by simpa using hkw)]
          · congr 2
            exact hk2.symm
        · have : k.val < nn.val := by scalar_tac
          omega
    · rw [if_neg hlt]
      have heq : k.val = nn.val := by scalar_tac
      exact ⟨ha, by simpa [heq] using hv⟩
  · exact ⟨hj, hacc, hm, hval⟩

theorem lagrange_basis_loop_spec (w : alloc.vec.Vec cpoly.field.Ext4) (nn sz : Std.Usize)
    (hw : VecReduced w) (hnn : nn.val = w.val.length) :
    ∀ (basis : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ sz.val → VecReduced basis →
      basis.val.map toExt
        = (List.range i.val).map (fun k => lagProd nn.val k (pointFn w 0)) →
      cpoly.cmlpoly.lagrange_basis_loop0 w nn sz basis i ⦃ z => VecReduced z ∧
        z.val.map toExt
          = (List.range sz.val).map (fun k => lagProd nn.val k (pointFn w 0)) ⦄ := by
  intro basis i hi hb hrel
  rw [cpoly.cmlpoly.lagrange_basis_loop0]
  apply loop.spec_decr_nat (fun s => sz.val - s.2.val)
    (fun s => s.2.val ≤ sz.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map (fun k => lagProd nn.val k (pointFn w 0)))
  · rintro ⟨b, k⟩ ⟨hk, hb1, hrel1⟩
    simp only [cpoly.cmlpoly.lagrange_basis_loop0.body]
    by_cases hlt : k < sz
    · rw [if_pos hlt]
      have hblen : b.val.length = k.val := by
        have h := congrArg List.length hrel1; simpa using h
      apply spec_bind (lagrange_basis_inner_spec w nn k.val hw hnn cpoly.field.EONE k 0#usize
        (by simp) reduced_EONE (by simp) (by simp))
      rintro acc ⟨haccR, haccF⟩
      step as ⟨b2, hb2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hb2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hb1 u h
        · rw [List.mem_singleton.mp h]; exact haccR
      · rw [hb2, hk2, List.range_succ]
        simp [hrel1, haccF]
      · have : k.val < sz.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : k.val = sz.val := by scalar_tac
      exact ⟨hb1, by simpa [heq] using hrel1⟩
  · exact ⟨hi, hb, hrel⟩

/-- `cpoly::cmlpoly::lagrange_basis` ↔ `CMlPolynomialEval.lagrangeBasis`. -/
theorem lagrange_basis_spec (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4)
    (hw : VecReduced w) (hwl : w.val.length = n) (hsz : 2 ^ n ≤ Std.Usize.max) :
    cpoly.cmlpoly.lagrange_basis w ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMlEval n z = CMlPolynomialEval.lagrangeBasis (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.lagrange_basis]
  apply spec_bind (pow2_spec (alloc.vec.Vec.len w) (by simpa [hwl] using hsz))
  intro sz hsz'
  apply spec_mono (lagrange_basis_loop_spec w w.len sz hw (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hz, hmap⟩
  have hszn : sz.val = 2 ^ n := by simpa [hwl] using hsz'
  have hlen : z.val.length = 2 ^ n := by
    have h := congrArg List.length hmap
    simpa [hszn] using h
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

theorem dot_loop_spec (a b : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (ha : VecReduced a) (hb : VecReduced b) :
    ∀ (acc : cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → Reduced acc →
      n.val ≤ a.val.length → n.val ≤ b.val.length →
      toExt acc = ∑ k ∈ Finset.range i.val, coeffFn a k * coeffFn b k →
      cpoly.cmlpoly.dot_loop a b n acc i ⦃ z => Reduced z ∧
        toExt z = ∑ k ∈ Finset.range n.val, coeffFn a k * coeffFn b k ⦄ := by
  intro acc i hi hacc han hbn heq
  rw [cpoly.cmlpoly.dot_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ Reduced s.1 ∧
      toExt s.1 = ∑ k ∈ Finset.range s.2.val, coeffFn a k * coeffFn b k)
  · rintro ⟨acc1, i1⟩ ⟨hi1, ha1, heq1⟩
    simp only [cpoly.cmlpoly.dot_loop.body]
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

/-- `cpoly::cmlpoly::dot` ↔ `Vector.dotProduct`, as a `Finset.range` sum. -/
theorem dot_spec (a b : alloc.vec.Vec cpoly.field.Ext4) (n : Std.Usize)
    (ha : VecReduced a) (hb : VecReduced b)
    (han : n.val ≤ a.val.length) (hbn : n.val ≤ b.val.length) :
    cpoly.cmlpoly.dot a b n ⦃ z => Reduced z ∧
      toExt z = ∑ k ∈ Finset.range n.val, coeffFn a k * coeffFn b k ⦄ := by
  rw [cpoly.cmlpoly.dot]
  apply dot_loop_spec a b n ha hb cpoly.field.EZERO 0#usize
  · simp
  · exact reduced_EZERO
  · exact han
  · exact hbn
  · simp

/-! ## `eval`, `eval_lagrange`, `eq_tilde` -/

/-- `cpoly::cmlpoly::eval` ↔ `CMlPolynomial.eval`. -/
theorem eval_spec (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.cmlpoly.eval p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomial.eval (toMl n p) (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.eval]
  apply spec_bind (monomial_basis_spec n w hw hwl (pow2_le_usize_max hpl))
  intro basis hb
  apply spec_mono (dot_spec p basis (alloc.vec.Vec.len basis) hp hb.1
    (by simp [hb.2.1, hpl]) (by simp))
  intro z hz
  refine ⟨hz.1, ?_⟩
  rw [hz.2, ← mlVal_eq_eval n p w 0]
  unfold mlVal
  rw [show (alloc.vec.Vec.len basis).val = 2 ^ n by simp [hb.2.1]]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 1
  rw [← toMl_getElem n basis k hk, hb.2.2, monomialBasis_getElem']

/-- `cpoly::cmlpoly::eval_lagrange` ↔ `CMlPolynomialEval.eval`. -/
theorem eval_lagrange_spec (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.cmlpoly.eval_lagrange p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.eval (toMlEval n p) (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.eval_lagrange]
  apply spec_bind (lagrange_basis_spec n w hw hwl (pow2_le_usize_max hpl))
  intro basis hb
  apply spec_mono (dot_spec p basis (alloc.vec.Vec.len basis) hp hb.1
    (by simp [hb.2.1, hpl]) (by simp))
  intro z hz
  refine ⟨hz.1, ?_⟩
  rw [hz.2, ← mlValL_eq_eval n p w 0]
  unfold mlValL
  rw [show (alloc.vec.Vec.len basis).val = 2 ^ n by simp [hb.2.1]]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 1
  rw [← toMl_getElem n basis k hk]
  change (toMlEval n basis)[k] = _
  rw [hb.2.2, lagrangeBasis_getElem']

/-- `cpoly::cmlpoly::eq_tilde` ↔ `CMlPolynomialEval.eqTilde`. -/
theorem eq_tilde_spec (n : ℕ) (w x : alloc.vec.Vec cpoly.field.Ext4)
    (hw : VecReduced w) (hx : VecReduced x)
    (hwl : w.val.length = n) (hxl : x.val.length = n)
    (hsz : 2 ^ n ≤ Std.Usize.max) :
    cpoly.cmlpoly.eq_tilde w x ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.eqTilde (toPoint n w) (toPoint n x) ⦄ := by
  rw [cpoly.cmlpoly.eq_tilde]
  apply spec_bind (lagrange_basis_spec n w hw hwl hsz)
  intro b hb
  apply spec_mono (eval_lagrange_spec n b x hb.1 hx hb.2.1 hxl)
  intro z hz
  refine ⟨hz.1, ?_⟩
  rw [hz.2, hb.2.2]
  rfl

/-! ## `eval_horner` -/

theorem eval_horner_layer_loop_spec (c : alloc.vec.Vec cpoly.field.Ext4) (x0 : cpoly.field.Ext4)
    (half : Std.Usize) (hc : VecReduced c) (hx : Reduced x0)
    (hhalf : 2 * half.val ≤ c.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ half.val → VecReduced out →
      out.val.map toExt = (List.range j.val).map
        (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) →
      cpoly.cmlpoly.eval_horner_layer_loop c x0 half out j ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range half.val).map
          (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) ⦄ := by
  intro out j hj hout hrel
  rw [cpoly.cmlpoly.eval_horner_layer_loop]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)))
  · rintro ⟨out1, j1⟩ ⟨hj1, hout1, hrel1⟩
    simp only [cpoly.cmlpoly.eval_horner_layer_loop.body]
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
theorem eval_horner_layer_spec (n : ℕ) (c : alloc.vec.Vec cpoly.field.Ext4)
    (x0 : cpoly.field.Ext4)
    (hc : VecReduced c) (hx : Reduced x0) (hcl : c.val.length = 2 ^ (n + 1)) :
    cpoly.cmlpoly.eval_horner_layer c x0 ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      ∀ k, coeffFn z k
        = if k < 2 ^ n then coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1) else 0 ⦄ := by
  rw [cpoly.cmlpoly.eval_horner_layer]
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

theorem eval_horner_loop0_spec (p : alloc.vec.Vec cpoly.field.Ext4) (sz : Std.Usize)
    (hp : VecReduced p) (hsz : sz.val ≤ p.val.length) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ sz.val → VecReduced cur →
      cur.val = p.val.take i.val →
      cpoly.cmlpoly.eval_horner_loop0 p sz cur i ⦃ z => VecReduced z ∧
        z.val = p.val.take sz.val ⦄ := by
  intro cur i hi hc heq
  rw [cpoly.cmlpoly.eval_horner_loop0]
  apply loop.spec_decr_nat (fun s => sz.val - s.2.val)
    (fun s => s.2.val ≤ sz.val ∧ VecReduced s.1 ∧ s.1.val = p.val.take s.2.val)
  · rintro ⟨cur1, i1⟩ ⟨hi1, hc1, heq1⟩
    simp only [cpoly.cmlpoly.eval_horner_loop0.body]
    by_cases hlt : i1 < sz
    · rw [if_pos hlt]
      have hip : i1.val < p.val.length := by scalar_tac
      have hil : i1.val ≤ p.val.length := Nat.le_of_lt hip
      have hlen : cur1.val.length < Std.Usize.max := by
        rw [heq1, List.length_take, min_eq_left hil]
        exact lt_of_lt_of_le hip p.property
      step as ⟨e, he⟩
      step as ⟨cur2, hcur2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu
        rw [hcur2] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hc1 u hu
        · rw [List.mem_singleton.mp hu, he]
          exact hp _ (List.getElem_mem hip)
      · rw [hcur2, hi2, heq1, he, ← List.take_concat_get' _ _ hip]
      · have : i1.val < sz.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      simp only [spec_ok]
      have : i1.val = sz.val := by scalar_tac
      exact ⟨hc1, by rw [heq1, this]⟩
  · exact ⟨hi, hc, heq⟩

theorem eval_horner_loop1_spec (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (t : F) (hw : VecReduced w) (hwl : w.val.length = n) (hnn : nn.val = n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ (n - j.val) →
      mlVal (n - j.val) (coeffFn cur) (pointFn w j.val) = t →
      cpoly.cmlpoly.eval_horner_loop1 w nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 1 ∧ coeffFn z 0 = t ⦄ := by
  intro cur j hj hcur hcurlen hval
  rw [cpoly.cmlpoly.eval_horner_loop1]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧
      s.1.val.length = 2 ^ (n - s.2.val) ∧
      mlVal (n - s.2.val) (coeffFn s.1) (pointFn w s.2.val) = t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.cmlpoly.eval_horner_loop1.body]
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

/-- `cpoly::cmlpoly::eval_horner` ↔ `CMlPolynomial.evalHorner`.

The extracted code is the `O(2^n)` layered algorithm; the reference
`CMlPolynomial.evalHorner` is CompPoly's structurally-recursive version of the
same, and `CompPoly.CMlPolynomial.eval_horner_eq_eval` identifies both with the
`O(n · 2^n)` dot-product semantics. -/
theorem eval_horner_spec (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.cmlpoly.eval_horner p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomial.evalHorner (toMl n p) (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.eval_horner]
  have hlen : w.len.val = n := by simpa using hwl
  have hpw : 2 ^ w.len.val ≤ Std.Usize.max := hlen ▸ pow2_le_usize_max hpl
  apply spec_bind (pow2_spec w.len hpw)
  intro sz hsz
  have hszeq : sz.val = p.val.length := by rw [hsz, hlen, hpl]
  apply spec_bind (eval_horner_loop0_spec p sz hp (by omega)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  intro cur hc
  have htake : p.val.take sz.val = p.val := by rw [hszeq, List.take_length]
  have hcur : cur.val = p.val := hc.2.trans htake
  have hcurlen : cur.val.length = 2 ^ n := by rw [hcur, hpl]
  have hcurfn : coeffFn cur = coeffFn p := by unfold coeffFn; rw [hcur]
  apply spec_bind (eval_horner_loop1_spec n w w.len
    (mlVal n (coeffFn p) (pointFn w 0)) hw hwl hlen cur 0#usize
    (by simp) hc.1 (by simpa using hcurlen) (by simp [hcurfn]))
  intro z hz
  step as ⟨e, he⟩
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hz.1 _ (List.getElem_mem (by omega))
  · rw [he, ← coeffFn_of_lt z (by omega), hz.2.2, mlVal_eq_eval,
      CMlPolynomial.eval_horner_eq_eval]

/-! ## `eval_mle` -/

theorem eval_mle_layer_loop_spec (c : alloc.vec.Vec cpoly.field.Ext4)
    (x0 one_minus : cpoly.field.Ext4)
    (half : Std.Usize) (hc : VecReduced c) (hx : Reduced x0) (hom : Reduced one_minus)
    (homF : toExt one_minus = 1 - toExt x0) (hhalf : 2 * half.val ≤ c.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ half.val → VecReduced out →
      out.val.map toExt = (List.range j.val).map
        (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) →
      cpoly.cmlpoly.eval_mle_layer_loop c x0 half one_minus out j ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range half.val).map
          (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)) ⦄ := by
  intro out j hj hout hrel
  rw [cpoly.cmlpoly.eval_mle_layer_loop]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)))
  · rintro ⟨out1, j1⟩ ⟨hj1, hout1, hrel1⟩
    simp only [cpoly.cmlpoly.eval_mle_layer_loop.body]
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
      step as ⟨a, haR, haF⟩
      step as ⟨b, hbR, hbF⟩
      step as ⟨v, hvR, hvF⟩
      step as ⟨out2, hout2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hout2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hout1 u h
        · rw [List.mem_singleton.mp h]; exact hvR
      · rw [hout2, hj2, List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hvF, haF, hbF, homF]
        simp [coeffFn, hlo, hhi, hi, hi1, hloeq, hhiweq]
      · have : j1.val < half.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : j1.val = half.val := by scalar_tac
      exact ⟨hout1, by simpa [heq] using hrel1⟩
  · exact ⟨hj, hout, hrel⟩

/-- One extracted multilinear-extension layer halves the table and folds in `x0`. -/
theorem eval_mle_layer_spec (n : ℕ) (c : alloc.vec.Vec cpoly.field.Ext4) (x0 : cpoly.field.Ext4)
    (hc : VecReduced c) (hx : Reduced x0) (hcl : c.val.length = 2 ^ (n + 1)) :
    cpoly.cmlpoly.eval_mle_layer c x0 ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      ∀ k, coeffFn z k
        = if k < 2 ^ n
            then (1 - toExt x0) * coeffFn c (2 * k) + toExt x0 * coeffFn c (2 * k + 1)
            else 0 ⦄ := by
  rw [cpoly.cmlpoly.eval_mle_layer]
  step as ⟨half, hhalf⟩
  have hone : Reduced cpoly.field.EONE := reduced_EONE
  step as ⟨one_minus, hom, homF⟩
  have hclen : c.len.val = 2 ^ (n + 1) := by simpa using hcl
  have hhalfval : half.val = 2 ^ n := by
    calc
      half.val = c.len.val / 2 := hhalf
      _ = 2 ^ (n + 1) / 2 := by rw [hclen]
      _ = 2 ^ n := by rw [pow_succ]; omega
  apply spec_mono (eval_mle_layer_loop_spec c x0 one_minus half hc hx hom
    (by simpa using homF) (by rw [hhalfval, hcl, pow_succ]; omega)
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

theorem eval_mle_loop0_spec (values : alloc.vec.Vec cpoly.field.Ext4) (sz : Std.Usize)
    (hv : VecReduced values) (hsz : sz.val ≤ values.val.length) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ sz.val → VecReduced cur →
      cur.val = values.val.take i.val →
      cpoly.cmlpoly.eval_mle_loop0 values sz cur i ⦃ z => VecReduced z ∧
        z.val = values.val.take sz.val ⦄ := by
  exact eval_horner_loop0_spec values sz hv hsz

theorem eval_mle_loop1_spec (n : ℕ) (w : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (t : F) (hw : VecReduced w) (hwl : w.val.length = n) (hnn : nn.val = n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ (n - j.val) →
      mlValL (n - j.val) (coeffFn cur) (pointFn w j.val) = t →
      cpoly.cmlpoly.eval_mle_loop1 w nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 1 ∧ coeffFn z 0 = t ⦄ := by
  intro cur j hj hcur hcurlen hval
  rw [cpoly.cmlpoly.eval_mle_loop1]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧
      s.1.val.length = 2 ^ (n - s.2.val) ∧
      mlValL (n - s.2.val) (coeffFn s.1) (pointFn w s.2.val) = t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.cmlpoly.eval_mle_loop1.body]
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
      apply spec_bind (eval_mle_layer_spec (n - (j1.val + 1)) cur1 x hcur1 hxR hpow)
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
          mlValL (n - (j1.val + 1)) (coeffFn cur2) (fun k => pointFn w j1.val (k + 1)) =
              mlValL (n - (j1.val + 1))
                (fun k => (1 - pointFn w j1.val 0) * coeffFn cur1 (2 * k) + pointFn w j1.val 0 * coeffFn cur1 (2 * k + 1))
                (fun k => pointFn w j1.val (k + 1)) := by
                  unfold mlValL
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hfn2, if_pos (Finset.mem_range.mp hk)]
                  have hxpoint : toExt x = pointFn w j1.val 0 := by
                    simp [pointFn, hx, hjw]
                  rw [hxpoint]
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

/-- `cpoly::cmlpoly::eval_mle` ↔ `CMlPolynomialEval.evalMle`. -/
theorem eval_mle_spec (n : ℕ) (p w : alloc.vec.Vec cpoly.field.Ext4)
    (hp : VecReduced p) (hw : VecReduced w)
    (hpl : p.val.length = 2 ^ n) (hwl : w.val.length = n) :
    cpoly.cmlpoly.eval_mle p w ⦃ z => Reduced z ∧
      toExt z = CMlPolynomialEval.evalMle (toMlEval n p) (toPoint n w) ⦄ := by
  rw [cpoly.cmlpoly.eval_mle]
  have hlen : w.len.val = n := by simpa using hwl
  have hpw : 2 ^ w.len.val ≤ Std.Usize.max := hlen ▸ pow2_le_usize_max hpl
  apply spec_bind (pow2_spec w.len hpw)
  intro sz hsz
  have hszeq : sz.val = p.val.length := by rw [hsz, hlen, hpl]
  apply spec_bind (eval_mle_loop0_spec p sz hp (by omega)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  intro cur hc
  have htake : p.val.take sz.val = p.val := by rw [hszeq, List.take_length]
  have hcur : cur.val = p.val := hc.2.trans htake
  have hcurlen : cur.val.length = 2 ^ n := by rw [hcur, hpl]
  have hcurfn : coeffFn cur = coeffFn p := by unfold coeffFn; rw [hcur]
  apply spec_bind (eval_mle_loop1_spec n w w.len
    (mlValL n (coeffFn p) (pointFn w 0)) hw hwl hlen cur 0#usize
    (by simp) hc.1 (by simpa using hcurlen) (by simp [hcurfn]))
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

theorem mono_to_lagrange_level_loop_spec (v : alloc.vec.Vec cpoly.field.Ext4)
    (n stride : Std.Usize) (jv : ℕ) (hv : VecReduced v) (hn : n.val = v.val.length)
    (hstride : stride.val = 2 ^ jv) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                  else coeffFn v k) →
      cpoly.cmlpoly.mono_to_lagrange_level_loop v n stride r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map
          (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                    else coeffFn v k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.cmlpoly.mono_to_lagrange_level_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k + coeffFn v (k - 2 ^ jv)
                  else coeffFn v k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [Prod.fst, Prod.snd] at hi1 hr1 hrel1
    simp only [cpoly.cmlpoly.mono_to_lagrange_level_loop.body]
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

/-- `cpoly::cmlpoly::mono_to_lagrange_level` ↔ `CMlPolynomial.monoToLagrangeLevel`. -/
theorem mono_to_lagrange_level_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hj : j.val < n) :
    cpoly.cmlpoly.mono_to_lagrange_level v j ⦃ z => VecReduced z ∧
      z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.monoToLagrangeLevel ⟨j.val, hj⟩ (toMl n v) ⦄ := by
  rw [cpoly.cmlpoly.mono_to_lagrange_level]
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

theorem mono_to_lagrange_loop_spec (n : ℕ) (nn : Std.Usize) (hnn : nn.val = n)
    (t : CMlPolynomial F n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ n →
      toMl n cur = zetaUpTo n j.val t →
      cpoly.cmlpoly.mono_to_lagrange_loop nn cur j ⦃ z => VecReduced z ∧
        z.val.length = 2 ^ n ∧ toMl n z = CMlPolynomial.monoToLagrange n t ⦄ := by
  intro cur j hj hcur hlen hval
  rw [cpoly.cmlpoly.mono_to_lagrange_loop]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧ s.1.val.length = 2 ^ n ∧
      toMl n s.1 = zetaUpTo n s.2.val t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.cmlpoly.mono_to_lagrange_loop.body]
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
      exact ⟨hcur1, hlen1, by rw [hval1, heq, zetaUpTo_full]⟩
  · exact ⟨hj, hcur, hlen, hval⟩

/-- `cpoly::cmlpoly::mono_to_lagrange` ↔ `CMlPolynomial.monoToLagrange`. -/
theorem mono_to_lagrange_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hnn : nn.val = n) :
    cpoly.cmlpoly.mono_to_lagrange v nn ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMlEval n z = CMlPolynomial.monoToLagrange n (toMl n v) ⦄ := by
  rw [cpoly.cmlpoly.mono_to_lagrange]
  apply mono_to_lagrange_loop_spec n nn hnn (toMl n v) v 0#usize
  · simp
  · exact hv
  · exact hvl
  · simp

/-! ### `lagrange_to_mono` -/

theorem lagrange_to_mono_level_loop_spec (v : alloc.vec.Vec cpoly.field.Ext4)
    (n stride : Std.Usize) (jv : ℕ) (hv : VecReduced v) (hn : n.val = v.val.length)
    (hstride : stride.val = 2 ^ jv) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize), i.val ≤ n.val → VecReduced r →
      r.val.map toExt = (List.range i.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                  else coeffFn v k) →
      cpoly.cmlpoly.lagrange_to_mono_level_loop v n stride r i ⦃ z => VecReduced z ∧
        z.val.map toExt = (List.range n.val).map
          (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                    else coeffFn v k) ⦄ := by
  intro r i hi hr hrel
  rw [cpoly.cmlpoly.lagrange_to_mono_level_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
      s.1.val.map toExt = (List.range s.2.val).map
        (fun k => if Nat.testBit k jv then coeffFn v k - coeffFn v (k - 2 ^ jv)
                  else coeffFn v k))
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1, hrel1⟩
    simp only [Prod.fst, Prod.snd] at hi1 hr1 hrel1
    simp only [cpoly.cmlpoly.lagrange_to_mono_level_loop.body]
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

/-- `cpoly::cmlpoly::lagrange_to_mono_level` ↔ `CMlPolynomial.lagrangeToMonoLevel`. -/
theorem lagrange_to_mono_level_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hj : j.val < n) :
    cpoly.cmlpoly.lagrange_to_mono_level v j ⦃ z => VecReduced z ∧
      z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.lagrangeToMonoLevel ⟨j.val, hj⟩ (toMl n v) ⦄ := by
  rw [cpoly.cmlpoly.lagrange_to_mono_level]
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

theorem lagrange_to_mono_loop_spec (n : ℕ) (t : CMlPolynomial F n) :
    ∀ (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      j.val ≤ n → VecReduced cur → cur.val.length = 2 ^ n →
      toMl n cur = mobiusFrom n j.val t →
      cpoly.cmlpoly.lagrange_to_mono_loop cur j ⦃ z => VecReduced z ∧
        z.val.length = 2 ^ n ∧ toMl n z = CMlPolynomial.lagrangeToMono n t ⦄ := by
  intro cur j hj hcur hlen hval
  rw [cpoly.cmlpoly.lagrange_to_mono_loop]
  apply loop.spec_decr_nat (fun s => s.2.val)
    (fun s => s.2.val ≤ n ∧ VecReduced s.1 ∧ s.1.val.length = 2 ^ n ∧
      toMl n s.1 = mobiusFrom n s.2.val t)
  · rintro ⟨cur1, j1⟩ ⟨hj1, hcur1, hlen1, hval1⟩
    simp only [Prod.fst, Prod.snd] at hj1 hcur1 hlen1 hval1
    simp only [cpoly.cmlpoly.lagrange_to_mono_loop.body]
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

/-- `cpoly::cmlpoly::lagrange_to_mono` ↔ `CMlPolynomial.lagrangeToMono`. -/
theorem lagrange_to_mono_spec (n : ℕ) (v : alloc.vec.Vec cpoly.field.Ext4) (nn : Std.Usize)
    (hv : VecReduced v) (hvl : v.val.length = 2 ^ n) (hnn : nn.val = n) :
    cpoly.cmlpoly.lagrange_to_mono v nn ⦃ z => VecReduced z ∧ z.val.length = 2 ^ n ∧
      toMl n z = CMlPolynomial.lagrangeToMono n (toMlEval n v) ⦄ := by
  rw [cpoly.cmlpoly.lagrange_to_mono]
  apply lagrange_to_mono_loop_spec n (toMlEval n v) v nn
  · simp [hnn]
  · exact hv
  · exact hvl
  · rw [hnn, mobiusFrom_full]

end CPolyEquiv.Ml
