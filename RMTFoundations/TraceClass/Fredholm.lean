import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The finite-dimensional Fredholm expansion

This file proves, for a square matrix `K` over a commutative ring, the *finite*
Fredholm expansion

`det (1 + t • K) = ∑ k ≤ card n, t ^ k * ∑_{|s| = k} det (K restricted to s × s)`,

i.e. the determinant of `1 + t K` is the generating function of the sums of the
`k × k` principal minors of `K`.  This is the identity whose infinite-dimensional
analogue *is* the Fredholm determinant of a trace-class operator; every
coefficient here is the finite analogue of `tr (Λ^k K)`.

Mathlib supplies the coefficientwise statement
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors` for the polynomial
`det (1 + X • K.map C)`.  What is proved here and is *not* in mathlib is the
scalar identity itself: to get from coefficients to an evaluated finite sum one
needs the degree bound `natDegree ≤ card n`, supplied below, together with the
evaluation lemma.

Also proved here:

* multiplicativity in the "second Fredholm" form
  `det (1 + A + B + A * B) = det (1 + A) * det (1 + B)`;
* the Weinstein-Aronszajn / Sylvester identity in the scaled and rectangular
  form `det (1 + t • (A * B)) = det (1 + t • (B * A))` (mathlib has the
  unscaled `Matrix.det_one_add_mul_comm`; the scaled form includes
  the coupling constant `t`);
* the link to the characteristic polynomial, `charpoly.eval (-1)`, hence to the
  eigenvalues: over an algebraically closed field
  `det (1 + K) = ∏ over the roots λ of charpoly of (1 + λ)`;
* nonvanishing of `det (1 + K)` is equivalent to invertibility of `1 + K` over a
  field, and to `-1` not being an eigenvalue;
* the diagonal sanity check: for `K = diagonal d` the `k`-th Fredholm
  coefficient is the `k`-th elementary symmetric function of `d`, so the
  expansion really is `det (1 + t * D) = ∑ k, t ^ k * e_k (eigenvalues)`.

## What is NOT proved here

* Nothing infinite-dimensional.  There is no trace-class operator, no Schatten
  class and no convergent Fredholm series in this file; the sums are all finite
  because the index type is a `Fintype`.
* No bound on the coefficients (the Hadamard-type bound
  `|∑ minors of size k| ≤ binom n k * ‖K‖ ^ k`, which is what makes the series
  converge in the infinite-dimensional case, is not proved).
* No continuity or analyticity in `K`.
-/

namespace RMTFoundations.TraceClass

open Matrix Polynomial Finset

variable {n : Type* /- [definition] -/ } [DecidableEq n /- [definition] -/ ] [Fintype n /- [definition] -/ ]
variable {R : Type* /- [definition] -/ } [CommRing R /- [definition] -/ ]

/-- The `k × k` principal minor of `K` indexed by a subset `s`. -/
noncomputable def principalMinor (K : Matrix n n R /- [definition] -/ ) (s : Finset n /- [definition] -/ ) : R :=
  (K.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det

/-- The `k`-th Fredholm coefficient of `K`: the sum of all `k × k` principal
minors.  In the infinite-dimensional theory this is `tr (Λ^k K)`. -/
noncomputable def fredholmCoeff (K : Matrix n n R /- [definition] -/ ) (k : ℕ /- [definition] -/ ) : R :=
  ∑ s ∈ Finset.univ.powersetCard k, principalMinor K s

theorem fredholmCoeff_zero (K : Matrix n n R /- [definition] -/ ) : fredholmCoeff K 0 = 1 := by
  classical
  rw [fredholmCoeff, Finset.powersetCard_zero, Finset.sum_singleton, principalMinor]
  exact det_isEmpty

theorem fredholmCoeff_one (K : Matrix n n R /- [definition] -/ ) : fredholmCoeff K 1 = K.trace := by
  classical
  rw [← Matrix.coeff_det_one_add_X_smul_one K,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors K 1]
  rfl

/-- Evaluating the Fredholm polynomial at `t` gives `det (1 + t • K)`. -/
theorem eval_det_one_add_X_smul (K : Matrix n n R /- [definition] -/ ) (t : R /- [definition] -/ ) :
    (det (1 + (X : R[X]) • K.map C)).eval t = det (1 + t • K) := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_eq, map_add, map_one, coe_evalRingHom, eval_mul, eval_X,
      eval_C]
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_ne h, map_add, coe_evalRingHom, eval_mul, eval_X,
      eval_C, eval_zero, zero_add]

/-- The Fredholm polynomial has degree at most the size of the matrix. -/
theorem natDegree_det_one_add_X_smul_le (K : Matrix n n R /- [definition] -/ ) :
    (det (1 + (X : R[X]) • K.map C)).natDegree ≤ Fintype.card n := by
  have h : (1 : Matrix n n R[X]) = (1 : Matrix n n R).map C :=
    (Matrix.map_one C (map_zero C) (map_one C)).symm
  have := Polynomial.natDegree_det_X_add_C_le K (1 : Matrix n n R)
  rwa [add_comm, ← h] at this

/-- **The finite Fredholm expansion.**  `det (1 + t • K)` is the generating
polynomial of the sums of principal minors of `K`. -/
theorem det_one_add_smul_eq_sum_fredholmCoeff (K : Matrix n n R /- [definition] -/ ) (t : R /- [definition] -/ ) :
    det (1 + t • K) =
      ∑ k ∈ Finset.range (Fintype.card n + 1), t ^ k * fredholmCoeff K k := by
  rw [← eval_det_one_add_X_smul K t,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_det_one_add_X_smul_le K))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors K k, mul_comm]
  rfl

/-- The finite Fredholm expansion at `t = 1`: `det (1 + K)` is the sum over all
subsets of the corresponding principal minor. -/
theorem det_one_add_eq_sum_principalMinor (K : Matrix n n R /- [definition] -/ ) :
    det (1 + K) = ∑ s : Finset n, principalMinor K s := by
  classical
  have h := det_one_add_smul_eq_sum_fredholmCoeff K 1
  rw [one_smul] at h
  rw [h]
  simp only [one_pow, one_mul, fredholmCoeff]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext s
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, Finset.mem_univ, iff_true]
    exact ⟨s.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ s), rfl⟩
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_powersetCard]
    rintro s ⟨-, rfl⟩ ⟨-, h2⟩
    exact hab h2

/-- The second-order Taylor coefficient is visible in the expansion: the
constant term is `1` and the linear term is the trace. -/
theorem det_one_add_smul_eq_one_add_trace_add (K : Matrix n n R /- [definition] -/ ) (t : R /- [definition] -/ ) :
    det (1 + t • K) =
      1 + t * K.trace +
        ∑ k ∈ Finset.Ico 2 (Fintype.card n + 1), t ^ k * fredholmCoeff K k := by
  rcases Nat.lt_or_ge (Fintype.card n) 1 with hn | hn
  · have hcard : Fintype.card n = 0 := Nat.lt_one_iff.mp hn
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard
    rw [det_isEmpty, Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty, hcard,
      Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero, add_zero, add_zero]
  · rw [det_one_add_smul_eq_sum_fredholmCoeff K t]
    have h2 : 2 ≤ Fintype.card n + 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ h2]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_range_one, fredholmCoeff_zero,
      fredholmCoeff_one, pow_zero, pow_one, mul_one]

/-- The exact algebraic form of `det (1 + t • K) = 1 + t * tr K + O(t ^ 2)`:
the remainder is literally `t ^ 2` times a polynomial in `t`, over any
commutative ring and with no analysis. -/
theorem det_one_add_smul_sub_eq_sq_mul (K : Matrix n n R /- [definition] -/ ) (t : R /- [definition] -/ ) :
    det (1 + t • K) - 1 - t * K.trace =
      t ^ 2 * ∑ k ∈ Finset.Ico 2 (Fintype.card n + 1), t ^ (k - 2) * fredholmCoeff K k := by
  rw [det_one_add_smul_eq_one_add_trace_add K t, Finset.mul_sum,
    show ∀ a b c : R, a + b + c - a - b = c from fun a b c => by ring]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← mul_assoc, ← pow_add]
  congr 2
  have : 2 ≤ k := (Finset.mem_Ico.mp hk).1
  omega

/-! ### Multiplicativity -/

/-- Multiplicativity of the Fredholm determinant in the form it takes for
`1 + K`: the "group law" `(1 + A)(1 + B) = 1 + (A + B + A * B)`. -/
theorem det_one_add_add_add_mul (A B : Matrix n n R /- [definition] -/ ) :
    det (1 + (A + B + A * B)) = det (1 + A) * det (1 + B) := by
  rw [← Matrix.det_mul]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  abel

/-! ### Sylvester / Weinstein-Aronszajn -/

variable {m : Type* /- [definition] -/ } [DecidableEq m /- [definition] -/ ] [Fintype m /- [definition] -/ ]

/-- Scaled Sylvester identity: `det (1 + t • (A * B)) = det (1 + t • (B * A))`,
for rectangular `A` and `B`.  Mathlib has the unscaled
`Matrix.det_one_add_mul_comm`; here `t` is an arbitrary coupling constant. -/
theorem det_one_add_smul_mul_comm (t : R /- [definition] -/ ) (A : Matrix m n R /- [definition] -/ ) (B : Matrix n m R /- [definition] -/ ) :
    det (1 + t • (A * B)) = det (1 + t • (B * A)) := by
  have hA : t • (A * B) = (t • A) * B := (Matrix.smul_mul t A B).symm
  have hB : t • (B * A) = B * (t • A) := by
    rw [Matrix.mul_smul]
  rw [hA, hB, Matrix.det_one_add_mul_comm]

/-- Consequently the Fredholm coefficients of `A * B` and `B * A` agree in every
degree that both sides see.  Stated as the equality of the two generating
functions; this is the finite shadow of `det (1 - K₁K₂) = det (1 - K₂K₁)` for
trace-class products. -/
theorem sum_fredholmCoeff_mul_comm (t : R /- [definition] -/ ) (A : Matrix m n R /- [definition] -/ ) (B : Matrix n m R /- [definition] -/ ) :
    ∑ k ∈ Finset.range (Fintype.card m + 1), t ^ k * fredholmCoeff (A * B) k =
      ∑ k ∈ Finset.range (Fintype.card n + 1), t ^ k * fredholmCoeff (B * A) k := by
  rw [← det_one_add_smul_eq_sum_fredholmCoeff, ← det_one_add_smul_eq_sum_fredholmCoeff]
  exact det_one_add_smul_mul_comm t A B

/-! ### Relation to the characteristic polynomial and the eigenvalues -/

/-- `det (1 + K)` is, up to sign, the characteristic polynomial of `K` evaluated
at `-1`. -/
theorem charpoly_eval_neg_one (K : Matrix n n R /- [definition] -/ ) :
    K.charpoly.eval (-1) = (-1) ^ Fintype.card n * det (1 + K) := by
  have h : (evalRingHom (-1 : R)).mapMatrix K.charmatrix = -(1 + K) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply_eq]
      simp only [map_sub, coe_evalRingHom, eval_X, eval_C, Matrix.neg_apply, Matrix.add_apply,
        Matrix.one_apply_eq]
      ring
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply_ne K i j hij]
      simp only [map_neg, coe_evalRingHom, eval_C, Matrix.neg_apply, Matrix.add_apply,
        Matrix.one_apply_ne hij]
      ring
  rw [Matrix.charpoly, ← coe_evalRingHom, RingHom.map_det, h, Matrix.det_neg]

/-! ### Sanity check: the diagonal case gives the elementary symmetric functions -/

omit [Fintype n] in
/-- For a diagonal matrix the `s`-principal minor is the product of the diagonal
entries indexed by `s`. -/
theorem principalMinor_diagonal (d : n → R /- [definition] -/ ) (s : Finset n /- [definition] -/ ) :
    principalMinor (Matrix.diagonal d) s = ∏ i ∈ s, d i := by
  classical
  rw [principalMinor, Matrix.submatrix_diagonal d _ Subtype.val_injective, Matrix.det_diagonal]
  exact Finset.prod_coe_sort s d

/-- Hence for a diagonal matrix the `k`-th Fredholm coefficient is the `k`-th
elementary symmetric function of the diagonal entries, which for a diagonalisable
matrix are its eigenvalues.  Combined with
`det_one_add_smul_eq_sum_fredholmCoeff` this says
`det (1 + t * D) = ∑ k, t ^ k * e_k (eigenvalues)`. -/
theorem fredholmCoeff_diagonal (d : n → R /- [definition] -/ ) (k : ℕ /- [definition] -/ ) :
    fredholmCoeff (Matrix.diagonal d) k =
      ∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, d i := by
  rw [fredholmCoeff]
  exact Finset.sum_congr rfl fun s _ => principalMinor_diagonal d s

/-! ### Invertibility and eigenvalues -/

variable {F : Type* /- [definition] -/ } [Field F /- [definition] -/ ]

/-- Over a field, `1 + K` is invertible exactly when `det (1 + K) ≠ 0`.  This is
the finite-dimensional shadow of the Fredholm alternative for `1 + K`. -/
theorem isUnit_one_add_iff_det_ne_zero (K : Matrix n n F /- [definition] -/ ) :
    IsUnit (1 + K) ↔ det (1 + K) ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- `det (1 + K)` vanishes exactly when `-1` is an eigenvalue of `K`. -/
theorem det_one_add_eq_zero_iff_neg_one_mem_spectrum (K : Matrix n n F /- [definition] -/ ) :
    det (1 + K) = 0 ↔ (-1 : F) ∈ spectrum F K := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, charpoly_eval_neg_one]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    · exact h'

/-- `1 + K` is invertible exactly when `-1` is not an eigenvalue of `K`. -/
theorem isUnit_one_add_iff_neg_one_notMem_spectrum (K : Matrix n n F /- [definition] -/ ) :
    IsUnit (1 + K) ↔ (-1 : F) ∉ spectrum F K := by
  rw [isUnit_one_add_iff_det_ne_zero]
  exact not_congr (det_one_add_eq_zero_iff_neg_one_mem_spectrum K)

/-- **The Fredholm determinant as a product over eigenvalues.**  Over an
algebraically closed field, `det (1 + K) = ∏ (1 + λ)` over the eigenvalues `λ`
of `K` counted with algebraic multiplicity.  This is the finite model of the
Hadamard product formula for the Fredholm determinant. -/
theorem det_one_add_eq_prod_one_add_roots [IsAlgClosed F /- [definition] -/ ] (K : Matrix n n F /- [definition] -/ ) :
    det (1 + K) = (K.charpoly.roots.map (fun l => 1 + l)).prod := by
  have hsplit : K.charpoly.Splits := IsAlgClosed.splits K.charpoly
  have hcard : Multiset.card K.charpoly.roots = Fintype.card n := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, Matrix.charpoly_natDegree_eq_dim]
  have hev := hsplit.eval_eq_prod_roots_of_monic K.charpoly_monic (-1)
  rw [charpoly_eval_neg_one] at hev
  have hneg : (K.charpoly.roots.map (fun a => (-1 : F) - a)).prod =
      (-1) ^ Fintype.card n * (K.charpoly.roots.map (fun l => 1 + l)).prod := by
    have : (K.charpoly.roots.map (fun a => (-1 : F) - a)) =
        (K.charpoly.roots.map (fun l => 1 + l)).map Neg.neg := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun a _ => ?_
      show (-1 : F) - a = -(1 + a)
      ring
    rw [this, Multiset.prod_map_neg, Multiset.card_map, hcard]
  rw [hneg] at hev
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero (α := F)))) hev

end RMTFoundations.TraceClass

#print axioms RMTFoundations.TraceClass.principalMinor
#print axioms RMTFoundations.TraceClass.fredholmCoeff
#print axioms RMTFoundations.TraceClass.fredholmCoeff_zero
#print axioms RMTFoundations.TraceClass.fredholmCoeff_one
#print axioms RMTFoundations.TraceClass.eval_det_one_add_X_smul
#print axioms RMTFoundations.TraceClass.natDegree_det_one_add_X_smul_le
#print axioms RMTFoundations.TraceClass.det_one_add_smul_eq_sum_fredholmCoeff
#print axioms RMTFoundations.TraceClass.det_one_add_eq_sum_principalMinor
#print axioms RMTFoundations.TraceClass.det_one_add_smul_eq_one_add_trace_add
#print axioms RMTFoundations.TraceClass.det_one_add_smul_sub_eq_sq_mul
#print axioms RMTFoundations.TraceClass.det_one_add_add_add_mul
#print axioms RMTFoundations.TraceClass.det_one_add_smul_mul_comm
#print axioms RMTFoundations.TraceClass.sum_fredholmCoeff_mul_comm
#print axioms RMTFoundations.TraceClass.charpoly_eval_neg_one
#print axioms RMTFoundations.TraceClass.principalMinor_diagonal
#print axioms RMTFoundations.TraceClass.fredholmCoeff_diagonal
#print axioms RMTFoundations.TraceClass.isUnit_one_add_iff_det_ne_zero
#print axioms RMTFoundations.TraceClass.det_one_add_eq_zero_iff_neg_one_mem_spectrum
#print axioms RMTFoundations.TraceClass.isUnit_one_add_iff_neg_one_notMem_spectrum
#print axioms RMTFoundations.TraceClass.det_one_add_eq_prod_one_add_roots
