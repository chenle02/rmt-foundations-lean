import RMTFoundations.Airy.Contraction
import Mathlib
import RMTFoundations.Airy.Core
import RMTFoundations.Airy.Distribution
import RMTFoundations.Airy.KernelDeterminant
import RMTFoundations.Airy.FredholmBridge
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.AiryBounds

open MeasureTheory FourierTransform RMTFoundations.Airy
open Set Filter Complex
open scoped InnerProductSpace InnerProduct TemperedDistribution
open scoped SchwartzMap ENNReal Topology ContDiff

open FourierTransform LineDeriv
open scoped SchwartzMap TemperedDistribution
open Asymptotics
open scoped Asymptotics
open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open Filter

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open FourierTransform
open scoped SchwartzMap

open RMTFoundations.Airy
open Set

set_option backward.isDefEq.respectTransparency true

open Filter
open scoped Topology MatrixOrder

theorem real_matrix_det_principal_minors
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (M : Matrix ι ι ℝ /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : Matrix.det (1 + z • M) = ∑ s ∈ Finset.univ.powerset,
      Matrix.det (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) * z ^ s.card := by
  classical
  have hp : Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C) =
      ∑ s ∈ Finset.univ.powerset,
        Polynomial.C (Matrix.det (M.submatrix (Subtype.val : s → ι)
          (Subtype.val : s → ι))) * Polynomial.X ^ s.card := by
    apply Polynomial.ext
    intro k
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]
  have he := congrArg (Polynomial.evalRingHom z) hp
  rw [RingHom.map_det] at he
  have hmap : (Polynomial.evalRingHom z).mapMatrix
      (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C) = 1 + z • M := by
    ext i j
    change Polynomial.eval z ((if i = j then 1 else 0) +
      Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + z * M i j
    by_cases hij : i = j <;>
      simp only [hij, if_true, if_false, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X, Polynomial.eval_C]
  rw [hmap] at he
  simpa only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X] using he


/-- Positive principal minors give the determinant lower bound for I+C. -/
theorem one_le_det_one_add_of_posSemidef
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (C : Matrix ι ι ℝ /- [definition] -/ )
    (hC : C.PosSemidef /- [standing] -/ )
    : 1 ≤ Matrix.det (1 + C) := by
  have he := real_matrix_det_principal_minors C 1
  simp only [one_smul, one_pow, mul_one] at he
  rw [he]
  have hminor (s : Finset ι) : 0 ≤ Matrix.det
      (C.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) :=
    (hC.submatrix _).det_nonneg
  have h := Finset.single_le_sum
    (fun s (_ : s ∈ Finset.univ.powerset) => hminor s)
    (show (∅ : Finset ι) ∈ Finset.univ.powerset by simp)
  simpa using h

/-- Determinants are monotone on finite positive semidefinite matrices.
The argument conjugates by the positive square root; singular cases use det>=0. -/
theorem det_mono_of_posSemidef
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (A B : Matrix ι ι ℝ /- [definition] -/ )
    (hA : A.PosSemidef /- [standing] -/ )
    (hBA : (B - A).PosSemidef /- [standing] -/ )
    : Matrix.det A ≤ Matrix.det B := by
  have hB : B.PosSemidef := by
    have h := hA.add hBA
    convert h using 1 <;> abel
  by_cases hzero : Matrix.det A = 0
  · rw [hzero]
    exact hB.det_nonneg
  let S := CFC.sqrt A
  have hS : S.PosSemidef := by
    simpa only [Matrix.le_iff, sub_zero] using (CFC.sqrt_nonneg A)
  have hsq : S * S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hds : Matrix.det S ≠ 0 := by
    intro hz
    apply hzero
    rw [← hsq, Matrix.det_mul, hz, zero_mul]
  have hu : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hds
  let U := S⁻¹
  have hSU : S * U = 1 := Matrix.mul_nonsing_inv S hu
  have hUS : U * S = 1 := Matrix.nonsing_inv_mul S hu
  have hstarU : U.conjTranspose = U := hS.inv.isHermitian.eq
  have hbase : U.conjTranspose * A * U = 1 := by
    rw [hstarU, ← hsq]
    calc
      U * (S * S) * U = (U * S) * (S * U) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUS, hSU, Matrix.one_mul]
  let E := U.conjTranspose * (B - A) * U
  have hE : E.PosSemidef := hBA.conjTranspose_mul_mul_same U
  let Q := U.conjTranspose * B * U
  have hQ : 1 + E = Q := by
    dsimp [E, Q]
    rw [Matrix.mul_sub, Matrix.sub_mul, hbase]
    abel
  have hq : 1 ≤ Matrix.det Q := by
    rw [← hQ]
    exact one_le_det_one_add_of_posSemidef E hE
  have hback : S * Q * S = B := by
    dsimp [Q]
    rw [hstarU]
    calc
      S * (U * B * U) * S = (S * U) * B * (U * S) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hSU, hUS, Matrix.one_mul, Matrix.mul_one]
  have hdetA : Matrix.det A = Matrix.det S * Matrix.det S := by
    rw [← hsq, Matrix.det_mul]
  have hdetB : Matrix.det B = Matrix.det A * Matrix.det Q := by
    rw [← hback, Matrix.det_mul, Matrix.det_mul, hdetA]
    ring
  rw [hdetB]
  exact le_mul_of_one_le_right hA.det_nonneg hq

/-- The finite determinants of a positive contraction are between zero and one. -/
theorem det_one_sub_mem_Icc
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (A : Matrix ι ι ℝ /- [definition] -/ )
    (hA : A.PosSemidef /- [standing] -/ )
    (hI : (1 - A).PosSemidef /- [standing] -/ )
    : Matrix.det (1 - A) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hI.det_nonneg, ?_⟩
  have hdiff : ((1 : Matrix ι ι ℝ) - (1 - A)).PosSemidef := by
    convert hA using 1 <;> abel
  simpa using det_mono_of_posSemidef (1 - A) 1 hI hdiff

/-- Loewner comparison reverses the finite determinant for positive contractions. -/
theorem det_one_sub_antitone
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (A B : Matrix ι ι ℝ /- [definition] -/ )
    (hI : (1 - A).PosSemidef /- [standing] -/ )
    (hAB : (A - B).PosSemidef /- [standing] -/ )
    : Matrix.det (1 - A) ≤ Matrix.det (1 - B) := by
  have hdiff : ((1 - B) - (1 - A)).PosSemidef := by
    convert hAB using 1 <;> abel
  exact det_mono_of_posSemidef (1 - A) (1 - B) hI hdiff

/-- Bounds survive any genuine convergence of finite compressions. -/
theorem finite_compression_limit_mem_Icc
    {α : Type* /- [definition] -/ }
    (l : Filter α /- [definition] -/ )
    [l.NeBot /- [definition] -/ ]
    (n : α → ℕ /- [definition] -/ )
    (A : (a : α) → Matrix (Fin (n a)) (Fin (n a)) ℝ /- [definition] -/ )
    (hA : ∀ a, (A a).PosSemidef /- [standing] -/ )
    (hI : ∀ a, (1 - A a).PosSemidef /- [standing] -/ )
    (d : ℝ /- [definition] -/ )
    (hd : Tendsto (fun a => Matrix.det (1 - A a)) l (𝓝 d)  /- [standing] -/ )
    : d ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ge_of_tendsto hd (Filter.Eventually.of_forall fun a =>
      (det_one_sub_mem_Icc (A a) (hA a) (hI a)).1)
  · exact le_of_tendsto hd (Filter.Eventually.of_forall fun a =>
      (det_one_sub_mem_Icc (A a) (hA a) (hI a)).2)

/-- Comparison survives joint compression convergence, with no eigenvalue reindexing. -/
theorem finite_compression_limit_antitone
    {α : Type* /- [definition] -/ }
    (l : Filter α /- [definition] -/ )
    [l.NeBot /- [definition] -/ ]
    (n : α → ℕ /- [definition] -/ )
    (A B : (a : α) → Matrix (Fin (n a)) (Fin (n a)) ℝ /- [definition] -/ )
    (hI : ∀ a, (1 - A a).PosSemidef /- [standing] -/ )
    (hAB : ∀ a, (A a - B a).PosSemidef /- [standing] -/ )
    (d e : ℝ /- [definition] -/ )
    (hd : Tendsto (fun a => Matrix.det (1 - A a)) l (𝓝 d)  /- [standing] -/ )
    (he : Tendsto (fun a => Matrix.det (1 - B a)) l (𝓝 e)  /- [standing] -/ )
    : d ≤ e := by
  apply le_of_tendsto_of_tendsto hd he
  exact Filter.Eventually.of_forall fun a => det_one_sub_antitone (A a) (B a) (hI a) (hAB a)

/-- Nondegenerate simultaneous PSD, Loewner and limit instance. -/
theorem determinant_order_joint_probe
    : ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ (1 - A).PosSemidef ∧ B.PosSemidef ∧ (A - B).PosSemidef ∧
      A 0 0 = 1 / 2 ∧ B 0 0 = 1 / 4 ∧
      Matrix.det (1 - A) ∈ Set.Icc (0 : ℝ) 1 ∧
      Matrix.det (1 - A) ≤ Matrix.det (1 - B) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun _ => 1 / 2)
  let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun _ => 1 / 4)
  have hA : A.PosSemidef := Matrix.PosSemidef.diagonal (fun _ => by norm_num)
  have hB : B.PosSemidef := Matrix.PosSemidef.diagonal (fun _ => by norm_num)
  have hI : (1 - A).PosSemidef := by
    have he : (1 - A) = Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
      ext i j
      by_cases hij : i = j <;> simp [A, Matrix.diagonal, Matrix.one_apply, hij] <;> norm_num
    rw [he]
    exact hA
  have hAB : (A - B).PosSemidef := by
    have he : (A - B) = B := by
      ext i j
      by_cases hij : i = j <;> simp [A, B, Matrix.diagonal, hij] <;> norm_num
    rw [he]
    exact hB
  refine ⟨A, B, hA, hI, hB, hAB, ?_, ?_,
    det_one_sub_mem_Icc A hA hI, det_one_sub_antitone A B hI hAB⟩ <;>
    simp [A, B, Matrix.diagonal]

open scoped InnerProductSpace

/-- The exact matrix used by the real operator determinant's finite-compression API. -/
noncomputable def compressionMatrix
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    : Matrix ι ι ℝ := Matrix.of (fun i j => inner ℝ (b i) (T (b j)))

theorem compressionMatrix_quadratic
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (x : ι → ℝ /- [definition] -/ )
    : dotProduct (star x) (Matrix.mulVec (compressionMatrix b T) x) =
      inner ℝ (∑ i, x i • b i) (T (∑ i, x i • b i)) := by
  simp only [compressionMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply, star_trivial, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, starRingEnd_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem compressionMatrix_hermitian
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric /- [standing] -/ )
    : (compressionMatrix b T).IsHermitian := by
  ext i j
  change star (inner ℝ (b j) (T (b i))) = inner ℝ (b i) (T (b j))
  rw [star_trivial, real_inner_comm]
  exact hT (b i) (b j)

theorem compressionMatrix_posSemidef
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : T.IsPositive /- [standing] -/ )
    : (compressionMatrix b T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (compressionMatrix_hermitian b T hT.toLinearMap.isSymmetric)
  intro x
  rw [compressionMatrix_quadratic]
  exact hT.inner_nonneg_right _

theorem orthonormal_sum_norm_sq
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (hb : Orthonormal ℝ b /- [standing] -/ )
    (x : ι → ℝ /- [definition] -/ )
    : ‖∑ i, x i • b i‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp hb]
  simp [Finset.mul_sum, pow_two]

theorem compressionMatrix_one_sub_posSemidef
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (hb : Orthonormal ℝ b /- [standing] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric /- [standing] -/ )
    (hnorm : ‖T‖ ≤ 1 /- [standing] -/ )
    : (1 - compressionMatrix b T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (compressionMatrix_hermitian b T hT))
  intro x
  let v := ∑ i, x i • b i
  have hv : ‖v‖ ^ 2 = ∑ i, (x i) ^ 2 := orthonormal_sum_norm_sq b hb x
  have hTv : ‖T v‖ ≤ ‖v‖ := by
    calc
      ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hi : inner ℝ v (T v) ≤ ‖v‖ ^ 2 := by
    calc
      inner ℝ v (T v) ≤ ‖v‖ * ‖T v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_left hTv (norm_nonneg v)
      _ = ‖v‖ ^ 2 := (pow_two _).symm
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    compressionMatrix_quadratic]
  have hdot : dotProduct (star x) x = ∑ i, (x i) ^ 2 := by simp [dotProduct, pow_two]
  rw [hdot]
  exact sub_nonneg.mpr (hv ▸ hi)

theorem compressionMatrix_loewner
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hAB : (A - B).IsPositive /- [standing] -/ )
    : (compressionMatrix b A - compressionMatrix b B).PosSemidef := by
  have h := compressionMatrix_posSemidef b (A - B) hAB
  convert h using 1
  ext i j
  simp [compressionMatrix, inner_sub_right]

/-- Nonzero rank-one compression obeys all positivity/contraction premises. -/
theorem compression_joint_probe
    : ∃ b : Fin 2 → EuclideanSpace ℝ (Fin 2),
      ∃ T : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      Orthonormal ℝ b ∧ T.IsPositive ∧ ‖T‖ ≤ 1 ∧
      (compressionMatrix b T).PosSemidef ∧ (1 - compressionMatrix b T).PosSemidef ∧
      (compressionMatrix b T) 0 0 = 1 / 2 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let P := InnerProductSpace.rankOne ℝ (b 0) (b 0)
  let T := (1 / 2 : ℝ) • P
  have hpos : T.IsPositive := by
    apply (InnerProductSpace.isPositive_rankOne_self (b 0)).smul_of_nonneg
    norm_num
  have hnorm : ‖T‖ ≤ 1 := by
    norm_num [T, P, norm_smul, InnerProductSpace.norm_rankOne, b.norm_eq_one]
  refine ⟨b, T, b.orthonormal, hpos, hnorm,
    compressionMatrix_posSemidef b T hpos,
    compressionMatrix_one_sub_posSemidef b b.orthonormal T hpos.toLinearMap.isSymmetric hnorm, ?_⟩
  simp [compressionMatrix, T, P, InnerProductSpace.rankOne_apply,
    inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]

/-- Concrete operator compression, with positivity and norm premises actually used. -/
theorem compression_det_mem_Icc
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (hb : Orthonormal ℝ b /- [standing] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : T.IsPositive /- [standing] -/ )
    (hnorm : ‖T‖ ≤ 1 /- [standing] -/ )
    : Matrix.det (1 - compressionMatrix b T) ∈ Set.Icc (0 : ℝ) 1 :=
  det_one_sub_mem_Icc _ (compressionMatrix_posSemidef b T hT)
    (compressionMatrix_one_sub_posSemidef b hb T hT.toLinearMap.isSymmetric hnorm)

theorem compression_det_antitone
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : ι → E /- [definition] -/ )
    (hb : Orthonormal ℝ b /- [standing] -/ )
    (T S : E →L[ℝ] E /- [definition] -/ )
    (hT : T.IsPositive /- [standing] -/ )
    (hnorm : ‖T‖ ≤ 1 /- [standing] -/ )
    (hTS : (T - S).IsPositive /- [standing] -/ )
    : Matrix.det (1 - compressionMatrix b T) ≤ Matrix.det (1 - compressionMatrix b S) :=
  det_one_sub_antitone _ _
    (compressionMatrix_one_sub_posSemidef b hb T hT.toLinearMap.isSymmetric hnorm)
    (compressionMatrix_loewner b T S hTS)

/-- A limit of finite compression determinants of a positive contraction
lies in the interval [0, 1]. -/
theorem operator_compression_limit_mem_Icc
    {E ι : Type* /- [definition] -/ }
    [DecidableEq ι /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : T.IsPositive /- [standing] -/ )
    (hnorm : ‖T‖ ≤ 1 /- [standing] -/ )
    (d : ℝ /- [definition] -/ )
    (hconv : Tendsto (fun s : Finset ι => Matrix.det
      (1 - compressionMatrix (fun i : s => b i) T)) atTop (𝓝 d)  /- [standing] -/ )
    : d ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hp (s : Finset ι) := compression_det_mem_Icc (fun i : s => b i)
    (b.orthonormal.comp Subtype.val Subtype.val_injective) T hT hnorm
  exact ⟨ge_of_tendsto hconv (Filter.Eventually.of_forall fun s => (hp s).1),
    le_of_tendsto hconv (Filter.Eventually.of_forall fun s => (hp s).2)⟩

theorem operator_compression_limit_antitone
    {E ι : Type* /- [definition] -/ }
    [DecidableEq ι /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T S : E →L[ℝ] E /- [definition] -/ )
    (hT : T.IsPositive /- [standing] -/ )
    (hnorm : ‖T‖ ≤ 1 /- [standing] -/ )
    (hTS : (T - S).IsPositive /- [standing] -/ )
    (d e : ℝ /- [definition] -/ )
    (hconvT : Tendsto (fun s : Finset ι => Matrix.det
      (1 - compressionMatrix (fun i : s => b i) T)) atTop (𝓝 d)  /- [standing] -/ )
    (hconvS : Tendsto (fun s : Finset ι => Matrix.det
      (1 - compressionMatrix (fun i : s => b i) S)) atTop (𝓝 e)  /- [standing] -/ )
    : d ≤ e := by
  classical
  apply le_of_tendsto_of_tendsto hconvT hconvS
  exact Filter.Eventually.of_forall fun s => compression_det_antitone (fun i : s => b i)
    (b.orthonormal.comp Subtype.val Subtype.val_injective) T S hT hnorm hTS


open RMTFoundations.AiryDistribution RMTFoundations.AiryKernel RMTFoundations.Fredholm

/-- The contraction bound transfers to the actual physical Airy integral kernel. -/
theorem norm_K_operator_le_one
    (s : ℝ /- [definition] -/ )
    : ‖K_operator s‖ ≤ 1 := by
  rw [← H_square_eq_K_operator s]
  exact RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s

open scoped Classical in
set_option maxHeartbeats 1000000 in
theorem TW2R_compressions_tendsto_of_bridge
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (hbridge : ∀ s z : ℝ, kernelFredholm halfLineMeasure
      (fun x y => airyKernelIntegral (x + s) (y + s)) (z : ℂ) =
        (realOperatorDet b (airyKernelShift s) z : ℂ)  /- [standing] -/ )
    (s : ℝ /- [definition] -/ )
    : Tendsto (fun t : Finset ι => Matrix.det
      (1 - compressionMatrix (fun i : t => b i) (airyKernelShift s)))
        atTop (𝓝 (TW2R s)) := by
  classical
  letI := airyL2_basis_countable b
  have he : TW2R s = realOperatorDet b (airyKernelShift s) (-1) := by
    unfold TW2R TW2
    have hh := congrArg Complex.re (hbridge s (-1))
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_re] using hh
  rw [he]
  simp only [compressionMatrix]
  simpa only [neg_one_smul, sub_eq_add_neg] using
    realOperatorDet_matrix_det_tendsto b (airyKernelShift s)
      ⟨airyHankelShift s, airyHankelShift s, rfl,
        airyHankelShift_hs_summable b s, airyHankelShift_hs_summable b s⟩ (-1)

/-- Only the exact kernel/operator determinant bridge is a standing premise. -/
theorem TW2R_mem_Icc_of_bridge
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (hbridge : ∀ s z : ℝ, kernelFredholm halfLineMeasure
      (fun x y => airyKernelIntegral (x + s) (y + s)) (z : ℂ) =
        (realOperatorDet b (airyKernelShift s) z : ℂ)  /- [standing] -/ )
    (s : ℝ /- [definition] -/ )
    : TW2R s ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  exact operator_compression_limit_mem_Icc b (airyKernelShift s)
    (isPositive_airyKernelShift s) (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s) (TW2R s)
    (TW2R_compressions_tendsto_of_bridge b hbridge s)

theorem TW2R_monotone_of_bridge
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (hbridge : ∀ s z : ℝ, kernelFredholm halfLineMeasure
      (fun x y => airyKernelIntegral (x + s) (y + s)) (z : ℂ) =
        (realOperatorDet b (airyKernelShift s) z : ℂ)  /- [standing] -/ )
    : Monotone TW2R := by
  classical
  intro s t hst
  have hpos : (airyKernelShift s - airyKernelShift t).IsPositive := by
    exact (ContinuousLinearMap.le_def).mp (airyKernelShift_loewner_antitone hst)
  exact operator_compression_limit_antitone b (airyKernelShift s) (airyKernelShift t)
    (isPositive_airyKernelShift s) (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s) hpos
    (TW2R s) (TW2R t) (TW2R_compressions_tendsto_of_bridge b hbridge s)
    (TW2R_compressions_tendsto_of_bridge b hbridge t)

/-- Range and order bounds for the half-line Airy operators. -/
theorem TW2R_mem_Icc
    (s : ℝ /- [definition] -/ )
    : TW2R s ∈ Set.Icc (0 : ℝ) 1 := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  exact TW2R_mem_Icc_of_bridge b (airyKernelFredholm_eq_realOperatorDet b) s

theorem TW2R_monotone : Monotone TW2R := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  exact TW2R_monotone_of_bridge b (airyKernelFredholm_eq_realOperatorDet b)

/-- The sole conditional bridge, contraction, positivity, and Loewner binders hold
jointly on the nonzero canonical Airy model and two distinct real cutoffs. -/
theorem airy_TW2_order_joint_probe
    (s : ℝ /- [definition] -/ )
    : ∃ b : HilbertBasis (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ℝ
        (Lp ℝ 2 halfLineMeasure),
      (∀ u z : ℝ, kernelFredholm halfLineMeasure
        (fun x y => airyKernelIntegral (x + u) (y + u)) (z : ℂ) =
          (realOperatorDet b (airyKernelShift u) z : ℂ)) ∧
      airyAiReal 0 ≠ 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      (airyKernelShift s).IsPositive ∧ ‖airyKernelShift s‖ ≤ 1 ∧
      (airyKernelShift s - airyKernelShift (s + 1)).IsPositive ∧
      TW2R s ∈ Set.Icc (0 : ℝ) 1 ∧ TW2R s ≤ TW2R (s + 1) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  have hst : s ≤ s + 1 := by linarith
  exact ⟨b, airyKernelFredholm_eq_realOperatorDet b, airyAiReal_zero_pos.ne',
    shiftedUnitVector_norm 0, isPositive_airyKernelShift s, RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s,
    (ContinuousLinearMap.le_def).mp (airyKernelShift_loewner_antitone hst),
    TW2R_mem_Icc s, TW2R_monotone hst⟩

end RMTFoundations.AiryBounds

#print axioms RMTFoundations.AiryBounds.real_matrix_det_principal_minors
#print axioms RMTFoundations.AiryBounds.one_le_det_one_add_of_posSemidef
#print axioms RMTFoundations.AiryBounds.det_mono_of_posSemidef
#print axioms RMTFoundations.AiryBounds.det_one_sub_mem_Icc
#print axioms RMTFoundations.AiryBounds.det_one_sub_antitone
#print axioms RMTFoundations.AiryBounds.finite_compression_limit_mem_Icc
#print axioms RMTFoundations.AiryBounds.finite_compression_limit_antitone
#print axioms RMTFoundations.AiryBounds.determinant_order_joint_probe
#print axioms RMTFoundations.AiryBounds.compressionMatrix
#print axioms RMTFoundations.AiryBounds.compressionMatrix_quadratic
#print axioms RMTFoundations.AiryBounds.compressionMatrix_hermitian
#print axioms RMTFoundations.AiryBounds.compressionMatrix_posSemidef
#print axioms RMTFoundations.AiryBounds.orthonormal_sum_norm_sq
#print axioms RMTFoundations.AiryBounds.compressionMatrix_one_sub_posSemidef
#print axioms RMTFoundations.AiryBounds.compressionMatrix_loewner
#print axioms RMTFoundations.AiryBounds.compression_joint_probe
#print axioms RMTFoundations.AiryBounds.compression_det_mem_Icc
#print axioms RMTFoundations.AiryBounds.compression_det_antitone
#print axioms RMTFoundations.AiryBounds.operator_compression_limit_mem_Icc
#print axioms RMTFoundations.AiryBounds.operator_compression_limit_antitone
#print axioms RMTFoundations.AiryBounds.norm_K_operator_le_one
#print axioms RMTFoundations.AiryBounds.TW2R_compressions_tendsto_of_bridge
#print axioms RMTFoundations.AiryBounds.TW2R_mem_Icc_of_bridge
#print axioms RMTFoundations.AiryBounds.TW2R_monotone_of_bridge
#print axioms RMTFoundations.AiryBounds.TW2R_mem_Icc
#print axioms RMTFoundations.AiryBounds.TW2R_monotone
#print axioms RMTFoundations.AiryBounds.airy_TW2_order_joint_probe
