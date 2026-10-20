import RMTFoundations.TracyWidom.GUEIdentification
import RMTFoundations.TracyWidom.LargestEigenvalue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false

namespace RMTFoundations.TracyWidom.FiniteDysonGaussianLaw

open MeasureTheory ProbabilityTheory Matrix
open RMTFoundations.TracyWidom.GUEIdentification

/-- Independent standard real Gaussian innovations for each time and matrix coordinate. -/
noncomputable def innovationMeasure (m n : ℕ /- [definition] -/) :
    Measure ((Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance innovationMeasure_probability (m n : ℕ /- [definition] -/) :
    IsProbabilityMeasure (innovationMeasure m n) := by
  unfold innovationMeasure
  infer_instance

lemma innovation_coordinate_law (m n : ℕ /- [definition] -/)
    (q : Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2) /- [definition] -/) :
    (innovationMeasure m n).map (Function.eval q) = gaussianReal 0 1 := by
  exact (measurePreserving_eval (μ := fun _ => gaussianReal 0 1) q).map_eq

lemma innovations_independent (m n : ℕ /- [definition] -/) :
    iIndepFun (fun q x => x q) (innovationMeasure m n) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Triangular OU innovation coefficients. On increasing times the innovation
variance is 1-exp(-2 delta); the initial mode is transported from time zero. -/
noncomputable def ouCoefficient (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j k : Fin (m+1) /- [definition] -/) : ℝ :=
  if k ≤ j then
    Real.exp (-(t j.val - t k.val)) *
      (if k.val = 0 then 1 else
        Real.sqrt (1 - Real.exp (-2 * (t k.val - t (k.val-1)))))
  else 0

lemma ouCoefficient_initial (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (k : Fin (m+1) /- [definition] -/) :
    ouCoefficient m t 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [ouCoefficient]
  · have hnk : ¬ k ≤ 0 := by
      intro h
      exact hk (le_antisymm h (Fin.zero_le _))
    simp [ouCoefficient, hk, hnk]

lemma ouCoefficient_time_shift (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/)
    (j k : Fin (m+1) /- [definition] -/) :
    ouCoefficient m (fun a => t a + c) j k = ouCoefficient m t j k := by
  simp [ouCoefficient]

/-- The triangular formula has exactly the OU recursion coefficient. -/
lemma ouCoefficient_successor (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j l k : Fin (m+1) /- [definition] -/)
    (hnext : l.val = j.val+1 /- [standing] -/) :
    ouCoefficient m t l k = Real.exp (-(t l.val-t j.val)) * ouCoefficient m t j k +
      if k = l then Real.sqrt (1-Real.exp (-2*(t l.val-t j.val))) else 0 := by
  by_cases hkj : k ≤ j
  · have hkl : k ≤ l := by simp only [Fin.le_iff_val_le_val] at *; omega
    have hne : k ≠ l := by intro h; subst k; simp only [Fin.le_iff_val_le_val] at hkj; omega
    have he : Real.exp (-(t l.val-t k.val)) =
        Real.exp (-(t l.val-t j.val)) * Real.exp (-(t j.val-t k.val)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [ouCoefficient, hkl, hkj, if_true, hne, if_false, add_zero]
    rw [he]
    ring
  · by_cases hkl : k = l
    · subst k
      have hl0 : l.val ≠ 0 := by omega
      have hp : l.val-1 = j.val := by omega
      simp [ouCoefficient, hkj, hl0, hp]
    · have hnl : ¬ k ≤ l := by
        simp only [Fin.le_iff_val_le_val] at *
        have hneval : k.val ≠ l.val := by intro h; exact hkl (Fin.ext h)
        omega
      simp [ouCoefficient, hkj, hnl, hkl]

noncomputable def ouCoordinates (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ := fun q =>
  ∑ k : Fin (m+1), ouCoefficient m t j k * x (k,q)

lemma ouCoordinates_initial (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    ouCoordinates m n t 0 x = fun q => x (0,q) := by
  funext q
  simp [ouCoordinates, ouCoefficient_initial, ite_mul]

/-- At the initial sampled time the full matrix coordinate array has exactly
the  independent GUE Gaussian source law. -/
lemma initial_GUE_coordinate_law (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) :
    (innovationMeasure m n).map (ouCoordinates m n t 0) = gueMeasure n := by
  have hi : Function.Injective
      (fun q : Fin (n+1) × Fin (n+1) × Fin 2 => ((0 : Fin (m+1)),q)) := by
    intro q r h
    exact congrArg Prod.snd h
  have hind := (innovations_independent m n).precomp hi
  have hh := hind.map_fun_eq_pi_map
    (fun q => (measurable_pi_apply ((0 : Fin (m+1)),q)).aemeasurable)
  have he : ouCoordinates m n t 0 = fun x q => x (0,q) := by
    funext x
    exact ouCoordinates_initial m n t x
  rw [he]
  simpa only [innovation_coordinate_law, gueMeasure] using hh

lemma ouCoordinates_time_shift (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    ouCoordinates m n (fun a => t a+c) j x = ouCoordinates m n t j x := by
  funext q
  simp only [ouCoordinates, ouCoefficient_time_shift]

/-- Actual OU source recursion, with a new independent Gaussian innovation at l. -/
lemma ouCoordinates_successor (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j l : Fin (m+1) /- [definition] -/)
    (hnext : l.val = j.val+1 /- [standing] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/)
    (q : Fin (n+1) × Fin (n+1) × Fin 2 /- [definition] -/) :
    ouCoordinates m n t l x q =
      Real.exp (-(t l.val-t j.val))*ouCoordinates m n t j x q +
        Real.sqrt (1-Real.exp (-2*(t l.val-t j.val)))*x (l,q) := by
  simp only [ouCoordinates, ouCoefficient_successor m t j l _ hnext, add_mul]
  rw [Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ite_mul, zero_mul]
  simp

lemma ouCoordinates_continuous (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/) :
    Continuous (ouCoordinates m n t j) := by
  unfold ouCoordinates
  apply continuous_pi
  intro q
  apply continuous_finset_sum
  intro k hk
  exact continuous_const.mul (continuous_apply (k,q))

/-- Literal Hermitian matrix path, using the  GUE symmetrization map. -/
noncomputable def ouMatrix (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  gueMatrix n (ouCoordinates m n t j x)

lemma ouMatrix_hermitian (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    (ouMatrix m n t j x).IsHermitian :=
  gueMatrix_hermitian n (ouCoordinates m n t j x)

/-- Matrix OU recursion with precisely the same source innovation and time gap. -/
lemma ouMatrix_successor (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j l : Fin (m+1) /- [definition] -/)
    (hnext : l.val = j.val+1 /- [standing] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    ouMatrix m n t l x =
      ((Real.exp (-(t l.val-t j.val)) : ℝ) : ℂ) • ouMatrix m n t j x +
        ((Real.sqrt (1-Real.exp (-2*(t l.val-t j.val))) : ℝ) : ℂ) •
          gueMatrix n (fun q => x (l,q)) := by
  ext a b
  simp only [ouMatrix, gueMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    ouCoordinates_successor m n t j l hnext]
  push_cast
  ring

/-- All eigenvalues lie below their respective thresholds. This literal finite-N
source event does not assume a determinantal representation. -/
def matrixGap (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) :
    Set ((Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ) :=
  {x | ∀ j i, (ouMatrix_hermitian m n t j x).eigenvalues i ≤ s j}

noncomputable def matrixGapProbability (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) : ℝ :=
  (innovationMeasure m n).real (matrixGap m n t s)

lemma matrixGapProbability_bounds (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) :
    0 ≤ matrixGapProbability m n t s ∧ matrixGapProbability m n t s ≤ 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

lemma matrixGapProbability_monotone (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) :
    Monotone (matrixGapProbability m n t) := by
  intro s u hsu
  refine measureReal_mono (μ := innovationMeasure m n) ?_ (by finiteness)
  intro x hx j i
  exact (hx j i).trans (hsu j)

/-- The one-by-one top eigenvalue path is the real diagonal coordinate. -/
noncomputable def scalarPath (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (x : (Fin (m+1) × (Fin 1 × Fin 1 × Fin 2)) → ℝ /- [definition] -/) :
    Fin (m+1) → ℝ := fun j => ouCoordinates m 0 t j x (0,0,0)

lemma scalarPath_continuous (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : Continuous (scalarPath m t) := by
  apply continuous_pi
  intro j
  exact (continuous_apply (0,0,0)).comp (ouCoordinates_continuous m 0 t j)

lemma scalar_eigenvalue (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/)
    (x : (Fin (m+1) × (Fin 1 × Fin 1 × Fin 2)) → ℝ /- [definition] -/)
    (i : Fin 1 /- [definition] -/) :
    (ouMatrix_hermitian m 0 t j x).eigenvalues i = scalarPath m t x j := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h := congrArg Complex.re
    (Matrix.IsHermitian.trace_eq_sum_eigenvalues (ouMatrix_hermitian m 0 t j x))
  simpa [Matrix.trace, ouMatrix, gueMatrix_diagonal, scalarPath] using h.symm

/-- A genuine probability measure on all finite-time scalar top eigenvalues. -/
noncomputable def scalarJointLaw (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : Measure (Fin (m+1) → ℝ) :=
  (innovationMeasure m 0).map (scalarPath m t)

instance scalarJointLaw_probability (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : IsProbabilityMeasure (scalarJointLaw m t) := by
  exact (Measure.isProbabilityMeasure_map_iff (scalarPath_continuous m t).measurable.aemeasurable).2 inferInstance

lemma scalarOrthant_measurable (m : ℕ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) :
    MeasurableSet {y : Fin (m+1) → ℝ | ∀ j, y j ≤ s j} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const

lemma scalarJointLaw_gap (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) :
    (scalarJointLaw m t).real {y | ∀ j, y j ≤ s j} = matrixGapProbability m 0 t s := by
  unfold scalarJointLaw matrixGapProbability
  rw [map_measureReal_apply (scalarPath_continuous m t).measurable (scalarOrthant_measurable m s)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, matrixGap]
  constructor
  · intro h j i
    rw [scalar_eigenvalue]
    exact h j
  · intro h j
    rw [← scalar_eigenvalue m t j x 0]
    exact h j 0

/-- The matrix path is continuous in its finite Gaussian innovation source. -/
lemma ouMatrix_continuous (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j : Fin (m+1) /- [definition] -/) : Continuous (ouMatrix m n t j) := by
  have hq (q : Fin (n+1) × Fin (n+1) × Fin 2) :
      Continuous (fun x => ouCoordinates m n t j x q) :=
    (continuous_apply q).comp (ouCoordinates_continuous m n t j)
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  unfold ouMatrix gueMatrix
  exact (Complex.continuous_ofReal.comp (((hq (a,b,0)).add (hq (b,a,0))).div_const 2)).add
    (continuous_const.mul
      (Complex.continuous_ofReal.comp (((hq (a,b,1)).sub (hq (b,a,1))).div_const 2)))

/-- The literal largest eigenvalue at every sampled time. -/
noncomputable def topPath (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (x : (Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ /- [definition] -/) :
    Fin (m+1) → ℝ := fun j =>
  RMTFoundations.TracyWidom.LargestEigenvalue.lamMax (ouMatrix m n t j x)

lemma topPath_continuous (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : Continuous (topPath m n t) := by
  apply continuous_pi
  intro j
  exact RMTFoundations.TracyWidom.LargestEigenvalue.continuous_lamMax.comp (ouMatrix_continuous m n t j)

/-- Genuine finite-time probability law of the complex Hermitian top eigenvalues.
No determinantal law or external imported hypothesis is assumed. -/
noncomputable def topJointLaw (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : Measure (Fin (m+1) → ℝ) :=
  (innovationMeasure m n).map (topPath m n t)

instance topJointLaw_probability (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/) : IsProbabilityMeasure (topJointLaw m n t) := by
  exact (Measure.isProbabilityMeasure_map_iff (topPath_continuous m n t).measurable.aemeasurable).2 inferInstance

lemma topJointLaw_gap (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) :
    (topJointLaw m n t).real {y | ∀ j, y j ≤ s j} = matrixGapProbability m n t s := by
  unfold topJointLaw matrixGapProbability
  rw [map_measureReal_apply (topPath_continuous m n t).measurable (scalarOrthant_measurable m s)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, matrixGap, topPath]
  exact forall_congr' fun j => RMTFoundations.TracyWidom.LargestEigenvalue.lamMax_le_iff
    (ouMatrix m n t j x) (ouMatrix_hermitian m n t j x) (s j)

/-- Simultaneous translation of every time leaves the entire finite-N source
map and top-eigenvalue law unchanged. This is literal time stationarity of the
finite-time innovations construction, independent of its determinant gap. -/
lemma topJointLaw_time_shift (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/) :
    topJointLaw m n (fun a => t a+c) = topJointLaw m n t := by
  unfold topJointLaw
  congr 1
  funext x j
  simp only [topPath, ouMatrix, ouCoordinates_time_shift]

lemma matrixGap_measurable (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (s : Fin (m+1) → ℝ /- [definition] -/) : MeasurableSet (matrixGap m n t s) := by
  have he : matrixGap m n t s = (topPath m n t) ⁻¹' {y | ∀ j, y j ≤ s j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, matrixGap, topPath]
    exact forall_congr' fun j => (RMTFoundations.TracyWidom.LargestEigenvalue.lamMax_le_iff
      (ouMatrix m n t j x) (ouMatrix_hermitian m n t j x) (s j)).symm
  rw [he]
  exact (scalarOrthant_measurable m s).preimage (topPath_continuous m n t).measurable

/-- Entire finite-N construction exists together at increasing times and
positive innovations; the source is a literal product of nondegenerate Gaussians. -/
theorem finite_matrix_all_binder_joint_probe :
    ∃ t : ℕ → ℝ, StrictMono t ∧
      (∀ m n, IsProbabilityMeasure (innovationMeasure m n)) ∧
      (∀ m n, IsProbabilityMeasure (topJointLaw m n t)) ∧
      (∀ m n, (innovationMeasure m n).map (ouCoordinates m n t 0) = gueMeasure n) ∧
      (∀ m n, Continuous (topPath m n t)) ∧
      (∀ m n x j, (ouMatrix m n t j x).IsHermitian) ∧
      (∀ m n s, MeasurableSet (matrixGap m n t s)) ∧
      (∀ m n s, (topJointLaw m n t).real {y | ∀ j, y j ≤ s j} =
        matrixGapProbability m n t s) := by
  let t : ℕ → ℝ := fun k => k
  have ht : StrictMono t := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  exact ⟨t, ht, fun m n => inferInstance, fun m n => inferInstance,
    fun m n => initial_GUE_coordinate_law m n t,
    fun m n => topPath_continuous m n t, fun m n x j => ouMatrix_hermitian m n t j x,
    fun m n => matrixGap_measurable m n t, fun m n => topJointLaw_gap m n t⟩

/-- The innovation coefficient is real and strictly positive at every genuine
positive time gap; this excludes a collapsed later-time source. -/
lemma successor_innovation_positive (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j l : Fin (m+1) /- [definition] -/)
    (hnext : l.val = j.val+1 /- [standing] -/)
    (ht : t j.val < t l.val /- [standing] -/) :
    0 < ouCoefficient m t l l := by
  have hl0 : l.val ≠ 0 := by omega
  have hp : l.val-1 = j.val := by omega
  have hgap : -2*(t l.val-t j.val) < 0 := by linarith
  have he := Real.exp_lt_one_iff.mpr hgap
  simp only [ouCoefficient, le_refl, if_true, hl0, if_false, hp, sub_self,
    neg_zero, Real.exp_zero, one_mul]
  exact Real.sqrt_pos.2 (by linarith)

/-- The exact two-time covariance factor and variance-one algebra of the
OU innovations. Its probability-law identification is separate from this algebra. -/
lemma two_time_variance_coefficients (t : ℕ → ℝ /- [definition] -/)
    (ht : t 0 < t 1 /- [standing] -/) :
    ouCoefficient 1 t 1 0 = Real.exp (-(t 1-t 0)) ∧
      (ouCoefficient 1 t 1 0)^2 + (ouCoefficient 1 t 1 1)^2 = 1 := by
  have he : Real.exp (-2*(t 1-t 0)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hs : 0 ≤ 1-Real.exp (-2*(t 1-t 0)) := by linarith
  have hexp : (Real.exp (-(t 1-t 0)))^2 = Real.exp (-2*(t 1-t 0)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [ouCoefficient, Fin.zero_le, le_refl, if_true, Fin.val_zero,
    Fin.val_one, one_ne_zero, if_false, sub_self, neg_zero, Real.exp_zero,
    one_mul, mul_one, Nat.sub_self]
  exact ⟨True.intro, by rw [Real.sq_sqrt hs, hexp]; ring⟩

/-- Joint example covers both standing successor premises on the same
nondegenerate finite matrix model used by the actual probability producer. -/
theorem successor_all_binder_joint_probe :
    ∃ t : ℕ → ℝ, StrictMono t ∧
      (1 : Fin 2).val = (0 : Fin 2).val+1 ∧ t 0 < t 1 ∧
      0 < ouCoefficient 1 t 1 1 ∧
      IsProbabilityMeasure (topJointLaw 1 2 t) ∧
      (innovationMeasure 1 2).map (ouCoordinates 1 2 t 0) = gueMeasure 2 ∧
      (ouCoefficient 1 t 1 0)^2 + (ouCoefficient 1 t 1 1)^2 = 1 ∧
      (∀ x q, ouCoordinates 1 2 t 1 x q =
        Real.exp (-(t 1-t 0))*ouCoordinates 1 2 t 0 x q +
          Real.sqrt (1-Real.exp (-2*(t 1-t 0)))*x (1,q)) ∧
      (∀ x, ouMatrix 1 2 t 1 x =
        ((Real.exp (-(t 1-t 0)) : ℝ) : ℂ) • ouMatrix 1 2 t 0 x +
          ((Real.sqrt (1-Real.exp (-2*(t 1-t 0))) : ℝ) : ℂ) •
            gueMatrix 2 (fun q => x (1,q))) := by
  let t : ℕ → ℝ := fun k => k
  have ht : StrictMono t := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  have hgap : t 0 < t 1 := ht (by omega)
  exact ⟨t, ht, by norm_num, hgap,
    successor_innovation_positive 1 t 0 1 (by norm_num) hgap,
    inferInstance, initial_GUE_coordinate_law 1 2 t,
    (two_time_variance_coefficients t hgap).2,
    ouCoordinates_successor 1 2 t 0 1 (by norm_num),
    ouMatrix_successor 1 2 t 0 1 (by norm_num)⟩

/-- Nondegenerate simultaneous instance: distinct times, positive two-time
innovation coefficient, probability source and joint law, Hermitian matrices,
and literal one-dimensional spectral identification all coexist. -/
theorem finite_gaussian_all_binder_joint_probe :
    ∃ t : ℕ → ℝ, StrictMono t ∧
      IsProbabilityMeasure (innovationMeasure 1 0) ∧
      IsProbabilityMeasure (scalarJointLaw 1 t) ∧
      0 < ouCoefficient 1 t 1 1 ∧
      (∀ x j, (ouMatrix 1 0 t j x).IsHermitian) ∧
      (∀ x j i, (ouMatrix_hermitian 1 0 t j x).eigenvalues i = scalarPath 1 t x j) ∧
      (∀ s, (scalarJointLaw 1 t).real {y | ∀ j, y j ≤ s j} = matrixGapProbability 1 0 t s) := by
  let t : ℕ → ℝ := fun k => k
  have ht : StrictMono t := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  refine ⟨t, ht, inferInstance, inferInstance, ?_, (fun x j => ouMatrix_hermitian 1 0 t j x),
    (fun x j i => scalar_eigenvalue 1 t j x i), scalarJointLaw_gap 1 t⟩
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  simp only [ouCoefficient, le_refl, if_true, Fin.val_one, one_ne_zero, if_false,
    t, Nat.cast_one, Nat.sub_self, Nat.cast_zero, sub_self, neg_zero, Real.exp_zero, one_mul]
  apply Real.sqrt_pos.2
  norm_num only [sub_zero, mul_one]
  linarith

end RMTFoundations.TracyWidom.FiniteDysonGaussianLaw

#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.innovationMeasure
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.innovationMeasure_probability
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoefficient
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoordinates
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoordinates_continuous
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouMatrix
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouMatrix_hermitian
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.matrixGap
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.matrixGapProbability
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.matrixGapProbability_bounds
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.matrixGapProbability_monotone
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarPath
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarPath_continuous
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalar_eigenvalue
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarJointLaw
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarJointLaw_probability
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarOrthant_measurable
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.scalarJointLaw_gap
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.finite_gaussian_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouMatrix_continuous
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topPath
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topPath_continuous
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topJointLaw
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topJointLaw_probability
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topJointLaw_gap
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.matrixGap_measurable
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.finite_matrix_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoefficient_time_shift
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoefficient_successor
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoordinates_time_shift
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoordinates_successor
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.topJointLaw_time_shift
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.innovation_coordinate_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.innovations_independent
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoefficient_initial
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouCoordinates_initial
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.initial_GUE_coordinate_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.successor_innovation_positive
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.two_time_variance_coefficients
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.successor_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.FiniteDysonGaussianLaw.ouMatrix_successor
