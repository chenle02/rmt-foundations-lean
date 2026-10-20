import RMTFoundations.TracyWidom.GUEExtendedHermite
import RMTFoundations.TracyWidom.OUTransitionPositivity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.OUMehlerConjugation
open RMTFoundations.TracyWidom.GUEProjection RMTFoundations.TracyWidom.OUTransitionPositivity
open RMTFoundations.TracyWidom.GUEExtendedHermite Matrix MeasureTheory
open scoped Matrix NNReal

/-- Literal conjugation of the  Mehler expression to the variance-one
OU transition; no infinite-series identity is used. -/
theorem mehler_ground_conjugation (tau x y : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    mehlerKernel tau x y * hermiteFunction 0 y =
      hermiteFunction 0 x * ouTransition (Real.exp tau) x y := by
  have hq : 0 < Real.exp tau := Real.exp_pos _
  have hq1 : Real.exp tau < 1 := Real.exp_lt_one_iff.mpr htau
  have hv : 1 - (Real.exp tau)^2 ≠ 0 := ne_of_gt (variance_pos _ hq hq1)
  simp only [mehlerKernel, ouTransition, hermiteFunction, Polynomial.hermite_zero,
    map_one, one_mul]
  rw [← mul_div_mul_comm, ← mul_div_mul_comm, ← Real.exp_add, ← Real.exp_add]
  have he :
      -((1+(Real.exp tau)^2)*(x^2+y^2)-4*Real.exp tau*x*y)/
        (4*(1-(Real.exp tau)^2)) + -(y^2/4) =
      -(x^2/4) + -(y-Real.exp tau*x)^2/(2*(1-(Real.exp tau)^2)) := by
    field_simp [hv]
    ring
  rw [he]
  ring

/-- Detailed balance for the physical OU transition with ground-state-square
stationary density. -/
theorem ou_detailed_balance (tau x y : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    (hermiteFunction 0 x)^2 * ouTransition (Real.exp tau) x y =
      (hermiteFunction 0 y)^2 * ouTransition (Real.exp tau) y x := by
  have hxy := mehler_ground_conjugation tau x y htau
  have hyx := mehler_ground_conjugation tau y x htau
  rw [mehlerKernel_spatial_symmetry tau y x] at hyx
  nlinarith [congrArg (fun z : ℝ => hermiteFunction 0 x * z) hxy,
    congrArg (fun z : ℝ => hermiteFunction 0 y * z) hyx]

/-- Conjugation transports the literal N-particle transition determinant.
Both diagonal factors are the  nonzero Hermite ground states. -/
theorem transition_determinant_conjugation (N : ℕ /- [definition] -/)
    (tau : ℝ /- [definition] -/)
    (x y : Fin N → ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) *
      (∏ j, hermiteFunction 0 (y j)) =
    (∏ i, hermiteFunction 0 (x i)) *
      Matrix.det (show Matrix (Fin N) (Fin N) ℝ from fun i j => ouTransition (Real.exp tau) (x i) (y j)) := by
  change Matrix.det (Matrix.of (fun i j : Fin N => mehlerKernel tau (x i) (y j))) *
    (∏ j, hermiteFunction 0 (y j)) = (∏ i, hermiteFunction 0 (x i)) *
    Matrix.det (Matrix.of (fun i j : Fin N => ouTransition (Real.exp tau) (x i) (y j)))
  have hmatrix :
      (Matrix.of (fun i j : Fin N => mehlerKernel tau (x i) (y j))) *
        Matrix.diagonal (fun j => hermiteFunction 0 (y j)) =
      Matrix.diagonal (fun i => hermiteFunction 0 (x i)) *
        (Matrix.of (fun i j : Fin N => ouTransition (Real.exp tau) (x i) (y j))) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    change mehlerKernel tau (x i) (y j) * hermiteFunction 0 (y j) =
      hermiteFunction 0 (x i) * ouTransition (Real.exp tau) (x i) (y j)
    exact mehler_ground_conjugation tau (x i) (y j) htau
  have h := congrArg Matrix.det hmatrix
  simpa only [Matrix.det_mul, Matrix.det_diagonal] using h

/-- Every hypothesis is witnessed jointly at strictly separated nonzero
configurations and nonzero ground states; the actual transition is positive. -/
theorem conjugation_all_binder_joint_probe :
    ∃ tau : ℝ, ∃ x y : Fin 2 → ℝ,
      tau < 0 ∧ x 0 < x 1 ∧ y 0 < y 1 ∧
      (∀ i, 0 < hermiteFunction 0 (x i) ∧ 0 < hermiteFunction 0 (y i)) ∧
      (∀ i j, 0 < ouTransition (Real.exp tau) (x i) (y j)) ∧
      Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) *
        (∏ j, hermiteFunction 0 (y j)) =
      (∏ i, hermiteFunction 0 (x i)) *
        Matrix.det (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => ouTransition (Real.exp tau) (x i) (y j)) := by
  let x : Fin 2 → ℝ := ![-1,1]
  let y : Fin 2 → ℝ := ![0,2]
  have ht : (-1 : ℝ) < 0 := by norm_num
  refine ⟨-1,x,y,ht,by norm_num [x],by norm_num [y],
    fun i => ⟨hermiteFunction_zero_pos _,hermiteFunction_zero_pos _⟩,?_,
    transition_determinant_conjugation 2 (-1) x y ht⟩
  intro i j
  exact ouTransition_pos _ _ _ (Real.exp_pos _) (Real.exp_lt_one_iff.mpr ht)


/-- The transition is exactly the Mathlib Gaussian density, with the physical
variance 1-q². -/
theorem ouTransition_eq_gaussianPDFReal (q x y : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) :
    ouTransition q x y = ProbabilityTheory.gaussianPDFReal (q*x)
      ⟨1-q^2,(variance_pos q hq hq1).le⟩ y := by
  change Real.exp (-(y-q*x)^2/(2*(1-q^2))) / Real.sqrt (2*Real.pi*(1-q^2)) =
    (Real.sqrt (2*Real.pi*(1-q^2)))⁻¹ * Real.exp (-(y-q*x)^2/(2*(1-q^2)))
  ring

/-- Normalization of the genuine conditional OU transition density. -/
theorem ouTransition_integral (q x : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) :
    (∫ y : ℝ, ouTransition q x y) = 1 := by
  simp_rw [ouTransition_eq_gaussianPDFReal q x _ hq hq1]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one _
    (by exact ne_of_gt (show (0 : ℝ≥0) < ⟨1-q^2,(variance_pos q hq hq1).le⟩ from
      variance_pos q hq hq1))

theorem ouTransition_integrable (q x : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) :
    MeasureTheory.Integrable (fun y : ℝ => ouTransition q x y) := by
  simp_rw [ouTransition_eq_gaussianPDFReal q x _ hq hq1]
  exact ProbabilityTheory.integrable_gaussianPDFReal _ _

/-- The actual Mehler operator fixes the nonzero  Hermite ground
state. This proves the lowest-mode spectral action without a series import. -/
theorem mehler_ground_integral (tau x : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    (∫ y : ℝ, mehlerKernel tau x y * hermiteFunction 0 y) = hermiteFunction 0 x := by
  simp_rw [mehler_ground_conjugation tau x _ htau]
  rw [MeasureTheory.integral_const_mul,
    ouTransition_integral _ x (Real.exp_pos _) (Real.exp_lt_one_iff.mpr htau),mul_one]

theorem mehler_ground_integrable (tau x : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    MeasureTheory.Integrable (fun y : ℝ => mehlerKernel tau x y * hermiteFunction 0 y) := by
  simp_rw [mehler_ground_conjugation tau x _ htau]
  exact (ouTransition_integrable _ x (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr htau)).const_mul _

/-- The literal N=1 two-time extended Hermite correlation has normalized
conditional marginal, with no determinant gap identity assumed. -/
theorem scalar_correlation_marginal (t r x : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    (∫ y : ℝ, Matrix.det ![
      ![extendedHermiteKernel 1 t x t x,extendedHermiteKernel 1 t x r y],
      ![extendedHermiteKernel 1 r y t x,extendedHermiteKernel 1 r y r y]]) =
        (hermiteFunction 0 x)^2 := by
  simp_rw [scalar_two_time_determinant t r x _ htr,
    show ∀ y : ℝ, hermiteFunction 0 x * hermiteFunction 0 y * mehlerKernel (t-r) x y =
      hermiteFunction 0 x * (mehlerKernel (t-r) x y * hermiteFunction 0 y) by
        intro y; ring]
  rw [MeasureTheory.integral_const_mul,mehler_ground_integral (t-r) x (sub_neg.mpr htr)]
  ring

/-- Joint normalization of the literal N=1 physical two-time determinant. -/
theorem scalar_correlation_iterated_integral (t r : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    (∫ x : ℝ, ∫ y : ℝ, Matrix.det ![
      ![extendedHermiteKernel 1 t x t x,extendedHermiteKernel 1 t x r y],
      ![extendedHermiteKernel 1 r y t x,extendedHermiteKernel 1 r y r y]]) = 1 := by
  simp_rw [scalar_correlation_marginal t r _ htr,pow_two]
  simpa using hermiteFunction_orthogonality 0 0

/-- All analytic and chronological binders share one physical nonzero
instance. Includes literal normalized scalar two-time correlation. -/
theorem scalar_normalization_all_binder_probe :
    ∃ tau t r x : ℝ, tau < 0 ∧ t < r ∧ t-r = tau ∧ x ≠ 0 ∧
      0 < hermiteFunction 0 x ∧
      MeasureTheory.Integrable (fun y : ℝ => mehlerKernel tau x y * hermiteFunction 0 y) ∧
      (∫ y : ℝ, mehlerKernel tau x y * hermiteFunction 0 y) = hermiteFunction 0 x ∧
      (∫ u : ℝ, ∫ v : ℝ, Matrix.det ![
        ![extendedHermiteKernel 1 t u t u,extendedHermiteKernel 1 t u r v],
        ![extendedHermiteKernel 1 r v t u,extendedHermiteKernel 1 r v r v]]) = 1 := by
  have ht : (-1 : ℝ) < 0 := by norm_num
  have htr : (0 : ℝ) < 1 := by norm_num
  exact ⟨-1,0,1,1,ht,htr,by norm_num,by norm_num,hermiteFunction_zero_pos _,
    mehler_ground_integrable (-1) 1 ht,mehler_ground_integral (-1) 1 ht,
    scalar_correlation_iterated_integral 0 1 htr⟩


/-- Strict two-particle Mehler transition positivity follows from the actual
OU TP2 theorem and literal determinant conjugation. -/
theorem mehler_two_particle_det_pos (tau : ℝ /- [definition] -/)
    (x y : Fin 2 → ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/)
    (hx : x 0 < x 1 /- [standing] -/)
    (hy : y 0 < y 1 /- [standing] -/) :
    0 < Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) := by
  have h := transition_determinant_conjugation 2 tau x y htau
  have hp := transitionDetTwo_pos (Real.exp tau) x y (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr htau) hx hy
  have hpx : 0 < ∏ i, hermiteFunction 0 (x i) :=
    Finset.prod_pos (fun i _ => hermiteFunction_zero_pos _)
  have hpy : 0 < ∏ i, hermiteFunction 0 (y i) :=
    Finset.prod_pos (fun i _ => hermiteFunction_zero_pos _)
  have hmul : 0 < Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) *
      (∏ j, hermiteFunction 0 (y j)) := by
    rw [h]
    exact mul_pos hpx hp
  exact (mul_pos_iff_of_pos_right hpy).mp hmul

/-- Literal scalar physical correlation density on the product state space. -/
noncomputable def scalarJointDensity (tau : ℝ /- [definition] -/)
    (z : ℝ × ℝ /- [definition] -/) : ℝ :=
  hermiteFunction 0 z.1 * hermiteFunction 0 z.2 * mehlerKernel tau z.1 z.2

theorem scalarJointDensity_continuous (tau : ℝ /- [definition] -/) :
    Continuous (scalarJointDensity tau) := by
  unfold scalarJointDensity mehlerKernel
  exact ((continuous_hermiteFunction 0).comp continuous_fst |>.mul
    ((continuous_hermiteFunction 0).comp continuous_snd)).mul
      (by fun_prop)

theorem scalarJointDensity_pos (tau : ℝ /- [definition] -/)
    (z : ℝ × ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    0 < scalarJointDensity tau z := by
  exact mul_pos (mul_pos (hermiteFunction_zero_pos _) (hermiteFunction_zero_pos _))
    (mehlerKernel_pos tau _ _ htau)

theorem scalarJointDensity_section (tau x y : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    scalarJointDensity tau (x,y) =
      (hermiteFunction 0 x)^2 * ouTransition (Real.exp tau) x y := by
  unfold scalarJointDensity
  have h := mehler_ground_conjugation tau x y htau
  calc
    _ = hermiteFunction 0 x * (mehlerKernel tau x y * hermiteFunction 0 y) := by ring
    _ = _ := by rw [h]; ring

theorem scalarJointDensity_section_integrable (tau x : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    Integrable (fun y : ℝ => scalarJointDensity tau (x,y)) := by
  simp_rw [scalarJointDensity_section tau x _ htau]
  exact (ouTransition_integrable _ x (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr htau)).const_mul _

theorem scalarJointDensity_marginal_integral (tau x : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    (∫ y : ℝ, scalarJointDensity tau (x,y)) = (hermiteFunction 0 x)^2 := by
  simp_rw [scalarJointDensity_section tau x _ htau]
  rw [integral_const_mul,
    ouTransition_integral _ x (Real.exp_pos _) (Real.exp_lt_one_iff.mpr htau),mul_one]

theorem scalarJointDensity_integrable (tau : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    Integrable (scalarJointDensity tau) ((volume : Measure ℝ).prod volume) := by
  apply (integrable_prod_iff (scalarJointDensity_continuous tau).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => scalarJointDensity_section_integrable tau x htau),?_⟩
  simp_rw [Real.norm_eq_abs,abs_of_pos (scalarJointDensity_pos tau _ htau),
    scalarJointDensity_marginal_integral tau _ htau,pow_two]
  exact integrable_hermiteFunction_product 0 0

theorem scalarJointDensity_integral (tau : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    (∫ z : ℝ × ℝ, scalarJointDensity tau z ∂(volume : Measure ℝ).prod volume) = 1 := by
  rw [integral_prod _ (scalarJointDensity_integrable tau htau)]
  simp_rw [scalarJointDensity_marginal_integral tau _ htau,pow_two]
  simpa using hermiteFunction_orthogonality 0 0

/-- A genuine scalar two-time law whose density is the physical extended
Hermite N=1 two-point determinant; no all-N Fredholm identity is asserted. -/
noncomputable def scalarHermiteJointLaw (tau : ℝ /- [definition] -/) : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod volume).withDensity
    (fun z => ENNReal.ofReal (scalarJointDensity tau z))

theorem scalarHermiteJointLaw_probability (tau : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    IsProbabilityMeasure (scalarHermiteJointLaw tau) := by
  constructor
  rw [scalarHermiteJointLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (scalarJointDensity_integrable tau htau)
      (Filter.Eventually.of_forall (fun z => (scalarJointDensity_pos tau z htau).le)),
    scalarJointDensity_integral tau htau,ENNReal.ofReal_one]

/-- Nondegenerate common instance for all chronological, ordering and
normalization binders; physical two-particle determinant and scalar law. -/
theorem scalar_law_all_binder_joint_probe :
    ∃ tau : ℝ, ∃ x y : Fin 2 → ℝ, tau < 0 ∧ x 0 < x 1 ∧ y 0 < y 1 ∧
      0 < Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) ∧
      (∀ z : ℝ × ℝ, 0 < scalarJointDensity tau z) ∧
      Integrable (scalarJointDensity tau) ((volume : Measure ℝ).prod volume) ∧
      (∫ z : ℝ × ℝ, scalarJointDensity tau z ∂(volume : Measure ℝ).prod volume) = 1 ∧
      IsProbabilityMeasure (scalarHermiteJointLaw tau) := by
  let x : Fin 2 → ℝ := ![-1,1]
  let y : Fin 2 → ℝ := ![0,2]
  have ht : (-1 : ℝ) < 0 := by norm_num
  have hx : x 0 < x 1 := by norm_num [x]
  have hy : y 0 < y 1 := by norm_num [y]
  exact ⟨-1,x,y,ht,hx,hy,mehler_two_particle_det_pos (-1) x y ht hx hy,
    fun z => scalarJointDensity_pos (-1) z ht,scalarJointDensity_integrable (-1) ht,
    scalarJointDensity_integral (-1) ht,scalarHermiteJointLaw_probability (-1) ht⟩


/-- Identifies the new concrete scalar density with the literal physical
extended-kernel correlation; both time coordinates are the caller's. -/
theorem scalarJointDensity_eq_correlation (t r x y : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    scalarJointDensity (t-r) (x,y) = Matrix.det ![
      ![extendedHermiteKernel 1 t x t x,extendedHermiteKernel 1 t x r y],
      ![extendedHermiteKernel 1 r y t x,extendedHermiteKernel 1 r y r y]] := by
  exact (scalar_two_time_determinant t r x y htr).symm

/-- Explicit common strictly positive q witnesses all Gaussian-density,
conditional-integrability and normalization binders together. -/
theorem ou_density_all_binder_joint_probe :
    ∃ q x : ℝ, 0 < q ∧ q < 1 ∧ x ≠ 0 ∧
      (∀ y, 0 < ouTransition q x y) ∧
      Integrable (fun y : ℝ => ouTransition q x y) ∧
      (∫ y : ℝ, ouTransition q x y) = 1 := by
  have hq : 0 < (1/2 : ℝ) := by norm_num
  have hq1 : (1/2 : ℝ) < 1 := by norm_num
  exact ⟨1/2,1,hq,hq1,by norm_num,fun y => ouTransition_pos _ _ _ hq hq1,
    ouTransition_integrable _ _ hq hq1,ouTransition_integral _ _ hq hq1⟩

end RMTFoundations.TracyWidom.OUMehlerConjugation

#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.mehler_ground_conjugation
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.ou_detailed_balance
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.transition_determinant_conjugation
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.conjugation_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.ouTransition_eq_gaussianPDFReal
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.ouTransition_integral
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.ouTransition_integrable
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.mehler_ground_integral
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.mehler_ground_integrable
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalar_correlation_marginal
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalar_correlation_iterated_integral
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalar_normalization_all_binder_probe
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.mehler_two_particle_det_pos
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_continuous
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_pos
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_section
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_section_integrable
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_marginal_integral
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_integrable
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_integral
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarHermiteJointLaw
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarHermiteJointLaw_probability
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalar_law_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.scalarJointDensity_eq_correlation
#print axioms RMTFoundations.TracyWidom.OUMehlerConjugation.ou_density_all_binder_joint_probe
