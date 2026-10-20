import RMTFoundations.TracyWidom.Airy2Derivative
import RMTFoundations.TracyWidom.Airy2Volterra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

/-- The genuine derivative kernel on the caller's shifted time-space domain. -/
noncomputable def shiftedExtendedYDerivative
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (p q : TimeSpace m /- [definition] -/) : ℝ :=
    extendedAiryYDerivative (times p.1) (times q.1) (p.2+cuts p.1) (q.2+cuts q.1)

/-- The genuine derivative kernel is jointly measurable. -/
theorem shiftedExtendedYDerivative_measurable
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    Measurable (Function.uncurry (shiftedExtendedYDerivative m times cuts)) := by
  have hm : Measurable (fun z : (TimeSpace m × TimeSpace m) × ℝ =>
      extendedAiryDerivativeIntegrand (times z.1.1.1) (times z.1.2.1)
        (z.1.1.2+cuts z.1.1.1) (z.1.2.2+cuts z.1.2.1) z.2) := by
    have hAi := measurable_airyAiReal
    have hDer := continuous_deriv_airyAiReal.measurable
    unfold extendedAiryDerivativeIntegrand
    apply Measurable.ite (by measurability) (by fun_prop) (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Each time family has a genuinely admissible common derivative rate and constants. -/
theorem finiteTime_derivative_parameters
    (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      (∀ x : ℝ, |airyAiReal x| ≤ C*Real.exp (-a*x)) ∧
      (∀ x : ℝ, |deriv airyAiReal x| ≤ C*Real.exp (-a*x)) ∧
      (∀ i j, times i < times j → 4*a ≤ times j-times i) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate m times
  obtain ⟨C,hC,hAi,hDer⟩ := Ai_and_deriv_envelope (a/2) (by linarith) (by linarith)
  refine ⟨C,a/2,hC,by linarith,hAi,hDer,?_⟩
  intro i j hij
  have hg := hgap i j hij
  linarith

/-- Removing finitely many cutoff weights gives a common unshifted spatial envelope. -/
theorem finite_cuts_envelope
    (m : ℕ /- [definition] -/)
    (cuts : Fin m → ℝ /- [definition] -/)
    (E a : ℝ /- [definition] -/)
    (hE : 0 ≤ E /- [standing] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : TimeSpace m,
      E*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) ≤
        C*Real.exp (-a*p.2)*Real.exp (-a*q.2) := by
  classical
  let S : ℝ := ∑ i, Real.exp (-a*cuts i)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Real.exp_nonneg _)
  have hs : ∀ i, Real.exp (-a*cuts i) ≤ S+1 := by
    intro i
    have hh := Finset.single_le_sum (fun j _ => Real.exp_nonneg (-a*cuts j)) (Finset.mem_univ i)
    dsimp [S]
    linarith
  refine ⟨E*(S+1)^2+1,by positivity,?_⟩
  intro p q
  have hc : E*Real.exp (-a*cuts p.1)*Real.exp (-a*cuts q.1) ≤ E*(S+1)^2+1 := by
    have hh := mul_le_mul (hs p.1) (hs q.1) (Real.exp_nonneg _) (by linarith : 0 ≤ S+1)
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hh)]
  calc E*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1))
      = (E*Real.exp (-a*cuts p.1)*Real.exp (-a*cuts q.1))*Real.exp (-a*p.2)*Real.exp (-a*q.2) := by
        rw [show -a*(p.2+cuts p.1) = -a*p.2 + -a*cuts p.1 by ring,
          show -a*(q.2+cuts q.1) = -a*q.2 + -a*cuts q.1 by ring]
        simp only [Real.exp_add]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-- Genuine physical derivative and original-kernel bounds hold jointly, including every spatial derivative identity. -/
theorem shiftedExtended_joint_derivative_envelope
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      (∀ p q, |shiftedExtendedKernel m times cuts p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2)) ∧
      (∀ p q, |shiftedExtendedYDerivative m times cuts p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2)) ∧
      (∀ p j y, HasDerivAt (fun u : ℝ => shiftedExtendedKernel m times cuts p (j,u))
        (shiftedExtendedYDerivative m times cuts p (j,y)) y) := by
  obtain ⟨D,a,hD,ha,hAi,hDer,hgap⟩ := finiteTime_derivative_parameters m times
  let E : ℝ := D^2*∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
  obtain ⟨C,hC,hcuts⟩ := finite_cuts_envelope m cuts E a hE
  refine ⟨C,a,hC,ha,?_,?_,?_⟩
  · intro p q
    exact (extendedAiryKernel_spatial_envelope D a _ _ _ _ hD.le ha hAi (hgap p.1 q.1)).trans (hcuts p q)
  · intro p q
    exact (extendedAiryYDerivative_bound D a _ _ _ _ hD.le ha hAi hDer (hgap p.1 q.1)).trans (hcuts p q)
  · intro p j y
    have hh := (extendedAiryKernel_hasDerivAt_y_of_envelope D a (times p.1) (times j)
      (p.2+cuts p.1) (y+cuts j) hD.le ha hAi hDer (hgap p.1 j)).comp y
      ((hasDerivAt_id y).add_const (cuts j))
    simpa only [Function.comp_def,mul_one,shiftedExtendedKernel,shiftedExtendedYDerivative,id_eq] using hh

/-- The complete physical extended Airy operator is trace class at every finite time/cut family. -/
theorem extendedAiryOperator_isTraceClass
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    IsTraceClass (extendedAiryOperator m times cuts) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨C,a,hC,ha,hK,hD,hder⟩ := shiftedExtended_joint_derivative_envelope m times cuts
  exact timeSpace_kernel_isTraceClass_of_derivative_envelope m (shiftedExtendedKernel m times cuts)
    (shiftedExtendedYDerivative m times cuts) C a hC.le ha
    (shiftedExtendedKernel_measurable m times cuts) (shiftedExtendedYDerivative_measurable m times cuts) hK hD hder

/-- The full-domain assertion and every physical common-factor hypothesis hold jointly at distinct times and mixed cuts. -/
theorem full_traceClass_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Measurable (Function.uncurry (shiftedExtendedYDerivative 2 times cuts)) ∧
      (∃ C a : ℝ, 0 < C ∧ 0 < a ∧
        (∀ p q, |shiftedExtendedKernel 2 times cuts p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2)) ∧
        (∀ p q, |shiftedExtendedYDerivative 2 times cuts p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2)) ∧
        (∀ p j y, HasDerivAt (fun u : ℝ => shiftedExtendedKernel 2 times cuts p (j,u))
          (shiftedExtendedYDerivative 2 times cuts p (j,y)) y)) ∧
      IsTraceClass (extendedAiryOperator 2 times cuts) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,shiftedExtendedYDerivative_measurable _ _ _,
    shiftedExtended_joint_derivative_envelope _ _ _,extendedAiryOperator_isTraceClass _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij


/-- Every actual time-space Hilbert basis has countable index. -/
theorem timeSpaceL2_basis_countable
    {ι : Type*} -- [definition]
    (m : ℕ /- [definition] -/)
    (b : HilbertBasis ι ℝ (TimeSpaceL2 m) /- [definition] -/)
    : Countable ι := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1 / 2 : ℝ))
      (Metric.ball (b j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hi : dist (b i) v < 1 / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hvi
    have hj : dist v (b j) < 1 / 2 := hvj
    have hdist : dist (b i) (b j) < 1 := by
      have ht := dist_triangle (b i) v (b j)
      linarith
    have hsq : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, b.orthonormal.1 i,
        b.orthonormal.1 j, b.orthonormal.2 hij]
      norm_num
    nlinarith [(dist_nonneg : 0 ≤ dist (b i) (b j))]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)


/-- Operator determinant identification for the original Airy2 candidate at all finite time/cut families. -/
theorem airy2FredholmCandidate_eq_realOperatorDet
    {ι : Type* /- [definition] -/}
    (m : ℕ /- [definition] -/)
    (b : HilbertBasis ι ℝ (TimeSpaceL2 m) /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    airy2FredholmCandidate m times cuts = (realOperatorDet b (extendedAiryOperator m times cuts) (-1) : ℂ) := by
  letI := timeSpaceL2_basis_countable m b
  obtain ⟨C,a,hC,ha,hK,hD,hder⟩ := shiftedExtended_joint_derivative_envelope m times cuts
  simpa only [airy2FredholmCandidate,Complex.ofReal_neg,Complex.ofReal_one,extendedAiryOperator] using
    timeSpace_kernelFredholm_eq_realOperatorDet m (shiftedExtendedKernel m times cuts)
      (shiftedExtendedYDerivative m times cuts) C a hC.le ha
      (shiftedExtendedKernel_measurable m times cuts) (shiftedExtendedYDerivative_measurable m times cuts)
      hK hD hder b (-1)


/-- A nondegenerate physical two-time family jointly realizes the full operator determinant bridge. -/
theorem determinant_bridge_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      IsTraceClass (extendedAiryOperator 2 times cuts) ∧
      airy2FredholmCandidate 2 times cuts =
        (realOperatorDet (canonicalBasis ℝ (TimeSpaceL2 2)) (extendedAiryOperator 2 times cuts) (-1) : ℂ) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,extendedAiryOperator_isTraceClass _ _ _,
    airy2FredholmCandidate_eq_realOperatorDet _ _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedYDerivative
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedYDerivative_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.finiteTime_derivative_parameters
#print axioms RMTFoundations.TracyWidom.Airy2.finite_cuts_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtended_joint_derivative_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryOperator_isTraceClass
#print axioms RMTFoundations.TracyWidom.Airy2.full_traceClass_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceL2_basis_countable
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_eq_realOperatorDet
#print axioms RMTFoundations.TracyWidom.Airy2.determinant_bridge_all_binder_joint_probe
