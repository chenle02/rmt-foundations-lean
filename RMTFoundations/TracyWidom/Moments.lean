import RMTFoundations.TracyWidom.ExponentialMoments
import RMTFoundations.TracyWidom.ExponentialTails
import RMTFoundations.TracyWidom.MeanTailIntegral


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
open RMTFoundations.AiryKernel

/-- Both actual TW1/TW2 laws have a common positive exponential absolute moment. -/
theorem TW1_TW2_exponential_absolute_integrable :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x : ℝ => Real.exp (a*|x|)) TW1Measure ∧
      Integrable (fun x : ℝ => Real.exp (a*|x|)) TW2Measure := by
  letI := TW1Measure_probability
  letI := TW2Measure_probability
  obtain ⟨b,C,hb,hC,hT⟩ := TW1_TW2_exponential_absolute_tails
  refine ⟨b/2,by positivity,?_,?_⟩
  · exact exponential_absolute_integrable_of_tail TW1Measure C b (b/2)
      hC.le (by positivity) (by linarith) (fun t ht => (hT t ht).1)
  · exact exponential_absolute_integrable_of_tail TW2Measure C b (b/2)
      hC.le (by positivity) (by linarith) (fun t ht => (hT t ht).2)

/-- All absolute real moments of TW1Measure are integrable for p >= 0. -/
theorem TW1_absolute_moment_integrable
    (p : ℝ /- [definition] -/)
    (hp : 0 ≤ p /- [standing] -/) : Integrable (fun x : ℝ => |x|^p) TW1Measure := by
  obtain ⟨a,ha,h1,_⟩ := TW1_TW2_exponential_absolute_integrable
  exact all_absolute_moments_of_exponential_integrable TW1Measure a ha h1 p hp

/-- All absolute real moments of TW2Measure are integrable for p >= 0. -/
theorem TW2_absolute_moment_integrable
    (p : ℝ /- [definition] -/)
    (hp : 0 ≤ p /- [standing] -/) : Integrable (fun x : ℝ => |x|^p) TW2Measure := by
  obtain ⟨a,ha,_,h2⟩ := TW1_TW2_exponential_absolute_integrable
  exact all_absolute_moments_of_exponential_integrable TW2Measure a ha h2 p hp

/-- Reusable TW1 moment integrable with the exact hypotheses of the named declaration. -/
theorem TW1_moment_integrable
    (n : ℕ /- [definition] -/) : Integrable (fun x : ℝ => x^n) TW1Measure := by
  apply (integrable_norm_iff (f := fun x : ℝ => x^n) (by fun_prop)).mp
  simp only [Real.norm_eq_abs,abs_pow]
  simpa using TW1_absolute_moment_integrable (n:ℝ) (by positivity)

/-- Reusable TW2 moment integrable with the exact hypotheses of the named declaration. -/
theorem TW2_moment_integrable
    (n : ℕ /- [definition] -/) : Integrable (fun x : ℝ => x^n) TW2Measure := by
  apply (integrable_norm_iff (f := fun x : ℝ => x^n) (by fun_prop)).mp
  simp only [Real.norm_eq_abs,abs_pow]
  simpa using TW2_absolute_moment_integrable (n:ℝ) (by positivity)

/-- The real first-moment integral of the actual TW1 law. -/
noncomputable def TW1Mean : ℝ := ∫ x : ℝ, x ∂TW1Measure
/-- The real first-moment integral of the actual TW2 law. -/
noncomputable def TW2Mean : ℝ := ∫ x : ℝ, x ∂TW2Measure
/-- The variance of the identity random variable under the actual TW1 law. -/
noncomputable def TW1Variance : ℝ := variance (fun x : ℝ => x) TW1Measure
/-- The variance of the identity random variable under the actual TW2 law. -/
noncomputable def TW2Variance : ℝ := variance (fun x : ℝ => x) TW2Measure

/-- Reusable TW1Mean eq tail integrals with the exact hypotheses of the named declaration. -/
theorem TW1Mean_eq_tail_integrals :
    TW1Mean = (∫ t in Ioi (0:ℝ), 1-TW1R t) - ∫ t in Ioi (0:ℝ), TW1R (-t) := by
  letI := TW1Measure_probability
  have h := mean_eq_cdf_tail_integrals TW1Measure (by simpa using TW1_moment_integrable 1)
  simpa only [TW1Mean,TW1Measure_cdf] using h

/-- Reusable TW2Mean eq tail integrals with the exact hypotheses of the named declaration. -/
theorem TW2Mean_eq_tail_integrals :
    TW2Mean = (∫ t in Ioi (0:ℝ), 1-TW2R t) - ∫ t in Ioi (0:ℝ), TW2R (-t) := by
  letI := TW2Measure_probability
  have h := mean_eq_cdf_tail_integrals TW2Measure (by simpa using TW2_moment_integrable 1)
  simpa only [TW2Mean,TW2Measure_cdf] using h

/-- Reusable TW1Variance eq centered integral with the exact hypotheses of the named declaration. -/
theorem TW1Variance_eq_centered_integral :
    TW1Variance = ∫ x : ℝ, (x-TW1Mean)^2 ∂TW1Measure :=
  variance_eq_integral measurable_id.aemeasurable

/-- Reusable TW2Variance eq centered integral with the exact hypotheses of the named declaration. -/
theorem TW2Variance_eq_centered_integral :
    TW2Variance = ∫ x : ℝ, (x-TW2Mean)^2 ∂TW2Measure :=
  variance_eq_integral measurable_id.aemeasurable

/-- Reusable TW1Variance eq second moment with the exact hypotheses of the named declaration. -/
theorem TW1Variance_eq_second_moment :
    TW1Variance = (∫ x : ℝ, x^2 ∂TW1Measure) - TW1Mean^2 := by
  letI := TW1Measure_probability
  exact variance_eq_second_moment_sub_mean_square TW1Measure (TW1_moment_integrable 2)

/-- Reusable TW2Variance eq second moment with the exact hypotheses of the named declaration. -/
theorem TW2Variance_eq_second_moment :
    TW2Variance = (∫ x : ℝ, x^2 ∂TW2Measure) - TW2Mean^2 := by
  letI := TW2Measure_probability
  exact variance_eq_second_moment_sub_mean_square TW2Measure (TW2_moment_integrable 2)

/-- Every moment input holds together on the two actual, nonzero Fredholm laws. -/
theorem TW_moments_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      IsProbabilityMeasure TW1Measure ∧ IsProbabilityMeasure TW2Measure ∧
      (∃ a : ℝ, 0 < a ∧
        Integrable (fun x : ℝ => Real.exp (a*|x|)) TW1Measure ∧
        Integrable (fun x : ℝ => Real.exp (a*|x|)) TW2Measure) ∧
      (∀ p : ℝ, 0 ≤ p → Integrable (fun x : ℝ => |x|^p) TW1Measure ∧
        Integrable (fun x : ℝ => |x|^p) TW2Measure) ∧
      (∀ n : ℕ, Integrable (fun x : ℝ => x^n) TW1Measure ∧
        Integrable (fun x : ℝ => x^n) TW2Measure) ∧
      TW1Variance = (∫ x : ℝ, x^2 ∂TW1Measure)-TW1Mean^2 ∧
      TW2Variance = (∫ x : ℝ, x^2 ∂TW2Measure)-TW2Mean^2 :=
  ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne',
    TW1Measure_probability,TW2Measure_probability,TW1_TW2_exponential_absolute_integrable,
    fun p hp => ⟨TW1_absolute_moment_integrable p hp,TW2_absolute_moment_integrable p hp⟩,
    fun n => ⟨TW1_moment_integrable n,TW2_moment_integrable n⟩,
    TW1Variance_eq_second_moment,TW2Variance_eq_second_moment⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW1_TW2_exponential_absolute_integrable
#print axioms RMTFoundations.TracyWidom.TW1_absolute_moment_integrable
#print axioms RMTFoundations.TracyWidom.TW2_absolute_moment_integrable
#print axioms RMTFoundations.TracyWidom.TW1_moment_integrable
#print axioms RMTFoundations.TracyWidom.TW2_moment_integrable
#print axioms RMTFoundations.TracyWidom.TW1Mean
#print axioms RMTFoundations.TracyWidom.TW2Mean
#print axioms RMTFoundations.TracyWidom.TW1Variance
#print axioms RMTFoundations.TracyWidom.TW2Variance
#print axioms RMTFoundations.TracyWidom.TW1Mean_eq_tail_integrals
#print axioms RMTFoundations.TracyWidom.TW2Mean_eq_tail_integrals
#print axioms RMTFoundations.TracyWidom.TW1Variance_eq_centered_integral
#print axioms RMTFoundations.TracyWidom.TW2Variance_eq_centered_integral
#print axioms RMTFoundations.TracyWidom.TW1Variance_eq_second_moment
#print axioms RMTFoundations.TracyWidom.TW2Variance_eq_second_moment
#print axioms RMTFoundations.TracyWidom.TW_moments_all_binder_joint_probe
