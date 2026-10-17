import Mathlib


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

/-- Reusable mean eq cdf tail integrals with the exact hypotheses of the named declaration. -/
theorem mean_eq_cdf_tail_integrals
    (μ : Measure ℝ /- [definition] -/)
    [IsProbabilityMeasure μ] /- [standing] -/
    (hi : Integrable (fun x : ℝ => x) μ /- [standing] -/) :
    (∫ x : ℝ, x ∂μ) = (∫ t in Ioi (0:ℝ), 1-cdf μ t) -
      ∫ t in Ioi (0:ℝ), cdf μ (-t) := by
  have hp := hi.pos_part
  have hn := hi.neg_part
  have hpos := hp.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall (fun x => le_max_right x 0))
  have hneg := hn.integral_eq_integral_meas_le
    (Filter.Eventually.of_forall (fun x => le_max_right (-x) 0))
  have hepos : (∫ t in Ioi (0:ℝ), μ.real {x : ℝ | t < max x 0}) =
      ∫ t in Ioi (0:ℝ), 1-cdf μ t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hs : {x : ℝ | t < max x 0} = Ioi t := by
      ext x
      simp only [mem_setOf_eq, mem_Ioi, lt_max_iff]
      exact or_iff_left (not_lt.mpr ht.le)
    change μ.real {x : ℝ | t < max x 0} = 1-cdf μ t
    rw [hs, cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic]
    simp
  have heneg : (∫ t in Ioi (0:ℝ), μ.real {x : ℝ | t ≤ max (-x) 0}) =
      ∫ t in Ioi (0:ℝ), cdf μ (-t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hs : {x : ℝ | t ≤ max (-x) 0} = Iic (-t) := by
      ext x
      simp only [mem_setOf_eq, mem_Iic, le_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · exact False.elim (not_le.mpr ht h)
      · intro h
        left
        linarith
    change μ.real {x : ℝ | t ≤ max (-x) 0} = cdf μ (-t)
    rw [hs, cdf_eq_real]
  rw [hepos] at hpos
  rw [heneg] at hneg
  rw [← hpos, ← hneg, ← integral_sub hp hn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]

/-- Reusable variance eq second moment sub mean square with the exact hypotheses of the named declaration. -/
theorem variance_eq_second_moment_sub_mean_square
    (μ : Measure ℝ /- [definition] -/)
    [IsProbabilityMeasure μ] /- [standing] -/
    (hi : Integrable (fun x : ℝ => x^2) μ /- [standing] -/) :
    variance (fun x : ℝ => x) μ =
      (∫ x : ℝ, x^2 ∂μ) - (∫ x : ℝ, x ∂μ)^2 := by
  apply variance_eq_sub
  exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hi

/-- A law with positive mass at both -1 and 1 inhabits every integral-API binder. -/
theorem mean_integral_all_binder_joint_probe :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Iio 0) > 0 ∧ μ (Ioi 0) > 0 ∧
      Integrable (fun x : ℝ => x) μ ∧ Integrable (fun x : ℝ => x^2) μ ∧
      (∫ x : ℝ, x ∂μ) = (∫ t in Ioi (0:ℝ), 1-cdf μ t) -
        ∫ t in Ioi (0:ℝ), cdf μ (-t) := by
  let μ : Measure ℝ := (1/2:ℝ≥0∞) • Measure.dirac (-1) + (1/2:ℝ≥0∞) • Measure.dirac 1
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simpa [μ, one_div] using (ENNReal.add_halves 1)
  letI := hprob
  have hi : Integrable (fun x : ℝ => x) μ := by
    dsimp [μ]
    apply integrable_add_measure.mpr
    constructor <;> apply Integrable.smul_measure <;>
      first | exact integrable_dirac (by finiteness) | finiteness
  have hi2 : Integrable (fun x : ℝ => x^2) μ := by
    dsimp [μ]
    apply integrable_add_measure.mpr
    constructor <;> apply Integrable.smul_measure <;>
      first | exact integrable_dirac (by finiteness) | finiteness
  refine ⟨μ,hprob,?_,?_,hi,hi2,mean_eq_cdf_tail_integrals μ hi⟩
  · norm_num [μ]
  · norm_num [μ]
end RMTFoundations.TracyWidom
#print axioms RMTFoundations.TracyWidom.mean_eq_cdf_tail_integrals
#print axioms RMTFoundations.TracyWidom.variance_eq_second_moment_sub_mean_square
#print axioms RMTFoundations.TracyWidom.mean_integral_all_binder_joint_probe
