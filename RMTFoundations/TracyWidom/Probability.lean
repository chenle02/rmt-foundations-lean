import RMTFoundations.TracyWidom.OrderOneMonotone
import RMTFoundations.TracyWidom.OrderTwo
import RMTFoundations.TracyWidom.LeftTail
import Mathlib

/-! Probability measures, CDF uniqueness and interior quantiles for the canonical Fredholm functions. -/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
open RMTFoundations.AiryKernel RMTFoundations.TWOneMonotone
open RMTFoundations.TWLeftTail RMTFoundations.AiryBounds

/-- The order-one Fredholm CDF as a monotone, right-continuous Stieltjes function. -/
noncomputable def TW1CDF : StieltjesFunction ℝ where
  toFun := TW1R
  mono' := monotone_TW1R
  right_continuous' := fun _s => TW1R_continuous.continuousAt.continuousWithinAt

/-- The order-two Fredholm CDF as a monotone, right-continuous Stieltjes function. -/
noncomputable def TW2CDF : StieltjesFunction ℝ where
  toFun := TW2R
  mono' := TW2R_monotone
  right_continuous' := fun _s => TW2R_continuous.continuousAt.continuousWithinAt

/-- The canonical order-one Borel measure constructed from TW1CDF. -/
noncomputable def TW1Measure : Measure ℝ := TW1CDF.measure
/-- The canonical order-two Borel measure constructed from TW2CDF. -/
noncomputable def TW2Measure : Measure ℝ := TW2CDF.measure

/-- The order-one Fredholm measure has total mass one. -/
theorem TW1Measure_probability : IsProbabilityMeasure TW1Measure :=
  TW1CDF.isProbabilityMeasure TW1R_tendsto_atBot_zero_unconditional TW1R_tendsto_atTop_one

/-- The order-two Fredholm measure has total mass one. -/
theorem TW2Measure_probability : IsProbabilityMeasure TW2Measure :=
  TW2CDF.isProbabilityMeasure TW2R_tendsto_atBot_zero_unconditional TW2R_tendsto_atTop_one

/-- The canonical Mathlib CDF of TW1Measure equals the order-one Fredholm function. -/
theorem TW1Measure_cdf
    (s : ℝ /- [definition] -/) : cdf TW1Measure s = TW1R s := by
  have h := cdf_measure_stieltjesFunction TW1CDF
    TW1R_tendsto_atBot_zero_unconditional TW1R_tendsto_atTop_one
  exact congrArg (fun f : StieltjesFunction ℝ => f s) h

/-- The canonical Mathlib CDF of TW2Measure equals the order-two Fredholm function. -/
theorem TW2Measure_cdf
    (s : ℝ /- [definition] -/) : cdf TW2Measure s = TW2R s := by
  have h := cdf_measure_stieltjesFunction TW2CDF
    TW2R_tendsto_atBot_zero_unconditional TW2R_tendsto_atTop_one
  exact congrArg (fun f : StieltjesFunction ℝ => f s) h

/-- The order-one measure of a closed lower half-line equals its Fredholm CDF. -/
theorem TW1Measure_Iic
    (s : ℝ /- [definition] -/) : TW1Measure (Iic s) = ENNReal.ofReal (TW1R s) := by
  simpa [TW1Measure, TW1CDF] using TW1CDF.measure_Iic TW1R_tendsto_atBot_zero_unconditional s

/-- The order-two measure of a closed lower half-line equals its Fredholm CDF. -/
theorem TW2Measure_Iic
    (s : ℝ /- [definition] -/) : TW2Measure (Iic s) = ENNReal.ofReal (TW2R s) := by
  simpa [TW2Measure, TW2CDF] using TW2CDF.measure_Iic TW2R_tendsto_atBot_zero_unconditional s

/-- A probability measure with the order-one Fredholm CDF is TW1Measure. -/
theorem TW1Measure_unique
    (μ : Measure ℝ /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (hcdf : ∀ s, cdf μ s = TW1R s /- [standing] -/) : μ = TW1Measure := by
  letI := hμ
  letI := TW1Measure_probability
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro s
  rw [hcdf s, TW1Measure_cdf]

/-- A probability measure with the order-two Fredholm CDF is TW2Measure. -/
theorem TW2Measure_unique
    (μ : Measure ℝ /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (hcdf : ∀ s, cdf μ s = TW2R s /- [standing] -/) : μ = TW2Measure := by
  letI := hμ
  letI := TW2Measure_probability
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro s
  rw [hcdf s, TW2Measure_cdf]

/-- A continuous monotone real function with endpoint limits zero and one attains every interior probability. -/
theorem continuous_cdf_quantile_exists
    (F : ℝ → ℝ /- [definition] -/)
    (hc : Continuous F /- [standing] -/)
    (hm : Monotone F /- [standing] -/)
    (h0 : Tendsto F atBot (𝓝 0) /- [standing] -/)
    (h1 : Tendsto F atTop (𝓝 1) /- [standing] -/)
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃ s, F s = q := by
  obtain ⟨a, ha⟩ := (h0.eventually (gt_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := (h1.eventually (lt_mem_nhds hq1)).exists
  have hab : a ≤ b := by
    by_contra hn
    have := hm (le_of_lt (lt_of_not_ge hn))
    linarith
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha.le, hb.le⟩
  exact ⟨s, hs⟩

/-- The order-one Fredholm CDF attains each probability strictly between zero and one. -/
theorem TW1R_quantile_exists
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃ s, TW1R s = q :=
  continuous_cdf_quantile_exists TW1R TW1R_continuous monotone_TW1R
    TW1R_tendsto_atBot_zero_unconditional TW1R_tendsto_atTop_one q hq0 hq1

/-- The order-two Fredholm CDF attains each probability strictly between zero and one. -/
theorem TW2R_quantile_exists
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃ s, TW2R s = q :=
  continuous_cdf_quantile_exists TW2R TW2R_continuous TW2R_monotone
    TW2R_tendsto_atBot_zero_unconditional TW2R_tendsto_atTop_one q hq0 hq1

/-- The order-one Fredholm CDF has a finite cutoff with value one half. -/
theorem TW1R_median_exists : ∃ s, TW1R s = 1/2 :=
  TW1R_quantile_exists (1/2) (by norm_num) (by norm_num)

/-- The order-two Fredholm CDF has a finite cutoff with value one half. -/
theorem TW2R_median_exists : ∃ s, TW2R s = 1/2 :=
  TW2R_quantile_exists (1/2) (by norm_num) (by norm_num)

/-- The CDF, probability and interior-quantile premises hold simultaneously for both genuine Fredholm laws. -/
theorem cdf_all_binder_joint_probe :
    Continuous TW1R ∧ Monotone TW1R ∧ Tendsto TW1R atBot (𝓝 0) ∧
    Tendsto TW1R atTop (𝓝 1) ∧ (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧
    IsProbabilityMeasure TW1Measure ∧ IsProbabilityMeasure TW2Measure ∧
    (∀ s, cdf TW1Measure s = TW1R s ∧ cdf TW2Measure s = TW2R s) ∧
    (∃ s, TW1Measure (Iic s) = ENNReal.ofReal (1/2)) ∧
    (∃ s, TW2Measure (Iic s) = ENNReal.ofReal (1/2)) := by
  obtain ⟨s1, h1⟩ := TW1R_median_exists
  obtain ⟨s2, h2⟩ := TW2R_median_exists
  refine ⟨TW1R_continuous, monotone_TW1R, TW1R_tendsto_atBot_zero_unconditional,
    TW1R_tendsto_atTop_one, by norm_num, by norm_num,
    TW1Measure_probability, TW2Measure_probability,
    fun s => ⟨TW1Measure_cdf s, TW2Measure_cdf s⟩, ?_, ?_⟩
  · exact ⟨s1, by rw [TW1Measure_Iic, h1]⟩
  · exact ⟨s2, by rw [TW2Measure_Iic, h2]⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW1CDF
#print axioms RMTFoundations.TracyWidom.TW2CDF
#print axioms RMTFoundations.TracyWidom.TW1Measure
#print axioms RMTFoundations.TracyWidom.TW2Measure
#print axioms RMTFoundations.TracyWidom.TW1Measure_probability
#print axioms RMTFoundations.TracyWidom.TW2Measure_probability
#print axioms RMTFoundations.TracyWidom.TW1Measure_cdf
#print axioms RMTFoundations.TracyWidom.TW2Measure_cdf
#print axioms RMTFoundations.TracyWidom.TW1Measure_Iic
#print axioms RMTFoundations.TracyWidom.TW2Measure_Iic
#print axioms RMTFoundations.TracyWidom.TW1Measure_unique
#print axioms RMTFoundations.TracyWidom.TW2Measure_unique
#print axioms RMTFoundations.TracyWidom.continuous_cdf_quantile_exists
#print axioms RMTFoundations.TracyWidom.TW1R_quantile_exists
#print axioms RMTFoundations.TracyWidom.TW2R_quantile_exists
#print axioms RMTFoundations.TracyWidom.TW1R_median_exists
#print axioms RMTFoundations.TracyWidom.TW2R_median_exists
#print axioms RMTFoundations.TracyWidom.cdf_all_binder_joint_probe
