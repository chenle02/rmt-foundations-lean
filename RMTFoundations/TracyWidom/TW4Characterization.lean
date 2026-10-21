import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.OrderFourEndpoints
import RMTFoundations.TracyWidom.Probability
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory ProbabilityTheory
open RMTFoundations.AiryKernel RMTFoundations.TracyWidom.ResolventCoordinates

/-- The positive TW96 scale does not change the monotonicity obligation. -/
theorem TW4R_monotone_iff_raw_monotone : Monotone TW4R ↔ Monotone TW4AiryR := by
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · intro hm a b hab
    have h := hm (div_le_div_of_nonneg_right hab hp.le)
    simpa only [TW4R_raw_scaling] using h
  · intro hm a b hab
    exact hm (mul_le_mul_of_nonneg_left hab hp.le)

/-- Probability-law existence is exactly the still-open physical monotonicity.
This exports a characterization, not an assumed or instantiated GSE law. -/
theorem TW4_probability_exists_iff_monotone :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ s : ℝ, cdf μ s = TW4R s)) ↔
      Monotone TW4R := by
  constructor
  · rintro ⟨μ,hμ,hcdf⟩ a b hab
    letI := hμ
    rw [←hcdf a,←hcdf b]
    exact (cdf μ).mono hab
  · intro hm
    let F : StieltjesFunction ℝ :=
      { toFun := TW4R, mono' := hm,
        right_continuous' := fun s => continuous_TW4R.continuousAt.continuousWithinAt }
    have hp : IsProbabilityMeasure F.measure :=
      F.isProbabilityMeasure tendsto_TW4R_atBot tendsto_TW4R_atTop
    refine ⟨F.measure,hp,?_⟩
    intro s
    have he := cdf_measure_stieltjesFunction F tendsto_TW4R_atBot tendsto_TW4R_atTop
    exact congrArg (fun f : StieltjesFunction ℝ => f s) he

/-- All analytic CDF requirements are discharged except the exact Airy response sign. -/
theorem TW4_probability_exists_iff_resolvent_sign :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ s : ℝ, cdf μ s = TW4R s)) ↔
      ∀ s : ℝ, (hankelDetPlus s-TW1R s)*resolventQ s ≤
        (TW1R s+hankelDetPlus s)*resolventU s := by
  rw [TW4_probability_exists_iff_monotone,TW4R_monotone_iff_raw_monotone,
    TW4AiryR_monotone_iff_resolvent_sign]

/-- This complete characterization is available on the actual nonzero physical model;
no probability-measure witness or physical sign is asserted by the example. -/
theorem TW4_characterization_all_binder_joint_probe :
    0 < TW4R 0 ∧ Continuous TW4R ∧
      (∃ s : ℝ, TW4R s = 1/2) ∧
      ((∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ s : ℝ, cdf μ s = TW4R s)) ↔
        ∀ s : ℝ, (hankelDetPlus s-TW1R s)*resolventQ s ≤
          (TW1R s+hankelDetPlus s)*resolventU s) :=
  ⟨TW4R_positive 0,continuous_TW4R,TW4R_half_level_exists,
    TW4_probability_exists_iff_resolvent_sign⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4R_monotone_iff_raw_monotone
#print axioms RMTFoundations.TracyWidom.TW4_probability_exists_iff_monotone
#print axioms RMTFoundations.TracyWidom.TW4_probability_exists_iff_resolvent_sign
#print axioms RMTFoundations.TracyWidom.TW4_characterization_all_binder_joint_probe
