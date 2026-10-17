import RMTFoundations.TracyWidom.Probability
import RMTFoundations.TracyWidom.Distribution


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The GOE CDF as Mathlib's monotone, right-continuous Stieltjes function. -/
noncomputable abbrev TW1Stieltjes : StieltjesFunction ℝ := TW1CDF
/-- The GUE CDF as Mathlib's monotone, right-continuous Stieltjes function. -/
noncomputable abbrev TW2Stieltjes : StieltjesFunction ℝ := TW2CDF
/-- Register the shared GOE measure's proved total mass one. -/
instance isProbabilityMeasure_TW1Measure : IsProbabilityMeasure TW1Measure :=
  TW1Measure_probability
/-- Register the shared GUE measure's proved total mass one. -/
instance isProbabilityMeasure_TW2Measure : IsProbabilityMeasure TW2Measure :=
  TW2Measure_probability
/-- Bundled GOE law, sharing the exact measure used in TW1Measure. -/
noncomputable def TW1Law : ProbabilityMeasure ℝ := ⟨TW1Measure, inferInstance⟩
/-- Bundled GUE law, sharing the exact measure used in TW2Measure. -/
noncomputable def TW2Law : ProbabilityMeasure ℝ := ⟨TW2Measure, inferInstance⟩
/-- Literal agreement between the bundled GOE law and its measure. -/
theorem TW1Law_toMeasure : (TW1Law : Measure ℝ) = TW1Measure := rfl
/-- Literal agreement between the bundled GUE law and its measure. -/
theorem TW2Law_toMeasure : (TW2Law : Measure ℝ) = TW2Measure := rfl
/-- Mathlib's canonical CDF of the GOE measure agrees with TW1R. -/
theorem cdf_TW1Measure (s : ℝ /- [definition] -/) : cdf TW1Measure s = TW1R s :=
  TW1Measure_cdf s
/-- Mathlib's canonical CDF of the GUE measure agrees with TW2R. -/
theorem cdf_TW2Measure (s : ℝ /- [definition] -/) : cdf TW2Measure s = TW2R s :=
  TW2Measure_cdf s
/-- The GOE measure gives strictly intermediate mass to each finite lower half-line. -/
theorem TW1Measure_Iic_bounds (s : ℝ /- [definition] -/) :
    0 < TW1Measure (Iic s) ∧ TW1Measure (Iic s) < 1 := by
  rw [TW1Measure_Iic]
  exact ⟨ENNReal.ofReal_pos.mpr (TW1R_bounds s).1,
    ENNReal.ofReal_lt_one.mpr (TW1R_bounds s).2⟩
/-- All constructions coexist; both laws have a finite half-line of mass one half. -/
theorem measures_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      IsProbabilityMeasure TW1Measure ∧ IsProbabilityMeasure TW2Measure ∧
      (TW1Law : Measure ℝ) = TW1Measure ∧ (TW2Law : Measure ℝ) = TW2Measure ∧
      (∀ s : ℝ, cdf TW1Measure s = TW1R s ∧ cdf TW2Measure s = TW2R s ∧
        TW1Measure (Iic s) = ENNReal.ofReal (TW1R s) ∧
        TW2Measure (Iic s) = ENNReal.ofReal (TW2R s)) ∧
      (∃ s : ℝ, TW1Measure (Iic s) = ENNReal.ofReal (1/2 : ℝ)) ∧
      (∃ s : ℝ, TW2Measure (Iic s) = ENNReal.ofReal (1/2 : ℝ)) := by
  obtain ⟨s1,h1⟩ := TW1R_median_exists
  obtain ⟨s2,h2⟩ := TW2R_median_exists
  exact ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne', inferInstance, inferInstance,
    TW1Law_toMeasure, TW2Law_toMeasure,
    fun s => ⟨cdf_TW1Measure s, cdf_TW2Measure s, TW1Measure_Iic s, TW2Measure_Iic s⟩,
    ⟨s1, by rw [TW1Measure_Iic,h1]⟩, ⟨s2, by rw [TW2Measure_Iic,h2]⟩⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW1Stieltjes
#print axioms RMTFoundations.TracyWidom.TW2Stieltjes
#print axioms RMTFoundations.TracyWidom.isProbabilityMeasure_TW1Measure
#print axioms RMTFoundations.TracyWidom.isProbabilityMeasure_TW2Measure
#print axioms RMTFoundations.TracyWidom.TW1Law
#print axioms RMTFoundations.TracyWidom.TW2Law
#print axioms RMTFoundations.TracyWidom.TW1Law_toMeasure
#print axioms RMTFoundations.TracyWidom.TW2Law_toMeasure
#print axioms RMTFoundations.TracyWidom.cdf_TW1Measure
#print axioms RMTFoundations.TracyWidom.cdf_TW2Measure
#print axioms RMTFoundations.TracyWidom.TW1Measure_Iic_bounds
#print axioms RMTFoundations.TracyWidom.measures_all_binder_joint_probe
