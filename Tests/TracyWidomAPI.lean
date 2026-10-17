import RMTFoundations.TracyWidom.Measures


set_option autoImplicit false
namespace RMTFoundations.TracyWidomTests
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom

/-- The public headline names are jointly usable by an ordinary native theorem. -/
theorem distribution_interface :
    Monotone TW1R ∧ Monotone TW2R ∧ Continuous TW1R ∧ Continuous TW2R ∧
    Tendsto TW1R atBot (𝓝 0) ∧ Tendsto TW2R atBot (𝓝 0) ∧
    Tendsto TW1R atTop (𝓝 1) ∧ Tendsto TW2R atTop (𝓝 1) :=
  ⟨monotone_TW1R, monotone_TW2R, continuous_TW1R, continuous_TW2R,
    tendsto_TW1R_atBot, tendsto_TW2R_atBot, tendsto_TW1R_atTop, tendsto_TW2R_atTop⟩

/-- Registered instances and bundled measures agree in the public namespace. -/
theorem probability_interface :
    IsProbabilityMeasure TW1Measure ∧ IsProbabilityMeasure TW2Measure ∧
    (TW1Law : Measure ℝ) = TW1Measure ∧ (TW2Law : Measure ℝ) = TW2Measure :=
  ⟨inferInstance, inferInstance, TW1Law_toMeasure, TW2Law_toMeasure⟩

/-- All uniqueness binders have one genuine nondegenerate joint instance. -/
theorem uniqueness_joint_probe :
    ∃ μ ν : Measure ℝ, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      (∀ s, cdf μ s = TW1R s) ∧ (∀ s, cdf ν s = TW2R s) ∧
      μ = TW1Measure ∧ ν = TW2Measure ∧
      (∃ s, μ (Iic s) = ENNReal.ofReal (1/2 : ℝ)) ∧
      (∃ s, ν (Iic s) = ENNReal.ofReal (1/2 : ℝ)) := by
  obtain ⟨s1, h1⟩ := TW1R_median_exists
  obtain ⟨s2, h2⟩ := TW2R_median_exists
  refine ⟨TW1Measure, TW2Measure, inferInstance, inferInstance,
    TW1Measure_cdf, TW2Measure_cdf, ?_, ?_, ?_, ?_⟩
  · exact TW1Measure_unique TW1Measure inferInstance TW1Measure_cdf
  · exact TW2Measure_unique TW2Measure inferInstance TW2Measure_cdf
  · exact ⟨s1, by rw [TW1Measure_Iic, h1]⟩
  · exact ⟨s2, by rw [TW2Measure_Iic, h2]⟩
end RMTFoundations.TracyWidomTests

#print axioms RMTFoundations.TracyWidomTests.distribution_interface
#print axioms RMTFoundations.TracyWidomTests.probability_interface
#print axioms RMTFoundations.TracyWidomTests.uniqueness_joint_probe
