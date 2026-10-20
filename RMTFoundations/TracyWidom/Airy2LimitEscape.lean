import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitEscape
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability

/-- A literal counterinstance to bare pointwise-limit probability construction.
The measures are genuine, but escape to positive infinity. -/
noncomputable def escapingLaw (n : ℕ /- [definition] -/) :
    ProbabilityMeasure (Fin 1 → ℝ) := ⟨Measure.dirac (fun _ => (n : ℝ)), inferInstance⟩

theorem escapingLaw_cdf_limit : ∀ s : Fin 1 → ℝ,
    Tendsto (fun n => jointCDF 1 (escapingLaw n) s) atTop (𝓝 0) := by
  intro s
  obtain ⟨N,hN⟩ := exists_nat_gt (s 0)
  have he : (fun n => jointCDF 1 (escapingLaw n) s) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : s 0 < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hx : (fun _ : Fin 1 => (n : ℝ)) ∉ lowerBox 1 s := by
      intro hx
      exact (not_le.mpr h) (hx 0)
    simp [jointCDF,escapingLaw,Measure.real,hx]
  exact tendsto_const_nhds.congr' he.symm

theorem zero_is_not_probability_cdf :
    ¬ ∃ ν : ProbabilityMeasure (Fin 1 → ℝ), ∀ s, jointCDF 1 ν s = 0 := by
  rintro ⟨ν,hν⟩
  have ht := jointCDF_common_atTop 1 ν ν.prop
  simp only [hν] at ht
  have hf : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at hf

/-- All pointwise-limit and continuity binders are jointly satisfiable while law
existence fails. This is a generic escape counterexample, not physical Airy2. -/
theorem escaping_all_binder_joint_counterinstance :
    (∀ n, IsProbabilityMeasure (escapingLaw n : Measure (Fin 1 → ℝ))) ∧
    (∀ s, Tendsto (fun n => jointCDF 1 (escapingLaw n) s) atTop (𝓝 0)) ∧
    Continuous (fun _ : Fin 1 → ℝ => (0 : ℝ)) ∧
    ¬ (∃ ν : ProbabilityMeasure (Fin 1 → ℝ), ∀ s, jointCDF 1 ν s = 0) := by
  exact ⟨fun n => (escapingLaw n).prop,escapingLaw_cdf_limit,continuous_const,
    zero_is_not_probability_cdf⟩
end RMTFoundations.TracyWidom.Airy2LimitEscape

#print axioms RMTFoundations.TracyWidom.Airy2LimitEscape.escapingLaw
#print axioms RMTFoundations.TracyWidom.Airy2LimitEscape.escapingLaw_cdf_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitEscape.zero_is_not_probability_cdf
#print axioms RMTFoundations.TracyWidom.Airy2LimitEscape.escaping_all_binder_joint_counterinstance
