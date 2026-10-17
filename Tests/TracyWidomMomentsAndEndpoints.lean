import RMTFoundations.TracyWidom.Moments
import RMTFoundations.TracyWidom.OrderFourEndpoints
import RMTFoundations.TracyWidom.Airy2
import RMTFoundations.TracyWidom.GUEHermite
import RMTFoundations.TracyWidom.GUEIdentification

set_option autoImplicit false
namespace Tests.TracyWidomMomentsAndEndpoints
open MeasureTheory Filter RMTFoundations.TracyWidom
open scoped Topology

/-- Moment, GSE endpoint, singleton Airy2 and growing Hermite APIs coexist on genuine data. -/
theorem moments_endpoints_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
    (∃ a : ℝ, 0 < a ∧
      Integrable (fun x : ℝ => Real.exp (a*|x|)) TW1Measure ∧
      Integrable (fun x : ℝ => Real.exp (a*|x|)) TW2Measure) ∧
    (∀ p : ℝ, 0 ≤ p → Integrable (fun x : ℝ => |x|^p) TW1Measure ∧
      Integrable (fun x : ℝ => |x|^p) TW2Measure) ∧
    Continuous TW4R ∧ Tendsto TW4R atBot (𝓝 0) ∧ Tendsto TW4R atTop (𝓝 1) ∧
    (∃ s : ℝ, TW4R s = 1/2) ∧
    (∀ t s : ℝ, Airy2.oneTimeFredholm t s = TW2 s) ∧
    (∀ N : ℕ, 0 < GUEHermite.hermiteDensity (N+1) (fun i => (i.val : ℝ))) :=
  ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne',
    TW1_TW2_exponential_absolute_integrable,
    fun p hp => ⟨TW1_absolute_moment_integrable p hp,TW2_absolute_moment_integrable p hp⟩,
    continuous_TW4R,tendsto_TW4R_atBot,tendsto_TW4R_atTop,TW4R_half_level_exists,
    Airy2.oneTimeFredholm_eq_TW2,GUEHermite.hermite_density_all_binder_joint_probe.2⟩

/-- GUE transport retains precisely the physical edge-convergence hypothesis. -/
theorem conditional_GUE_consumer
    (hFredholm : GUEIdentification.GUELimit TW2R /- [standing] -/) :
    ∀ s : ℝ, Tendsto (fun n => GUEIdentification.gueCDF n s) atTop (𝓝 (TW2R s)) :=
  GUEIdentification.application_cdf_at_TW2R GUEIdentification.gueCDF TW2R
    hFredholm hFredholm hFredholm
end Tests.TracyWidomMomentsAndEndpoints

#print axioms Tests.TracyWidomMomentsAndEndpoints.moments_endpoints_all_binder_joint_probe
#print axioms Tests.TracyWidomMomentsAndEndpoints.conditional_GUE_consumer
