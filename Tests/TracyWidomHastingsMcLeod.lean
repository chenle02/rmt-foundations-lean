import RMTFoundations.TracyWidom.HastingsMcLeod
import RMTFoundations.TracyWidom.HMVolterraRepresentation
import RMTFoundations.TracyWidom.HMAsymptotic
set_option autoImplicit false
namespace Tests.TracyWidomHastingsMcLeod
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom

/-- The unique nonzero response and both TW integral formulas use the same actual function. -/
theorem canonical_formulas_joint_probe :
    Painleve.q ≠ 0 ∧ Differentiable ℝ Painleve.q ∧
    (∀ s, HasDerivAt (deriv Painleve.q) (s*Painleve.q s+2*(Painleve.q s)^3) s) ∧
    Tendsto (fun s => Painleve.q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) ∧
    (∀ s, IntegrableOn Painleve.q (Ioi s) ∧
      IntegrableOn (fun t => (Painleve.q t)^2) (Ioi s) ∧
      IntegrableOn (fun t => (t-s)*(Painleve.q t)^2) (Ioi s)) ∧
    (∀ s, TW2R s=Real.exp (-(∫ t in Ioi s,(t-s)*(Painleve.q t)^2))) ∧
    (∀ s, TW1R s^2=TW2R s*Real.exp (-(∫ t in Ioi s,Painleve.q t))) := by
  obtain ⟨q,r,hnq,_,_,_,_,_,_,_,_,he⟩ := HastingsMcLeod.all_binder_joint_probe
  have hn : Painleve.q ≠ 0 := by simpa only [he] using hnq
  exact ⟨hn,Painleve.differentiable_q,Painleve.hasDerivAt_deriv_q,
    Painleve.tendsto_q_div_Ai_atTop,Painleve.integrable_tails,
    Painleve.TW2R_integral_formula,Painleve.TW1R_squared_integral_formula⟩

/-- The public uniqueness theorem has exactly the classical ODE and relative normalization binders. -/
theorem normalized_solution_consumer
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) /- [standing] -/) :
    q=Painleve.q := HastingsMcLeod.eq_canonical q hq hqq hnq
end Tests.TracyWidomHastingsMcLeod

#print axioms Tests.TracyWidomHastingsMcLeod.canonical_formulas_joint_probe
#print axioms Tests.TracyWidomHastingsMcLeod.normalized_solution_consumer
