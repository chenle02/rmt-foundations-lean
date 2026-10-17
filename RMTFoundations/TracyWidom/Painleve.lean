import RMTFoundations.TracyWidom.CanonicalPainleveWitness
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.Functions

/-! Canonical Fredholm response, Painleve II, Airy normalization and integral formulas.
No uniqueness theorem for arbitrary global Painleve II solutions is asserted here. -/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Painleve
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom

/-- The actual endpoint response of the inverse physical Airy-kernel operator. -/
noncomputable abbrev q : ℝ → ℝ := ResolventCoordinates.resolventQ

/-- The canonical response is differentiable on the entire real line. -/
theorem differentiable_q : Differentiable ℝ q :=
  fun s => (EndpointCalculus.hasDerivAt_resolventQ s).differentiableAt

/-- The canonical Fredholm response solves Painleve II at every real cutoff. -/
theorem hasDerivAt_deriv_q (s : ℝ /- [definition] -/) :
    HasDerivAt (deriv q) (s*q s+2*(q s)^3) s :=
  PhysicalPainleveII.hasDerivAt_deriv_resolventQ s

/-- Relative Airy normalization holds at the positive endpoint. -/
theorem tendsto_q_div_Ai_atTop :
    Tendsto (fun s => q s / RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) :=
  HMNormalization.resolventQ_relative_Airy_atTop

/-- The canonical response and its two square tails are absolutely integrable. -/
theorem integrable_tails (s : ℝ /- [definition] -/) :
    IntegrableOn q (Ioi s) ∧ IntegrableOn (fun t => (q t)^2) (Ioi s) ∧
      IntegrableOn (fun t => (t-s)*(q t)^2) (Ioi s) :=
  ⟨IntegralRepresentations.integrableOn_resolventQ s,
    (IntegralRepresentations.resolventQ_square_tail_integrals s).1,
    (IntegralRepresentations.resolventQ_square_tail_integrals s).2.2.1⟩

/-- The genuine GUE Fredholm CDF is the weighted-square Painleve tail exponential. -/
theorem TW2R_integral_formula (s : ℝ /- [definition] -/) :
    TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(q t)^2)) :=
  IntegralRepresentations.TW2R_eq_exp_negative_weighted_square_tail s

/-- The squared GOE CDF is the GUE CDF times the unweighted response tail exponential. -/
theorem TW1R_squared_integral_formula (s : ℝ /- [definition] -/) :
    TW1R s^2 = TW2R s * Real.exp (-(∫ t in Ioi s, q t)) :=
  IntegralRepresentations.TW1R_sq_eq_TW2R_mul_exp_negative_tail s

/-- ODE, normalization, integrability and both formulas coexist in the nonzero physical model. -/
theorem painleve_api_joint_probe :
    RMTFoundations.TWOneBounds.airyBoundaryVector 0 ≠ 0 ∧
    Differentiable ℝ q ∧
    (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
    Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) ∧
    (∀ s, IntegrableOn q (Ioi s) ∧ IntegrableOn (fun t => (q t)^2) (Ioi s) ∧
      IntegrableOn (fun t => (t-s)*(q t)^2) (Ioi s)) ∧
    (∀ s, TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(q t)^2))) ∧
    (∀ s, TW1R s^2 = TW2R s*Real.exp (-(∫ t in Ioi s, q t))) :=
  ⟨RMTFoundations.TWOneBounds.airyBoundaryVector_ne_zero 0,
    differentiable_q, hasDerivAt_deriv_q, tendsto_q_div_Ai_atTop,
    integrable_tails, TW2R_integral_formula, TW1R_squared_integral_formula⟩
end RMTFoundations.TracyWidom.Painleve

#print axioms RMTFoundations.TracyWidom.Painleve.q
#print axioms RMTFoundations.TracyWidom.Painleve.differentiable_q
#print axioms RMTFoundations.TracyWidom.Painleve.hasDerivAt_deriv_q
#print axioms RMTFoundations.TracyWidom.Painleve.tendsto_q_div_Ai_atTop
#print axioms RMTFoundations.TracyWidom.Painleve.integrable_tails
#print axioms RMTFoundations.TracyWidom.Painleve.TW2R_integral_formula
#print axioms RMTFoundations.TracyWidom.Painleve.TW1R_squared_integral_formula
#print axioms RMTFoundations.TracyWidom.Painleve.painleve_api_joint_probe
