import RMTFoundations.TracyWidom.EndpointCalculus



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus

/-- The genuine first integral solves the second scalar coordinate algebraically. -/
theorem resolventV_eq_first_integral
    (s : ℝ) -- [definition]
    : resolventV s = ((resolventU s)^2 - (resolventQ s)^2) / 2 := by
  have h := resolvent_first_integral s
  linarith

/-- Differentiating the actual first integral gives the physical v derivative,
without a further regularity assumption on the second response. -/
theorem hasDerivAt_resolventV
    (s : ℝ) -- [definition]
    : HasDerivAt resolventV (-(resolventP s * resolventQ s)) s := by
  have he : (fun t => ((resolventU t)^2 - (resolventQ t)^2) / 2) = resolventV :=
    funext (fun t => (resolventV_eq_first_integral t).symm)
  have h := (((hasDerivAt_resolventU_negative_q_sq s).pow 2).fun_sub
    ((hasDerivAt_resolventQ s).pow 2)).div_const 2
  simp only [Pi.pow_apply] at h
  rw [he] at h
  convert! h using 1
  ring

/-- The three genuine scalar first-order equations and first integral hold together. -/
theorem physical_first_order_system
    (s : ℝ) -- [definition]
    : HasDerivAt resolventQ (resolventP s - resolventU s * resolventQ s) s ∧
      HasDerivAt resolventU (-(resolventQ s)^2) s ∧
      HasDerivAt resolventV (-(resolventP s * resolventQ s)) s ∧
      (resolventU s)^2 - 2 * resolventV s = (resolventQ s)^2 := by
  exact ⟨hasDerivAt_resolventQ s, hasDerivAt_resolventU_negative_q_sq s,
    hasDerivAt_resolventV s, resolvent_first_integral s⟩

/-- The system coexists globally with genuine nonzero Airy sources and response at zero. -/
theorem physical_first_order_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      (∀ s : ℝ, HasDerivAt resolventV (-(resolventP s * resolventQ s)) s) ∧
      (∀ s : ℝ, (resolventU s)^2 - 2 * resolventV s = (resolventQ s)^2) ∧
      (∀ s : ℝ, HasDerivAt resolventQ (resolventP s - resolventU s * resolventQ s) s ∧
        HasDerivAt resolventU (-(resolventQ s)^2) s) := by
  have hp := response_derivative_all_binder_joint_probe
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hasDerivAt_resolventV, resolvent_first_integral,
    fun s => ⟨hasDerivAt_resolventQ s, hasDerivAt_resolventU_negative_q_sq s⟩⟩

end RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

#print axioms RMTFoundations.TracyWidom.PhysicalFirstOrderSystem.resolventV_eq_first_integral
#print axioms RMTFoundations.TracyWidom.PhysicalFirstOrderSystem.hasDerivAt_resolventV
#print axioms RMTFoundations.TracyWidom.PhysicalFirstOrderSystem.physical_first_order_system
#print axioms RMTFoundations.TracyWidom.PhysicalFirstOrderSystem.physical_first_order_all_binder_joint_probe
