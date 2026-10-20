import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWLogRegularity2
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus RMTFoundations.TracyWidom.PhysicalPainleveII
open RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

open RMTFoundations.TracyWidom.OrderTwoLogDerivative

/-- The actual log CDF has the second derivative furnished by the endpoint system. -/
theorem hasDerivAt_deriv_log_TW2R
    (s : ℝ /- [definition] -/) :
    HasDerivAt (deriv (fun t => Real.log (TW2R t))) (-(resolventQ s)^2) s := by
  have he : deriv (fun t => Real.log (TW2R t)) = fun s => resolventU s :=
    funext fun s => (hasDerivAt_log_TW2R_coordinates s).deriv
  rw [he]
  exact hasDerivAt_resolventU_negative_q_sq s

/-- The logarithm of the physical CDF is C2 on the entire line. -/
theorem log_TW2R_contDiff_two : ContDiff ℝ 2 (fun t => Real.log (TW2R t)) := by
  have hq : Continuous resolventQ :=
    (show Differentiable ℝ resolventQ from fun s => (hasDerivAt_resolventQ s).differentiableAt).continuous
  have hp : Continuous resolventP :=
    (show Differentiable ℝ resolventP from fun s => (hasDerivAt_resolventP s).differentiableAt).continuous
  have hu := resolventU_continuous
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun s => (hasDerivAt_log_TW2R_coordinates s).differentiableAt, ?_, ?_⟩
  · simp
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hasDerivAt_deriv_log_TW2R s).differentiableAt, ?_⟩
    have he : deriv (deriv (fun t => Real.log (TW2R t))) = fun s => -(resolventQ s)^2 :=
      funext fun s => (hasDerivAt_deriv_log_TW2R s).deriv
    rw [he]
    exact hq.pow 2 |>.neg

/-- The entire derivative family holds in one physical nonzero model. -/
theorem log_regular_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ 0 < TW2Density (-3) ∧
    (∀ s : ℝ, HasDerivAt (deriv (fun t => Real.log (TW2R t))) (-(resolventQ s)^2) s) ∧
    ContDiff ℝ 2 (fun t => Real.log (TW2R t)) :=
  ⟨airyBoundaryVector_ne_zero (-3), TW2Density_positive (-3),
    hasDerivAt_deriv_log_TW2R, log_TW2R_contDiff_two⟩

end RMTFoundations.TracyWidom.TWLogRegularity2

#print axioms RMTFoundations.TracyWidom.TWLogRegularity2.hasDerivAt_deriv_log_TW2R
#print axioms RMTFoundations.TracyWidom.TWLogRegularity2.log_TW2R_contDiff_two
#print axioms RMTFoundations.TracyWidom.TWLogRegularity2.log_regular_all_binder_joint_probe
