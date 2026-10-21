import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWLogRegularity1
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
theorem hasDerivAt_deriv_log_TW1R
    (s : ℝ /- [definition] -/) :
    HasDerivAt (deriv (fun t => Real.log (TW1R t))) ((resolventP s - resolventU s * resolventQ s - (resolventQ s)^2) / 2) s := by
  have he : deriv (fun t => Real.log (TW1R t)) = fun s => (resolventQ s + resolventU s) / 2 :=
    funext fun s => (hasDerivAt_log_TW1R_coordinates s).deriv
  rw [he]
  simpa only [Pi.add_apply, sub_eq_add_neg] using
    ((hasDerivAt_resolventQ s).add (hasDerivAt_resolventU_negative_q_sq s)).div_const 2

/-- The logarithm of the physical CDF is C2 on the entire line. -/
theorem log_TW1R_contDiff_two : ContDiff ℝ 2 (fun t => Real.log (TW1R t)) := by
  have hq : Continuous resolventQ :=
    (show Differentiable ℝ resolventQ from fun s => (hasDerivAt_resolventQ s).differentiableAt).continuous
  have hp : Continuous resolventP :=
    (show Differentiable ℝ resolventP from fun s => (hasDerivAt_resolventP s).differentiableAt).continuous
  have hu := resolventU_continuous
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun s => (hasDerivAt_log_TW1R_coordinates s).differentiableAt, ?_, ?_⟩
  · simp
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hasDerivAt_deriv_log_TW1R s).differentiableAt, ?_⟩
    have he : deriv (deriv (fun t => Real.log (TW1R t))) = fun s => (resolventP s - resolventU s * resolventQ s - (resolventQ s)^2) / 2 :=
      funext fun s => (hasDerivAt_deriv_log_TW1R s).deriv
    rw [he]
    exact ((hp.sub (hu.mul hq)).sub (hq.pow 2)).div_const 2

/-- The entire derivative family holds in one physical nonzero model. -/
theorem log_regular_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ 0 < TW1Density (-3) ∧
    (∀ s : ℝ, HasDerivAt (deriv (fun t => Real.log (TW1R t))) ((resolventP s - resolventU s * resolventQ s - (resolventQ s)^2) / 2) s) ∧
    ContDiff ℝ 2 (fun t => Real.log (TW1R t)) :=
  ⟨airyBoundaryVector_ne_zero (-3), TW1Density_positive (-3),
    hasDerivAt_deriv_log_TW1R, log_TW1R_contDiff_two⟩

end RMTFoundations.TracyWidom.TWLogRegularity1

#print axioms RMTFoundations.TracyWidom.TWLogRegularity1.hasDerivAt_deriv_log_TW1R
#print axioms RMTFoundations.TracyWidom.TWLogRegularity1.log_TW1R_contDiff_two
#print axioms RMTFoundations.TracyWidom.TWLogRegularity1.log_regular_all_binder_joint_probe
