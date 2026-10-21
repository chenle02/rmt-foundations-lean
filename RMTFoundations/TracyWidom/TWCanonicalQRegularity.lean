import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWCanonicalQRegularity
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus RMTFoundations.TracyWidom.PhysicalPainleveII
open RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

/-- Independent direct second-order regularity of the canonical PII solution. -/
theorem canonical_q_contDiff_two : ContDiff ℝ 2 resolventQ := by
  have dq : Differentiable ℝ resolventQ := fun s => (hasDerivAt_resolventQ s).differentiableAt
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨dq, ?_, contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩⟩
  · simp
  · exact fun s => (hasDerivAt_deriv_resolventQ s).differentiableAt
  · have he : deriv (deriv resolventQ) = fun s => s * resolventQ s + 2 * (resolventQ s)^3 :=
      funext fun s => (hasDerivAt_deriv_resolventQ s).deriv
    rw [he]
    exact (continuous_id.mul dq.continuous).add (continuous_const.mul (dq.continuous.pow 3))

/-- The direct PII route is inhabited by the actual nonzero endpoint response. -/
theorem q_C2_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
    (∀ s : ℝ, HasDerivAt (deriv resolventQ) (s * resolventQ s + 2 * (resolventQ s)^3) s) ∧
    ContDiff ℝ 2 resolventQ :=
  ⟨airyBoundaryVector_ne_zero 0, response_derivative_all_binder_joint_probe.2.2.1,
    hasDerivAt_deriv_resolventQ, canonical_q_contDiff_two⟩

end RMTFoundations.TracyWidom.TWCanonicalQRegularity

#print axioms RMTFoundations.TracyWidom.TWCanonicalQRegularity.canonical_q_contDiff_two
#print axioms RMTFoundations.TracyWidom.TWCanonicalQRegularity.q_C2_all_binder_joint_probe
