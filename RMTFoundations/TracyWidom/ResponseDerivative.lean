import RMTFoundations.TracyWidom.AiryBoundaryDerivative
import RMTFoundations.TracyWidom.AiryNormDerivative
import RMTFoundations.TracyWidom.ResolventCoordinates



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.ResponseDerivative

open MeasureTheory InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.AiryBoundaryDerivative
open RMTFoundations.TracyWidom.AiryNormDerivative

/-- The actual L2 Airy response under the square-kernel inverse. -/
noncomputable def responseVector
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure :=
  Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s)

/-- The actual derivative-source response. -/
noncomputable def derivativeResponseVector
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure :=
  Ring.inverse (1 - airyKernelShift s) (airyBoundaryDerivative s)

/-- The physical second scalar coordinate. -/
noncomputable def resolventV
    (s : ℝ) -- [definition]
    : ℝ := inner ℝ (airyBoundaryVector s) (derivativeResponseVector s)

/-- Actual L2 first-order response identity Q'=P-uQ. Evaluation at an endpoint
requires an independently justified continuous representative. -/
theorem hasDerivAt_responseVector
    (s : ℝ) -- [definition]
    : HasDerivAt responseVector
      (derivativeResponseVector s - resolventU s • responseVector s) s := by
  have h := (hasDerivAt_airyKernelResolvent_rankOne s).clm_apply
    (hasDerivAt_airyBoundaryVector s)
  convert! h using 1
  change derivativeResponseVector s - resolventU s • responseVector s =
    (-RMTFoundations.Airy.rankOne ℝ (responseVector s) (responseVector s)) (airyBoundaryVector s) +
      derivativeResponseVector s
  simp only [neg_apply, rankOne_apply]
  rw [← real_inner_comm (responseVector s) (airyBoundaryVector s)]
  change derivativeResponseVector s - resolventU s • responseVector s =
    -(resolventU s • responseVector s) + derivativeResponseVector s
  abel

/-- The genuine scalar derivative u'=2v-u^2 from L2 calculus and inverse symmetry. -/
theorem hasDerivAt_resolventU
    (s : ℝ) -- [definition]
    : HasDerivAt resolventU (2 * resolventV s - (resolventU s)^2) s := by
  have h := (hasDerivAt_airyBoundaryVector s).inner ℝ (hasDerivAt_responseVector s)
  have hp : inner ℝ (airyBoundaryDerivative s) (responseVector s) = resolventV s := by
    rw [responseVector, ← airyKernelResolvent_symmetric]
    rw [real_inner_comm]
    rfl
  convert! h using 1
  simp only [inner_sub_right, real_inner_smul_right, hp]
  change 2 * resolventV s - (resolventU s)^2 =
    (resolventV s - resolventU s * resolventU s) + resolventV s
  ring

/-- Both responses are nonzero in the genuine shift-zero Airy instance. -/
theorem response_derivative_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧
      responseVector 0 ≠ 0 ∧ derivativeResponseVector 0 ≠ 0 ∧
      HasDerivAt responseVector
        (derivativeResponseVector 0 - resolventU 0 • responseVector 0) 0 ∧
      HasDerivAt resolventU (2 * resolventV 0 - (resolventU 0)^2) 0 := by
  have hQ : responseVector 0 ≠ 0 := by
    intro hz
    have h := contraction_ringInverse_right (airyKernelShift 0)
      (norm_airyKernelShift_lt_one 0) (airyBoundaryVector 0)
    change responseVector 0 - airyKernelShift 0 (responseVector 0) = airyBoundaryVector 0 at h
    exact airyBoundaryVector_ne_zero 0 (by simpa [hz] using h.symm)
  have hP : derivativeResponseVector 0 ≠ 0 := by
    intro hz
    have h := contraction_ringInverse_right (airyKernelShift 0)
      (norm_airyKernelShift_lt_one 0) (airyBoundaryDerivative 0)
    change derivativeResponseVector 0 - airyKernelShift 0 (derivativeResponseVector 0) =
      airyBoundaryDerivative 0 at h
    exact airyBoundaryDerivative_zero_ne (by simpa [hz] using h.symm)
  exact ⟨airyBoundaryVector_ne_zero 0, airyBoundaryDerivative_zero_ne, hQ, hP,
    hasDerivAt_responseVector 0, hasDerivAt_resolventU 0⟩

end RMTFoundations.TracyWidom.ResponseDerivative

#print axioms RMTFoundations.TracyWidom.ResponseDerivative.responseVector
#print axioms RMTFoundations.TracyWidom.ResponseDerivative.derivativeResponseVector
#print axioms RMTFoundations.TracyWidom.ResponseDerivative.resolventV
#print axioms RMTFoundations.TracyWidom.ResponseDerivative.hasDerivAt_responseVector
#print axioms RMTFoundations.TracyWidom.ResponseDerivative.hasDerivAt_resolventU
#print axioms RMTFoundations.TracyWidom.ResponseDerivative.response_derivative_all_binder_joint_probe
