import RMTFoundations.TracyWidom.ResolventDiagonal
import RMTFoundations.TracyWidom.ResponseDerivative
import RMTFoundations.TracyWidom.AiryEndpointRowDerivative
import RMTFoundations.TracyWidom.ScalarResolventDerivative



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.EndpointCalculus

open MeasureTheory InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.AiryNormDerivative
open RMTFoundations.TracyWidom.ResolventDiagonal RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.AiryEndpointRowDerivative RMTFoundations.TracyWidom.AiryBoundaryDerivative
open RMTFoundations.TracyWidom

/-- Physical endpoint derivative-source coordinate, defined by the scalar row formula. -/
noncomputable def resolventP
    (s : ℝ) -- [definition]
    : ℝ := deriv airyAiReal s + inner ℝ (boundaryKernelRow s) (derivativeResponseVector s)

/-- The genuine endpoint kernel row has its rank-one norm derivative. -/
theorem hasDerivAt_boundaryKernelRow
    (s : ℝ) -- [definition]
    : HasDerivAt boundaryKernelRow ((-airyAiReal s) • airyBoundaryVector s) s := by
  have he : boundaryKernelRow = airyEndpointRow := rfl
  rw [he]
  exact hasDerivAt_airyEndpointRow s

/-- Actual diagonal-resolvent differentiation gives u'=-q². This evaluates
scalar row formulas and never evaluates an arbitrary L2 representative. -/
theorem hasDerivAt_resolventU_negative_q_sq
    (s : ℝ) -- [definition]
    : HasDerivAt resolventU (-(resolventQ s)^2) s := by
  let T := fun t => Ring.inverse (1 - airyKernelShift t)
  let Q := responseVector s
  let U := -RMTFoundations.Airy.rankOne ℝ Q Q
  have he : (fun t => airyEnergy t + inner ℝ (boundaryKernelRow t)
      (T t (boundaryKernelRow t))) = resolventU :=
    funext (fun t => (resolventU_eq_scalar_diagonal t).symm)
  have h := hasDerivAt_scalar_resolvent_kernel airyEnergy boundaryKernelRow
    boundaryKernelRow T U s (airyAiReal s) (airyAiReal s) (airyBoundaryVector s) Q
    (by simpa only [pow_two] using hasDerivAt_airyEnergy s)
    (hasDerivAt_boundaryKernelRow s) (hasDerivAt_boundaryKernelRow s)
    (hasDerivAt_airyKernelResolvent_rankOne s)
    (by simp only [U, neg_apply, rankOne_apply, neg_smul])
    rfl (by exact (airyKernelResolvent_symmetric s (airyBoundaryVector s)
      (boundaryKernelRow s)).symm)
  rw [he] at h
  convert! h using 1
  rw [resolventQ_eq_scalar_endpoint]
  change - (airyAiReal s + inner ℝ (boundaryKernelRow s) Q)^2 =
    -((airyAiReal s + inner ℝ (boundaryKernelRow s) Q) *
      (airyAiReal s + inner ℝ (boundaryKernelRow s) Q))
  ring

/-- Genuine endpoint differentiation gives q'=p-uq on the entire real line. -/
theorem hasDerivAt_resolventQ
    (s : ℝ) -- [definition]
    : HasDerivAt resolventQ (resolventP s - resolventU s * resolventQ s) s := by
  have he : (fun t => airyAiReal t + inner ℝ (boundaryKernelRow t) (responseVector t)) =
      resolventQ := funext (fun t => (resolventQ_eq_scalar_endpoint t).symm)
  have h := (hasDerivAt_airyAiReal' s).fun_add
    ((hasDerivAt_boundaryKernelRow s).inner ℝ (hasDerivAt_responseVector s))
  rw [he] at h
  convert! h using 1
  simp only [real_inner_smul_left, inner_sub_right, real_inner_smul_right]
  rw [resolventQ_eq_scalar_endpoint,resolventP]
  change deriv airyAiReal s + inner ℝ (boundaryKernelRow s) (derivativeResponseVector s) -
      resolventU s * (airyAiReal s + inner ℝ (boundaryKernelRow s) (responseVector s)) =
    deriv airyAiReal s + (inner ℝ (boundaryKernelRow s) (derivativeResponseVector s) -
        resolventU s * inner ℝ (boundaryKernelRow s) (responseVector s) +
          (-airyAiReal s) * resolventU s)
  ring

/-- The two independent actual u derivatives prove the first integral. -/
theorem resolvent_first_integral
    (s : ℝ) -- [definition]
    : (resolventU s)^2 - 2 * resolventV s = (resolventQ s)^2 := by
  have h := (hasDerivAt_resolventU s).unique (hasDerivAt_resolventU_negative_q_sq s)
  linarith

/-- All actual analytic identities coexist in a genuine nonzero Airy model. -/
theorem endpoint_calculus_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧
      airyEndpointRowDerivative 0 ≠ 0 ∧ 0 < resolventU 0 ∧
      HasDerivAt resolventU (-(resolventQ 0)^2) 0 ∧
      HasDerivAt resolventQ (resolventP 0 - resolventU 0 * resolventQ 0) 0 ∧
      (resolventU 0)^2 - 2 * resolventV 0 = (resolventQ 0)^2 := by
  exact ⟨airyBoundaryVector_ne_zero 0, airyBoundaryDerivative_zero_ne,
    airyEndpointRowDerivative_zero_ne, airy_inverse_square_boundary_positive 0,
    hasDerivAt_resolventU_negative_q_sq 0, hasDerivAt_resolventQ 0, resolvent_first_integral 0⟩

end RMTFoundations.TracyWidom.EndpointCalculus

#print axioms RMTFoundations.TracyWidom.EndpointCalculus.resolventP
#print axioms RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_boundaryKernelRow
#print axioms RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_resolventU_negative_q_sq
#print axioms RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_resolventQ
#print axioms RMTFoundations.TracyWidom.EndpointCalculus.resolvent_first_integral
#print axioms RMTFoundations.TracyWidom.EndpointCalculus.endpoint_calculus_all_binder_joint_probe
