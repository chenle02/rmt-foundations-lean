import RMTFoundations.TracyWidom.EndpointCalculus
import RMTFoundations.TracyWidom.AiryBoundarySecondDerivative
import RMTFoundations.TracyWidom.AiryWeightedResponse
import RMTFoundations.TracyWidom.AiryWeightedEndpointRow
import RMTFoundations.TracyWidom.PIIReduction



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.PhysicalPainleveII

open MeasureTheory Filter InnerProductSpace
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.ResponseDerivative RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.AiryBoundarySecondDerivative
open RMTFoundations.TracyWidom.AiryWeightedResponse RMTFoundations.TracyWidom.AiryWeightedEndpointRow
open RMTFoundations.TracyWidom.AiryEndpointRowDerivative RMTFoundations.TracyWidom.AiryNormDerivative
open RMTFoundations.TracyWidom

/-- Actual derivative-source response calculus, before invoking the multiplication commutator. -/
theorem hasDerivAt_derivativeResponseVector
    (s : ℝ) -- [definition]
    : HasDerivAt derivativeResponseVector
      (-resolventV s • responseVector s +
        Ring.inverse (1-airyKernelShift s)
          (RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector s)) s := by
  have h := (hasDerivAt_airyKernelResolvent_rankOne s).clm_apply
    (hasDerivAt_airyBoundaryDerivative s)
  convert! h using 1
  change -resolventV s • responseVector s +
      Ring.inverse (1-airyKernelShift s)
        (RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector s) =
    (-RMTFoundations.Airy.rankOne ℝ (responseVector s) (responseVector s))
        (airyBoundaryDerivative s) +
      Ring.inverse (1-airyKernelShift s)
        (RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector s)
  simp only [neg_apply, rankOne_apply]
  rw [← real_inner_comm (responseVector s) (airyBoundaryDerivative s),
    derivative_source_response_pairing]
  simp only [neg_smul]

/-- Endpoint pairing with MQ is an actual weighted integral, never a formal application
of an unbounded multiplication operator to an arbitrary L2 vector. -/
theorem endpoint_weighted_response_pairing
    (s : ℝ) -- [definition]
    : inner ℝ (boundaryKernelRow s) (weightedResponseVector s) =
      deriv airyAiReal s * resolventU s - airyAiReal s * resolventV s := by
  have he : inner ℝ (boundaryKernelRow s) (weightedResponseVector s) =
      inner ℝ (weightedEndpointRow s) (responseVector s) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [weightedResponseVector_apply_ae s,
      weightedEndpointRow_eq_mul_endpointRow_ae s] with x hM hrow
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hM,hrow]
    change (x*(responseVector s) x)*(airyEndpointRow s x) =
      (responseVector s) x*(x*(airyEndpointRow s x))
    ring
  rw [he,weightedEndpointRow,inner_sub_left,real_inner_smul_left,real_inner_smul_left]
  rw [derivative_source_response_pairing]
  rfl

/-- The physical endpoint-source derivative p'=sq+up-2vq follows from the genuine
Airy ODE vector and the multiplication-domain commutator. -/
theorem hasDerivAt_resolventP
    (s : ℝ) -- [definition]
    : HasDerivAt resolventP
      (s*resolventQ s + resolventU s*resolventP s - 2*resolventV s*resolventQ s) s := by
  have h := (hasDerivAt_deriv_airyAiReal' s).fun_add
    ((hasDerivAt_boundaryKernelRow s).inner ℝ
      (hasDerivAt_derivativeResponseVector s))
  have he : (fun t => deriv airyAiReal t +
      inner ℝ (boundaryKernelRow t) (derivativeResponseVector t)) = resolventP := rfl
  rw [he] at h
  convert! h using 1
  rw [inverse_airyBoundaryODEVector]
  simp only [inner_add_right,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  rw [endpoint_weighted_response_pairing]
  rw [resolventQ_eq_scalar_endpoint,resolventP]
  change s*(airyAiReal s+inner ℝ (boundaryKernelRow s) (responseVector s)) +
      resolventU s*(deriv airyAiReal s+inner ℝ (boundaryKernelRow s) (derivativeResponseVector s)) -
      2*resolventV s*(airyAiReal s+inner ℝ (boundaryKernelRow s) (responseVector s)) = _
  unfold resolventV
  ring

/-- The actual Fredholm endpoint coordinate satisfies Painleve II at every real shift.
The relative Airy asymptotic is a separate analytic theorem. -/
theorem hasDerivAt_deriv_resolventQ
    (s : ℝ) -- [definition]
    : HasDerivAt (deriv resolventQ) (s*resolventQ s+2*(resolventQ s)^3) s :=
  hasDerivAt_deriv_tw_painleveII resolventQ resolventP resolventU resolventV s
    (Eventually.of_forall hasDerivAt_resolventQ) (hasDerivAt_resolventP s)
    (hasDerivAt_resolventU_negative_q_sq s) (resolvent_first_integral s)

/-- Unconditional PII for the canonical physical Fredholm coordinate. -/
theorem deriv_deriv_resolventQ
    (s : ℝ) -- [definition]
    : deriv (deriv resolventQ) s = s*resolventQ s+2*(resolventQ s)^3 :=
  (hasDerivAt_deriv_resolventQ s).deriv

/-- The physical model realizes all inputs of the abstract reduction simultaneously;
its source, derivative source and response are nonzero. -/
theorem physical_painleveII_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      0 < resolventU 0 ∧
      (∀ s : ℝ, HasDerivAt resolventQ (resolventP s-resolventU s*resolventQ s) s) ∧
      (∀ s : ℝ, HasDerivAt resolventP
        (s*resolventQ s+resolventU s*resolventP s-2*resolventV s*resolventQ s) s) ∧
      (∀ s : ℝ, HasDerivAt resolventU (-(resolventQ s)^2) s) ∧
      (∀ s : ℝ, (resolventU s)^2-2*resolventV s=(resolventQ s)^2) ∧
      (∀ s : ℝ, deriv (deriv resolventQ) s=s*resolventQ s+2*(resolventQ s)^3) :=
  ⟨airyBoundaryVector_ne_zero 0,airyBoundaryDerivative_zero_ne,
    response_derivative_all_binder_joint_probe.2.2.1,airy_inverse_square_boundary_positive 0,
    hasDerivAt_resolventQ,hasDerivAt_resolventP,hasDerivAt_resolventU_negative_q_sq,
    resolvent_first_integral,deriv_deriv_resolventQ⟩

end RMTFoundations.TracyWidom.PhysicalPainleveII

#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.hasDerivAt_derivativeResponseVector
#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.endpoint_weighted_response_pairing
#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.hasDerivAt_resolventP
#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.hasDerivAt_deriv_resolventQ
#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.deriv_deriv_resolventQ
#print axioms RMTFoundations.TracyWidom.PhysicalPainleveII.physical_painleveII_all_binder_joint_probe
