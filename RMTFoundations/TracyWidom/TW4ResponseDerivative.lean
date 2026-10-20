import RMTFoundations.TracyWidom.TW4CoshDerivative
import RMTFoundations.TracyWidom.EndpointCalculus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom.IntegralRepresentations

/-- The actual response sign, scaled to avoid the exponentially small determinant factor. -/
noncomputable def TW4Response
    (s : ℝ) -- [definition]
    : ℝ := resolventU s-resolventQ s*Real.tanh (TWEndpointTail s/2)

/-- The endpoint-tail derivative uses the physical logarithmic identity. -/
theorem TWEndpointTail_hasDerivAt
    (s : ℝ) -- [definition]
    : HasDerivAt TWEndpointTail (-resolventQ s) s := by
  have he : TWEndpointTail = fun t => Real.log (TW2R t)-Real.log (TW1R t^2) :=
    funext integral_resolventQ_tail
  rw [he]
  have hd := (RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_log_TW2R_coordinates s).sub
    (hasDerivAt_log_TW1R_sq_coordinates s)
  convert! hd using 1 <;> ring

/-- Exact normalization of the GSE derivative by its positive value. -/
theorem TW4AirySlope_eq_value_mul_response
    (s : ℝ) -- [definition]
    : TW4AirySlope s = TW4AiryR s*TW4Response s/2 := by
  rw [TW4AirySlope_eq_cosh_response,TW4AiryR_eq_sqrt_TW2R_cosh_tail,
    TW4Response,Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (TWEndpointTail s/2)).ne']

/-- The physical normalized response derivative, with every coordinate retained. -/
theorem TW4Response_hasDerivAt
    (s : ℝ) -- [definition]
    : HasDerivAt TW4Response
      (-(resolventQ s)^2-
        (resolventP s-resolventU s*resolventQ s)*Real.tanh (TWEndpointTail s/2)+
        (resolventQ s)^2/(2*(Real.cosh (TWEndpointTail s/2))^2)) s := by
  have hc := (TWEndpointTail_hasDerivAt s).div_const 2
  have hquot := hc.sinh.div hc.cosh (Real.cosh_pos (TWEndpointTail s/2)).ne'
  have hnum :
      Real.cosh (TWEndpointTail s/2)*(-resolventQ s/2)*Real.cosh (TWEndpointTail s/2)-
        Real.sinh (TWEndpointTail s/2)*(Real.sinh (TWEndpointTail s/2)*(-resolventQ s/2)) =
      -resolventQ s/2 := by
    calc
      _ = (-resolventQ s/2)*((Real.cosh (TWEndpointTail s/2))^2-
        (Real.sinh (TWEndpointTail s/2))^2) := by ring
      _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; ring
  rw [hnum] at hquot
  have h := (hasDerivAt_resolventU_negative_q_sq s).sub
    ((hasDerivAt_resolventQ s).mul hquot)
  have he : (fun t => resolventU t-resolventQ t*
      (Real.sinh (TWEndpointTail t/2)/Real.cosh (TWEndpointTail t/2))) = TW4Response := by
    funext t
    simp only [TW4Response,Real.tanh_eq_sinh_div_cosh]
  change HasDerivAt (fun t => resolventU t-resolventQ t*
      (Real.sinh (TWEndpointTail t/2)/Real.cosh (TWEndpointTail t/2))) _ s at h
  rw [he] at h
  convert! h using 1
  simp only [Real.tanh_eq_sinh_div_cosh,Pi.div_apply] at *
  ring

/-- The normalized and unnormalized physical density signs are exactly equivalent. -/
theorem TW4AirySlope_positive_iff_response
    (s : ℝ) -- [definition]
    : 0 < TW4AirySlope s ↔ 0 < TW4Response s := by
  rw [TW4AirySlope_eq_value_mul_response,div_pos_iff_of_pos_right (by norm_num : (0:ℝ)<2)]
  exact mul_pos_iff_of_pos_left (TW4AiryR_positive s)

/-- Every normalized-response binder and derivative identity is supplied on the same physical model. -/
theorem TW4_response_derivative_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < TW4AiryR 0 ∧ 0 < resolventU 0 ∧
      (∀ s : ℝ, HasDerivAt TWEndpointTail (-resolventQ s) s) ∧
      (∀ s : ℝ, TW4AirySlope s = TW4AiryR s*TW4Response s/2) ∧
      (∀ s : ℝ, HasDerivAt TW4Response
        (-(resolventQ s)^2-
          (resolventP s-resolventU s*resolventQ s)*Real.tanh (TWEndpointTail s/2)+
          (resolventQ s)^2/(2*(Real.cosh (TWEndpointTail s/2))^2)) s) :=
  ⟨airyBoundaryVector_ne_zero 0,TW4AiryR_positive 0,airy_inverse_square_boundary_positive 0,
    TWEndpointTail_hasDerivAt,TW4AirySlope_eq_value_mul_response,TW4Response_hasDerivAt⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4Response
#print axioms RMTFoundations.TracyWidom.TWEndpointTail_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_eq_value_mul_response
#print axioms RMTFoundations.TracyWidom.TW4Response_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_positive_iff_response
#print axioms RMTFoundations.TracyWidom.TW4_response_derivative_all_binder_joint_probe
