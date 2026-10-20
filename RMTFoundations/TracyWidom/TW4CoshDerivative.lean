import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.TW4IntegralFormula
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates

/-- The actual GSE derivative, with the positive square root branch fixed. -/
theorem TW4AirySlope_eq_cosh_response
    (s : ℝ /- [definition] -/)
    : TW4AirySlope s = Real.sqrt (TW2R s)/2 *
      (resolventU s*Real.cosh (TWEndpointTail s/2)-
        resolventQ s*Real.sinh (TWEndpointTail s/2)) := by
  rw [TW4AirySlope,TW1R_eq_sqrt_TW2R_mul_exp,hankelDetPlus_eq_sqrt_TW2R_mul_exp,
    Real.cosh_eq,Real.sinh_eq]
  rw [show -(TWEndpointTail s/2) = -TWEndpointTail s/2 by ring]
  ring

/-- The physical logarithmic slope has its exact cosh/sinh response form. -/
theorem TW4AiryR_hasDerivAt_log_cosh_response
    (s : ℝ /- [definition] -/)
    : HasDerivAt (fun t => Real.log (TW4AiryR t))
      ((resolventU s-resolventQ s*Real.sinh (TWEndpointTail s/2)/
        Real.cosh (TWEndpointTail s/2))/2) s := by
  have h := TW4AiryR_log_derivative s
  rw [TW4AirySlope_eq_cosh_response,TW4AiryR_eq_sqrt_TW2R_cosh_tail] at h
  convert! h using 1
  field_simp [(Real.sqrt_pos.mpr (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s)).ne',
    (Real.cosh_pos (TWEndpointTail s/2)).ne']
  <;> ring

/-- Exact sign equivalence, without assuming a physical sign or a probability law. -/
theorem TW4AirySlope_nonneg_iff_cosh_response
    (s : ℝ /- [definition] -/)
    : 0 ≤ TW4AirySlope s ↔
      resolventQ s*Real.sinh (TWEndpointTail s/2) ≤
        resolventU s*Real.cosh (TWEndpointTail s/2) := by
  rw [TW4AirySlope_eq_cosh_response]
  have hp : 0 < Real.sqrt (TW2R s)/2 :=
    div_pos (Real.sqrt_pos.mpr (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s)) (by norm_num)
  rw [mul_nonneg_iff_of_pos_left hp,sub_nonneg]

/-- Every point binder and response identity coexist on the actual nonzero Airy row. -/
theorem TW4_cosh_derivative_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < TW2R 0 ∧ 0 < TW4AiryR 0 ∧
      (∀ s : ℝ, TW4AirySlope s = Real.sqrt (TW2R s)/2 *
        (resolventU s*Real.cosh (TWEndpointTail s/2)-
          resolventQ s*Real.sinh (TWEndpointTail s/2))) ∧
      (∀ s : ℝ, HasDerivAt (fun t => Real.log (TW4AiryR t))
        ((resolventU s-resolventQ s*Real.sinh (TWEndpointTail s/2)/
          Real.cosh (TWEndpointTail s/2))/2) s) :=
  ⟨airyBoundaryVector_ne_zero 0,RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0,
    TW4AiryR_positive 0,TW4AirySlope_eq_cosh_response,TW4AiryR_hasDerivAt_log_cosh_response⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4AirySlope_eq_cosh_response
#print axioms RMTFoundations.TracyWidom.TW4AiryR_hasDerivAt_log_cosh_response
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_nonneg_iff_cosh_response
#print axioms RMTFoundations.TracyWidom.TW4_cosh_derivative_all_binder_joint_probe
