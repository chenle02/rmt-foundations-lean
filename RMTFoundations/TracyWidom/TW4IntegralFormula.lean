import RMTFoundations.TracyWidom.OrderFourFredholm
import RMTFoundations.TracyWidom.IntegralRepresentations
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.IntegralRepresentations

/-- The physical q tail, whose absolute integrability is already proved. -/
noncomputable def TWEndpointTail (s : ℝ /- [definition] -/) : ℝ :=
  ∫ t in Ioi s, resolventQ t

/-- The positive square root branch is forced by determinant positivity. -/
theorem TW1R_eq_sqrt_TW2R_mul_exp
    (s : ℝ /- [definition] -/) :
    TW1R s = Real.sqrt (TW2R s)*Real.exp (-TWEndpointTail s/2) := by
  have hb := RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s
  have hs : (Real.sqrt (TW2R s)*Real.exp (-TWEndpointTail s/2))^2 = (TW1R s)^2 := by
    rw [mul_pow,Real.sq_sqrt hb.le,pow_two,← Real.exp_add]
    have he : -TWEndpointTail s/2 + -TWEndpointTail s/2 = -TWEndpointTail s := by ring
    rw [he]
    exact (TW1R_sq_eq_TW2R_mul_exp_negative_tail s).symm
  have hp : 0 < Real.sqrt (TW2R s)*Real.exp (-TWEndpointTail s/2) :=
    mul_pos (Real.sqrt_pos.mpr hb) (Real.exp_pos _)
  nlinarith [(TW1R_positive_bounds s).1]

/-- The plus determinant supplies the opposite exponential branch. -/
theorem hankelDetPlus_eq_sqrt_TW2R_mul_exp
    (s : ℝ /- [definition] -/) :
    hankelDetPlus s = Real.sqrt (TW2R s)*Real.exp (TWEndpointTail s/2) := by
  have hb := RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s
  have hs := Real.sq_sqrt hb.le
  have hm : Real.exp (-TWEndpointTail s/2)*Real.exp (TWEndpointTail s/2) = 1 := by
    rw [←Real.exp_add]
    have he : -TWEndpointTail s/2+TWEndpointTail s/2 = 0 := by ring
    rw [he,Real.exp_zero]
  have hf := TW2R_factorization s
  rw [TW1R_eq_sqrt_TW2R_mul_exp] at hf
  have hp := Real.sqrt_pos.mpr hb
  have he := Real.exp_pos (-TWEndpointTail s/2)
  nlinarith [mul_pos hp he]

/-- Actual GSE equation (54), on its raw Airy cutoff and positive branch. -/
theorem TW4AiryR_eq_sqrt_TW2R_cosh_tail
    (s : ℝ /- [definition] -/) :
    TW4AiryR s = Real.sqrt (TW2R s)*Real.cosh (TWEndpointTail s/2) := by
  rw [TW4AiryR,TW1R_eq_sqrt_TW2R_mul_exp,hankelDetPlus_eq_sqrt_TW2R_mul_exp,
    Real.cosh_eq]
  rw [show -(TWEndpointTail s/2) = -TWEndpointTail s/2 by ring]
  ring

/-- The normalized Ferrari-Spohn/TW96 squared formula is an identity of actual objects. -/
theorem TW4R_scaled_square_formula
    (s : ℝ /- [definition] -/) :
    (TW4R (s/Real.sqrt 2))^2 = TW2R s*(Real.cosh (TWEndpointTail s/2))^2 := by
  rw [TW4R_raw_scaling,TW4AiryR_eq_sqrt_TW2R_cosh_tail,mul_pow,
    Real.sq_sqrt (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s).le]

/-- The tail and both exponential branches coexist with nonzero physical data. -/
theorem TW4_integral_all_binder_joint_probe :
    RMTFoundations.TWOneBounds.airyBoundaryVector 0 ≠ 0 ∧
    IntegrableOn resolventQ (Ioi 0) ∧ 0 < TW1R 0 ∧ 0 < TW2R 0 ∧
    (∀ s : ℝ, TW4AiryR s = Real.sqrt (TW2R s)*Real.cosh (TWEndpointTail s/2)) :=
  ⟨airyBoundaryVector_ne_zero 0,integrableOn_resolventQ 0,(TW1R_positive_bounds 0).1,
    RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0,TW4AiryR_eq_sqrt_TW2R_cosh_tail⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TWEndpointTail
#print axioms RMTFoundations.TracyWidom.TW1R_eq_sqrt_TW2R_mul_exp
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_eq_sqrt_TW2R_mul_exp
#print axioms RMTFoundations.TracyWidom.TW4AiryR_eq_sqrt_TW2R_cosh_tail
#print axioms RMTFoundations.TracyWidom.TW4R_scaled_square_formula
#print axioms RMTFoundations.TracyWidom.TW4_integral_all_binder_joint_probe
