import RMTFoundations.TracyWidom.OrderTwoLogDerivative
import RMTFoundations.TracyWidom.EndpointCalculus
import RMTFoundations.TracyWidom.ConcavePrimitiveTail



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.IntegralRepresentations

open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom

/-- The actual diagonal response decreases by the square of the physical endpoint response. -/
theorem resolventU_antitone : Antitone resolventU :=
  antitone_of_hasDerivAt_nonpos hasDerivAt_resolventU_negative_q_sq
    (fun t => neg_nonpos.mpr (sq_nonneg (resolventQ t)))

/-- The physical TW2 logarithm has its genuine normalized right limit. -/
theorem log_TW2R_tendsto_zero :
    Tendsto (fun t => Real.log (TW2R t)) atTop (𝓝 0) := by
  simpa only [Real.log_one,Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp TW2R_tendsto_atTop_one

/-- Both square tail integrals are genuine Lebesgue integrals with proved integrability. -/
theorem resolventQ_square_tail_integrals
    (s : ℝ) -- [definition]
    : IntegrableOn (fun t => (resolventQ t)^2) (Ioi s) ∧
      (∫ t in Ioi s, (resolventQ t)^2) = resolventU s ∧
      IntegrableOn (fun t => (t-s)*(resolventQ t)^2) (Ioi s) ∧
      (∫ t in Ioi s, (t-s)*(resolventQ t)^2) = -Real.log (TW2R s) :=
  primitive_square_tail_integrals (fun t => Real.log (TW2R t)) resolventU resolventQ
    resolventU_continuous hasDerivAt_log_TW2R_coordinates
    (fun t => (airy_inverse_square_boundary_positive t).le) resolventU_antitone
    log_TW2R_tendsto_zero hasDerivAt_resolventU_negative_q_sq s

/-- Unconditional Tracy--Widom F2 integral representation for the physical Fredholm coordinate. -/
theorem TW2R_eq_exp_negative_weighted_square_tail
    (s : ℝ) -- [definition]
    : TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(resolventQ t)^2)) := by
  rw [(resolventQ_square_tail_integrals s).2.2.2,neg_neg,
    Real.exp_log (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s)]

/-- The actual diagonal coordinate is integrable on every upper tail. -/
theorem integrableOn_resolventU
    (s : ℝ) -- [definition]
    : IntegrableOn resolventU (Ioi s) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hasDerivAt_log_TW2R_coordinates t)
    (fun t _ => (airy_inverse_square_boundary_positive t).le) log_TW2R_tendsto_zero

/-- The diagonal tail is the negative genuine Fredholm logarithm. -/
theorem integral_resolventU_tail
    (s : ℝ) -- [definition]
    : (∫ t in Ioi s, resolventU t) = -Real.log (TW2R s) := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => hasDerivAt_log_TW2R_coordinates t)
    (fun t _ => (airy_inverse_square_boundary_positive t).le) log_TW2R_tendsto_zero

/-- The actual positive and monotone F1 determinant gives a nonnegative logarithmic slope. -/
theorem resolventQ_add_resolventU_nonneg
    (s : ℝ) -- [definition]
    : 0 ≤ resolventQ s+resolventU s := by
  have hm : Monotone (fun t => Real.log (TW1R t^2)) := by
    intro a b hab
    apply Real.log_le_log (sq_pos_of_pos (TW1R_positive_bounds a).1)
    have hp := (TW1R_positive_bounds a).1
    have hq := (TW1R_positive_bounds b).1
    have he := monotone_TW1R hab
    nlinarith
  have h := hm.deriv_nonneg (x := s)
  rwa [(hasDerivAt_log_TW1R_sq_coordinates s).deriv] at h

/-- Genuine F1 right normalization for its squared logarithm. -/
theorem log_TW1R_sq_tendsto_zero :
    Tendsto (fun t => Real.log (TW1R t^2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t => TW1R t^2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using TW1R_tendsto_atTop_one.pow 2
  simpa only [Real.log_one,Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h

/-- Absolute integrability of the physical q follows from the two monotone determinant primitives. -/
theorem integrableOn_resolventQ
    (s : ℝ) -- [definition]
    : IntegrableOn resolventQ (Ioi s) := by
  have hsum : IntegrableOn (fun t => resolventQ t+resolventU t) (Ioi s) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hasDerivAt_log_TW1R_sq_coordinates t)
      (fun t _ => resolventQ_add_resolventU_nonneg t) log_TW1R_sq_tendsto_zero
  have h := hsum.sub (integrableOn_resolventU s)
  have he : ((fun t => resolventQ t+resolventU t)-resolventU) = resolventQ := by
    funext t
    exact add_sub_cancel_right (resolventQ t) (resolventU t)
  rw [he] at h
  exact h

/-- The physical endpoint response has the genuine logarithmic-ratio tail integral. -/
theorem integral_resolventQ_tail
    (s : ℝ) -- [definition]
    : (∫ t in Ioi s, resolventQ t) = Real.log (TW2R s)-Real.log (TW1R s^2) := by
  have hsum : IntegrableOn (fun t => resolventQ t+resolventU t) (Ioi s) :=
    (integrableOn_resolventQ s).add (integrableOn_resolventU s)
  have he : (∫ t in Ioi s, resolventQ t+resolventU t) = -Real.log (TW1R s^2) := by
    simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun t _ => hasDerivAt_log_TW1R_sq_coordinates t)
      (fun t _ => resolventQ_add_resolventU_nonneg t) log_TW1R_sq_tendsto_zero
  rw [integral_add (integrableOn_resolventQ s) (integrableOn_resolventU s),
    integral_resolventU_tail] at he
  linarith

/-- Unconditional Tracy--Widom F1 squared integral representation, with genuine q integrability. -/
theorem TW1R_sq_eq_TW2R_mul_exp_negative_tail
    (s : ℝ) -- [definition]
    : TW1R s^2 = TW2R s*Real.exp (-(∫ t in Ioi s, resolventQ t)) := by
  rw [integral_resolventQ_tail,neg_sub,Real.exp_sub,
    Real.exp_log (sq_pos_of_pos (TW1R_positive_bounds s).1),
    Real.exp_log (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s)]
  field_simp [(RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s).ne']

/-- All tail integrability and both physical representations hold jointly at shift zero;
no empty event, absent family or zero source is used. -/
theorem integral_representations_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ 0 < TW1R 0 ∧ 0 < TW2R 0 ∧ 0 < resolventU 0 ∧
      IntegrableOn resolventQ (Ioi 0) ∧
      IntegrableOn (fun t => (resolventQ t)^2) (Ioi 0) ∧
      IntegrableOn (fun t => t*(resolventQ t)^2) (Ioi 0) ∧
      TW2R 0 = Real.exp (-(∫ t in Ioi 0, t*(resolventQ t)^2)) ∧
      TW1R 0^2 = TW2R 0*Real.exp (-(∫ t in Ioi 0, resolventQ t)) := by
  refine ⟨airyBoundaryVector_ne_zero 0,(TW1R_positive_bounds 0).1,
    RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0,airy_inverse_square_boundary_positive 0,
    integrableOn_resolventQ 0,(resolventQ_square_tail_integrals 0).1,?_,?_,
    TW1R_sq_eq_TW2R_mul_exp_negative_tail 0⟩
  · simpa only [sub_zero] using (resolventQ_square_tail_integrals 0).2.2.1
  · simpa only [sub_zero] using TW2R_eq_exp_negative_weighted_square_tail 0

end RMTFoundations.TracyWidom.IntegralRepresentations

#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.resolventU_antitone
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.log_TW2R_tendsto_zero
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.resolventQ_square_tail_integrals
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.TW2R_eq_exp_negative_weighted_square_tail
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.integrableOn_resolventU
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.integral_resolventU_tail
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.resolventQ_add_resolventU_nonneg
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.log_TW1R_sq_tendsto_zero
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.integrableOn_resolventQ
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.integral_resolventQ_tail
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.TW1R_sq_eq_TW2R_mul_exp_negative_tail
#print axioms RMTFoundations.TracyWidom.IntegralRepresentations.integral_representations_all_binder_joint_probe
