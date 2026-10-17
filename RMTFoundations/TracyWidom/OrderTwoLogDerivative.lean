import RMTFoundations.TracyWidom.PlusDerivative
import RMTFoundations.TracyWidom.OrderTwoFactorization
import RMTFoundations.TracyWidom.OrderTwoPositive
import RMTFoundations.TracyWidom.ResolventCoordinates
import RMTFoundations.TracyWidom.AiryNormDerivative



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.OrderTwoLogDerivative

open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone
open RMTFoundations.TracyWidom.OrderTwoFactorization RMTFoundations.TracyWidom.PlusDerivative
open RMTFoundations.TracyWidom.OrderTwoPositive RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.AiryBoundaryContinuity RMTFoundations.TracyWidom.AiryNormDerivative

/-- The actual plus Hankel derivative in the fixed canonical basis. -/
theorem hasDerivAt_Dplus
    (s : ℝ) -- [definition]
    : HasDerivAt Dplus
      (-Dplus s * (airyAiReal s - inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1 + airyHankelShift s) (airyBoundaryVector s))) / 2) s := by
  exact hasDerivAt_airyPlus_realOperatorDet_canonical_resolvent
    (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)) s

/-- Genuine TW2 determinant differentiation. Its two boundary terms cancel
through the actual even/odd inverse parity, with no derivative premise. -/
theorem hasDerivAt_TW2R_coordinates
    (s : ℝ) -- [definition]
    : HasDerivAt TW2R (TW2R s * resolventU s) s := by
  have h := (hasDerivAt_TW1R_canonical_resolvent s).fun_mul (hasDerivAt_Dplus s)
  have he : (fun t => TW1R t * Dplus t) = TW2R :=
    funext (fun t => (TW2R_factorization t).symm)
  rw [he] at h
  have hd : TW1R s *
      (airyAiReal s + inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1 - airyHankelShift s) (airyBoundaryVector s))) / 2 * Dplus s +
      TW1R s * (-Dplus s * (airyAiReal s - inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1 + airyHankelShift s) (airyBoundaryVector s))) / 2) =
      TW2R s * resolventU s := by
    rw [TW2R_factorization, resolventU]
    have hp := airy_inverse_quadratic_parity_sum s (airyBoundaryVector s)
    rw [← hp]
    ring
  rw [hd] at h
  exact h

/-- The actual positive Fredholm determinant has the canonical logarithmic derivative. -/
theorem hasDerivAt_log_TW2R_coordinates
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Real.log (TW2R t)) (resolventU s) s := by
  have hn : TW2R s ≠ 0 := (TW2R_positive s).ne'
  have h := (hasDerivAt_TW2R_coordinates s).log hn
  have hd : TW2R s * resolventU s / TW2R s = resolventU s := by field_simp
  rw [hd] at h
  exact h

/-- The genuine logarithmic ratio isolates the endpoint response q. Integral
identification and Hastings--McLeod normalization remain separate obligations. -/
theorem hasDerivAt_log_TW1R_sq_sub_log_TW2R
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Real.log (TW1R t ^ 2) - Real.log (TW2R t))
      (resolventQ s) s := by
  have h := (hasDerivAt_log_TW1R_sq_coordinates s).fun_sub
    (hasDerivAt_log_TW2R_coordinates s)
  have hd : resolventQ s + resolventU s - resolventU s = resolventQ s := by ring
  rw [hd] at h
  exact h

/-- Actual operator inverse regularity and actual boundary continuity imply
continuity of the canonical diagonal coordinate. -/
theorem resolventU_continuous : Continuous resolventU := by
  have hi : Continuous (fun t => Ring.inverse (1 - airyKernelShift t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hasDerivAt_airyKernelResolvent_norm t).continuousAt)
  exact airyBoundaryVector_continuous.inner
    (hi.clm_apply airyBoundaryVector_continuous)

/-- The genuine finite-interval logarithmic primitive. This is a u-coordinate
identity; identifying u with the q-square tail remains an analytic obligation. -/
theorem integral_resolventU_eq_log_TW2R_sub
    (a b : ℝ) -- [definition]
    : (∫ t in a..b, resolventU t) = Real.log (TW2R b) - Real.log (TW2R a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_log_TW2R_coordinates t)
    (resolventU_continuous.intervalIntegrable a b)

/-- Exact finite-interval exponential transport for the actual determinant. -/
theorem TW2R_eq_mul_exp_integral_resolventU
    (a b : ℝ) -- [definition]
    : TW2R b = TW2R a * Real.exp (∫ t in a..b, resolventU t) := by
  rw [integral_resolventU_eq_log_TW2R_sub, Real.exp_sub,
    Real.exp_log (TW2R_positive b), Real.exp_log (TW2R_positive a)]
  field_simp [(TW2R_positive a).ne']

/-- The finite-interval theorem has a noncollapsed physical interval and nonzero row. -/
theorem integral_primitive_all_binder_joint_probe
    : (0 : ℝ) < 1 ∧ airyBoundaryVector 0 ≠ 0 ∧ 0 < TW2R 0 ∧ 0 < TW2R 1 ∧
      Continuous resolventU ∧
      (∫ t in (0 : ℝ)..1, resolventU t) = Real.log (TW2R 1) - Real.log (TW2R 0) ∧
      TW2R 1 = TW2R 0 * Real.exp (∫ t in (0 : ℝ)..1, resolventU t) := by
  exact ⟨zero_lt_one, airyBoundaryVector_ne_zero 0, TW2R_positive 0,
    TW2R_positive 1, resolventU_continuous,
    integral_resolventU_eq_log_TW2R_sub 0 1,
    TW2R_eq_mul_exp_integral_resolventU 0 1⟩

/-- All actual objects and derivatives coexist at the nonzero shift-zero Airy row. -/
theorem log_derivative_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ 0 < TW1R 0 ∧ 0 < TW2R 0 ∧
      0 < resolventU 0 ∧
      HasDerivAt TW2R (TW2R 0 * resolventU 0) 0 ∧
      HasDerivAt (fun t => Real.log (TW2R t)) (resolventU 0) 0 ∧
      HasDerivAt (fun t => Real.log (TW1R t ^ 2) - Real.log (TW2R t))
        (resolventQ 0) 0 := by
  exact ⟨airyBoundaryVector_ne_zero 0, (TW1R_positive_bounds 0).1,
    TW2R_positive 0, airy_inverse_square_boundary_positive 0,
    hasDerivAt_TW2R_coordinates 0, hasDerivAt_log_TW2R_coordinates 0,
    hasDerivAt_log_TW1R_sq_sub_log_TW2R 0⟩

end RMTFoundations.TracyWidom.OrderTwoLogDerivative

#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_Dplus
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_TW2R_coordinates
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_log_TW2R_coordinates
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_log_TW1R_sq_sub_log_TW2R
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.log_derivative_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.resolventU_continuous
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.integral_resolventU_eq_log_TW2R_sub
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.TW2R_eq_mul_exp_integral_resolventU
#print axioms RMTFoundations.TracyWidom.OrderTwoLogDerivative.integral_primitive_all_binder_joint_probe
