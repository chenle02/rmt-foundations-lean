import Mathlib
import RMTFoundations.TracyWidom.AiryGaussianIntegral
import RMTFoundations.TracyWidom.GaussianCubicEstimate
import RMTFoundations.Airy.Damping
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics
open RMTFoundations.Airy

theorem cube_sqrt (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) : (Real.sqrt x) ^ 3 = x ^ (3/2 : ℝ) := by
  rw [← Real.rpow_natCast (Real.sqrt x) 3, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  norm_num

theorem reciprocal_quarter_sqrt (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) : (Real.sqrt (Real.sqrt x))⁻¹ = x ^ (-1/4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  rw [show (-1/4 : ℝ) = -(1/4 : ℝ) from by norm_num, Real.rpow_neg hx.le]
  norm_num

theorem gaussian_prefactor (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    (1 / (2 * Real.pi)) * Real.sqrt (Real.pi / r) =
      (1 / (2 * Real.sqrt Real.pi)) * (Real.sqrt r)⁻¹ := by
  rw [Real.sqrt_div Real.pi_pos.le]
  have hp := Real.sq_sqrt Real.pi_pos.le
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hs, (Real.sqrt_pos.mpr hr).ne', Real.pi_ne_zero]
  nlinarith

/-- The classical positive-side Airy leading term. -/
noncomputable def leading (x : ℝ /- [definition] -/) : ℝ :=
  (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) *
    Real.exp (-(2/3) * x ^ (3/2 : ℝ))

/-- Before undoing the saddle exponential, the error is already explicit and one-sided. -/
theorem scaled_square_error (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    0 ≤ (1 / (2 * Real.pi)) * Real.sqrt (Real.pi / r) -
      Real.exp ((2/3) * r ^ 3) * airyAiReal (r ^ 2) ∧
    (1 / (2 * Real.pi)) * Real.sqrt (Real.pi / r) -
      Real.exp ((2/3) * r ^ 3) * airyAiReal (r ^ 2) ≤
        ((1 / (2 * Real.pi)) * Real.sqrt (Real.pi / r)) * (5 / (48 * r ^ 3)) := by
  have h := RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussian_cubic_error r hr
  rw [RMTFoundations.TracyWidom.AiryGaussianIntegral.saddle_integral r hr]
  constructor
  · simpa only [RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussianCubic, mul_sub] using
      mul_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi)) h.1
  · simpa only [RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussianCubic, mul_sub, mul_assoc] using
      mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ 1 / (2 * Real.pi))

/-- Explicit DLMF leading-term error, derived from an absolutely convergent integral. -/
theorem airy_error (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) :
    0 ≤ leading x - airyAiReal x ∧
      leading x - airyAiReal x ≤ leading x * (5 / (48 * x ^ (3/2 : ℝ))) := by
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := scaled_square_error (Real.sqrt x) hr
  rw [Real.sq_sqrt hx.le, cube_sqrt x hx, gaussian_prefactor (Real.sqrt x) hr,
    reciprocal_quarter_sqrt x hx] at h
  have he : Real.exp ((2/3) * x ^ (3/2 : ℝ)) * leading x =
      (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) := by
    unfold leading
    rw [show -(2/3) * x ^ (3/2 : ℝ) = -((2/3) * x ^ (3/2 : ℝ)) from by ring]
    rw [show Real.exp ((2/3) * x ^ (3/2 : ℝ)) *
        ((1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) *
          Real.exp (-((2/3) * x ^ (3/2 : ℝ)))) =
        ((1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ)) *
          (Real.exp ((2/3) * x ^ (3/2 : ℝ)) * Real.exp (-((2/3) * x ^ (3/2 : ℝ)))) from by ring,
      ← Real.exp_add]
    simp
  rw [← he, ← mul_sub] at h
  constructor
  · exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h.1
  · apply (mul_le_mul_iff_right₀ (Real.exp_pos ((2/3) * x ^ (3/2 : ℝ)))).mp
    nlinarith [h.2]

/-- The explicit error in the conventional normalized leading-term form. -/
theorem airy_relative_error (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) :
    |airyAiReal x / leading x - 1| ≤ 5 / (48 * x ^ (3/2 : ℝ)) := by
  have h := airy_error x hx
  have hl : 0 < leading x := by unfold leading; positivity
  rw [show airyAiReal x / leading x - 1 = -((leading x - airyAiReal x) / leading x) from by
    field_simp [hl.ne']; ring, abs_neg, abs_of_nonneg (div_nonneg h.1 hl.le)]
  apply (div_le_iff₀ hl).mpr
  nlinarith [h.2]

/-- Reuse the exact Ai equivalence with the shared leading-term definition. -/
theorem airy_leading_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop airyAiReal leading :=
  airyAiReal_isEquivalent

/-- Positivity is inherited from the Airy construction on the entire closed ray. -/
theorem airy_positive (x : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/) : 0 < airyAiReal x :=
  airyAiReal_pos_of_nonneg hx

/-- A genuine positive point jointly satisfies every positive-side premise. -/
theorem airy_error_joint_probe :
    ∃ x r : ℝ, 0 < x ∧ 0 < r ∧ r ^ 2 = x ∧
      0 < airyAiReal x ∧ 0 < leading x := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, by norm_num,
    airyAiReal_pos_of_nonneg zero_le_one, ?_⟩
  unfold leading
  positivity

end RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics

#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.cube_sqrt
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.reciprocal_quarter_sqrt
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.gaussian_prefactor
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.leading
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.scaled_square_error
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.airy_error
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.airy_positive
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.airy_error_joint_probe
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.airy_relative_error
#print axioms RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics.airy_leading_isEquivalent
