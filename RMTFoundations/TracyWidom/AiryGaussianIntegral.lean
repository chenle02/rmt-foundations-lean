import Mathlib
import RMTFoundations.Airy.Damping
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryGaussianIntegral
open MeasureTheory
open RMTFoundations.Airy
open scoped FourierTransform

/-- The positive-damping inversion integrand, with its phase already combined. -/
noncomputable def integrand (β x ξ : ℝ /- [definition] -/) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * (ξ * x)) * Complex.I) +
    (airyLaplaceFrequency β ξ) ^ 3 / 3)

theorem integrand_re (β x ξ : ℝ /- [definition] -/) :
    (integrand β x ξ).re =
      Real.exp (β ^ 3 / 3 - β * (2 * Real.pi * ξ) ^ 2) *
      Real.cos ((2 * Real.pi * ξ) * (x - β ^ 2) + (2 * Real.pi * ξ) ^ 3 / 3) := by
  rw [integrand, Complex.exp_re]
  congr 1 <;> simp [airyLaplaceFrequency, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, pow_succ] <;> ring

theorem integrand_integrable (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) : Integrable (integrand β x) := by
  have hg : Integrable (fun ξ : ℝ =>
      Real.exp (β ^ 3 / 3) * Real.exp (-(β * (2 * Real.pi) ^ 2) * ξ ^ 2)) :=
    (integrable_exp_neg_mul_sq (mul_pos hβ (sq_pos_of_pos (by positivity)))).const_mul _
  apply hg.mono'
  · exact (by unfold integrand airyLaplaceFrequency; fun_prop : Continuous (integrand β x)).aestronglyMeasurable
  · apply ae_of_all
    intro ξ
    rw [integrand, Complex.norm_exp, ← Real.exp_add]
    apply le_of_eq
    congr 1
    simp [airyLaplaceFrequency, Complex.add_re, Complex.mul_re, Complex.mul_im,
      pow_succ]
    ring

/-- An absolutely convergent Gaussian-cubic representation at every real argument. -/
theorem damped_integral (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    Real.exp (β * x) * airyAiReal x =
      ∫ ξ : ℝ, Real.exp (β ^ 3 / 3 - β * (2 * Real.pi * ξ) ^ 2) *
        Real.cos ((2 * Real.pi * ξ) * (x - β ^ 2) + (2 * Real.pi * ξ) ^ 3 / 3) := by
  have h := airyDamped_inverse_fourier β x hβ
  rw [Real.fourierInv_eq'] at h
  simp only [Real.inner_apply] at h
  have hi : (∫ ξ : ℝ, Complex.exp (↑(2 * Real.pi * (ξ * x)) * Complex.I) •
      (𝓕 (laplaceDamped airyAiComplexReal β)) ξ) = ∫ ξ : ℝ, integrand β x ξ := by
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    dsimp only
    rw [airyDamped_fourier_eq β ξ hβ, smul_eq_mul, ← Complex.exp_add]
    rfl
  rw [hi] at h
  have hr : (∫ ξ : ℝ, (integrand β x ξ).re) = (laplaceDamped airyAiComplexReal β x).re :=
    (integral_re (integrand_integrable β x hβ)).trans (congrArg Complex.re h)
  simp only [laplaceDamped, airyAiComplexReal, Complex.mul_re, Complex.exp_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, Real.cos_zero, mul_one] at hr
  rw [← hr]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  exact integrand_re β x ξ

/-- On the positive square scale the exact contour becomes a Gaussian-cubic integral. -/
theorem saddle_integral (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    Real.exp ((2/3) * r ^ 3) * airyAiReal (r ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ, Real.exp (-r * t ^ 2) * Real.cos (t ^ 3 / 3) := by
  have h := damped_integral r (r ^ 2) hr
  have he : (fun ξ : ℝ => Real.exp (r ^ 3 / 3 - r * (2 * Real.pi * ξ) ^ 2) *
      Real.cos ((2 * Real.pi * ξ) * (r ^ 2 - r ^ 2) + (2 * Real.pi * ξ) ^ 3 / 3)) =
      fun ξ => Real.exp (r ^ 3 / 3) *
        (Real.exp (-r * (2 * Real.pi * ξ) ^ 2) * Real.cos ((2 * Real.pi * ξ) ^ 3 / 3)) := by
    funext ξ
    rw [sub_self, mul_zero, zero_add, sub_eq_add_neg, Real.exp_add]
    ring
  rw [he, integral_const_mul] at h
  have hs := Measure.integral_comp_mul_left
    (fun t : ℝ => Real.exp (-r * t ^ 2) * Real.cos (t ^ 3 / 3)) (2 * Real.pi)
  simp only [abs_inv, abs_of_pos (mul_pos two_pos Real.pi_pos), smul_eq_mul] at hs
  rw [hs] at h
  have hx : Real.exp (r * r ^ 2) =
      Real.exp (r ^ 3 / 3) * Real.exp ((2/3) * r ^ 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hx, mul_assoc] at h
  have hc := mul_left_cancel₀ (Real.exp_ne_zero (r ^ 3 / 3)) h
  simpa only [one_div] using hc

/-- Damping and positivity jointly occur for the genuine Airy function. -/
theorem contour_joint_probe :
    ∃ β x : ℝ, 0 < β ∧ 0 < x ∧ 0 < airyAiReal x ∧ Integrable (integrand β x) := by
  exact ⟨1, 1, zero_lt_one, zero_lt_one, airyAiReal_pos_of_nonneg zero_le_one,
    integrand_integrable 1 1 zero_lt_one⟩

end RMTFoundations.TracyWidom.AiryGaussianIntegral

#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.integrand
#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.integrand_re
#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.integrand_integrable
#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.damped_integral
#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.saddle_integral
#print axioms RMTFoundations.TracyWidom.AiryGaussianIntegral.contour_joint_probe
