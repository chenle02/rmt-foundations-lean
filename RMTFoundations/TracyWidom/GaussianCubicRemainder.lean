import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GaussianCubicRemainder
open MeasureTheory

/-- Global quadratic cosine error, with no small-phase restriction. -/
theorem one_sub_cos_le (t : ℝ /- [definition] -/) :
    0 ≤ 1 - Real.cos t ∧ 1 - Real.cos t ≤ t ^ 2 / 2 := by
  refine ⟨by linarith [Real.cos_le_one t], ?_⟩
  have h : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := Real.sin_sq_le_sq
  have hcos := Real.cos_two_mul (t / 2)
  have hsum := Real.sin_sq_add_cos_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hcos
  nlinarith

/-- The first cubic oscillatory correction is bounded by its sixth-degree envelope. -/
theorem cubic_cos_bound (c t : ℝ /- [definition] -/) :
    0 ≤ 1 - Real.cos (c * t ^ 3) ∧
      1 - Real.cos (c * t ^ 3) ≤ c ^ 2 * t ^ 6 / 2 := by
  have h := one_sub_cos_le (c * t ^ 3)
  constructor
  · exact h.1
  · calc 1 - Real.cos (c * t ^ 3) ≤ (c * t ^ 3) ^ 2 / 2 := h.2
         _ = c ^ 2 * t ^ 6 / 2 := by ring


/-- A sixth moment controls the cubic cosine correction for any nonnegative integrable weight. -/
theorem weighted_integral_error
    (μ : MeasureTheory.Measure ℝ /- [definition] -/)
    (w : ℝ → ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/)
    (hw : MeasureTheory.Integrable w μ /- [standing] -/)
    (hnn : ∀ᵐ t ∂μ, 0 ≤ w t /- [standing] -/)
    (h6 : MeasureTheory.Integrable (fun t => w t * t ^ 6) μ /- [standing] -/) :
    0 ≤ (∫ t, w t ∂μ) - (∫ t, w t * Real.cos (c * t ^ 3) ∂μ) ∧
    (∫ t, w t ∂μ) - (∫ t, w t * Real.cos (c * t ^ 3) ∂μ) ≤
      c ^ 2 / 2 * (∫ t, w t * t ^ 6 ∂μ) := by
  have hcos : MeasureTheory.Integrable (fun t => w t * Real.cos (c * t ^ 3)) μ := by
    have h := hw.bdd_mul (by fun_prop : Continuous (fun t : ℝ => Real.cos (c * t ^ 3))).aestronglyMeasurable
      (MeasureTheory.ae_of_all μ fun t => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (c * t ^ 3))
    exact h.congr (MeasureTheory.ae_of_all μ fun t => mul_comm _ _)
  rw [← MeasureTheory.integral_sub hw hcos]
  constructor
  · apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [hnn] with t ht
    change 0 ≤ w t - w t * Real.cos (c * t ^ 3)
    have h := mul_le_mul_of_nonneg_left (Real.cos_le_one (c * t ^ 3)) ht
    nlinarith
  · rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono_ae (hw.sub hcos) (h6.const_mul _)
    filter_upwards [hnn] with t ht
    change w t - w t * Real.cos (c * t ^ 3) ≤ c ^ 2 / 2 * (w t * t ^ 6)
    have h := mul_le_mul_of_nonneg_left (cubic_cos_bound c t).2 ht
    nlinarith

/-- The analytic premises hold jointly for a genuine Gaussian weight and a nonzero phase. -/
theorem gaussian_joint_probe :
    MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) ∧
    (∀ t : ℝ, 0 < Real.exp (-(t ^ 2))) ∧
    MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(t ^ 2)) * t ^ 6) ∧
    (1 : ℝ) ≠ 0 := by
  refine ⟨?_, fun t => Real.exp_pos _, ?_, one_ne_zero⟩
  · simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  · have h := integrable_rpow_mul_exp_neg_mul_sq
      (b := 1) (s := 6) (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast, mul_comm] using h

end RMTFoundations.TracyWidom.GaussianCubicRemainder

#print axioms RMTFoundations.TracyWidom.GaussianCubicRemainder.one_sub_cos_le
#print axioms RMTFoundations.TracyWidom.GaussianCubicRemainder.cubic_cos_bound
#print axioms RMTFoundations.TracyWidom.GaussianCubicRemainder.weighted_integral_error
#print axioms RMTFoundations.TracyWidom.GaussianCubicRemainder.gaussian_joint_probe
