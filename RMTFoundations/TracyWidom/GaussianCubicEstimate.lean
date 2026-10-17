import Mathlib
import RMTFoundations.TracyWidom.GaussianCubicRemainder
import RMTFoundations.TracyWidom.GaussianEvenMoments
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GaussianCubicEstimate
open MeasureTheory

theorem sixth_moment_relative (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    (1/18 : ℝ) * ((1/r) ^ (7/2 : ℝ) * (15 * Real.sqrt Real.pi / 8)) =
      Real.sqrt (Real.pi / r) * (5 / (48 * r ^ 3)) := by
  have hp : (1/r) ^ (7/2 : ℝ) = r ^ (-7/2 : ℝ) := by
    rw [Real.div_rpow zero_le_one hr.le, Real.one_rpow,
      show (-7/2 : ℝ) = -(7/2 : ℝ) from by norm_num, Real.rpow_neg hr.le]
    simp only [one_div]
  have hi : r ^ (-7/2 : ℝ) * Real.sqrt r * r ^ 3 = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 3, ← Real.rpow_add hr, ← Real.rpow_add hr]
    norm_num
  rw [hp, Real.sqrt_div Real.pi_pos.le]
  field_simp [(Real.sqrt_pos.mpr hr).ne', hr.ne']
  nlinarith [congrArg (fun a : ℝ => a * Real.sqrt Real.pi) hi]

/-- The Gaussian integral with cubic cosine phase. -/
noncomputable def gaussianCubic (r : ℝ /- [definition] -/) : ℝ :=
  ∫ t : ℝ, Real.exp (-r * t ^ 2) * Real.cos (t ^ 3 / 3)

/-- An explicit relative error for the cubic Gaussian integral at every positive scale. -/
theorem gaussian_cubic_error (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    0 ≤ Real.sqrt (Real.pi / r) - gaussianCubic r ∧
      Real.sqrt (Real.pi / r) - gaussianCubic r ≤
        Real.sqrt (Real.pi / r) * (5 / (48 * r ^ 3)) := by
  have hw := integrable_exp_neg_mul_sq hr
  have h6 : Integrable (fun t : ℝ => Real.exp (-r * t ^ 2) * t ^ 6) := by
    simpa [Real.rpow_natCast, mul_comm] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := r) (s := (6 : ℝ)) hr (by norm_num))
  have h := RMTFoundations.TracyWidom.GaussianCubicRemainder.weighted_integral_error volume
    (fun t : ℝ => Real.exp (-r * t ^ 2)) (1/3) hw
    (ae_of_all _ fun t => (Real.exp_pos _).le) h6
  have hp : (fun t : ℝ => Real.exp (-r * t ^ 2) * Real.cos ((1/3) * t ^ 3)) =
      fun t : ℝ => Real.exp (-r * t ^ 2) * Real.cos (t ^ 3 / 3) := by
    funext t
    congr 1
    congr 1
    ring
  have hm : (∫ t : ℝ, Real.exp (-r * t ^ 2) * t ^ 6) =
      (1 / r) ^ (7/2 : ℝ) * (15 * Real.sqrt Real.pi / 8) := by
    rw [integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)]
    exact RMTFoundations.TracyWidom.GaussianEvenMoments.integral_sixth_full r hr
  rw [hp, integral_gaussian, hm] at h
  norm_num only at h
  rw [sixth_moment_relative r hr] at h
  exact h

/-- The scale premise and all integration premises have a joint Gaussian witness. -/
theorem gaussian_cubic_joint_probe :
    ∃ r : ℝ, 0 < r ∧
      Integrable (fun t : ℝ => Real.exp (-r * t ^ 2)) ∧
      Integrable (fun t : ℝ => Real.exp (-r * t ^ 2) * t ^ 6) ∧
      (∀ t : ℝ, 0 < Real.exp (-r * t ^ 2)) := by
  refine ⟨1, zero_lt_one, ?_, ?_, fun t => Real.exp_pos _⟩
  · exact integrable_exp_neg_mul_sq zero_lt_one
  · simpa [Real.rpow_natCast, mul_comm] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (6 : ℝ))
        zero_lt_one (by norm_num))

end RMTFoundations.TracyWidom.GaussianCubicEstimate

#print axioms RMTFoundations.TracyWidom.GaussianCubicEstimate.sixth_moment_relative
#print axioms RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussianCubic
#print axioms RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussian_cubic_error
#print axioms RMTFoundations.TracyWidom.GaussianCubicEstimate.gaussian_cubic_joint_probe
