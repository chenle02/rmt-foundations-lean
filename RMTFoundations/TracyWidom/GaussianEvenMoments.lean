import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GaussianEvenMoments
open MeasureTheory Set

/-- Exact sixth Gaussian moment on the positive half-line. -/
theorem integral_sixth (b : ℝ /- [definition] -/)
    (hb : 0 < b /- [standing] -/) :
    (∫ t : ℝ in Ioi 0, t ^ 6 * Real.exp (-b * t ^ 2)) =
      (1 / b) ^ (7 / 2 : ℝ) * (15 * Real.sqrt Real.pi / 16) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 7 / 2) (r := b) (by norm_num) hb
  rw [← integral_comp_rpow_Ioi_of_pos zero_lt_two] at h
  have hi : (∫ t : ℝ in Ioi 0, (2 * t ^ ((2 : ℝ) - 1)) •
      ((t ^ (2 : ℝ)) ^ ((7 / 2 : ℝ) - 1) * Real.exp (-(b * t ^ (2 : ℝ))))) =
      2 * (∫ t : ℝ in Ioi 0, t ^ 6 * Real.exp (-b * t ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [smul_eq_mul, ← Real.rpow_mul ht.le]
    norm_num [Real.rpow_natCast]
    ring
  rw [hi] at h
  have hg : Real.Gamma (7 / 2) = 15 * Real.sqrt Real.pi / 8 := by
    convert Real.Gamma_nat_add_half 3 using 1 <;> norm_num [Nat.doubleFactorial]
  rw [hg] at h
  nlinarith

theorem integral_sixth_full (b : ℝ /- [definition] -/)
    (hb : 0 < b /- [standing] -/) :
    (∫ t : ℝ, t ^ 6 * Real.exp (-b * t ^ 2)) =
      (1 / b) ^ (7/2 : ℝ) * (15 * Real.sqrt Real.pi / 8) := by
  have hi : Integrable (fun t : ℝ => t ^ 6 * Real.exp (-b * t ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := b) (s := (6 : ℝ)) hb (by norm_num))
  have hsum := integral_add_compl measurableSet_Ioi hi (s := Ioi 0)
  rw [compl_Ioi] at hsum
  have hn : (∫ t in Iic 0, t ^ 6 * Real.exp (-b * t ^ 2)) =
      ∫ t in Ioi 0, t ^ 6 * Real.exp (-b * t ^ 2) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun t : ℝ => t ^ 6 * Real.exp (-b * t ^ 2))
    have he : (fun t : ℝ => (-t) ^ 6 * Real.exp (-b * (-t) ^ 2)) =
        fun t : ℝ => t ^ 6 * Real.exp (-b * t ^ 2) := by
      funext t
      rw [show (-t) ^ 6 = t ^ 6 from by ring, show (-t) ^ 2 = t ^ 2 from by ring]
    change (∫ t in Iic 0, (-t) ^ 6 * Real.exp (-b * (-t) ^ 2)) = _ at h
    rw [he] at h
    simpa only [neg_zero] using h
  rw [hn, integral_sixth b hb] at hsum
  linarith

/-- The Gaussian moment hypotheses are jointly witnessed by an actual positive density. -/
theorem gaussian_moment_joint_probe :
    ∃ b : ℝ, 0 < b ∧
      Integrable (fun t : ℝ => t ^ 6 * Real.exp (-b * t ^ 2)) ∧
      (∀ t : ℝ, 0 < Real.exp (-b * t ^ 2)) := by
  refine ⟨1, zero_lt_one, ?_, fun t => Real.exp_pos _⟩
  simpa [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (6 : ℝ))
      zero_lt_one (by norm_num : (-1 : ℝ) < 6))

end RMTFoundations.TracyWidom.GaussianEvenMoments

#print axioms RMTFoundations.TracyWidom.GaussianEvenMoments.integral_sixth
#print axioms RMTFoundations.TracyWidom.GaussianEvenMoments.integral_sixth_full
#print axioms RMTFoundations.TracyWidom.GaussianEvenMoments.gaussian_moment_joint_probe
