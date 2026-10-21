import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourGaussianIntegral
open Real Set MeasureTheory Filter
/-- Dominate the entire angular integral by the full-line Gaussian integral. -/
theorem gaussian_domination (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (b : ℝ /- [definition] -/)
    (hb : 0 < b /- [standing] -/)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi, f t ≤ exp (-b*t^2) /- [standing] -/) :
    (∫ t in Icc (-Real.pi) Real.pi, f t) ≤ sqrt (Real.pi/b) := by
  have hfi : IntegrableOn f (Icc (-Real.pi) Real.pi) := hf.integrableOn_Icc
  have hi := integrable_exp_neg_mul_sq hb
  calc
    _ ≤ ∫ t in Icc (-Real.pi) Real.pi, exp (-b*t^2) :=
      setIntegral_mono_on hfi hi.integrableOn measurableSet_Icc hbound
    _ ≤ ∫ t : ℝ, exp (-b*t^2) :=
      setIntegral_le_integral hi (ae_of_all _ fun t => (exp_pos _).le)
    _ = _ := integral_gaussian b
/-- Actual positive Gaussians witness every analytic premise jointly. -/
theorem gaussian_joint_probe (k : ℕ /- [definition] -/) :
    ∃ b : ℝ, ∃ f : ℝ → ℝ, 0 < b ∧ Continuous f ∧ 0 < f 0 ∧
      (∀ t ∈ Icc (-Real.pi) Real.pi, f t ≤ exp (-b*t^2)) ∧
      (∫ t in Icc (-Real.pi) Real.pi, f t) ≤ sqrt (Real.pi/b) := by
  let b : ℝ := (k:ℝ)+1
  let f : ℝ → ℝ := fun t => exp (-b*t^2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : Continuous f := by dsimp [f]; fun_prop
  exact ⟨b,f,hb,hf,by dsimp [f]; positivity,fun _ _ => le_rfl,
    gaussian_domination f hf b hb (fun _ _ => le_rfl)⟩
lemma angular_gaussian_scale (h : ℝ /- [definition] -/)
    (hh : 0 < h /- [standing] -/) :
    sqrt (Real.pi/(2*h/Real.pi^2)) ≤ 2*Real.pi/sqrt h := by
  have hpi8 : Real.pi ≤ 8 := le_trans (Real.pi_lt_four.le) (by norm_num)
  have hq : Real.pi^3 ≤ 8*Real.pi^2 := by
    have H := mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hpi8)
    nlinarith
  have hleft : (sqrt (Real.pi/(2*h/Real.pi^2)))^2=Real.pi^3/(2*h) := by
    rw [sq_sqrt (by positivity)]
    field_simp
  have hright : (2*Real.pi/sqrt h)^2=4*Real.pi^2/h := by
    rw [div_pow,sq_sqrt hh.le]
    ring
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [hleft,hright]
  calc
    _ = (Real.pi^3/2)/h := by ring
    _ ≤ (4*Real.pi^2)/h := div_le_div_of_nonneg_right (by linarith) hh.le
/-- A convenient coarse angular mean bound suffices to cancel dimension powers. -/
theorem angular_mean_bound (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (h : ℝ /- [definition] -/)
    (hh : 0 < h /- [standing] -/)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi,
      f t ≤ exp (-(2*h/Real.pi^2)*t^2) /- [standing] -/) :
    (∫ t in Icc (-Real.pi) Real.pi, f t)/(2*Real.pi) ≤ 1/sqrt h := by
  have H := (gaussian_domination f hf (2*h/Real.pi^2) (by positivity) hbound).trans
    (angular_gaussian_scale h hh)
  calc
    _ ≤ (2*Real.pi/sqrt h)/(2*Real.pi) := div_le_div_of_nonneg_right H (by positivity)
    _ = _ := by field_simp
theorem angular_mean_joint_probe (k : ℕ /- [definition] -/) :
    ∃ h : ℝ, ∃ f : ℝ → ℝ, 0 < h ∧ Continuous f ∧ 0 < f 0 ∧
      (∀ t ∈ Icc (-Real.pi) Real.pi, f t ≤ exp (-(2*h/Real.pi^2)*t^2)) ∧
      (∫ t in Icc (-Real.pi) Real.pi, f t)/(2*Real.pi) ≤ 1/sqrt h := by
  let h : ℝ := (k:ℝ)+1
  let f : ℝ → ℝ := fun t => exp (-(2*h/Real.pi^2)*t^2)
  have hh : 0 < h := by dsimp [h]; positivity
  have hf : Continuous f := by dsimp [f]; fun_prop
  exact ⟨h,f,hh,hf,by dsimp [f]; positivity,fun _ _ => le_rfl,
    angular_mean_bound f hf h hh (fun _ _ => le_rfl)⟩
end RMTFoundations.TracyWidom.ContourGaussianIntegral

#print axioms RMTFoundations.TracyWidom.ContourGaussianIntegral.gaussian_domination
#print axioms RMTFoundations.TracyWidom.ContourGaussianIntegral.gaussian_joint_probe
#print axioms RMTFoundations.TracyWidom.ContourGaussianIntegral.angular_gaussian_scale
#print axioms RMTFoundations.TracyWidom.ContourGaussianIntegral.angular_mean_bound
#print axioms RMTFoundations.TracyWidom.ContourGaussianIntegral.angular_mean_joint_probe
