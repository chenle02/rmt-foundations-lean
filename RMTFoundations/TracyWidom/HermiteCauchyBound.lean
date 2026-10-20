import RMTFoundations.TracyWidom.HermiteGenerating
import RMTFoundations.TracyWidom.HermiteComplexCast
import RMTFoundations.TracyWidom.ContourAngularDecay
import RMTFoundations.TracyWidom.ContourGaussianIntegral
import RMTFoundations.TracyWidom.ContourCircleNorm
import RMTFoundations.TracyWidom.ContourCircleIntegral
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCauchyBound
open Real Set MeasureTheory Complex
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteGenerating
open RMTFoundations.TracyWidom.HermiteComplexCast RMTFoundations.TracyWidom.ContourAngularDecay
open RMTFoundations.TracyWidom.ContourGaussianIntegral RMTFoundations.TracyWidom.ContourCircleNorm
open RMTFoundations.TracyWidom.ContourCircleIntegral
/-- Cauchy's exact coefficient formula with a Gaussian angular estimate. -/
theorem hermite_cauchy_bound (n : ℕ /- [definition] -/)
    (x r h : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/)
    (hh : 0 < h /- [standing] -/)
    (hgap : h ≤ r*(x-2*r) /- [standing] -/) :
    |hpoly n x| ≤ (n.factorial:ℝ)*Real.exp (x*r-r^2/2)/(r^n*Real.sqrt h) := by
  let E : ℝ := x*r-r^2/2
  let f : ℝ → ℝ := fun t => Real.exp (x*r*Real.cos t-r^2/2*Real.cos (2*t)-E)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hb : ∀ t ∈ Icc (-Real.pi) Real.pi,
      f t ≤ Real.exp (-(2*h/Real.pi^2)*t^2) := by
    intro t ht
    apply Real.exp_le_exp.mpr
    have H := angular_exponent_upper r x t h (abs_le.mpr ht) hh.le hgap
    convert H using 1 <;> first | rfl | ring
  have hm := angular_mean_bound f hf h hh hb
  have hp : ∀ t : ℝ,
      ‖deriv (circleMap 0 r) t*((circleMap 0 r t)^(n+1))⁻¹*
        generating (x:ℂ) (circleMap 0 r t)‖ =
      (Real.exp E/r^n)*f t := by
    intro t
    rw [generating,cauchy_path_norm n x r t hr]
    have he : Real.exp E*f t = Real.exp (x*r*Real.cos t-r^2/2*Real.cos (2*t)) := by
      dsimp [f]
      rw [←Real.exp_add]
      congr 1
      ring
    rw [←he,pow_succ]
    field_simp
  have H := norm_circle_integral_le_centered
    (fun z => (z^(n+1))⁻¹*generating (x:ℂ) z) r
  simp_rw [←mul_assoc,hp] at H
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ←integral_Icc_eq_integral_Ioc] at H
  rw [hermite_cauchy_circle n (x:ℂ) r hr,complex_hpoly] at H
  have hfac : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn : ‖((2*Real.pi*Complex.I)/(n.factorial:ℂ))*(hpoly n x:ℂ)‖ =
      (2*Real.pi/(n.factorial:ℝ))*|hpoly n x| := by
    simp [Real.pi_pos.le,abs_of_nonneg]
  rw [hn] at H
  have Hi : (∫ t in Icc (-Real.pi) Real.pi, f t) ≤ 2*Real.pi/Real.sqrt h := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mp at hm
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hm
  have HR := H.trans (mul_le_mul_of_nonneg_left Hi (by positivity))
  have hrn : 0 < r^n := pow_pos hr n
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  apply (le_div_iff₀ (mul_pos hrn hs)).mpr
  have HH := (mul_le_mul_of_nonneg_right HR (mul_nonneg hfac.le (mul_nonneg hrn.le hs.le)))
  field_simp at HH
  nlinarith
/-- Nonzero monic polynomials and growing positive radii satisfy all premises jointly. -/
theorem cauchy_bound_joint_probe (n : ℕ /- [definition] -/) :
    ∃ r x h : ℝ, 0 < r ∧ 0 < h ∧ h ≤ r*(x-2*r) ∧
      Polynomial.hermite n ≠ 0 ∧
      |hpoly n x| ≤ (n.factorial:ℝ)*Real.exp (x*r-r^2/2)/(r^n*Real.sqrt h) := by
  let r : ℝ := (n:ℝ)+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : r ≤ r*((2*r+1)-2*r) := by ring_nf; exact le_rfl
  exact ⟨r,2*r+1,r,hr,hr,hg,(Polynomial.hermite_monic n).ne_zero,
    hermite_cauchy_bound n (2*r+1) r r hr hr hg⟩
end RMTFoundations.TracyWidom.HermiteCauchyBound

#print axioms RMTFoundations.TracyWidom.HermiteCauchyBound.hermite_cauchy_bound
#print axioms RMTFoundations.TracyWidom.HermiteCauchyBound.cauchy_bound_joint_probe
