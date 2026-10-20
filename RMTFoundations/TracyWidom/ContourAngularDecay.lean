import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourAngularDecay
open Real
lemma one_sub_cos_quadratic (t : ℝ /- [definition] -/)
    (ht : |t| ≤ Real.pi /- [standing] -/) :
    2*t^2/Real.pi^2 ≤ 1-cos t := by
  have hb := mul_le_sin (show 0 ≤ |t|/2 by positivity)
    (show |t|/2 ≤ Real.pi/2 by linarith)
  have hb' : |t|/Real.pi ≤ sin (|t|/2) := by convert hb using 1; ring
  have hz : 0 ≤ |t|/Real.pi := div_nonneg (abs_nonneg t) pi_pos.le
  have hs : (|t|/Real.pi)^2 ≤ sin (|t|/2)^2 := by nlinarith
  have hc : cos |t| = cos t := by
    rcases le_total 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,cos_neg]
  have H := cos_two_mul (|t|/2)
  rw [show 2*(|t|/2) = |t| by ring,hc] at H
  have Hs := sin_sq_add_cos_sq (|t|/2)
  have ha : |t|^2=t^2 := sq_abs t
  have hden : (|t|/Real.pi)^2=t^2/Real.pi^2 := by rw [div_pow,ha]
  rw [hden] at hs
  have hscale : 2*t^2/Real.pi^2 = 2*(t^2/Real.pi^2) := by ring
  rw [hscale]
  linarith
lemma angular_exponent_identity (r x t : ℝ /- [definition] -/) :
    x*r*cos t-r^2/2*cos (2*t)-(x*r-r^2/2) =
      -r^2*(1-cos t)^2-r*(x-2*r)*(1-cos t) := by
  rw [cos_two_mul]
  ring
/-- Gaussian angular suppression; no pointwise convergence premise is used. -/
theorem angular_exponent_upper (r x t h : ℝ /- [definition] -/)
    (ht : |t| ≤ Real.pi /- [standing] -/)
    (hh : 0 ≤ h /- [standing] -/)
    (hr : h ≤ r*(x-2*r) /- [standing] -/) :
    x*r*cos t-r^2/2*cos (2*t)-(x*r-r^2/2) ≤ -2*h*t^2/Real.pi^2 := by
  rw [angular_exponent_identity]
  have hc : 0 ≤ 1-cos t := sub_nonneg.mpr (cos_le_one t)
  have hq := one_sub_cos_quadratic t ht
  have H1 := mul_le_mul_of_nonneg_right hr hc
  have H2 := mul_le_mul_of_nonneg_left hq hh
  have H3 := mul_nonneg (sq_nonneg r) (sq_nonneg (1-cos t))
  calc
    _ ≤ -h*(1-cos t) := by nlinarith
    _ ≤ -(h*(2*t^2/Real.pi^2)) := by linarith
    _ = _ := by ring
/-- Both angular endpoints and unbounded radial sizes satisfy the complete premises. -/
theorem angular_joint_probe (n : ℕ /- [definition] -/) :
    ∃ r x h : ℝ, 0 < r ∧ 0 < h ∧ h ≤ r*(x-2*r) ∧
      ∀ t, |t| ≤ Real.pi →
        x*r*cos t-r^2/2*cos (2*t)-(x*r-r^2/2) ≤ -2*h*t^2/Real.pi^2 := by
  let r : ℝ := (n:ℝ)+1
  have hp : 0 < r := by dsimp [r]; positivity
  have hbound : r ≤ r*((2*r+1)-2*r) := by ring_nf; exact le_rfl
  exact ⟨r,2*r+1,r,hp,hp,hbound,fun t ht => angular_exponent_upper r (2*r+1) t r ht hp.le hbound⟩
end RMTFoundations.TracyWidom.ContourAngularDecay

#print axioms RMTFoundations.TracyWidom.ContourAngularDecay.one_sub_cos_quadratic
#print axioms RMTFoundations.TracyWidom.ContourAngularDecay.angular_exponent_identity
#print axioms RMTFoundations.TracyWidom.ContourAngularDecay.angular_exponent_upper
#print axioms RMTFoundations.TracyWidom.ContourAngularDecay.angular_joint_probe
