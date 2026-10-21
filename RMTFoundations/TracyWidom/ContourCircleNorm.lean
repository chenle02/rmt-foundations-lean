import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourCircleNorm
open Complex
/-- Literal angular modulus of the Gaussian generating function. -/
lemma gaussian_circle_norm (x r t : ℝ /- [definition] -/) :
    ‖Complex.exp ((x:ℂ)*circleMap 0 r t-(circleMap 0 r t)^2/2)‖ =
      Real.exp (x*r*Real.cos t-r^2/2*Real.cos (2*t)) := by
  rw [Complex.norm_exp]
  congr 1
  have hsquare : (circleMap 0 r t)^2 = circleMap 0 (r^2) (2*t) := by
    simpa using circleMap_zero_pow 2 r t
  rw [hsquare]
  norm_num [Complex.sub_re,Complex.mul_re,Complex.div_re,
    Complex.normSq_apply,circleMap_zero_re,circleMap_zero_im]
  ring
/-- The exact Cauchy path norm retains the Gaussian angular factor. -/
lemma cauchy_path_norm (n : ℕ /- [definition] -/)
    (x r t : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    ‖deriv (circleMap 0 r) t * ((circleMap 0 r t)^(n+1))⁻¹ *
      Complex.exp ((x:ℂ)*circleMap 0 r t-(circleMap 0 r t)^2/2)‖ =
      (r/r^(n+1))*Real.exp (x*r*Real.cos t-r^2/2*Real.cos (2*t)) := by
  rw [(hasDerivAt_circleMap 0 r t).deriv]
  simp only [norm_mul,norm_inv,norm_pow,norm_circleMap_zero,abs_of_pos hr,
    Complex.norm_I,mul_one]
  rw [gaussian_circle_norm]
  simp only [div_eq_mul_inv]
/-- Positive radii and actual, nonzero generating values satisfy the full interface. -/
theorem circle_norm_joint_probe (n : ℕ /- [definition] -/) :
    ∃ r : ℝ, 0 < r ∧
      ‖deriv (circleMap 0 r) 0 * ((circleMap 0 r 0)^(n+1))⁻¹ *
        Complex.exp ((2:ℂ)*circleMap 0 r 0-(circleMap 0 r 0)^2/2)‖ =
        (r/r^(n+1))*Real.exp (2*r-r^2/2) := by
  refine ⟨(n:ℝ)+1,by positivity,?_⟩
  simpa using
    cauchy_path_norm n 2 ((n:ℝ)+1) 0 (by positivity)
end RMTFoundations.TracyWidom.ContourCircleNorm

#print axioms RMTFoundations.TracyWidom.ContourCircleNorm.gaussian_circle_norm
#print axioms RMTFoundations.TracyWidom.ContourCircleNorm.cauchy_path_norm
#print axioms RMTFoundations.TracyWidom.ContourCircleNorm.circle_norm_joint_probe
