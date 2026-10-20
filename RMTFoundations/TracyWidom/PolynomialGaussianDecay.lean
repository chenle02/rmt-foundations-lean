import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.PolynomialGaussianDecay
open Filter Topology Real Polynomial Asymptotics

/-- Literal polynomial times a positive Gaussian tends to zero. -/
theorem polynomial_gaussian_tendsto
    (p : Polynomial ℝ /- [definition] -/)
    (b : ℝ /- [definition] -/)
    (hb : 0 < b /- [standing] -/) :
    Tendsto (fun x : ℝ => p.eval x * exp (-b*x^2)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add,add_mul,add_zero] using hp.add hq
  | monomial n a =>
    have he : Tendsto (fun x : ℝ => exp (-(1/2:ℝ)*x)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (show (0:ℝ)<1/2 by norm_num))
    have H := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (n:ℝ)).tendsto_zero_of_tendsto he
    have H' : Tendsto (fun x : ℝ => x^n * exp (-b*x^2)) atTop (𝓝 0) := by
      convert H using 1
      funext x
      rw [Real.rpow_natCast]
    simpa only [Polynomial.eval_monomial,mul_assoc,mul_zero] using H'.const_mul a

/-- Complete joint witness, retaining positive Gaussian rate and unbounded degree. -/
theorem polynomial_gaussian_joint_probe (n : ℕ /- [definition] -/) :
    ∃ p : Polynomial ℝ, p.natDegree = n+1 ∧ p ≠ 0 ∧
      Tendsto (fun x : ℝ => p.eval x*exp (-(1:ℝ)*x^2)) atTop (𝓝 0) := by
  refine ⟨Polynomial.X^(n+1),by simp,by simp,?_⟩
  exact polynomial_gaussian_tendsto _ 1 (by norm_num)

end RMTFoundations.TracyWidom.PolynomialGaussianDecay

#print axioms RMTFoundations.TracyWidom.PolynomialGaussianDecay.polynomial_gaussian_tendsto
#print axioms RMTFoundations.TracyWidom.PolynomialGaussianDecay.polynomial_gaussian_joint_probe
