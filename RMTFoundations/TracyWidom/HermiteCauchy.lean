import RMTFoundations.TracyWidom.GUEHermite
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCauchy
open Polynomial Complex
open RMTFoundations.TracyWidom.GUEHermite

noncomputable def complexPolynomial (n : ℕ /- [definition] -/) : Polynomial ℂ :=
  (realHermite n).map Complex.ofRealHom

noncomputable def complexHermite (n : ℕ /- [definition] -/)
    (z : ℂ /- [definition] -/) : ℂ := (complexPolynomial n).eval z

lemma complex_hermite_of_real (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : complexHermite n x = (hpoly n x : ℂ) := by
  exact Polynomial.eval_map_apply Complex.ofRealHom x

lemma complex_polynomial_succ (n : ℕ /- [definition] -/) :
    complexPolynomial (n+1) = X * complexPolynomial n - derivative (complexPolynomial n) := by
  simp only [complexPolynomial, realHermite, Polynomial.hermite_succ,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.derivative_map]

lemma complex_hermite_succ (n : ℕ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    complexHermite (n+1) z = z * complexHermite n z -
      (complexPolynomial n).derivative.eval z := by
  simp only [complexHermite, complex_polynomial_succ, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_X]

noncomputable def generating (x z : ℂ /- [definition] -/) : ℂ :=
  Complex.exp (x*z-z^2/2)

lemma generating_has_deriv (x z : ℂ /- [definition] -/) :
    HasDerivAt (generating x) ((x-z)*generating x z) z := by
  have hp := ((hasDerivAt_id z).const_mul x).sub
    (((hasDerivAt_id z).pow 2).div_const 2)
  have hphase : HasDerivAt (fun t : ℂ => x*t-t^2/2) (x-z) z := by
    apply hp.congr_deriv
    norm_num <;> ring
  exact hphase.cexp.congr_deriv (mul_comm _ _)

lemma generating_entire (x : ℂ /- [definition] -/) :
    Differentiable ℂ (generating x) := by
  intro z
  exact (generating_has_deriv x z).differentiableAt

lemma hermite_generating_derivative (n : ℕ /- [definition] -/)
    (x z : ℂ /- [definition] -/) :
    HasDerivAt (fun t : ℂ => complexHermite n (x-t)*generating x t)
      (complexHermite (n+1) (x-z)*generating x z) z := by
  have hp := ((complexPolynomial n).hasDerivAt (x-z)).comp z
    ((hasDerivAt_id z).const_sub x)
  have h := hp.mul (generating_has_deriv x z)
  apply h.congr_deriv
  rw [complex_hermite_succ]
  dsimp [complexHermite, Function.comp_apply]
  ring

/-- Exact exponential generating-function derivative formula for the literal Hermite polynomial. -/
theorem iterated_generating (n : ℕ /- [definition] -/)
    (x : ℂ /- [definition] -/) :
    iteratedDeriv n (generating x) =
      fun z => complexHermite n (x-z)*generating x z := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    funext z
    simp [complexHermite, complexPolynomial, realHermite]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hermite_generating_derivative n x z).deriv

lemma iterated_generating_zero (n : ℕ /- [definition] -/)
    (x : ℂ /- [definition] -/) :
    iteratedDeriv n (generating x) 0 = complexHermite n x := by
  rw [iterated_generating]
  simp [generating]

/-- Literal Cauchy coefficient representation, with positive radius supplied explicitly.
No asymptotic or contour-deformation premise is taken. -/
theorem hermite_cauchy_integral (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (R : ℝ /- [definition] -/)
    (hR : 0 < R /- [standing] -/) :
    circleIntegral (fun z : ℂ => (1/z^(n+1))*generating x z) 0 R =
      (2*Real.pi*Complex.I/(n.factorial : ℂ)) * (hpoly n x : ℂ) := by
  have h := ((generating_entire x).differentiableOn).circleIntegral_one_div_sub_center_pow_smul
    (c := (0 : ℂ)) hR n
  simpa only [sub_zero, smul_eq_mul, iterated_generating_zero, complex_hermite_of_real] using h

/-- The contour representation includes the literal existing Gaussian/factorial normalization. -/
theorem hermite_mode_cauchy (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (R : ℝ /- [definition] -/)
    (hR : 0 < R /- [standing] -/) :
    (hermiteMode n x : ℂ) =
      (gaussianWeight x * hermiteNormalizer n * (n.factorial : ℝ) : ℂ) /
        (2*Real.pi*Complex.I) *
          circleIntegral (fun z : ℂ => (1/z^(n+1))*generating x z) 0 R := by
  rw [hermite_cauchy_integral n x R hR]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi : (2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  simp only [hermiteMode, Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp

/-- Complete growing joint example on the actual generating function, with nonzero source value
and the coalescing-saddle radius sqrt(N), every standing radius premise proved by terms. -/
theorem hermite_cauchy_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < Real.sqrt (n+1 : ℕ) ∧
      generating (2*Real.sqrt (n+1 : ℕ)) 0 = 1 ∧
      circleIntegral (fun z : ℂ => (1/z^(n+1+1))*
        generating (2*Real.sqrt (n+1 : ℕ)) z) 0 (Real.sqrt (n+1 : ℕ)) =
        (2*Real.pi*Complex.I/((n+1).factorial : ℂ)) *
          (hpoly (n+1) (2*Real.sqrt (n+1 : ℕ)) : ℂ)) := by
  refine ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, fun n => ?_⟩
  have hR : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  refine ⟨hR, by simp [generating], ?_⟩
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hermite_cauchy_integral (n+1)
    (2*Real.sqrt (n+1 : ℕ)) (Real.sqrt (n+1 : ℕ)) hR
end RMTFoundations.TracyWidom.HermiteCauchy

#print axioms RMTFoundations.TracyWidom.HermiteCauchy.complexPolynomial
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.complexHermite
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.complex_hermite_of_real
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.complex_polynomial_succ
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.complex_hermite_succ
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.generating
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.generating_has_deriv
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.generating_entire
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.hermite_generating_derivative
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.iterated_generating
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.iterated_generating_zero
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.hermite_cauchy_integral
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.hermite_mode_cauchy
#print axioms RMTFoundations.TracyWidom.HermiteCauchy.hermite_cauchy_joint_probe
