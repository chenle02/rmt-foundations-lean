import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourRadiusAlgebra
open Real
lemma radius_gap_identity (N d y : ℝ /- [definition] -/)
    (hN : 0 ≤ N /- [standing] -/) :
    (sqrt N*(1-d))*(sqrt N*(2+d^2*y)-2*(sqrt N*(1-d))) =
      N*d*(1-d)*(2+d*y) := by
  calc
    _ = (sqrt N)^2*d*(1-d)*(2+d*y) := by ring
    _ = _ := by rw [sq_sqrt hN]
lemma radial_exponent_identity (N d y : ℝ /- [definition] -/)
    (hN : 0 ≤ N /- [standing] -/) :
    -N-2*N*log (1-d)+2*(sqrt N*(2+d^2*y))*(sqrt N*(1-d))-
      (sqrt N*(1-d))^2-(sqrt N*(2+d^2*y))^2/2 =
      2*N*(-log (1-d)-d-d^2/2-y*d^3-y^2*d^4/4) := by
  calc
    _ = -N-2*N*log (1-d)+(sqrt N)^2*
        (2*(2+d^2*y)*(1-d)-(1-d)^2-(2+d^2*y)^2/2) := by ring
    _ = _ := by rw [sq_sqrt hN]; ring
lemma radius_factor_identity (n : ℕ /- [definition] -/)
    (hn : 0 < n /- [standing] -/)
    (d : ℝ /- [definition] -/)
    (hd : d < 1 /- [standing] -/) :
    (((n:ℝ)/exp 1)^n)/((sqrt (n:ℝ)*(1-d))^(2*n)) =
      exp (-(n:ℝ)-2*(n:ℝ)*log (1-d)) := by
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp : 0 < 1-d := by linarith
  have hs : (sqrt (n:ℝ))^(2*n) = (n:ℝ)^n := by
    rw [pow_mul,sq_sqrt hN.le]
  have he : (exp 1)^n = exp (n:ℝ) := by rw [←exp_nat_mul]; simp
  have hdexp : (1-d)^(2*n) = exp (2*(n:ℝ)*log (1-d)) := by
    rw [show 2*(n:ℝ)*log (1-d) = ((2*n:ℕ):ℝ)*log (1-d) by push_cast; ring,
      exp_nat_mul,exp_log hp]
  rw [div_pow,mul_pow,hs,he,hdexp]
  have heN : exp (n:ℝ) ≠ 0 := (exp_pos _).ne'
  have heD : exp (2*(n:ℝ)*log (1-d)) ≠ 0 := (exp_pos _).ne'
  have hpow : (n:ℝ)^n ≠ 0 := pow_ne_zero n hN.ne'
  calc
    _ = (exp (n:ℝ)*exp (2*(n:ℝ)*log (1-d)))⁻¹ := by field_simp
    _ = exp (-(n:ℝ)-2*(n:ℝ)*log (1-d)) := by
      rw [←exp_add,←exp_neg]
      congr 1
      ring
/-- Positive dimensions, positive radii and arbitrary points coexist. -/
theorem radius_joint_probe (k : ℕ /- [definition] -/) :
    ∃ n : ℕ, k < n ∧ ∃ d : ℝ, 0 < d ∧ d < 1 ∧
      (((n:ℝ)/exp 1)^n)/((sqrt (n:ℝ)*(1-d))^(2*n)) =
        exp (-(n:ℝ)-2*(n:ℝ)*log (1-d)) := by
  exact ⟨k+1,by omega,1/4,by norm_num,by norm_num,
    radius_factor_identity (k+1) (by omega) (1/4) (by norm_num)⟩
end RMTFoundations.TracyWidom.ContourRadiusAlgebra

#print axioms RMTFoundations.TracyWidom.ContourRadiusAlgebra.radius_gap_identity
#print axioms RMTFoundations.TracyWidom.ContourRadiusAlgebra.radial_exponent_identity
#print axioms RMTFoundations.TracyWidom.ContourRadiusAlgebra.radius_factor_identity
#print axioms RMTFoundations.TracyWidom.ContourRadiusAlgebra.radius_joint_probe
