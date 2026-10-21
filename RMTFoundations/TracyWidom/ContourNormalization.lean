import RMTFoundations.TracyWidom.HermiteStirlingBound
import RMTFoundations.TracyWidom.ContourRadiusAlgebra
import RMTFoundations.TracyWidom.ContourEdgePowers
import RMTFoundations.TracyWidom.ContourRadialLog
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourNormalization
open Real
open RMTFoundations.TracyWidom.HermiteStirlingBound RMTFoundations.TracyWidom.ContourRadiusAlgebra
open RMTFoundations.TracyWidom.ContourEdgePowers RMTFoundations.TracyWidom.ContourRadialLog
open RMTFoundations.TracyWidom.HermiteEdgeReduction
/-- Normalize a genuine coefficient estimate without dropping its angular factor. -/
lemma normalized_coefficient_bound (n : ℕ /- [definition] -/)
    (a r h x P : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/)
    (hh : 0 < h /- [standing] -/)
    (hP : |P| ≤ (n.factorial:ℝ)*exp (x*r-r^2/2)/(r^n*sqrt h) /- [standing] -/) :
    a^2*P^2*exp (-x^2/2)/(sqrt (2*Real.pi)*(n.factorial:ℝ)) ≤
      (a^2*exp (2*x*r-r^2-x^2/2)/(sqrt (2*Real.pi)*h))*
        ((n.factorial:ℝ)/r^(2*n)) := by
  have hfac : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : 0 < sqrt h := sqrt_pos.mpr hh
  have hc : 0 ≤ (n.factorial:ℝ)*exp (x*r-r^2/2)/(r^n*sqrt h) := by positivity
  have H := (sq_le_sq₀ (abs_nonneg P) hc).mpr hP
  rw [sq_abs] at H
  have HM := mul_le_mul_of_nonneg_left H
    (show 0 ≤ a^2*exp (-x^2/2)/(sqrt (2*Real.pi)*(n.factorial:ℝ)) by positivity)
  calc
    _ = (a^2*exp (-x^2/2)/(sqrt (2*Real.pi)*(n.factorial:ℝ)))*P^2 := by ring
    _ ≤ _ := HM
    _ = _ := by
      rw [div_pow,mul_pow,mul_pow,sq_sqrt hh.le,←exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show 2*(x*r-r^2/2)=2*x*r-r^2 by ring]
      have he : exp (2*x*r-r^2-x^2/2) = exp (-x^2/2)*exp (2*x*r-r^2) := by
        rw [←exp_add]
        congr 1
        ring
      have hpow : r^(2*n)=(r^n)^2 := by rw [Nat.mul_comm 2 n,pow_mul]
      rw [he,hpow]
      field_simp
/-- Factorial growth is cancelled by the edge amplitude and angular scale. -/
lemma radial_normalization_bound (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (y : ℝ /- [definition] -/)
    (hd : edgeDelta N < 1 /- [standing] -/) :
    ((edgeAmplitude N)^2*
      exp (2*(sqrt (N:ℝ)*(2+(edgeDelta N)^2*y))*(sqrt (N:ℝ)*(1-edgeDelta N))-
        (sqrt (N:ℝ)*(1-edgeDelta N))^2-(sqrt (N:ℝ)*(2+(edgeDelta N)^2*y))^2/2)/
      (sqrt (2*Real.pi)*((N:ℝ)*edgeDelta N/2)))*
      ((N.factorial:ℝ)/(sqrt (N:ℝ)*(1-edgeDelta N))^(2*N)) ≤
      (2*exp 1/sqrt (2*Real.pi))*exp (2*radial (N:ℝ) (edgeDelta N) y) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp := edgeDelta_pos N hN
  have hf := factorial_upper N hN
  let r := sqrt (N:ℝ)*(1-edgeDelta N)
  let x := sqrt (N:ℝ)*(2+(edgeDelta N)^2*y)
  have hr : 0 < r := by dsimp [r]; positivity
  have H := div_le_div_of_nonneg_right hf (pow_nonneg hr.le (2*N))
  have HC := mul_le_mul_of_nonneg_left H
    (show 0 ≤ (edgeAmplitude N)^2*exp (2*x*r-r^2-x^2/2)/
      (sqrt (2*Real.pi)*((N:ℝ)*edgeDelta N/2)) by positivity)
  calc
    _ ≤ _ := HC
    _ = _ := by
      rw [show (exp 1*sqrt (N:ℝ)*(((N:ℝ)/exp 1)^N))/r^(2*N) =
        exp 1*sqrt (N:ℝ)*((((N:ℝ)/exp 1)^N)/r^(2*N)) by ring]
      dsimp [r]
      rw [radius_factor_identity N hN (edgeDelta N) hd]
      have hex : exp (2*x*(sqrt (N:ℝ)*(1-edgeDelta N))-
          (sqrt (N:ℝ)*(1-edgeDelta N))^2-x^2/2)*
          exp (-(N:ℝ)-2*(N:ℝ)*log (1-edgeDelta N)) =
          exp (2*radial (N:ℝ) (edgeDelta N) y) := by
        rw [←exp_add]
        congr 1
        dsimp [x,radial]
        have HE := radial_exponent_identity (N:ℝ) (edgeDelta N) y hn.le
        nlinarith only [HE]
      have ha := amplitude_delta_balance N hN
      have hrearr : ((edgeAmplitude N)^2*
          exp (2*x*(sqrt (N:ℝ)*(1-edgeDelta N))-
            (sqrt (N:ℝ)*(1-edgeDelta N))^2-x^2/2)/
          (sqrt (2*Real.pi)*((N:ℝ)*edgeDelta N/2)))*
          (exp 1*sqrt (N:ℝ)*exp (-(N:ℝ)-2*(N:ℝ)*log (1-edgeDelta N))) =
          ((edgeAmplitude N)^2*sqrt (N:ℝ))*exp 1*
          (exp (2*x*(sqrt (N:ℝ)*(1-edgeDelta N))-
            (sqrt (N:ℝ)*(1-edgeDelta N))^2-x^2/2)*
          exp (-(N:ℝ)-2*(N:ℝ)*log (1-edgeDelta N)))/
          (sqrt (2*Real.pi)*((N:ℝ)*edgeDelta N/2)) := by ring
      rw [hrearr,hex,ha]
      field_simp
/-- Nonzero coefficients and growing positive dimensions jointly witness the algebraic interface. -/
theorem normalization_bound_joint_probe (k : ℕ /- [definition] -/) :
    ∃ n : ℕ, k < n ∧ ∃ a r h x P : ℝ,
      0 < a ∧ 0 < r ∧ 0 < h ∧ P ≠ 0 ∧
      |P| ≤ (n.factorial:ℝ)*exp (x*r-r^2/2)/(r^n*sqrt h) ∧
      a^2*P^2*exp (-x^2/2)/(sqrt (2*Real.pi)*(n.factorial:ℝ)) ≤
        (a^2*exp (2*x*r-r^2-x^2/2)/(sqrt (2*Real.pi)*h))*
          ((n.factorial:ℝ)/r^(2*n)) := by
  let n := k+1
  let P : ℝ := (n.factorial:ℝ)*exp (3-(1:ℝ)/2)/2
  have hPpos : 0 < P := by dsimp [P]; positivity
  have H : |P| ≤ (n.factorial:ℝ)*exp (3*1-(1:ℝ)^2/2)/((1:ℝ)^n*sqrt 1) := by
    rw [abs_of_pos hPpos]
    dsimp [P]
    norm_num
    positivity
  exact ⟨n,by dsimp [n];omega,1,1,1,3,P,by norm_num,by norm_num,
    by norm_num,hPpos.ne',H,normalized_coefficient_bound n 1 1 1 3 P (by norm_num) (by norm_num) H⟩
/-- The radial normalization premises hold on the actual scales at arbitrarily large dimensions. -/
theorem radial_normalization_joint_probe (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < N ∧ edgeDelta N < 1 ∧ ∀ y : ℝ,
    ((edgeAmplitude N)^2*
      exp (2*(sqrt (N:ℝ)*(2+(edgeDelta N)^2*y))*(sqrt (N:ℝ)*(1-edgeDelta N))-
        (sqrt (N:ℝ)*(1-edgeDelta N))^2-(sqrt (N:ℝ)*(2+(edgeDelta N)^2*y))^2/2)/
      (sqrt (2*Real.pi)*((N:ℝ)*edgeDelta N/2)))*
      ((N.factorial:ℝ)/(sqrt (N:ℝ)*(1-edgeDelta N))^(2*N)) ≤
      (2*exp 1/sqrt (2*Real.pi))*exp (2*radial (N:ℝ) (edgeDelta N) y) := by
  let N := max 8 (k+1)
  have hn : 0 < N := by dsimp [N];omega
  have hd : edgeDelta N < 1 := lt_of_le_of_lt (edgeDelta_half N (le_max_left _ _)) (by norm_num)
  exact ⟨N,by dsimp [N];omega,hn,hd,fun y => radial_normalization_bound N hn y hd⟩
end RMTFoundations.TracyWidom.ContourNormalization

#print axioms RMTFoundations.TracyWidom.ContourNormalization.normalized_coefficient_bound
#print axioms RMTFoundations.TracyWidom.ContourNormalization.radial_normalization_bound
#print axioms RMTFoundations.TracyWidom.ContourNormalization.normalization_bound_joint_probe
#print axioms RMTFoundations.TracyWidom.ContourNormalization.radial_normalization_joint_probe
