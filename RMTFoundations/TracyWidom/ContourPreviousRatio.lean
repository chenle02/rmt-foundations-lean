import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourPreviousRatio
open Real
lemma previous_factorial_ratio (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    ((N-1).factorial:ℝ)/r^(2*(N-1)) =
      ((N.factorial:ℝ)/r^(2*N))*(r^2/(N:ℝ)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [Nat.succ_sub_one,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  rw [show 2*(k+1)=2*k+2 by omega,pow_add]
  field_simp
lemma edge_radius_ratio (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (d : ℝ /- [definition] -/) :
    (sqrt (N:ℝ)*(1-d))^2/(N:ℝ)=(1-d)^2 := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [mul_pow,sq_sqrt hn.le]
  field_simp
lemma previous_factorial_le (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (d : ℝ /- [definition] -/)
    (hd0 : 0 ≤ d /- [standing] -/)
    (hd1 : d < 1 /- [standing] -/) :
    ((N-1).factorial:ℝ)/(sqrt (N:ℝ)*(1-d))^(2*(N-1)) ≤
      (N.factorial:ℝ)/(sqrt (N:ℝ)*(1-d))^(2*N) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hr : 0 < sqrt (N:ℝ)*(1-d) := by positivity
  rw [previous_factorial_ratio N hN _ hr,edge_radius_ratio N hN d]
  have H : (1-d)^2 ≤ 1 := by nlinarith
  simpa using mul_le_mul_of_nonneg_left H
    (by positivity : 0 ≤ (N.factorial:ℝ)/(sqrt (N:ℝ)*(1-d))^(2*N))
theorem previous_ratio_joint_probe (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < N ∧ ∃ d : ℝ, 0 < d ∧ d < 1 ∧
      ((N-1).factorial:ℝ)/(sqrt (N:ℝ)*(1-d))^(2*(N-1)) ≤
      (N.factorial:ℝ)/(sqrt (N:ℝ)*(1-d))^(2*N) := by
  exact ⟨k+1,by omega,by omega,1/4,by norm_num,by norm_num,
    previous_factorial_le (k+1) (by omega) (1/4) (by norm_num) (by norm_num)⟩
end RMTFoundations.TracyWidom.ContourPreviousRatio

#print axioms RMTFoundations.TracyWidom.ContourPreviousRatio.previous_factorial_ratio
#print axioms RMTFoundations.TracyWidom.ContourPreviousRatio.edge_radius_ratio
#print axioms RMTFoundations.TracyWidom.ContourPreviousRatio.previous_factorial_le
#print axioms RMTFoundations.TracyWidom.ContourPreviousRatio.previous_ratio_joint_probe
