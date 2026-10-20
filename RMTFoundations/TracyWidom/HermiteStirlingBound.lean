import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteStirlingBound
open Real Stirling
/-- A simple factorial upper bound is enough for the N powers to cancel. -/
theorem factorial_upper (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    (N.factorial : ℝ) ≤ exp 1 *sqrt (N:ℝ)*((N:ℝ)/exp 1)^N := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have H := stirlingSeq'_antitone (show 0 ≤ n by omega)
  change stirlingSeq (n+1) ≤ stirlingSeq 1 at H
  rw [stirlingSeq_one,stirlingSeq] at H
  have hp : 0 < sqrt (2*((n+1:ℕ):ℝ))*(((n+1:ℕ):ℝ)/exp 1)^(n+1) := by positivity
  have hsqrt : sqrt (2*((n+1:ℕ):ℝ)) = sqrt 2*sqrt ((n+1:ℕ):ℝ) := by
    rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have htwo : sqrt (2:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.2 (by norm_num))
  apply (div_le_iff₀ hp).mp at H
  rw [hsqrt] at H
  convert H using 1
  all_goals first | rfl | field_simp [htwo]
/-- Every positive dimension is covered, with strictly positive normalization. -/
theorem factorial_joint_probe (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < (N.factorial:ℝ) ∧
      (N.factorial:ℝ) ≤ exp 1*sqrt (N:ℝ)*((N:ℝ)/exp 1)^N := by
  exact ⟨k+1,by omega,by positivity,factorial_upper (k+1) (by omega)⟩
end RMTFoundations.TracyWidom.HermiteStirlingBound

#print axioms RMTFoundations.TracyWidom.HermiteStirlingBound.factorial_upper
#print axioms RMTFoundations.TracyWidom.HermiteStirlingBound.factorial_joint_probe
