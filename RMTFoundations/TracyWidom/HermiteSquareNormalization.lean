import RMTFoundations.TracyWidom.GUEHermite
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteSquareNormalization
open Real Polynomial
open RMTFoundations.TracyWidom.GUEHermite
/-- Exact square of the  normalized probabilists' Hermite function. -/
lemma hermiteMode_square (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    (hermiteMode n x)^2 = (hpoly n x)^2*exp (-x^2/2)/
      (sqrt (2*Real.pi)*(n.factorial:ℝ)) := by
  rw [hermiteMode,mul_pow,mul_pow,hermiteNormalizer_square,gaussianWeight,
    ←exp_nat_mul]
  have he : (2:ℝ)*(-(x^2)/4) = -x^2/2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  ring
lemma scaled_hermiteMode_square (n : ℕ /- [definition] -/)
    (a x : ℝ /- [definition] -/) :
    (a*hermiteMode n x)^2 = a^2*(hpoly n x)^2*exp (-x^2/2)/
      (sqrt (2*Real.pi)*(n.factorial:ℝ)) := by
  rw [mul_pow,hermiteMode_square]
  ring
lemma previous_normalizer (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    sqrt (N:ℝ)*hermiteNormalizer N=hermiteNormalizer (N-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simpa using sqrt_mul_hermiteNormalizer_succ k
/-- Positive Gaussian weight, positive normalization and growing degrees coexist. -/
theorem normalization_joint_probe (k : ℕ /- [definition] -/) :
    ∃ n : ℕ, k < n ∧ 0 < hermiteNormalizer n ∧ Monic (realHermite n) ∧
      ∀ x : ℝ, 0 < gaussianWeight x ∧
        (hermiteMode n x)^2 = (hpoly n x)^2*exp (-x^2/2)/
          (sqrt (2*Real.pi)*(n.factorial:ℝ)) := by
  exact ⟨k+1,by omega,hermiteNormalizer_pos _,
    (hermite_monic (k+1)).map (Int.castRingHom ℝ),
    fun x => ⟨exp_pos _,hermiteMode_square _ x⟩⟩
end RMTFoundations.TracyWidom.HermiteSquareNormalization

#print axioms RMTFoundations.TracyWidom.HermiteSquareNormalization.hermiteMode_square
#print axioms RMTFoundations.TracyWidom.HermiteSquareNormalization.scaled_hermiteMode_square
#print axioms RMTFoundations.TracyWidom.HermiteSquareNormalization.previous_normalizer
#print axioms RMTFoundations.TracyWidom.HermiteSquareNormalization.normalization_joint_probe
