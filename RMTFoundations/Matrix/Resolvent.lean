import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Resolvent identities and estimates for finite complex matrices.
-/

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace RMTFoundations.Resolvent

variable {n : Type* /- [definition] -/ } [Fintype n /- [definition] -/ ] [DecidableEq n /- [definition] -/ ]

omit [Fintype n] in
/-- The two shifts differ by a scalar. -/
theorem shift_sub (H : Matrix n n ℂ /- [definition] -/ ) (z₁ z₂ : ℂ /- [definition] -/ ) :
    (H - z₂ • (1 : Matrix n n ℂ)) - (H - z₁ • (1 : Matrix n n ℂ))
      = (z₁ - z₂) • (1 : Matrix n n ℂ) := by
  rw [sub_sub_sub_cancel_left, ← sub_smul]

/-- **The first resolvent identity**, for any two invertible shifts. -/
theorem resolvent_identity (H : Matrix n n ℂ /- [definition] -/ ) (z₁ z₂ : ℂ /- [definition] -/ )
    (h₁ : IsUnit (H - z₁ • (1 : Matrix n n ℂ)).det /- [standing] -/ )
    (h₂ : IsUnit (H - z₂ • (1 : Matrix n n ℂ)).det /- [standing] -/ ) :
    (H - z₁ • (1 : Matrix n n ℂ))⁻¹ - (H - z₂ • (1 : Matrix n n ℂ))⁻¹
      = (z₁ - z₂) • ((H - z₁ • (1 : Matrix n n ℂ))⁻¹ * (H - z₂ • (1 : Matrix n n ℂ))⁻¹) := by
  set A := H - z₁ • (1 : Matrix n n ℂ) with hA
  set B := H - z₂ • (1 : Matrix n n ℂ) with hB
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A h₁
  have hBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B h₂
  have e1 : A⁻¹ * (B - A) = A⁻¹ * B - 1 := by
    rw [Matrix.mul_sub, hAinv]
  have hkey : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    rw [e1, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hBinv, Matrix.mul_one]
  rw [← hkey, shift_sub H z₁ z₂, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- The norm form the interpolation argument uses: the resolvent difference is
controlled by the gap times the two resolvent norms. -/
theorem resolvent_diff_norm_le (H : Matrix n n ℂ /- [definition] -/ ) (z₁ z₂ : ℂ /- [definition] -/ )
    (h₁ : IsUnit (H - z₁ • (1 : Matrix n n ℂ)).det /- [standing] -/ )
    (h₂ : IsUnit (H - z₂ • (1 : Matrix n n ℂ)).det /- [standing] -/ ) :
    ‖(H - z₁ • (1 : Matrix n n ℂ))⁻¹ - (H - z₂ • (1 : Matrix n n ℂ))⁻¹‖
      ≤ ‖z₁ - z₂‖ * (‖(H - z₁ • (1 : Matrix n n ℂ))⁻¹‖
        * ‖(H - z₂ • (1 : Matrix n n ℂ))⁻¹‖) := by
  rw [resolvent_identity H z₁ z₂ h₁ h₂, norm_smul]
  exact mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)

/-- At equal arguments the identity is vacuous, which pins the orientation of
the scalar factor. -/
theorem resolvent_identity_self (H : Matrix n n ℂ /- [definition] -/ ) (z : ℂ /- [definition] -/ )
    (_h : IsUnit (H - z • (1 : Matrix n n ℂ)).det /- [standing] -/ ) :
    (H - z • (1 : Matrix n n ℂ))⁻¹ - (H - z • (1 : Matrix n n ℂ))⁻¹ = 0 := by
  simp

/-- The resolvents at two invertible shifts commute, a consequence of the
identity being symmetric under swapping the two arguments. -/
theorem resolvent_comm (H : Matrix n n ℂ /- [definition] -/ ) (z₁ z₂ : ℂ /- [definition] -/ )
    (h₁ : IsUnit (H - z₁ • (1 : Matrix n n ℂ)).det /- [standing] -/ )
    (h₂ : IsUnit (H - z₂ • (1 : Matrix n n ℂ)).det /- [standing] -/ ) :
    (H - z₁ • (1 : Matrix n n ℂ))⁻¹ * (H - z₂ • (1 : Matrix n n ℂ))⁻¹
      = (H - z₂ • (1 : Matrix n n ℂ))⁻¹ * (H - z₁ • (1 : Matrix n n ℂ))⁻¹ := by
  have h12 := resolvent_identity H z₁ z₂ h₁ h₂
  have h21 := resolvent_identity H z₂ z₁ h₂ h₁
  have hsum : (z₁ - z₂) • ((H - z₁ • (1 : Matrix n n ℂ))⁻¹ * (H - z₂ • (1 : Matrix n n ℂ))⁻¹)
      = -((z₂ - z₁) • ((H - z₂ • (1 : Matrix n n ℂ))⁻¹ * (H - z₁ • (1 : Matrix n n ℂ))⁻¹)) := by
    rw [← h12, ← h21]
    abel
  rcases eq_or_ne z₁ z₂ with rfl | hne
  · rfl
  · have hz : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
    rw [show z₂ - z₁ = -(z₁ - z₂) by ring, neg_smul, neg_neg] at hsum
    exact smul_right_injective _ hz hsum

end RMTFoundations.Resolvent

#print axioms RMTFoundations.Resolvent.shift_sub
#print axioms RMTFoundations.Resolvent.resolvent_identity
#print axioms RMTFoundations.Resolvent.resolvent_diff_norm_le
#print axioms RMTFoundations.Resolvent.resolvent_identity_self
#print axioms RMTFoundations.Resolvent.resolvent_comm
