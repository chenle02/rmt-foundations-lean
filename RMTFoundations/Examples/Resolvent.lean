import RMTFoundations.Matrix.Resolvent
namespace RMTFoundations.ResolventProbe
open Matrix
open scoped Matrix Matrix.Norms.L2Operator
/-- All resolvent binders hold simultaneously for a nonzero matrix and two distinct shifts. -/
theorem joint :
    ∃ (H : Matrix (Fin 1) (Fin 1) ℂ) (z₁ z₂ : ℂ),
      H ≠ 0 ∧ z₁ ≠ z₂ ∧ IsUnit (H-z₁ • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det ∧
      IsUnit (H-z₂ • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det ∧
      (H-z₁ • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹-
      (H-z₂ • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹ =
      (z₁-z₂) • ((H-z₁ • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹ *
      (H-z₂ • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹) := by
  let H : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 2
  have hH : H ≠ 0 := by
    intro h
    have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    norm_num [H] at he
  have h₁ : IsUnit (H-(0:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_one]
    rw [Matrix.sub_apply, Matrix.smul_apply]
    norm_num [H, Matrix.one_apply]
  have h₂ : IsUnit (H-(1:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_one]
    rw [Matrix.sub_apply, Matrix.smul_apply]
    norm_num [H, Matrix.one_apply]
  exact ⟨H,0,1,hH,by norm_num,h₁,h₂,RMTFoundations.Resolvent.resolvent_identity H 0 1 h₁ h₂⟩
end RMTFoundations.ResolventProbe

#print axioms RMTFoundations.ResolventProbe.joint
