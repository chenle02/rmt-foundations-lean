import RMTFoundations.TracyWidom.GUEProjectionLaw
import RMTFoundations.TracyWidom.GUETruncatedGram

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjectionDeterminant
open MeasureTheory Matrix
open RMTFoundations.TracyWidom.GUEProjection RMTFoundations.TracyWidom.GUEProjectionLaw
open RMTFoundations.TracyWidom.GUETruncatedGram

/-- The actual finite projection law's one-time gap has its compressed Gram
matrix determinant. This proves a static probability identity; the matrix
OU multi-time Fredholm identity remains a separate obligation. -/
theorem projectionGap_eq_gram_det (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    projectionGap N s = Matrix.det (fun i j : Fin N =>
      ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x) := by
  rw [projectionGap_density_integral, gue_static_gap_integral]

/-- Positivity and normalization bound for the actual compressed determinant,
obtained from its proved probability representation rather than an assumption. -/
theorem gram_gap_det_bounds (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    0 ≤ Matrix.det (fun i j : Fin N =>
      ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x) ∧
    Matrix.det (fun i j : Fin N =>
      ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x) ≤ 1 := by
  rw [← projectionGap_eq_gram_det]
  exact ⟨projectionGap_nonneg N s, projectionGap_le_one N s⟩

theorem gram_gap_det_monotone (N : ℕ /- [definition] -/) :
    Monotone (fun s : ℝ => Matrix.det (fun i j : Fin N =>
      ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x)) := by
  simpa only [← projectionGap_eq_gram_det] using projectionGap_monotone N

/-- Same nondegenerate Hermite ensemble for every static determinant conclusion. -/
theorem projection_determinant_all_binder_joint_probe :
    ∃ x : Fin 3 → ℝ, Function.Injective x ∧ 0 < gueDensity 3 x ∧
      IsProbabilityMeasure (projectionLaw 3) ∧
      (∀ s, projectionGap 3 s = Matrix.det (fun i j : Fin 3 =>
        ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x)) ∧
      (∀ s, 0 ≤ Matrix.det (fun i j : Fin 3 =>
        ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x) ∧
        Matrix.det (fun i j : Fin 3 =>
          ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x) ≤ 1) ∧
      Monotone (fun s : ℝ => Matrix.det (fun i j : Fin 3 =>
        ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x * hermiteFunction j.val x)) := by
  obtain ⟨x,hx,hpos,hprob,hmono,hbounds,hint⟩ := projectionLaw_all_binder_joint_probe
  exact ⟨x,hx,hpos,hprob,projectionGap_eq_gram_det 3,gram_gap_det_bounds 3,
    gram_gap_det_monotone 3⟩

end RMTFoundations.TracyWidom.GUEProjectionDeterminant

#print axioms RMTFoundations.TracyWidom.GUEProjectionDeterminant.projectionGap_eq_gram_det
#print axioms RMTFoundations.TracyWidom.GUEProjectionDeterminant.gram_gap_det_bounds
#print axioms RMTFoundations.TracyWidom.GUEProjectionDeterminant.gram_gap_det_monotone
#print axioms RMTFoundations.TracyWidom.GUEProjectionDeterminant.projection_determinant_all_binder_joint_probe
