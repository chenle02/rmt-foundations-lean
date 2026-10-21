import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set

/-- Finite-grid sign transfer with explicit covering radius and variation budget.
Every numerical value is a premise to be certified by a caller; no certificate is invented. -/
theorem finite_grid_positive_of_margin
    (ι : Type*) -- [definition]
    [Fintype ι] -- [definition]
    (f : ℝ → ℝ) -- [definition]
    (grid : ι → ℝ) -- [definition]
    (a b radius L margin : ℝ) -- [definition]
    (hL : 0 ≤ L) -- [standing]
    (hcover : ∀ x ∈ Icc a b, ∃ i, |x-grid i| ≤ radius) -- [standing]
    (hvariation : ∀ x ∈ Icc a b, ∀ i, |f x-f (grid i)| ≤ L*|x-grid i|) -- [standing]
    (hgrid : ∀ i, margin ≤ f (grid i)) -- [standing]
    (hbudget : L*radius < margin) -- [standing]
    : ∀ x ∈ Icc a b, 0 < f x := by
  intro x hx
  obtain ⟨i,hi⟩ := hcover x hx
  have hv := abs_le.mp (hvariation x hx i)
  have hb := mul_le_mul_of_nonneg_left hi hL
  have hg := hgrid i
  linarith

/-- A nonconstant affine function on a genuine interval supplies all certificate inputs
jointly, on the same singleton grid and with a positive error budget. -/
theorem finite_grid_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (grid : Fin 1 → ℝ) (a b radius L margin : ℝ),
      a < b ∧ f a ≠ f b ∧ 0 < L ∧ 0 < radius ∧
      (∀ x ∈ Icc a b, ∃ i, |x-grid i| ≤ radius) ∧
      (∀ x ∈ Icc a b, ∀ i, |f x-f (grid i)| ≤ L*|x-grid i|) ∧
      (∀ i, margin ≤ f (grid i)) ∧ L*radius < margin ∧
      (∀ x ∈ Icc a b, 0 < f x) := by
  let f : ℝ → ℝ := fun x => 2+x/10
  let grid : Fin 1 → ℝ := fun _ => 0
  have hc : ∀ x ∈ Icc (-1:ℝ) 1, ∃ i : Fin 1, |x-grid i| ≤ 1 := by
    intro x hx
    exact ⟨0, by dsimp [grid]; rw [sub_zero,abs_le]; constructor <;> linarith [hx.1,hx.2]⟩
  have hv : ∀ x ∈ Icc (-1:ℝ) 1, ∀ i : Fin 1,
      |f x-f (grid i)| ≤ (1/10:ℝ)*|x-grid i| := by
    intro x hx i
    dsimp [f,grid]
    ring_nf
    rw [abs_mul]
    norm_num
  have hg : ∀ i : Fin 1, (1:ℝ) ≤ f (grid i) := by intro i; norm_num [f,grid]
  exact ⟨f,grid,-1,1,1,1/10,1,by norm_num,by norm_num [f],by norm_num,
    by norm_num,hc,hv,hg,by norm_num,
    finite_grid_positive_of_margin (Fin 1) f grid (-1) 1 1 (1/10) 1
      (by norm_num) hc hv hg (by norm_num)⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.finite_grid_positive_of_margin
#print axioms RMTFoundations.TracyWidom.finite_grid_all_binder_joint_probe
