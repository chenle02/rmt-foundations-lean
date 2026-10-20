import Mathlib

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.WeightedVolterraFoundation
open MeasureTheory Set Filter

/-- Weighted supremum on the evaluation domain; boundedness is explicit. -/
noncomputable def weightedSize {α : Type* /- [definition] -/}
    (S : Set α /- [definition] -/)
    (w u : α → ℝ /- [definition] -/) : ℝ :=
  sSup ((fun x => |u x| / w x) '' S)

/-- A genuine integral kernel estimate from an integrable majorant. -/
theorem kernel_norm_bound {α : Type* /- [definition] -/} [MeasurableSpace α /- [definition] -/]
    (μ : Measure α /- [definition] -/)
    (S : Set α /- [definition] -/)
    (w k u : α → ℝ /- [definition] -/)
    (K : α → α → ℝ /- [definition] -/)
    (M : ℝ /- [definition] -/)
    (hM : 0 ≤ M /- [standing] -/)
    (hsupport : ∀ᵐ t ∂μ, t ∈ S /- [standing] -/)
    (hk : Integrable k μ /- [standing] -/)
    (hw : ∀ t ∈ S, 0 < w t /- [standing] -/)
    (hkn : ∀ t ∈ S, 0 ≤ k t /- [standing] -/)
    (hK : ∀ x ∈ S, ∀ t ∈ S, |K x t| * w t ≤ k t * w x /- [standing] -/)
    (hu : ∀ t ∈ S, |u t| ≤ M * w t /- [standing] -/)
    (x : α /- [definition] -/)
    (hx : x ∈ S /- [standing] -/) :
    |∫ t, K x t * u t ∂μ| ≤ (∫ t, k t ∂μ) * M * w x := by
  have hb : ∀ᵐ t ∂μ, ‖K x t * u t‖ ≤ k t * (M * w x) := by
    filter_upwards [hsupport] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |K x t| * |u t| ≤ |K x t| * (M * w t) :=
        mul_le_mul_of_nonneg_left (hu t ht) (abs_nonneg _)
      _ = M * (|K x t| * w t) := by ring
      _ ≤ M * (k t * w x) := mul_le_mul_of_nonneg_left (hK x hx t ht) hM
      _ = k t * (M * w x) := by ring
  have H := norm_integral_le_of_norm_le (hk.mul_const (M * w x)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at H
  simpa only [mul_assoc] using H

/-- A bounded weighted Volterra solution has an explicit relative error.
The smallness budget is the actual integral of the kernel majorant. -/
theorem solution_bounds {α : Type* /- [definition] -/} [MeasurableSpace α /- [definition] -/]
    (μ : Measure α /- [definition] -/)
    (S : Set α /- [definition] -/)
    (w k a u : α → ℝ /- [definition] -/)
    (K : α → α → ℝ /- [definition] -/)
    (hS : S.Nonempty /- [standing] -/)
    (hsupport : ∀ᵐ t ∂μ, t ∈ S /- [standing] -/)
    (hk : Integrable k μ /- [standing] -/)
    (hw : ∀ t ∈ S, 0 < w t /- [standing] -/)
    (hkn : ∀ t ∈ S, 0 ≤ k t /- [standing] -/)
    (hK : ∀ x ∈ S, ∀ t ∈ S, |K x t| * w t ≤ k t * w x /- [standing] -/)
    (ha : ∀ x ∈ S, |a x| ≤ w x /- [standing] -/)
    (hbdd : BddAbove ((fun x => |u x| / w x) '' S) /- [standing] -/)
    (hsol : ∀ x ∈ S, u x = a x + ∫ t, K x t * u t ∂μ /- [standing] -/)
    (hsmall : (∫ t, k t ∂μ) < 1 /- [standing] -/) :
    weightedSize S w u ≤ 1 / (1 - ∫ t, k t ∂μ) ∧
    ∀ x ∈ S, |u x - a x| ≤
      ((∫ t, k t ∂μ) / (1 - ∫ t, k t ∂μ)) * w x := by
  let budget : ℝ := ∫ t, k t ∂μ
  let M : ℝ := weightedSize S w u
  have hbudget : 0 ≤ budget := integral_nonneg_of_ae (hsupport.mono fun t ht => hkn t ht)
  have hden : 0 < 1 - budget := sub_pos.mpr hsmall
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hS
    exact (div_nonneg (abs_nonneg _) (hw x hx).le).trans
      (le_csSup hbdd (mem_image_of_mem _ hx))
  have hu : ∀ t ∈ S, |u t| ≤ M * w t := by
    intro t ht
    exact (div_le_iff₀ (hw t ht)).mp (le_csSup hbdd (mem_image_of_mem _ ht))
  have hbound : M ≤ 1 + budget * M := by
    apply csSup_le (hS.image _)
    rintro z ⟨x, hx, rfl⟩
    apply (div_le_iff₀ (hw x hx)).mpr
    calc
      |u x| = |a x + ∫ t, K x t * u t ∂μ| := congrArg abs (hsol x hx)
      _ ≤ |a x| + |∫ t, K x t * u t ∂μ| := abs_add_le _ _
      _ ≤ w x + budget * M * w x := add_le_add (ha x hx)
        (kernel_norm_bound μ S w k u K M hM hsupport hk hw hkn hK hu x hx)
      _ = (1 + budget * M) * w x := by ring
  have hsize : M ≤ 1 / (1 - budget) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨hsize, ?_⟩
  intro x hx
  have he : u x - a x = ∫ t, K x t * u t ∂μ := by linarith [hsol x hx]
  rw [he]
  calc
    |∫ t, K x t * u t ∂μ| ≤ budget * M * w x :=
      kernel_norm_bound μ S w k u K M hM hsupport hk hw hkn hK hu x hx
    _ ≤ budget * (1 / (1 - budget)) * w x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hbudget) (hw x hx).le
    _ = (budget / (1 - budget)) * w x := by ring

/-- Nonzero two-point kernel, positive weights and a strictly perturbed solution
jointly inhabit every binder of the integral and solution estimates. -/
theorem solution_all_binder_joint_probe :
    weightedSize (univ : Set (Fin 2)) (fun _ => 1) (fun _ => 4 / 3) ≤
      1 / (1 - (1 / 4 : ℝ)) ∧
    ∀ x : Fin 2, |(4 / 3 : ℝ) - 1| ≤ (1 / 4 : ℝ) / (1 - 1 / 4) := by
  have h := solution_bounds (Measure.count : Measure (Fin 2)) univ
    (fun _ => 1) (fun _ => 1 / 8) (fun _ => 1) (fun _ => 4 / 3)
    (fun _ _ => 1 / 8)
    (by exact ⟨0, mem_univ _⟩)
    (by simp) (by exact integrable_const _) (by intros; norm_num)
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    (by refine ⟨4 / 3, ?_⟩; rintro z ⟨x, hx, rfl⟩; norm_num)
    (by intros; simp [integral_fintype, Fin.sum_univ_two]; norm_num)
    (by simp [integral_fintype, Fin.sum_univ_two]; norm_num)
  norm_num [integral_fintype, Fin.sum_univ_two] at h ⊢
  exact h

end RMTFoundations.TracyWidom.WeightedVolterraFoundation

#print axioms RMTFoundations.TracyWidom.WeightedVolterraFoundation.weightedSize
#print axioms RMTFoundations.TracyWidom.WeightedVolterraFoundation.kernel_norm_bound
#print axioms RMTFoundations.TracyWidom.WeightedVolterraFoundation.solution_bounds
#print axioms RMTFoundations.TracyWidom.WeightedVolterraFoundation.solution_all_binder_joint_probe
