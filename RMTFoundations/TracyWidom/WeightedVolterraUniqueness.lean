import Mathlib
import RMTFoundations.TracyWidom.WeightedVolterraFoundation
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.WeightedVolterraUniqueness
open MeasureTheory Set Filter
open RMTFoundations.TracyWidom.WeightedVolterraFoundation

/-- The genuine small kernel budget gives uniqueness in the bounded weighted
class; integrability needed for subtracting the two equations is explicit. -/
theorem solution_unique {α : Type* /- [definition] -/} [MeasurableSpace α /- [definition] -/]
    (μ : Measure α /- [definition] -/)
    (S : Set α /- [definition] -/)
    (w k a u v : α → ℝ /- [definition] -/)
    (K : α → α → ℝ /- [definition] -/)
    (hS : S.Nonempty /- [standing] -/)
    (hsupport : ∀ᵐ t ∂μ, t ∈ S /- [standing] -/)
    (hk : Integrable k μ /- [standing] -/)
    (hw : ∀ t ∈ S, 0 < w t /- [standing] -/)
    (hkn : ∀ t ∈ S, 0 ≤ k t /- [standing] -/)
    (hK : ∀ x ∈ S, ∀ t ∈ S, |K x t| * w t ≤ k t * w x /- [standing] -/)
    (hbdd : BddAbove ((fun x => |u x-v x| / w x) '' S) /- [standing] -/)
    (hiu : ∀ x ∈ S, Integrable (fun t => K x t*u t) μ /- [standing] -/)
    (hiv : ∀ x ∈ S, Integrable (fun t => K x t*v t) μ /- [standing] -/)
    (hu : ∀ x ∈ S, u x = a x + ∫ t, K x t*u t ∂μ /- [standing] -/)
    (hv : ∀ x ∈ S, v x = a x + ∫ t, K x t*v t ∂μ /- [standing] -/)
    (hsmall : (∫ t, k t ∂μ) < 1 /- [standing] -/) :
    ∀ x ∈ S, u x = v x := by
  let d : α → ℝ := fun t => u t-v t
  let M : ℝ := weightedSize S w d
  let budget : ℝ := ∫ t, k t ∂μ
  have hM : 0 ≤ M := by
    obtain ⟨x,hx⟩ := hS
    exact (div_nonneg (abs_nonneg _) (hw x hx).le).trans
      (le_csSup hbdd (mem_image_of_mem _ hx))
  have hd : ∀ t ∈ S, |d t| ≤ M*w t := by
    intro t ht; exact (div_le_iff₀ (hw t ht)).mp (le_csSup hbdd (mem_image_of_mem _ ht))
  have heq (x : α) (hx : x ∈ S) : d x = ∫ t, K x t*d t ∂μ := by
    have H : (∫ t, K x t*d t ∂μ) =
        (∫ t, K x t*u t ∂μ)-(∫ t, K x t*v t ∂μ) := by
      calc
        (∫ t, K x t*d t ∂μ) = ∫ t, K x t*u t-K x t*v t ∂μ := by
          congr 1; ext t; dsimp [d]; ring
        _ = _ := integral_sub (hiu x hx) (hiv x hx)
    dsimp [d]; linarith [hu x hx,hv x hx,H]
  have hm : M ≤ budget*M := by
    apply csSup_le (hS.image _)
    rintro z ⟨x,hx,rfl⟩
    apply (div_le_iff₀ (hw x hx)).mpr
    rw [heq x hx]
    exact kernel_norm_bound μ S w k d K M hM hsupport hk hw hkn hK hd x hx
  have hm0 : M = 0 := by
    have hh : budget < 1 := hsmall
    nlinarith
  intro x hx
  have H := hd x hx
  rw [hm0,zero_mul] at H
  exact sub_eq_zero.mp (abs_nonpos_iff.mp H)

/-- Positive two-point kernel and nontrivial common solution jointly realize
all uniqueness data, including the actual integrability premises. -/
theorem uniqueness_all_binder_joint_probe :
    ∀ x : Fin 2, (4 / 3 : ℝ) = 4 / 3 := by
  have H := solution_unique (Measure.count : Measure (Fin 2)) univ
    (fun _ => 1) (fun _ => 1 / 8) (fun _ => 1) (fun _ => 4 / 3)
    (fun _ => 4 / 3) (fun _ _ => 1 / 8)
    (by exact ⟨0,mem_univ _⟩) (by simp) (by exact integrable_const _)
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    (by refine ⟨0,?_⟩; rintro z ⟨x,hx,rfl⟩; norm_num)
    (by intros; exact integrable_const _) (by intros; exact integrable_const _)
    (by intros; simp [integral_fintype]; norm_num)
    (by intros; simp [integral_fintype]; norm_num)
    (by simp [integral_fintype]; norm_num)

  intro x; exact H x (mem_univ _)

end RMTFoundations.TracyWidom.WeightedVolterraUniqueness

#print axioms RMTFoundations.TracyWidom.WeightedVolterraUniqueness.solution_unique
#print axioms RMTFoundations.TracyWidom.WeightedVolterraUniqueness.uniqueness_all_binder_joint_probe
