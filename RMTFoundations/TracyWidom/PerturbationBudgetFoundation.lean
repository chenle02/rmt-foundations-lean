import Mathlib
import RMTFoundations.TracyWidom.WeightedVolterraFoundation
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.PerturbationBudgetFoundation
open MeasureTheory Set Filter
open RMTFoundations.TracyWidom.WeightedVolterraFoundation

/-- A sup-amplitude epsilon bound and an integrable tail envelope produce an
explicit normalized Volterra error. The budget is c*eta*integral(b), not a
placeholder dimension or an assumed comparison conclusion. -/
theorem amplitude_tail_bound {α : Type* /- [definition] -/} [MeasurableSpace α /- [definition] -/]
    (μ : Measure α /- [definition] -/)
    (S : Set α /- [definition] -/)
    (b ε u : α → ℝ /- [definition] -/)
    (G : α → α → ℝ /- [definition] -/)
    (c η : ℝ /- [definition] -/)
    (hS : S.Nonempty /- [standing] -/)
    (hsupport : ∀ᵐ t ∂μ, t ∈ S /- [standing] -/)
    (hc : 0 ≤ c /- [standing] -/)
    (hη : 0 ≤ η /- [standing] -/)
    (hb : Integrable b μ /- [standing] -/)
    (hbn : ∀ t ∈ S, 0 ≤ b t /- [standing] -/)
    (hε : ∀ t ∈ S, |ε t| ≤ η * b t /- [standing] -/)
    (hG : ∀ x ∈ S, ∀ t ∈ S, |G x t| ≤ c /- [standing] -/)
    (hbdd : BddAbove ((abs ∘ u) '' S) /- [standing] -/)
    (hsol : ∀ x ∈ S, u x = 1 + ∫ t, (G x t * ε t) * u t ∂μ /- [standing] -/)
    (hsmall : c * η * (∫ t, b t ∂μ) < 1 /- [standing] -/) :
    ∀ x ∈ S, |u x - 1| ≤
      (c * η * (∫ t, b t ∂μ)) / (1 - c * η * (∫ t, b t ∂μ)) := by
  let k : α → ℝ := fun t => (c*η)*b t
  let K : α → α → ℝ := fun x t => G x t*ε t
  have hk : Integrable k μ := hb.const_mul (c*η)
  have hkn : ∀ t ∈ S, 0 ≤ k t := by intro t ht; exact mul_nonneg (mul_nonneg hc hη) (hbn t ht)
  have hK : ∀ x ∈ S, ∀ t ∈ S, |K x t| * 1 ≤ k t*1 := by
    intro x hx t ht
    dsimp [K,k]
    simp only [mul_one,abs_mul]
    calc |G x t| * |ε t| ≤ c*(η*b t) :=
        mul_le_mul (hG x hx t ht) (hε t ht) (abs_nonneg _) hc
      _ = c*η*b t := by ring
  have H := solution_bounds μ S (fun _ => 1) k (fun _ => 1) u K
    hS hsupport hk (by intros; norm_num) hkn hK (by intros; norm_num)
    (by simpa [Function.comp_def] using hbdd) hsol
    (by simpa only [k,integral_const_mul] using hsmall)
  intro x hx
  simpa only [k,integral_const_mul,mul_one] using H.2 x hx

/-- All amplitude, tail, kernel and equation binders jointly hold with
strictly nonzero perturbation, positive budget, and a nontrivial fixed point. -/
theorem amplitude_all_binder_joint_probe :
    ∀ x : Fin 2, |(4 / 3 : ℝ) - 1| ≤ (1 / 4 : ℝ) / (1 - 1 / 4) := by
  have H := amplitude_tail_bound (Measure.count : Measure (Fin 2)) univ
    (fun _ => 1 / 2) (fun _ => 1 / 8) (fun _ => 4 / 3) (fun _ _ => 1) 1 (1 / 4)
    (by exact ⟨0,mem_univ _⟩) (by simp) (by norm_num) (by norm_num)
    (by exact integrable_const _) (by intros; norm_num) (by intros; norm_num)
    (by intros; norm_num)
    (by refine ⟨4 / 3,?_⟩; rintro z ⟨x,hx,rfl⟩; norm_num)
    (by intros; simp [integral_fintype]; norm_num)
    (by simp [integral_fintype]; norm_num)
  intro x
  convert! H x (mem_univ _) using 1 <;> norm_num [integral_fintype]

end RMTFoundations.TracyWidom.PerturbationBudgetFoundation

#print axioms RMTFoundations.TracyWidom.PerturbationBudgetFoundation.amplitude_tail_bound
#print axioms RMTFoundations.TracyWidom.PerturbationBudgetFoundation.amplitude_all_binder_joint_probe
