import Mathlib
import RMTFoundations.TracyWidom.WeightedVolterraUniqueness
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.WeightedVolterraNondegenerate
open MeasureTheory Set
open RMTFoundations.TracyWidom.WeightedVolterraUniqueness

/-- Distinct global functions solve the same genuine nonzero integral equation
on a two-point domain. Their equality on that domain is obtained by applying
uniqueness; equality of the global inputs is neither presumed nor true. -/
theorem distinct_inputs_all_binder_joint_probe :
    let μ : Measure (Fin 3) := Measure.dirac 0 + Measure.dirac 1
    let S : Set (Fin 3) := {0, 1}
    ∃ u v : Fin 3 → ℝ,
      u ≠ v ∧ S.Nonempty ∧ (∀ᵐ t ∂μ, t ∈ S) ∧
      Integrable (fun _ => (1 / 8 : ℝ)) μ ∧
      (∀ t ∈ S, 0 < (1 : ℝ)) ∧ (∀ t ∈ S, 0 ≤ (1 / 8 : ℝ)) ∧
      (∀ x ∈ S, ∀ t ∈ S, |(1 / 8 : ℝ)| * 1 ≤ (1 / 8) * 1) ∧
      BddAbove ((fun x => |u x - v x| / 1) '' S) ∧
      (∀ x ∈ S, Integrable (fun t => (1 / 8 : ℝ) * u t) μ) ∧
      (∀ x ∈ S, Integrable (fun t => (1 / 8 : ℝ) * v t) μ) ∧
      (∀ x ∈ S, u x = 1 + ∫ t, (1 / 8 : ℝ) * u t ∂μ) ∧
      (∀ x ∈ S, v x = 1 + ∫ t, (1 / 8 : ℝ) * v t ∂μ) ∧
      0 < (∫ t, (1 / 8 : ℝ) ∂μ) ∧ (∫ t, (1 / 8 : ℝ) ∂μ) < 1 ∧
      (∀ x ∈ S, u x = v x) := by
  dsimp only
  let μ : Measure (Fin 3) := Measure.dirac 0 + Measure.dirac 1
  let S : Set (Fin 3) := {0, 1}
  let u : Fin 3 → ℝ := fun _ => 4 / 3
  let v : Fin 3 → ℝ := fun x => if x = 2 then 7 else 1 + (1 / 8) * (8 / 3)
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hadd (f : Fin 3 → ℝ) : (∫ t, f t ∂μ) = f 0 + f 1 := by
    dsimp only [μ]
    rw [integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
      integral_dirac, integral_dirac]
  have hneq : u ≠ v := by
    intro h
    have H := congrFun h (2 : Fin 3)
    norm_num [u, v, h02, h12] at H
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  have hs : ∀ᵐ t ∂μ, t ∈ S := by simp [μ, S]
  have hk : Integrable (fun _ => (1 / 8 : ℝ)) μ := integrable_const _
  have hw : ∀ t ∈ S, 0 < (1 : ℝ) := by intros; norm_num
  have hn : ∀ t ∈ S, 0 ≤ (1 / 8 : ℝ) := by intros; norm_num
  have hK : ∀ x ∈ S, ∀ t ∈ S, |(1 / 8 : ℝ)| * 1 ≤ (1 / 8) * 1 := by intros; norm_num
  have hb : BddAbove ((fun x => |u x - v x| / 1) '' S) := by
    refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hx' : x = 0 ∨ x = 1 := by simpa [S] using hx
    rcases hx' with rfl | rfl <;> norm_num [u, v, h02, h12]
  have hiu : ∀ x ∈ S, Integrable (fun t => (1 / 8 : ℝ) * u t) μ := by
    intros
    change Integrable (fun _ : Fin 3 => (1 / 8 : ℝ) * (4 / 3)) μ
    exact integrable_const _
  have hiv : ∀ x ∈ S, Integrable (fun t => (1 / 8 : ℝ) * v t) μ := by
    intros
    exact integrable_add_measure.mpr
      ⟨integrable_dirac enorm_lt_top, integrable_dirac enorm_lt_top⟩
  have hu : ∀ x ∈ S, u x = 1 + ∫ t, (1 / 8 : ℝ) * u t ∂μ := by
    intros; rw [hadd]; norm_num [u]
  have hv : ∀ x ∈ S, v x = 1 + ∫ t, (1 / 8 : ℝ) * v t ∂μ := by
    intro x hx
    have hx' : x = 0 ∨ x = 1 := by simpa [S] using hx
    rcases hx' with rfl | rfl <;> rw [hadd] <;> norm_num [v, h02, h12]
  have hp : 0 < (∫ t, (1 / 8 : ℝ) ∂μ) := by
    rw [hadd]; norm_num
  have hsmall : (∫ t, (1 / 8 : ℝ) ∂μ) < 1 := by
    rw [hadd]; norm_num
  have H := solution_unique μ S (fun _ => 1) (fun _ => 1 / 8) (fun _ => 1)
    u v (fun _ _ => 1 / 8) hS hs hk hw hn hK hb hiu hiv hu hv hsmall
  exact ⟨u, v, hneq, hS, hs, hk, hw, hn, hK, hb, hiu, hiv, hu, hv, hp, hsmall, H⟩

end RMTFoundations.TracyWidom.WeightedVolterraNondegenerate

#print axioms RMTFoundations.TracyWidom.WeightedVolterraNondegenerate.distinct_inputs_all_binder_joint_probe
