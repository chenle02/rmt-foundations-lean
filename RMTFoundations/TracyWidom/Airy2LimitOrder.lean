import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitOrder
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.Airy2Probability

theorem pointwise_limit_bounds (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/) : ∀ s, 0 ≤ F s ∧ F s ≤ 1 := by
  intro s
  exact ⟨ge_of_tendsto (hlim s) (Eventually.of_forall fun n =>
    (jointCDF_bounds m _ (μ n).prop s).1),
    le_of_tendsto (hlim s) (Eventually.of_forall fun n =>
      (jointCDF_bounds m _ (μ n).prop s).2)⟩

theorem pointwise_limit_monotone (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/) : Monotone F := by
  intro s t hst
  exact le_of_tendsto_of_tendsto' (hlim s) (hlim t)
    fun n => jointCDF_monotone m _ (μ n).prop hst

/-- Rectangle positivity survives pointwise limits; all four corners are retained. -/
theorem pointwise_limit_rectangle_nonneg
    (μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) /- [definition] -/)
    (F : (Fin 2 → ℝ) → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (a b c d : ℝ /- [definition] -/)
    (hab : a ≤ b /- [standing] -/)
    (hcd : c ≤ d /- [standing] -/) :
    0 ≤ F ![b,d] - F ![a,d] - F ![b,c] + F ![a,c] := by
  apply ge_of_tendsto (((hlim ![b,d]).sub (hlim ![a,d])).sub
    (hlim ![b,c]) |>.add (hlim ![a,c]))
  exact Eventually.of_forall fun n => jointCDF_rectangle_nonneg _ (μ n).prop a b c d hab hcd

/-- Constant nondegenerate TW2 product laws test every pointwise premise at every cut. -/
theorem limit_order_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 2, TW2ProductLaw_probability 2⟩
    let F := jointCDF 2 (TW2ProductLaw 2)
    (∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s))) ∧
    Monotone F ∧ (∀ s, 0 ≤ F s ∧ F s ≤ 1) ∧
    0 ≤ F ![0,0] - F ![-1,0] - F ![0,-1] + F ![-1,-1] ∧
    0 < F (fun _ => 0) ∧ F (fun _ => 0) < 1 := by
  dsimp only
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 2, TW2ProductLaw_probability 2⟩
  have hl : ∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop
      (𝓝 (jointCDF 2 (TW2ProductLaw 2) s)) := fun _ => tendsto_const_nhds
  have hp := probability_core_all_binder_joint_probe
  exact ⟨hl, pointwise_limit_monotone 2 μ _ hl,
    pointwise_limit_bounds 2 μ _ hl, pointwise_limit_rectangle_nonneg μ _ hl
      (-1) 0 (-1) 0 (by norm_num) (by norm_num), hp.2.1, hp.2.2.1⟩
end RMTFoundations.TracyWidom.Airy2LimitOrder

#print axioms RMTFoundations.TracyWidom.Airy2LimitOrder.pointwise_limit_bounds
#print axioms RMTFoundations.TracyWidom.Airy2LimitOrder.pointwise_limit_monotone
#print axioms RMTFoundations.TracyWidom.Airy2LimitOrder.pointwise_limit_rectangle_nonneg
#print axioms RMTFoundations.TracyWidom.Airy2LimitOrder.limit_order_all_binder_joint_probe
