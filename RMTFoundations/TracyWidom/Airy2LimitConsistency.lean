import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitConsistency
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.Airy2Probability

/-- Law-level coordinate consistency survives weak limits of genuine finite
laws. Every finite-N consistency equality is an explicit input. -/
theorem selector_consistency_of_weak_limits (m n : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (η : ℕ → ProbabilityMeasure (Fin n → ℝ) /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (ρ : ProbabilityMeasure (Fin n → ℝ) /- [definition] -/)
    (f : Fin n → Fin m /- [definition] -/)
    (hm : Tendsto μ atTop (𝓝 ν) /- [standing] -/)
    (hn : Tendsto η atTop (𝓝 ρ) /- [standing] -/)
    (hfinite : ∀ k, (μ k : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = η k
      /- [standing] -/) :
    (ν : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = ρ := by
  have hc : Continuous (fun x : Fin m → ℝ => fun i : Fin n => x (f i)) :=
    continuous_pi fun i => continuous_apply (f i)
  have he (k : ℕ) : (μ k).map (fun x i => x (f i)) = η k :=
    Subtype.ext (hfinite k)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hm hc
  have hηmap : Tendsto (fun k => (μ k).map (fun x i => x (f i))) atTop (𝓝 ρ) :=
    hn.congr' (Eventually.of_forall fun k => (he k).symm)
  have heq : ν.map (fun x i => x (f i)) = ρ := tendsto_nhds_unique hmap hηmap
  exact congrArg (fun q : ProbabilityMeasure (Fin n → ℝ) => q.toMeasure) heq

/-- Every finite-N and limiting consistency binder has a genuine joint witness;
the retained TW2 coordinate inherits both tail limits. -/
theorem consistency_all_binder_joint_probe :
    let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
      ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    let f : Fin 1 → Fin 2 := fun _ => 1
    ∃ ρ : ProbabilityMeasure (Fin 1 → ℝ),
      Tendsto (fun _ : ℕ => ν) atTop (𝓝 ν) ∧
      Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) ∧
      (∀ _k : ℕ, (ν : Measure (Fin 2 → ℝ)).map (fun x i => x (f i)) = ρ) ∧
      (ν : Measure (Fin 2 → ℝ)).map (fun x i => x (f i)) = ρ ∧
      Tendsto (fun a : ℝ => jointCDF 1 ρ (fun _ => a)) atTop (𝓝 1) ∧
      Tendsto (fun a : ℝ => jointCDF 1 ρ (fun _ => a)) atBot (𝓝 0) ∧
      0 < jointCDF 2 ν (fun _ => 0) ∧ jointCDF 2 ν (fun _ => 0) < 1 := by
  dsimp only
  let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let f : Fin 1 → Fin 2 := fun _ => 1
  have hc : Continuous (fun x : Fin 2 → ℝ => fun i : Fin 1 => x (f i)) :=
    continuous_pi fun i => continuous_apply (f i)
  let ρ := ν.map (fun x i => x (f i))
  have hm : Tendsto (fun _ : ℕ => ν) atTop (𝓝 ν) := tendsto_const_nhds
  have hn : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := tendsto_const_nhds
  have hfinite : ∀ _k : ℕ, (ν : Measure (Fin 2 → ℝ)).map (fun x i => x (f i)) = ρ :=
    fun _ => rfl
  have hp := probability_core_all_binder_joint_probe
  exact ⟨ρ,hm,hn,hfinite,selector_consistency_of_weak_limits 2 1 (fun _ => ν)
    (fun _ => ρ) ν ρ f hm hn hfinite,jointCDF_common_atTop 1 ρ ρ.prop,
    jointCDF_common_atBot 1 (by norm_num) ρ ρ.prop,hp.2.1,hp.2.2.1⟩
end RMTFoundations.TracyWidom.Airy2LimitConsistency

#print axioms RMTFoundations.TracyWidom.Airy2LimitConsistency.selector_consistency_of_weak_limits
#print axioms RMTFoundations.TracyWidom.Airy2LimitConsistency.consistency_all_binder_joint_probe
