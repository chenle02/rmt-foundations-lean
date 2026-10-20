import RMTFoundations.TracyWidom.Airy2LimitLaws
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitMarginals
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability
open RMTFoundations.TracyWidom.Airy2LimitWeak
open RMTFoundations.TracyWidom.Airy2LimitLaws

noncomputable def coordinateLaw (m : ℕ /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (i : Fin m /- [definition] -/) : ProbabilityMeasure (Fin 1 → ℝ) :=
  ν.map (fun x => fun _ : Fin 1 => x i)

theorem coordinateLaw_jointCDF (m : ℕ /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (i : Fin m /- [definition] -/) (s : Fin 1 → ℝ /- [definition] -/) :
    jointCDF 1 (coordinateLaw m ν i) s = (ν : Measure (Fin m → ℝ)).real {x | x i ≤ s 0} := by
  rw [show (coordinateLaw m ν i : Measure (Fin 1 → ℝ)) =
    (ν : Measure (Fin m → ℝ)).map (fun x => fun _ : Fin 1 => x i) by rfl,
    jointCDF_map_coordinates m 1 _ (fun _ => i)]
  congr 1
  ext x
  constructor
  · intro hx; exact hx 0
  · intro hx j; simpa [Subsingleton.elim j (0 : Fin 1)] using hx

/-- Continuous scalar CDF limits identify the actual coordinate laws of a weak
joint limit, without exchanging the N and cutoff limits. -/
theorem coordinate_cdf_of_weak_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (i : Fin m /- [definition] -/) (G : ℝ → ℝ /- [definition] -/)
    (hw : Tendsto μ atTop (𝓝 ν) /- [standing] -/)
    (hc : Continuous G /- [standing] -/)
    (hl : ∀ s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (G s)) /- [standing] -/) :
    ∀ s, (ν : Measure (Fin m → ℝ)).real {x | x i ≤ s} = G s := by
  have hcw : Tendsto (fun n => coordinateLaw m (μ n) i) atTop (𝓝 (coordinateLaw m ν i)) := by
    have hp : Continuous (fun x : Fin m → ℝ => fun _ : Fin 1 => x i) :=
      continuous_pi fun _ => continuous_apply i
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hw hp
  have hcl : ∀ s : Fin 1 → ℝ, Tendsto (fun n => jointCDF 1 (coordinateLaw m (μ n) i) s)
      atTop (𝓝 (G (s 0))) := by
    intro s
    simpa only [coordinateLaw_jointCDF] using hl (s 0)
  have he := jointCDF_eq_of_weak_pointwise_limit 1 (fun n => coordinateLaw m (μ n) i)
    (coordinateLaw m ν i) (fun s => G (s 0)) hcw hcl (hc.comp (continuous_apply 0))
  intro s
  simpa only [coordinateLaw_jointCDF] using he (fun _ => s)

/-- The physical one-time TW2 measure, not just its CDF values, is inherited by
every coordinate once the finite-ensemble marginal limits hold. -/
theorem TW2_marginal_of_weak_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (i : Fin m /- [definition] -/)
    (hw : Tendsto μ atTop (𝓝 ν) /- [standing] -/)
    (hl : ∀ s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s)) /- [standing] -/) :
    (ν : Measure (Fin m → ℝ)).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure := by
  letI : IsProbabilityMeasure ((ν : Measure (Fin m → ℝ)).map (fun x => x i)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply i).aemeasurable).2 ν.prop
  have he := coordinate_cdf_of_weak_limit m μ ν i RMTFoundations.TracyWidom.TW2R hw
    RMTFoundations.TracyWidom.continuous_TW2R hl
  apply Measure.ext_of_Iic _ _
  intro s
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic]
  change (ν : Measure (Fin m → ℝ)).real {x | x i ≤ s} = _
  rw [he s,Measure.real,RMTFoundations.TracyWidom.TW2Measure_Iic,ENNReal.toReal_ofReal]
  exact (RMTFoundations.TracyWidom.TW2R_bounds s).1

/-- Complete weak/scalar/continuity example on a genuine TW2 product and a proper
coordinate; both true tail limits and exact measure identification are retained. -/
theorem marginal_limits_all_binder_joint_probe :
    let ν : ProbabilityMeasure (Fin 2 → ℝ) := ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ => ν
    Tendsto μ atTop (𝓝 ν) ∧ Continuous RMTFoundations.TracyWidom.TW2R ∧
    (∀ s, Tendsto (fun n => (μ n : Measure (Fin 2 → ℝ)).real {x | x 1 ≤ s})
      atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s))) ∧
    (∀ s, (ν : Measure (Fin 2 → ℝ)).real {x | x 1 ≤ s} = RMTFoundations.TracyWidom.TW2R s) ∧
    (ν : Measure (Fin 2 → ℝ)).map (fun x => x 1) = RMTFoundations.TracyWidom.TW2Measure ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atTop (𝓝 1) ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atBot (𝓝 0) ∧
    0 < jointCDF 2 ν (fun _ => 0) ∧ jointCDF 2 ν (fun _ => 0) < 1 := by
  dsimp only
  let ν : ProbabilityMeasure (Fin 2 → ℝ) := ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ => ν
  have hw : Tendsto μ atTop (𝓝 ν) := tendsto_const_nhds
  have hl : ∀ s, Tendsto (fun n => (μ n : Measure (Fin 2 → ℝ)).real {x | x 1 ≤ s})
      atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s)) := by
    intro s
    simp only [μ,ν,ProbabilityMeasure.coe_mk,TW2ProductLaw_coordinate_cdf]
    exact tendsto_const_nhds
  have hc := RMTFoundations.TracyWidom.continuous_TW2R
  have hp := probability_core_all_binder_joint_probe
  exact ⟨hw,hc,hl,coordinate_cdf_of_weak_limit 2 μ ν 1 _ hw hc hl,
    TW2_marginal_of_weak_limit 2 μ ν 1 hw hl,RMTFoundations.TracyWidom.tendsto_TW2R_atTop,
    RMTFoundations.TracyWidom.tendsto_TW2R_atBot,hp.2.1,hp.2.2.1⟩
end RMTFoundations.TracyWidom.Airy2LimitMarginals

#print axioms RMTFoundations.TracyWidom.Airy2LimitMarginals.coordinateLaw
#print axioms RMTFoundations.TracyWidom.Airy2LimitMarginals.coordinateLaw_jointCDF
#print axioms RMTFoundations.TracyWidom.Airy2LimitMarginals.coordinate_cdf_of_weak_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitMarginals.TW2_marginal_of_weak_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitMarginals.marginal_limits_all_binder_joint_probe
