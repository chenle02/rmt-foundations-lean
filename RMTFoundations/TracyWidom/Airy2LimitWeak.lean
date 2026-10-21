import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitWeak
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability

theorem lowerBox_isClosed (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) : IsClosed (lowerBox m s) := by
  have he : lowerBox m s = ⋂ i, (fun x : Fin m → ℝ => x i) ⁻¹' Iic (s i) := by
    ext x; simp [lowerBox]
  rw [he]
  exact isClosed_iInter fun i => isClosed_Iic.preimage (continuous_apply i)

def strictLowerBox (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) : Set (Fin m → ℝ) := {x | ∀ i, x i < s i}

theorem strictLowerBox_isOpen (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) : IsOpen (strictLowerBox m s) := by
  have he : strictLowerBox m s = ⋂ i, (fun x : Fin m → ℝ => x i) ⁻¹' Iio (s i) := by
    ext x; simp [strictLowerBox]
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_Iio.preimage (continuous_apply i)

/-- A continuous pointwise joint-CDF limit identifies every weak limit law.
These are generic, explicit hypotheses, not a physical Airy2 producer. -/
theorem jointCDF_eq_of_weak_pointwise_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hweak : Tendsto μ atTop (𝓝 ν) /- [standing] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (hc : Continuous F /- [standing] -/) :
    ∀ s, jointCDF m ν s = F s := by
  intro s
  have hnon (t : Fin m → ℝ) : 0 ≤ F t :=
    ge_of_tendsto (hlim t) (Eventually.of_forall fun n => measureReal_nonneg)
  have hE (t : Fin m → ℝ) :
      Tendsto (fun n => (μ n : Measure (Fin m → ℝ)) (lowerBox m t))
        atTop (𝓝 (ENNReal.ofReal (F t))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim t)
    simpa [Function.comp_def,jointCDF, Measure.real, ENNReal.ofReal_toReal, measure_ne_top] using h
  have hclosed : ENNReal.ofReal (F s) ≤ (ν : Measure (Fin m → ℝ)) (lowerBox m s) := by
    have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak
      (lowerBox_isClosed m s)
    rwa [(hE s).limsup_eq] at h
  have hlower : F s ≤ jointCDF m ν s := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hclosed
    simpa [jointCDF, Measure.real, ENNReal.toReal_ofReal (hnon s)] using h
  have hshift (a : ℝ) (ha : 0 < a) : jointCDF m ν s ≤ F (fun i => s i + a) := by
    let t : Fin m → ℝ := fun i => s i+a
    have hinc : lowerBox m s ⊆ strictLowerBox m t := by
      intro x hx i
      exact (hx i).trans_lt (lt_add_of_pos_right _ ha)
    have hinc' : strictLowerBox m t ⊆ lowerBox m t := fun x hx i => (hx i).le
    have ho := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
      (strictLowerBox_isOpen m t)
    have hb : (ν : Measure (Fin m → ℝ)) (lowerBox m s) ≤ ENNReal.ofReal (F t) := by
      calc
        _ ≤ (ν : Measure (Fin m → ℝ)) (strictLowerBox m t) := measure_mono hinc
        _ ≤ atTop.liminf (fun n => (μ n : Measure (Fin m → ℝ)) (strictLowerBox m t)) := ho
        _ ≤ atTop.liminf (fun n => (μ n : Measure (Fin m → ℝ)) (lowerBox m t)) :=
          liminf_le_liminf (Eventually.of_forall fun n => measure_mono hinc')
        _ = ENNReal.ofReal (F t) := (hE t).liminf_eq
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa [jointCDF, Measure.real, ENNReal.toReal_ofReal (hnon t)] using h
  have ht : Tendsto (fun a : ℝ => F (fun i => s i+a)) (𝓝[>] 0) (𝓝 (F s)) := by
    have hp : Tendsto (fun a : ℝ => (fun i : Fin m => s i+a)) (𝓝[>] 0) (𝓝 s) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simpa using (tendsto_const_nhds.add ((tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds))
    exact hc.continuousAt.tendsto.comp hp
  exact le_antisymm (ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hshift a ha)) hlower

/-- Tightness constructs the probability measure; no target-law existence premise. -/
theorem exists_law_of_tight_continuous_pointwise_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (htight : IsTightMeasureSet (range (fun n => (μ n : Measure (Fin m → ℝ))))
      /- [standing] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (hc : Continuous F /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ), ∀ s, jointCDF m ν s = F s := by
  have he : {((ν : ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)) |
      ν ∈ range μ} = range (fun n => (μ n : Measure (Fin m → ℝ))) := by
    ext ν
    simp only [mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨ν', ⟨n,rfl⟩,rfl⟩; exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩; exact ⟨μ n,⟨n,rfl⟩,rfl⟩
  have hcompact : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (he.symm ▸ htight)
  obtain ⟨ν, _, u, hu, hν⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨ν, jointCDF_eq_of_weak_pointwise_limit m (fun n => μ (u n)) ν F hν ?_ hc⟩
  intro s
  exact (hlim s).comp hu.tendsto_atTop



theorem weak_converges_of_tight_pointwise_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (htight : IsTightMeasureSet (range (fun n => (μ n : Measure (Fin m → ℝ))))
      /- [standing] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (hc : Continuous F /- [standing] -/)
    (hν : ∀ s, jointCDF m ν s = F s /- [standing] -/) :
    Tendsto μ atTop (𝓝 ν) := by
  have he : {((ρ : ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)) |
      ρ ∈ range μ} = range (fun n => (μ n : Measure (Fin m → ℝ))) := by
    ext ρ
    simp only [mem_setOf_eq,mem_range]
    constructor
    · rintro ⟨ρ',⟨n,rfl⟩,rfl⟩; exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩; exact ⟨μ n,⟨n,rfl⟩,rfl⟩
  have hcompact : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (he.symm ▸ htight)
  apply tendsto_def.mpr
  intro V hV
  obtain ⟨U,hUV,hU,hνU⟩ := mem_nhds_iff.mp hV
  suffices ∀ᶠ n in atTop, μ n ∈ U from this.mono (fun _ h => hUV h)
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, μ n ∈ closure (range μ) ∩ Uᶜ :=
    (not_eventually.mp hnot).mono (fun n hn => ⟨subset_closure (mem_range_self n),hn⟩)
  obtain ⟨ρ,hρ,u,hu,hw⟩ :=
    (hcompact.inter_right hU.isClosed_compl).isSeqCompact.subseq_of_frequently_in hfreq
  have hl : ∀ s, Tendsto (fun n => jointCDF m (μ (u n)) s) atTop (𝓝 (F s)) :=
    fun s => (hlim s).comp hu.tendsto_atTop
  have hρF := jointCDF_eq_of_weak_pointwise_limit m (fun n => μ (u n)) ρ F hw hl hc
  have heq : ρ=ν := Subtype.ext (measure_eq_of_jointCDF m ρ ν ρ.prop ν.prop
    (fun s => (hρF s).trans (hν s).symm))
  exact hρ.2 (heq.symm ▸ hνU)

/-- The nondegenerate example target is jointly continuous at all cuts. -/
theorem TW2ProductLaw_jointCDF_continuous (m : ℕ /- [definition] -/) :
    Continuous (jointCDF m (TW2ProductLaw m)) := by
  have he : jointCDF m (TW2ProductLaw m) =
      (fun s => ∏ i, RMTFoundations.TracyWidom.TW2R (s i)) := by
    funext s
    exact TW2ProductLaw_jointCDF m s
  rw [he]
  exact continuous_finsetProd _ fun i _ =>
    RMTFoundations.TracyWidom.continuous_TW2R.comp (continuous_apply i)

/-- Every weak/tight/pointwise/continuity binder is supplied by terms on the
actual full-dimensional TW2 product, with both asymptotic limits. -/
theorem weak_limit_all_binder_joint_probe :
    let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
      ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ => ν
    let F := jointCDF 2 (TW2ProductLaw 2)
    Tendsto μ atTop (𝓝 ν) ∧
    IsTightMeasureSet (range (fun n => (μ n : Measure (Fin 2 → ℝ)))) ∧
    (∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s))) ∧
    Continuous F ∧ (∀ s, jointCDF 2 ν s = F s) ∧
    (∃ ρ : ProbabilityMeasure (Fin 2 → ℝ), ∀ s, jointCDF 2 ρ s = F s) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atBot (𝓝 0) ∧
    0 < F (fun _ => 0) ∧ F (fun _ => 0) < 1 := by
  dsimp only
  letI := TW2ProductLaw_probability 2
  let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ => ν
  let F := jointCDF 2 (TW2ProductLaw 2)
  have hw : Tendsto μ atTop (𝓝 ν) := tendsto_const_nhds
  have ht : IsTightMeasureSet (range (fun n => (μ n : Measure (Fin 2 → ℝ)))) := by
    simpa only [μ,ν,ProbabilityMeasure.coe_mk,range_const] using
      (isTightMeasureSet_singleton : IsTightMeasureSet {TW2ProductLaw 2})
  have hl : ∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s)) :=
    fun _ => tendsto_const_nhds
  have hc : Continuous F := TW2ProductLaw_jointCDF_continuous 2
  have hp := probability_core_all_binder_joint_probe
  have hwproved := weak_converges_of_tight_pointwise_limit 2 μ ν F ht hl hc (fun _ => rfl)
  exact ⟨hwproved,ht,hl,hc,jointCDF_eq_of_weak_pointwise_limit 2 μ ν F hw hl hc,
    exists_law_of_tight_continuous_pointwise_limit 2 μ F ht hl hc,
    hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hp.2.1,hp.2.2.1⟩

end RMTFoundations.TracyWidom.Airy2LimitWeak

#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.lowerBox_isClosed
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.strictLowerBox
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.strictLowerBox_isOpen
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.jointCDF_eq_of_weak_pointwise_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.exists_law_of_tight_continuous_pointwise_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.TW2ProductLaw_jointCDF_continuous
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.weak_limit_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitWeak.weak_converges_of_tight_pointwise_limit
