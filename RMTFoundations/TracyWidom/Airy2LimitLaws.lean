import RMTFoundations.TracyWidom.Airy2LimitWeak
import RMTFoundations.TracyWidom.Airy2ScalarTightness
import RMTFoundations.TracyWidom.Airy2CoordinateTightness
import RMTFoundations.TracyWidom.Airy2RectangleLimits
import RMTFoundations.TracyWidom.Airy2LimitConsistency
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitLaws
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability
open RMTFoundations.TracyWidom.Airy2LimitWeak
open RMTFoundations.TracyWidom.Airy2ScalarTightness
open RMTFoundations.TracyWidom.Airy2CoordinateTightness
open RMTFoundations.TracyWidom.Airy2RectangleLimits
open RMTFoundations.TracyWidom.Airy2LimitConsistency

/-- Coordinate CDF tail limits construct joint tightness without independence. -/
theorem coordinate_cdf_limits_tight (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (G : Fin m → ℝ → ℝ /- [definition] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (G i s)) /- [standing] -/)
    (hbot : ∀ i, Tendsto (G i) atBot (𝓝 0) /- [standing] -/)
    (htop : ∀ i, Tendsto (G i) atTop (𝓝 1) /- [standing] -/) :
    IsTightMeasureSet (range (fun n => (μ n : Measure (Fin m → ℝ)))) := by
  have hi : ∀ i, IsTightMeasureSet (range (fun n =>
      (μ n : Measure (Fin m → ℝ)).map (fun x => x i))) := by
    intro i
    let μi : ℕ → ProbabilityMeasure ℝ := fun n =>
      (μ n).map (fun x => x i)
    apply tight_of_cdf_limit μi (G i) ?_ (hbot i) (htop i)
    intro s
    have he (n : ℕ) : (μi n : Measure ℝ).real (Iic s) =
        (μ n : Measure (Fin m → ℝ)).real {x | x i ≤ s} := by
      exact map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic
    simpa only [he] using hcoord i s
  exact joint_tight_of_coordinate_tight m μ hi

/-- Construct the unique genuine joint law from finite probability laws and
pointwise joint/scalar CDF convergence. No tightness or target-law premise. -/
theorem finite_law_limit (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (G : Fin m → ℝ → ℝ /- [definition] -/)
    (hc : Continuous F /- [standing] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (G i s)) /- [standing] -/)
    (hbot : ∀ i, Tendsto (G i) atBot (𝓝 0) /- [standing] -/)
    (htop : ∀ i, Tendsto (G i) atTop (𝓝 1) /- [standing] -/) :
    ∃! ν : ProbabilityMeasure (Fin m → ℝ), ∀ s, jointCDF m ν s = F s := by
  have ht := coordinate_cdf_limits_tight m μ G hcoord hbot htop
  obtain ⟨ν,hν⟩ := exists_law_of_tight_continuous_pointwise_limit m μ F ht hlim hc
  refine ⟨ν,hν,?_⟩
  intro ρ hρ
  apply Subtype.ext
  exact measure_eq_of_jointCDF m ρ ν ρ.prop ν.prop (fun s => (hρ s).trans (hν s).symm)

/-- The full sequence converges weakly to the constructed law, with unique CDF. -/
theorem finite_law_limit_with_weak (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (G : Fin m → ℝ → ℝ /- [definition] -/)
    (hc : Continuous F /- [standing] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (F s))
      /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (G i s)) /- [standing] -/)
    (hbot : ∀ i, Tendsto (G i) atBot (𝓝 0) /- [standing] -/)
    (htop : ∀ i, Tendsto (G i) atTop (𝓝 1) /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ), (∀ s, jointCDF m ν s = F s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ ρ : ProbabilityMeasure (Fin m → ℝ), (∀ s, jointCDF m ρ s = F s) → ρ=ν) := by
  obtain ⟨ν,hν,huniq⟩ := finite_law_limit m μ F G hc hlim hcoord hbot htop
  exact ⟨ν,hν,weak_converges_of_tight_pointwise_limit m μ ν F
    (coordinate_cdf_limits_tight m μ G hcoord hbot htop) hlim hc hν,huniq⟩



theorem finite_law_limits_consistent (m n : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (η : ℕ → ProbabilityMeasure (Fin n → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (H : (Fin n → ℝ) → ℝ /- [definition] -/)
    (G : Fin m → ℝ → ℝ /- [definition] -/)
    (J : Fin n → ℝ → ℝ /- [definition] -/)
    (f : Fin n → Fin m /- [definition] -/)
    (hcF : Continuous F /- [standing] -/)
    (hcH : Continuous H /- [standing] -/)
    (hF : ∀ s, Tendsto (fun k => jointCDF m (μ k) s) atTop (𝓝 (F s)) /- [standing] -/)
    (hH : ∀ s, Tendsto (fun k => jointCDF n (η k) s) atTop (𝓝 (H s)) /- [standing] -/)
    (hG : ∀ i s, Tendsto (fun k => (μ k : Measure (Fin m → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (G i s)) /- [standing] -/)
    (hJ : ∀ i s, Tendsto (fun k => (η k : Measure (Fin n → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (J i s)) /- [standing] -/)
    (hGb : ∀ i, Tendsto (G i) atBot (𝓝 0) /- [standing] -/)
    (hGt : ∀ i, Tendsto (G i) atTop (𝓝 1) /- [standing] -/)
    (hJb : ∀ i, Tendsto (J i) atBot (𝓝 0) /- [standing] -/)
    (hJt : ∀ i, Tendsto (J i) atTop (𝓝 1) /- [standing] -/)
    (hfinite : ∀ k, (μ k : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = η k
      /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ), ∃ ρ : ProbabilityMeasure (Fin n → ℝ),
      (∀ s, jointCDF m ν s = F s) ∧ (∀ s, jointCDF n ρ s = H s) ∧
      (ν : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = ρ := by
  obtain ⟨ν,hν,hwν,_⟩ := finite_law_limit_with_weak m μ F G hcF hF hG hGb hGt
  obtain ⟨ρ,hρ,hwρ,_⟩ := finite_law_limit_with_weak n η H J hcH hH hJ hJb hJt
  exact ⟨ν,ρ,hν,hρ,selector_consistency_of_weak_limits m n μ η ν ρ f hwν hwρ hfinite⟩

/-- The genuine normalization and grounding limits of the constructed target
follow from its law; no N/cutoff limit interchange is used. -/
theorem limit_cdf_fields (m : ℕ /- [definition] -/)
    (hm : 0 < m /- [standing] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hF : ∀ s, jointCDF m ν s = F s /- [standing] -/) :
    Monotone F ∧ (∀ s, 0 ≤ F s ∧ F s ≤ 1) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atBot (𝓝 0) ∧
    (∀ l, l.Nodup → ∀ a b : Fin m → ℝ, (∀ i ∈ l, a i ≤ b i) →
      0 ≤ rectangleDifference m l F a b) := by
  have he : jointCDF m ν = F := funext hF
  rw [← he]
  exact ⟨jointCDF_monotone m ν ν.prop,jointCDF_bounds m ν ν.prop,
    jointCDF_common_atTop m ν ν.prop,jointCDF_common_atBot m hm ν ν.prop,
    fun l hl a b hab => rectangleDifference_jointCDF_nonneg m l hl ν a b hab⟩

/-- Genuine TW2 scalar marginals on the nondegenerate example law. -/
theorem TW2ProductLaw_coordinate_cdf (m : ℕ /- [definition] -/)
    (i : Fin m /- [definition] -/) (s : ℝ /- [definition] -/) :
    (TW2ProductLaw m).real {x | x i ≤ s} = RMTFoundations.TracyWidom.TW2R s := by
  have hp : (TW2ProductLaw m).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure := by
    simp [TW2ProductLaw,Measure.pi_map_eval]
  have hm := map_measureReal_apply (μ := TW2ProductLaw m) (measurable_pi_apply i)
    (measurableSet_Iic : MeasurableSet (Iic s))
  rw [hp] at hm
  change (TW2ProductLaw m).real ((fun x : Fin m → ℝ => x i) ⁻¹' Iic s) = _
  rw [← hm,Measure.real,RMTFoundations.TracyWidom.TW2Measure_Iic,ENNReal.toReal_ofReal]
  exact (RMTFoundations.TracyWidom.TW2R_bounds s).1

theorem TW2ProductLaw_single_selector (m : ℕ /- [definition] -/)
    (i : Fin m /- [definition] -/) :
    (TW2ProductLaw m).map (fun x => fun _ : Fin 1 => x i) = TW2ProductLaw 1 := by
  letI := TW2ProductLaw_probability m
  have hm : Measurable (fun x : Fin m → ℝ => fun _ : Fin 1 => x i) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply i
  apply measure_eq_of_jointCDF 1 _ _ ((Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance)
    (TW2ProductLaw_probability 1)
  intro s
  rw [jointCDF_map_coordinates m 1 _ (fun _ => i)]
  have he : {x : Fin m → ℝ | ∀ j : Fin 1, x i ≤ s j} = {x | x i ≤ s 0} := by
    ext x
    constructor
    · intro hx; exact hx 0
    · intro hx j; simpa [Subsingleton.elim j (0 : Fin 1)] using hx
  rw [he,TW2ProductLaw_coordinate_cdf,TW2ProductLaw_jointCDF]
  simp

/-- Every hypothesis of the full construction is satisfied on a genuine
full-dimensional TW2 model at every n and every cut, including both tails. -/
theorem finite_law_limit_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    let F := jointCDF 2 (TW2ProductLaw 2)
    let G : Fin 2 → ℝ → ℝ := fun _ => RMTFoundations.TracyWidom.TW2R
    Continuous F ∧
    (∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s))) ∧
    (∀ i s, Tendsto (fun n => (μ n : Measure (Fin 2 → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (G i s))) ∧
    (∀ i, Tendsto (G i) atBot (𝓝 0)) ∧ (∀ i, Tendsto (G i) atTop (𝓝 1)) ∧
    (∃! ν : ProbabilityMeasure (Fin 2 → ℝ), ∀ s, jointCDF 2 ν s = F s) ∧
    (∃ ν : ProbabilityMeasure (Fin 2 → ℝ), (∀ s, jointCDF 2 ν s = F s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ ρ : ProbabilityMeasure (Fin 2 → ℝ), (∀ s, jointCDF 2 ρ s = F s) → ρ=ν)) ∧
    Monotone F ∧ (∀ s, 0 ≤ F s ∧ F s ≤ 1) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => F (fun _ => a)) atBot (𝓝 0) ∧
    (∀ l, l.Nodup → ∀ a b : Fin 2 → ℝ, (∀ i ∈ l, a i ≤ b i) →
      0 ≤ rectangleDifference 2 l F a b) ∧
    0 < F (fun _ => 0) ∧ F (fun _ => 0) < 1 := by
  dsimp only
  letI := TW2ProductLaw_probability 2
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let F := jointCDF 2 (TW2ProductLaw 2)
  let G : Fin 2 → ℝ → ℝ := fun _ => RMTFoundations.TracyWidom.TW2R
  have hc : Continuous F := TW2ProductLaw_jointCDF_continuous 2
  have hl : ∀ s, Tendsto (fun n => jointCDF 2 (μ n) s) atTop (𝓝 (F s)) :=
    fun _ => tendsto_const_nhds
  have hco : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin 2 → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (G i s)) := by
    intro i s
    have he : (TW2ProductLaw 2).real {x | x i ≤ s} = G i s := TW2ProductLaw_coordinate_cdf 2 i s
    simpa only [μ,ProbabilityMeasure.coe_mk,he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => G i s) atTop (𝓝 (G i s)))
  have hb : ∀ i, Tendsto (G i) atBot (𝓝 0) := fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atBot
  have ht : ∀ i, Tendsto (G i) atTop (𝓝 1) := fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atTop
  have hp := probability_core_all_binder_joint_probe
  have hfields := limit_cdf_fields 2 (by norm_num)
    (⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩ : ProbabilityMeasure (Fin 2 → ℝ)) F (fun _ => rfl)
  exact ⟨hc,hl,hco,hb,ht,finite_law_limit 2 μ F G hc hl hco hb ht,
    finite_law_limit_with_weak 2 μ F G hc hl hco hb ht,
    hfields.1,hfields.2.1,hfields.2.2.1,hfields.2.2.2.1,hfields.2.2.2.2,
    hp.2.1,hp.2.2.1⟩
/-- Both finite-law sequences, both complete scalar tails and a proper retained
coordinate jointly realize every binder of the construction-plus-consistency root. -/
theorem consistent_limits_all_binder_joint_probe :
    ∃ ν : ProbabilityMeasure (Fin 2 → ℝ), ∃ ρ : ProbabilityMeasure (Fin 1 → ℝ),
      (∀ s, jointCDF 2 ν s = jointCDF 2 (TW2ProductLaw 2) s) ∧
      (∀ s, jointCDF 1 ρ s = jointCDF 1 (TW2ProductLaw 1) s) ∧
      (ν : Measure (Fin 2 → ℝ)).map (fun x => fun _ : Fin 1 => x 1) = ρ ∧
      0 < jointCDF 2 ν (fun _ => 0) ∧ jointCDF 2 ν (fun _ => 0) < 1 := by
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let η : ℕ → ProbabilityMeasure (Fin 1 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
  let F := jointCDF 2 (TW2ProductLaw 2)
  let H := jointCDF 1 (TW2ProductLaw 1)
  let G : Fin 2 → ℝ → ℝ := fun _ => RMTFoundations.TracyWidom.TW2R
  let J : Fin 1 → ℝ → ℝ := fun _ => RMTFoundations.TracyWidom.TW2R
  have hF : ∀ s, Tendsto (fun k => jointCDF 2 (μ k) s) atTop (𝓝 (F s)) :=
    fun _ => tendsto_const_nhds
  have hH : ∀ s, Tendsto (fun k => jointCDF 1 (η k) s) atTop (𝓝 (H s)) :=
    fun _ => tendsto_const_nhds
  have hG : ∀ i s, Tendsto (fun k => (μ k : Measure (Fin 2 → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (G i s)) := by
    intro i s
    simp only [μ,ProbabilityMeasure.coe_mk,TW2ProductLaw_coordinate_cdf]
    exact tendsto_const_nhds
  have hJ : ∀ i s, Tendsto (fun k => (η k : Measure (Fin 1 → ℝ)).real {x | x i ≤ s})
      atTop (𝓝 (J i s)) := by
    intro i s
    simp only [η,ProbabilityMeasure.coe_mk,TW2ProductLaw_coordinate_cdf]
    exact tendsto_const_nhds
  have hb := RMTFoundations.TracyWidom.tendsto_TW2R_atBot
  have ht := RMTFoundations.TracyWidom.tendsto_TW2R_atTop
  have hfinite : ∀ k, (μ k : Measure (Fin 2 → ℝ)).map
      (fun x => fun _ : Fin 1 => x 1) = η k := fun _ => TW2ProductLaw_single_selector 2 1
  obtain ⟨ν,ρ,hν,hρ,hmap⟩ := finite_law_limits_consistent 2 1 μ η F H G J (fun _ => 1)
    (TW2ProductLaw_jointCDF_continuous 2) (TW2ProductLaw_jointCDF_continuous 1) hF hH hG hJ
    (fun _ => hb) (fun _ => ht) (fun _ => hb) (fun _ => ht) hfinite
  have hp := probability_core_all_binder_joint_probe
  refine ⟨ν,ρ,hν,hρ,hmap,?_,?_⟩
  · rw [hν]; exact hp.2.1
  · rw [hν]; exact hp.2.2.1

end RMTFoundations.TracyWidom.Airy2LimitLaws

#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.finite_law_limit
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.limit_cdf_fields
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.finite_law_limit_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.coordinate_cdf_limits_tight
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.finite_law_limit_with_weak
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.finite_law_limits_consistent
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.TW2ProductLaw_coordinate_cdf
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.TW2ProductLaw_single_selector
#print axioms RMTFoundations.TracyWidom.Airy2LimitLaws.consistent_limits_all_binder_joint_probe
