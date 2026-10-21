import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2ScalarTightness
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- CDF convergence with both genuine tail limits forces tightness of a scalar sequence. -/
theorem tight_of_cdf_limit (μ : ℕ → ProbabilityMeasure ℝ /- [definition] -/)
    (G : ℝ → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => (μ n : Measure ℝ).real (Iic s)) atTop (𝓝 (G s))
      /- [standing] -/)
    (hbot : Tendsto G atBot (𝓝 0) /- [standing] -/)
    (htop : Tendsto G atTop (𝓝 1) /- [standing] -/) :
    IsTightMeasureSet (range (fun n => (μ n : Measure ℝ))) := by
  have hE (s : ℝ) : Tendsto (fun n => (μ n : Measure ℝ) (Iic s)) atTop
      (𝓝 (ENNReal.ofReal (G s))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim s)
    simpa [Function.comp_def,Measure.real, ENNReal.ofReal_toReal, measure_ne_top] using h
  have htail (r : ℝ) : atTop.limsup (fun n => (μ n : Measure ℝ) {x | r < ‖x‖}) ≤
      ENNReal.ofReal (G (-r)) + (1-ENNReal.ofReal (G r)) := by
    have he (n : ℕ) : (μ n : Measure ℝ) {x | r < ‖x‖} ≤
        (μ n : Measure ℝ) (Iic (-r)) + (1-(μ n : Measure ℝ) (Iic r)) := by
      have hi : {x : ℝ | r < ‖x‖} ⊆ Iic (-r) ∪ Ioi r := by
        intro x hx
        by_cases h : x ≤ -r
        · exact Or.inl h
        · have hh : -r < x := lt_of_not_ge h
          right
          have h' : r < |x| := hx
          rcases lt_abs.mp h' with h'|h'
          · exact h'
          · linarith
      calc
        _ ≤ (μ n : Measure ℝ) (Iic (-r) ∪ Ioi r) := measure_mono hi
        _ ≤ (μ n : Measure ℝ) (Iic (-r)) + (μ n : Measure ℝ) (Ioi r) := measure_union_le _ _
        _ = _ := by rw [show Ioi r = (Iic r)ᶜ by ext; simp,
          measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
    have hc : Tendsto (fun n => (1 : ℝ≥0∞) - (μ n : Measure ℝ) (Iic r)) atTop
        (𝓝 (1-ENNReal.ofReal (G r))) := ENNReal.Tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1))
      (hE r) (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ ∞))
    have ht := (hE (-r)).add hc
    calc
      _ ≤ atTop.limsup (fun n => (μ n : Measure ℝ) (Iic (-r)) +
          (1-(μ n : Measure ℝ) (Iic r))) := limsup_le_limsup (Eventually.of_forall he)
      _ = _ := ht.limsup_eq
  apply isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
  have hb : Tendsto (fun r : ℝ => ENNReal.ofReal (G (-r))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hbot.comp tendsto_neg_atTop_atBot)
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (G r)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp htop
  have hc : Tendsto (fun r : ℝ => (1 : ℝ≥0∞)-ENNReal.ofReal (G r)) atTop (𝓝 (1-1 : ℝ≥0∞)) :=
    ENNReal.Tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ≥0∞)) atTop (𝓝 1))
      ht (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ ∞))
  have hs := hb.add hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hs) (fun _ => bot_le) htail

/-- Full asymptotic example on the actual nondegenerate TW2 scalar measure. -/
theorem scalar_tight_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure ℝ := fun _ =>
      ⟨RMTFoundations.TracyWidom.TW2Measure, inferInstance⟩
    (∀ s, Tendsto (fun n => (μ n : Measure ℝ).real (Iic s)) atTop
      (𝓝 (RMTFoundations.TracyWidom.TW2R s))) ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atBot (𝓝 0) ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun n => (μ n : Measure ℝ))) ∧
    0 < RMTFoundations.TracyWidom.TW2R 0 ∧ RMTFoundations.TracyWidom.TW2R 0 < 1 := by
  dsimp only
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ =>
    ⟨RMTFoundations.TracyWidom.TW2Measure,inferInstance⟩
  have hl : ∀ s, Tendsto (fun n => (μ n : Measure ℝ).real (Iic s)) atTop
      (𝓝 (RMTFoundations.TracyWidom.TW2R s)) := by
    intro s
    have he : (RMTFoundations.TracyWidom.TW2Measure).real (Iic s) =
        RMTFoundations.TracyWidom.TW2R s := by
      rw [Measure.real,RMTFoundations.TracyWidom.TW2Measure_Iic,ENNReal.toReal_ofReal]
      exact (RMTFoundations.TracyWidom.TW2R_bounds s).1
    simpa only [μ,ProbabilityMeasure.coe_mk,he] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => RMTFoundations.TracyWidom.TW2R s) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s)))
  have hb := RMTFoundations.TracyWidom.tendsto_TW2R_atBot
  have ht := RMTFoundations.TracyWidom.tendsto_TW2R_atTop
  exact ⟨hl,hb,ht,tight_of_cdf_limit μ _ hl hb ht,
    RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0,
    (RMTFoundations.TracyWidom.TW2R_strictMono (by norm_num : (0 : ℝ) < 1)).trans_le
      (RMTFoundations.TracyWidom.TW2R_bounds 1).2⟩
end RMTFoundations.TracyWidom.Airy2ScalarTightness

#print axioms RMTFoundations.TracyWidom.Airy2ScalarTightness.tight_of_cdf_limit
#print axioms RMTFoundations.TracyWidom.Airy2ScalarTightness.scalar_tight_all_binder_joint_probe
