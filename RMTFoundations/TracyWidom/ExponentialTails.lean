import RMTFoundations.TracyWidom.TailBounds
import RMTFoundations.TracyWidom.Probability


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal
open RMTFoundations.AiryKernel RMTFoundations.TWLeftTail
open RMTFoundations.TWOneBounds RMTFoundations.AiryBounds
open RMTFoundations.TracyWidom.Tails

theorem measure_absolute_tail_le_cdf_tails
    (μ : Measure ℝ /- [definition] -/)
    [IsProbabilityMeasure μ] /- [standing] -/
    (t : ℝ /- [definition] -/)
    (ht : 0 ≤ t /- [standing] -/) :
    μ {x : ℝ | t < |x|} ≤ ENNReal.ofReal (cdf μ (-t) + (1-cdf μ t)) := by
  have hs : {x : ℝ | t < |x|} = Iio (-t) ∪ Ioi t := by
    ext x
    simp only [mem_setOf_eq,mem_union,mem_Iio,mem_Ioi]
    by_cases hx : x < 0
    · rw [abs_of_neg hx]
      constructor
      · intro h; left; linarith
      · rintro (h | h) <;> linarith
    · rw [abs_of_nonneg (le_of_not_gt hx)]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · linarith
        · exact h
  have hleft : μ (Iio (-t)) ≤ ENNReal.ofReal (cdf μ (-t)) := by
    rw [cdf_eq_real, ofReal_measureReal]
    exact measure_mono Iio_subset_Iic_self
  have hright : μ (Ioi t) = ENNReal.ofReal (1-cdf μ t) := by
    rw [← compl_Iic, cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic,
      ofReal_measureReal]
  rw [hs]
  apply (measure_union_le _ _).trans
  rw [hright, ENNReal.ofReal_add (cdf_nonneg μ (-t)) (sub_nonneg.mpr (cdf_le_one μ t))]
  exact add_le_add hleft le_rfl

theorem absolute_tail_extend_from_threshold
    (μ : Measure ℝ /- [definition] -/)
    [IsProbabilityMeasure μ] /- [standing] -/
    (C b R : ℝ /- [definition] -/)
    (hb : 0 < b /- [standing] -/)
    (htail : ∀ t : ℝ, R ≤ t → μ {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (C*Real.exp (-b*t)) /- [standing] -/) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 ≤ t →
      μ {x : ℝ | t < |x|} ≤ ENNReal.ofReal (D*Real.exp (-b*t)) := by
  let D := max C (Real.exp (b*R))
  have hD : 0 < D := (Real.exp_pos _).trans_le (le_max_right _ _)
  refine ⟨D,hD,?_⟩
  intro t ht
  by_cases hR : R ≤ t
  · apply (htail t hR).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · apply (prob_le_one (μ := μ)).trans
    have he : (1:ℝ) ≤ D*Real.exp (-b*t) := by
      calc
        (1:ℝ) ≤ Real.exp (b*R-b*t) := Real.one_le_exp_iff.mpr (by nlinarith)
        _ = Real.exp (b*R)*Real.exp (-b*t) := by rw [show b*R-b*t = b*R+(-b*t) by ring, Real.exp_add]
        _ ≤ D*Real.exp (-b*t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    simpa using ENNReal.ofReal_le_ofReal he

theorem TW1_TW2_exponential_cdf_tails :
    ∃ b C R : ℝ, 0 < b ∧ 0 < C ∧ 1 ≤ R ∧ ∀ t : ℝ, R ≤ t →
      TW1R (-t)+(1-TW1R t) ≤ C*Real.exp (-b*t) ∧
      TW2R (-t)+(1-TW2R t) ≤ C*Real.exp (-b*t) := by
  obtain ⟨C,hC,hT⟩ := TW_right_tail_bounds
  let b := min (originMass/8) (2/3:ℝ)
  let R := max 1 (traceTailThreshold C)
  let A := Real.exp (-signedTraceFloor)+(3/4*C)+(9/8*C^2)+1+(9/16*C^2)
  have hb : 0 < b := lt_min (div_pos originMass_pos (by norm_num)) (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨b,A,R,hb,hA,le_max_left _ _,?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htt : traceTailThreshold C ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  have hpow : t ≤ t^(3/2:ℝ) := by
    have h := rpow_three_halves_increment 1 t le_rfl ht1
    norm_num at h
    linarith
  have h2 : Real.exp (-(2/3*t^(3/2:ℝ))) ≤ Real.exp (-b*t) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right (originMass/8) (2/3:ℝ)
    dsimp [b]
    nlinarith
  have h4 : Real.exp (-(4/3*t^(3/2:ℝ))) ≤ Real.exp (-b*t) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right (originMass/8) (2/3:ℝ)
    dsimp [b]
    nlinarith
  have hm : b ≤ originMass/8 := min_le_left _ _
  have hl1 := TW1R_left_tail_linear (-t) (by linarith)
  have hl2 := TW2R_left_tail_linear (-t) (by linarith)
  rw [abs_neg,abs_of_nonneg ht0] at hl1 hl2
  have he1 : Real.exp (-signedTraceFloor-originMass*t/8) ≤
      Real.exp (-signedTraceFloor)*Real.exp (-b*t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have he2 : Real.exp (-originMass*t) ≤ Real.exp (-b*t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [originMass_pos]
  obtain ⟨hr1,hr2⟩ := hT t htt
  have hc1 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (3/4:ℝ)*C by positivity)
  have hc2 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (9/8:ℝ)*C^2 by positivity)
  have hc3 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (9/16:ℝ)*C^2 by positivity)
  dsimp [A]
  constructor
  · nlinarith [hl1.trans he1, hr1.2, Real.exp_pos (-b*t)]
  · have hextra : 0 ≤ (Real.exp (-signedTraceFloor)+(3/4*C)+(9/8*C^2))*Real.exp (-b*t) := by positivity
    nlinarith [hl2.trans he2, hr2.2]

theorem TW1_TW2_exponential_absolute_tails :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      TW1Measure {x : ℝ | t < |x|} ≤ ENNReal.ofReal (C*Real.exp (-b*t)) ∧
      TW2Measure {x : ℝ | t < |x|} ≤ ENNReal.ofReal (C*Real.exp (-b*t)) := by
  letI := TW1Measure_probability
  letI := TW2Measure_probability
  obtain ⟨b,C,R,hb,hC,hR,hT⟩ := TW1_TW2_exponential_cdf_tails
  have h1 : ∀ t : ℝ, R ≤ t → TW1Measure {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (C*Real.exp (-b*t)) := by
    intro t ht
    apply (measure_absolute_tail_le_cdf_tails TW1Measure t (by linarith)).trans
    rw [TW1Measure_cdf,TW1Measure_cdf]
    exact ENNReal.ofReal_le_ofReal (hT t ht).1
  have h2 : ∀ t : ℝ, R ≤ t → TW2Measure {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (C*Real.exp (-b*t)) := by
    intro t ht
    apply (measure_absolute_tail_le_cdf_tails TW2Measure t (by linarith)).trans
    rw [TW2Measure_cdf,TW2Measure_cdf]
    exact ENNReal.ofReal_le_ofReal (hT t ht).2
  obtain ⟨D1,hD1,h1⟩ := absolute_tail_extend_from_threshold TW1Measure C b R hb h1
  obtain ⟨D2,hD2,h2⟩ := absolute_tail_extend_from_threshold TW2Measure C b R hb h2
  refine ⟨b,max D1 D2,hb,hD1.trans_le (le_max_left _ _),?_⟩
  intro t ht
  constructor
  · exact (h1 t ht).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  · exact (h2 t ht).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le))

/-- Both actual measures inhabit the entire tail interface jointly. -/
theorem TW_absolute_tail_all_binder_joint_probe :
    ∃ b C R : ℝ, 0 < b ∧ 0 < C ∧ 1 ≤ R ∧
      IsProbabilityMeasure TW1Measure ∧ IsProbabilityMeasure TW2Measure ∧
      RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      (∀ t : ℝ, 0 ≤ t →
        TW1Measure {x : ℝ | t < |x|} ≤ ENNReal.ofReal (C*Real.exp (-b*t)) ∧
        TW2Measure {x : ℝ | t < |x|} ≤ ENNReal.ofReal (C*Real.exp (-b*t))) := by
  obtain ⟨b,C,hb,hC,h⟩ := TW1_TW2_exponential_absolute_tails
  exact ⟨b,C,1,hb,hC,le_rfl,TW1Measure_probability,TW2Measure_probability,
    RMTFoundations.Airy.airyAiReal_zero_pos.ne',h⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.measure_absolute_tail_le_cdf_tails
#print axioms RMTFoundations.TracyWidom.absolute_tail_extend_from_threshold
#print axioms RMTFoundations.TracyWidom.TW1_TW2_exponential_cdf_tails
#print axioms RMTFoundations.TracyWidom.TW1_TW2_exponential_absolute_tails
#print axioms RMTFoundations.TracyWidom.TW_absolute_tail_all_binder_joint_probe
