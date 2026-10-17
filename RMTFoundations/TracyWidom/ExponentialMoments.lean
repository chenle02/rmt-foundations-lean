import Mathlib


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- Reusable exponential absolute integrable of tail with the exact hypotheses of the named declaration. -/
theorem exponential_absolute_integrable_of_tail
    (μ : Measure ℝ /- [definition] -/)
    [IsFiniteMeasure μ] /- [standing] -/
    (C b a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hab : a < b /- [standing] -/)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {x : ℝ | t < |x|} ≤ ENNReal.ofReal (C * Real.exp (-b*t)) /- [standing] -/) :
    Integrable (fun x : ℝ => Real.exp (a*|x|)) μ := by
  let g : ℝ → ℝ := fun t => a * Real.exp (a*t)
  have hprim : ∀ x : ℝ, (∫ t in 0..|x|, g t) = Real.exp (a*|x|)-1 := by
    intro x
    have hder : ∀ t : ℝ, HasDerivAt (fun z : ℝ => Real.exp (a*z)) (g t) t := by
      intro t
      simpa [g, mul_comm] using ((hasDerivAt_id t).const_mul a).exp
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hder t) ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 |x|)
  have hkey := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun x : ℝ => |x|) (g := g) μ
    (Eventually.of_forall (fun x : ℝ => abs_nonneg x))
    continuous_abs.measurable.aemeasurable
    (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
    (Eventually.of_forall (fun t : ℝ => show 0 ≤ g t by dsimp [g]; positivity))
  have hi : Integrable (fun t : ℝ => (C*a)*Real.exp (-(b-a)*t))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hab)).const_mul (C*a)
  have hbound : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a*|x|)-1) ∂μ) ≤
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((C*a)*Real.exp (-(b-a)*t)) := by
    simp_rw [hprim] at hkey
    rw [hkey]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := mul_le_mul_of_nonneg_right (htail t ht.le) (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (g t) from bot_le)
    apply h.trans_eq
    rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_pos _).le)]
    congr 1
    dsimp [g]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 1
    ring
  have hnon : ∀ᵐ x : ℝ ∂μ, 0 ≤ Real.exp (a*|x|)-1 := by
    apply Eventually.of_forall
    intro x
    have := Real.one_le_exp_iff.mpr (mul_nonneg ha.le (abs_nonneg x))
    linarith
  have hm : AEStronglyMeasurable (fun x : ℝ => Real.exp (a*|x|)-1) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).sub
      continuous_const).aestronglyMeasurable
  have hmI : Integrable (fun x : ℝ => Real.exp (a*|x|)-1) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm hnon).mp
      (ne_of_lt (hbound.trans_lt hi.lintegral_lt_top))
  exact (hmI.add (integrable_const (1:ℝ))).congr
    (Eventually.of_forall (fun x => sub_add_cancel (Real.exp (a*|x|)) 1))

/-- Reusable all absolute moments of exponential integrable with the exact hypotheses of the named declaration. -/
theorem all_absolute_moments_of_exponential_integrable
    (μ : Measure ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/)
    (hi : Integrable (fun x : ℝ => Real.exp (a*|x|)) μ /- [standing] -/)
    (p : ℝ /- [definition] -/)
    (hp : 0 ≤ p /- [standing] -/) : Integrable (fun x : ℝ => |x|^p) μ := by
  have hpos : Integrable (fun x : ℝ => Real.exp (a*x)) μ := by
    apply hi.mono' (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (a*x)) μ)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ha.le)
  have hneg : Integrable (fun x : ℝ => Real.exp (-a*x)) μ := by
    apply hi.mono' (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (-a*x)) μ)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith [neg_le_abs x]
  exact integrable_rpow_abs_of_integrable_exp_mul ha.ne' hpos hneg hp

/-- The full exponential-tail interface holds on a law supported at both -1 and 1. -/
theorem exponential_moments_all_binder_joint_probe :
    ∃ μ : Measure ℝ, ∃ C b a : ℝ,
      IsProbabilityMeasure μ ∧ 0 < μ (Iio 0) ∧ 0 < μ (Ioi 0) ∧
      0 < C ∧ 0 < a ∧ a < b ∧
      (∀ t : ℝ, 0 ≤ t → μ {x : ℝ | t < |x|} ≤
        ENNReal.ofReal (C * Real.exp (-b*t))) ∧
      Integrable (fun x : ℝ => Real.exp (a*|x|)) μ ∧
      (∀ p : ℝ, 0 ≤ p → Integrable (fun x : ℝ => |x|^p) μ) := by
  let μ : Measure ℝ := (1/2:ℝ≥0∞) • Measure.dirac (-1) + (1/2:ℝ≥0∞) • Measure.dirac 1
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simpa [μ, one_div] using (ENNReal.add_halves 1)
  letI := hprob
  have ht : ∀ t : ℝ, 0 ≤ t → μ {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (Real.exp 2 * Real.exp (-2*t)) := by
    intro t ht
    by_cases h : t < 1
    · have hm : μ {x : ℝ | t < |x|} ≤ 1 := prob_le_one
      apply hm.trans
      have he : (1:ℝ) ≤ Real.exp 2 * Real.exp (-2*t) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        linarith
      simpa using ENNReal.ofReal_le_ofReal he
    · have hz : μ {x : ℝ | t < |x|} = 0 := by
        simp [μ, Measure.dirac_apply', h]
      rw [hz]
      exact bot_le
  have hi := exponential_absolute_integrable_of_tail μ (Real.exp 2) 2 1
    (Real.exp_pos _).le (by norm_num) (by norm_num) ht
  refine ⟨μ,Real.exp 2,2,1,hprob,?_,?_,Real.exp_pos _,by norm_num,by norm_num,ht,hi,?_⟩
  · norm_num [μ]
  · norm_num [μ]
  · intro p hp
    exact all_absolute_moments_of_exponential_integrable μ 1 (by norm_num) hi p hp

end RMTFoundations.TracyWidom
#print axioms RMTFoundations.TracyWidom.exponential_absolute_integrable_of_tail
#print axioms RMTFoundations.TracyWidom.all_absolute_moments_of_exponential_integrable

#print axioms RMTFoundations.TracyWidom.exponential_moments_all_binder_joint_probe
