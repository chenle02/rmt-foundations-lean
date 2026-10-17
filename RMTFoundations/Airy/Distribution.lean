import Mathlib
import RMTFoundations.Airy.Core
import RMTFoundations.Airy.Continuity

namespace RMTFoundations.AiryDistribution

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryContinuity

/-- The quadratic form of the genuine Airy square is a squared Hilbert norm. -/
theorem airyKernelShift_quadratic (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ⟪airyKernelShift s f, f⟫_ℝ = ‖airyHankelShift s f‖ ^ 2 := by
  have h := (isSelfAdjoint_airyHankelShift s).isSymmetric (airyHankelShift s f) f
  change ⟪airyKernelShift s f, f⟫_ℝ = ⟪airyHankelShift s f, airyHankelShift s f⟫_ℝ at h
  exact h.trans (real_inner_self_eq_norm_sq _)

theorem airyKernelShift_quadratic_nonneg (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    0 ≤ ⟪airyKernelShift s f, f⟫_ℝ := by
  rw [airyKernelShift_quadratic]
  exact sq_nonneg _

theorem isSelfAdjoint_airyKernelShift (s : ℝ /- [definition] -/) :
    IsSelfAdjoint (airyKernelShift s) := by
  have h := IsSelfAdjoint.star_mul_self (airyHankelShift s)
  rw [(isSelfAdjoint_airyHankelShift s).star_eq] at h
  exact h

theorem isPositive_airyKernelShift (s : ℝ /- [definition] -/) :
    (airyKernelShift s).IsPositive := by
  exact (ContinuousLinearMap.isPositive_iff' _).mpr
    ⟨isSelfAdjoint_airyKernelShift s, airyKernelShift_quadratic_nonneg s⟩

theorem airyKernelShift_nonneg (s : ℝ /- [definition] -/) : 0 ≤ airyKernelShift s :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_airyKernelShift s)

/-- A uniform exponential bound for the actual shifted kernels. -/
theorem airyHankelShift_eLpNorm_exp_bound : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
    eLpNorm (airyHankelShiftKernel s) 2 (halfLineMeasure.prod halfLineMeasure) ≤
      ENNReal.ofReal (C * Real.exp (-s)) *
        eLpNorm (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2)) 2
          (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨C, hC, hb⟩ := airyAiReal_abs_le_exp'
  refine ⟨C, hC, fun s => eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (memLp_airyHankelShiftKernel s).aestronglyMeasurable ?_ 2⟩
  apply Eventually.of_forall
  intro p
  simp only [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  calc |airyHankelShiftKernel s p| ≤ C * Real.exp (-(p.1 + p.2 + s)) := hb _
    _ = _ := by simp only [neg_add, Real.exp_add]; ring

/-- Right-tail decay in the genuine kernel L² norm. -/
theorem tendsto_airyHankelShift_eLpNorm_atTop :
    Tendsto (fun s => eLpNorm (airyHankelShiftKernel s) 2
      (halfLineMeasure.prod halfLineMeasure)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := airyHankelShift_eLpNorm_exp_bound
  have hc : Tendsto (fun s : ℝ => C * Real.exp (-s)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot)
    simpa only [Function.comp_def, mul_zero] using h.const_mul C
  have ho : Tendsto (fun s : ℝ => ENNReal.ofReal (C * Real.exp (-s))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  have hp := ENNReal.Tendsto.mul ho (Or.inr memLp_expPair.eLpNorm_ne_top)
    tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
  simp only [zero_mul] at hp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hb)

theorem tendsto_hsENorm_airyHankelShift_atTop :
    Tendsto (fun s => hsENorm (airyHankelShift s)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_airyHankelShift_eLpNorm_atTop (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun s => hsENorm_kernelOperator_le (memLp_airyHankelShiftKernel s))

/-- The projective HS-product trace norm tends to zero on the right tail. -/
theorem tendsto_traceENorm_airyKernelShift_atTop :
    Tendsto (fun s => traceENorm (airyKernelShift s)) atTop (𝓝 0) := by
  have hp := ENNReal.Tendsto.mul tendsto_hsENorm_airyHankelShift_atTop
    (Or.inr ENNReal.zero_ne_top) tendsto_hsENorm_airyHankelShift_atTop
    (Or.inr ENNReal.zero_ne_top)
  simp only [zero_mul] at hp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun s => traceENorm_comp_le (airyHankelShift s) (airyHankelShift s))

theorem tendsto_traceNorm_airyKernelShift_atTop :
    Tendsto (fun s => traceNorm (airyKernelShift s)) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    tendsto_traceENorm_airyKernelShift_atTop
  simpa only [traceNorm, ENNReal.toReal_zero, Function.comp_def] using h

theorem tendsto_norm_airyKernelShift_atTop :
    Tendsto (fun s => ‖airyKernelShift s‖) atTop (𝓝 0) := by
  have he := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_traceENorm_airyKernelShift_atTop (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun s => enorm_le_traceENorm (airyKernelShift s))
  simpa only [toReal_enorm, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he

/-- The norm-disk condition is proved eventually, without asserting it on the left tail. -/
theorem eventually_norm_airyKernelShift_lt_one :
    ∀ᶠ s : ℝ in atTop, ‖airyKernelShift s‖ < 1 :=
  tendsto_norm_airyKernelShift_atTop.eventually (Iio_mem_nhds zero_lt_one)

theorem distribution_joint_probe (s : ℝ /- [definition] -/) :
    ‖shiftedUnitVector 0‖ = 1 ∧ airyAiReal 0 ≠ 0 ∧
      IsSelfAdjoint (airyHankelShift s) ∧ (airyKernelShift s).IsPositive ∧
      IsTraceClass (airyKernelShift s) ∧ traceENorm (airyKernelShift s) ≠ ⊤ := by
  exact ⟨shiftedUnitVector_norm 0, airyAiReal_zero_pos.ne',
    isSelfAdjoint_airyHankelShift s, isPositive_airyKernelShift s,
    isTraceClass_airyKernelShift s, traceENorm_airyKernelShift_ne_top s⟩


/-- Restricting the output to a later half-line decreases its measure. -/
theorem halfLineShiftMeasure_le (d : ℝ /- [definition] -/)
    (hd : 0 ≤ d /- [standing] -/) : halfLineShiftMeasure d ≤ halfLineMeasure :=
  Measure.restrict_mono_set volume (fun _ hx => lt_of_le_of_lt hd hx)

/-- Restrict to (d,∞), then translate back to (0,∞). -/
noncomputable def rightShift (d : ℝ /- [definition] -/)
    (hd : 0 ≤ d /- [standing] -/) : AiryOp :=
  (shiftIsometry d).toLinearIsometry.toContinuousLinearMap ∘L
    Lp.LpToLpOfMeasureLeSMul (c := 1) ENNReal.one_ne_top
      (by simpa using halfLineShiftMeasure_le d hd)

theorem rightShift_norm_apply_le (d : ℝ /- [definition] -/)
    (hd : 0 ≤ d /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) : ‖rightShift d hd f‖ ≤ ‖f‖ := by
  let R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 (halfLineShiftMeasure d) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) ENNReal.one_ne_top
      (by simpa using halfLineShiftMeasure_le d hd)
  have hR : ‖R‖ ≤ 1 := by
    simpa [R] using Lp.norm_LpToLpOfMeasureLeSMul_le (p := 2) (E := ℝ)
      (c := 1) ENNReal.one_ne_top (by simpa using halfLineShiftMeasure_le d hd)
  change ‖shiftIsometry d (R f)‖ ≤ ‖f‖
  rw [(shiftIsometry d).norm_map]
  exact (R.le_opNorm f).trans (by simpa using mul_le_mul_of_nonneg_right hR (norm_nonneg f))

theorem rightShift_apply_ae (d : ℝ /- [definition] -/)
    (hd : 0 ≤ d /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    rightShift d hd f =ᵐ[halfLineMeasure] fun x => f (x + d) := by
  let R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 (halfLineShiftMeasure d) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) ENNReal.one_ne_top
      (by simpa using halfLineShiftMeasure_le d hd)
  have hr : R f =ᵐ[halfLineShiftMeasure d] f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top _ f
  exact (shiftIsometry_apply_ae d (R f)).trans
    ((measurePreserving_shift_add d).quasiMeasurePreserving.ae_eq_comp hr)

/-- Cutoff translation is restriction of the Hankel output; no pointwise Ai monotonicity
is assumed, including at negative cutoffs. -/
theorem airyHankelShift_add_eq_rightShift (s d : ℝ /- [definition] -/)
    (hd : 0 ≤ d /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    airyHankelShift (s + d) f = rightShift d hd (airyHankelShift s f) := by
  apply Lp.ext
  have hr : airyHankelShift s f =ᵐ[halfLineShiftMeasure d]
      fun x => ∫ t, airyAiReal (x + t + s) * f t ∂halfLineMeasure :=
    (airyHankelShift_apply_ae s f).filter_mono (ae_mono (halfLineShiftMeasure_le d hd))
  have hc := (measurePreserving_shift_add d).quasiMeasurePreserving.ae_eq_comp hr
  filter_upwards [airyHankelShift_apply_ae (s + d) f,
    rightShift_apply_ae d hd (airyHankelShift s f), hc] with x hx hy hz
  dsimp only [Function.comp_def] at hz
  rw [hx, hy, hz]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change airyAiReal (x + t + (s + d)) * f t = airyAiReal (x + d + t + s) * f t
    exact congrArg (fun u : ℝ => airyAiReal u * f t)
      (show x + t + (s + d) = x + d + t + s by ring)

theorem airyHankelShift_norm_antitone (s t : ℝ /- [definition] -/)
    (hst : s ≤ t /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ‖airyHankelShift t f‖ ≤ ‖airyHankelShift s f‖ := by
  have he := airyHankelShift_add_eq_rightShift s (t - s) (sub_nonneg.mpr hst) f
  rw [add_sub_cancel] at he
  rw [he]
  exact rightShift_norm_apply_le _ _ _

theorem airyKernelShift_quadratic_antitone (s t : ℝ /- [definition] -/)
    (hst : s ≤ t /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ⟪airyKernelShift t f, f⟫_ℝ ≤ ⟪airyKernelShift s f, f⟫_ℝ := by
  rw [airyKernelShift_quadratic, airyKernelShift_quadratic]
  exact pow_le_pow_left₀ (norm_nonneg _) (airyHankelShift_norm_antitone s t hst f) 2

/-- The shifted Airy squares decrease in the genuine Loewner order. -/
theorem airyKernelShift_loewner_antitone : Antitone airyKernelShift := by
  intro s t hst
  apply ContinuousLinearMap.le_def.mpr
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨(isSelfAdjoint_airyKernelShift s).sub (isSelfAdjoint_airyKernelShift t), ?_⟩
  intro f
  change 0 ≤ ⟪airyKernelShift s f - airyKernelShift t f, f⟫_ℝ
  rw [inner_sub_left]
  exact sub_nonneg.mpr (airyKernelShift_quadratic_antitone s t hst f)

/-- All comparison binders hold together at two distinct real cutoffs with a unit vector. -/
theorem comparison_joint_probe (s : ℝ /- [definition] -/) :
    s < s + 1 ∧ (0 : ℝ) ≤ 1 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      ‖airyHankelShift (s + 1) (shiftedUnitVector 0)‖ ≤
        ‖airyHankelShift s (shiftedUnitVector 0)‖ ∧
      airyKernelShift (s + 1) ≤ airyKernelShift s := by
  have h : s ≤ s + 1 := by linarith
  exact ⟨by linarith, zero_le_one, shiftedUnitVector_norm 0,
    airyHankelShift_norm_antitone s (s + 1) h _, airyKernelShift_loewner_antitone h⟩

end RMTFoundations.AiryDistribution

#print axioms RMTFoundations.AiryDistribution.airyKernelShift_quadratic
#print axioms RMTFoundations.AiryDistribution.airyKernelShift_quadratic_nonneg
#print axioms RMTFoundations.AiryDistribution.isSelfAdjoint_airyKernelShift
#print axioms RMTFoundations.AiryDistribution.isPositive_airyKernelShift
#print axioms RMTFoundations.AiryDistribution.airyKernelShift_nonneg
#print axioms RMTFoundations.AiryDistribution.airyHankelShift_eLpNorm_exp_bound
#print axioms RMTFoundations.AiryDistribution.tendsto_airyHankelShift_eLpNorm_atTop
#print axioms RMTFoundations.AiryDistribution.tendsto_hsENorm_airyHankelShift_atTop
#print axioms RMTFoundations.AiryDistribution.tendsto_traceENorm_airyKernelShift_atTop
#print axioms RMTFoundations.AiryDistribution.tendsto_traceNorm_airyKernelShift_atTop
#print axioms RMTFoundations.AiryDistribution.tendsto_norm_airyKernelShift_atTop
#print axioms RMTFoundations.AiryDistribution.eventually_norm_airyKernelShift_lt_one
#print axioms RMTFoundations.AiryDistribution.distribution_joint_probe
#print axioms RMTFoundations.AiryDistribution.halfLineShiftMeasure_le
#print axioms RMTFoundations.AiryDistribution.rightShift
#print axioms RMTFoundations.AiryDistribution.rightShift_norm_apply_le
#print axioms RMTFoundations.AiryDistribution.rightShift_apply_ae
#print axioms RMTFoundations.AiryDistribution.airyHankelShift_add_eq_rightShift
#print axioms RMTFoundations.AiryDistribution.airyHankelShift_norm_antitone
#print axioms RMTFoundations.AiryDistribution.airyKernelShift_quadratic_antitone
#print axioms RMTFoundations.AiryDistribution.airyKernelShift_loewner_antitone
#print axioms RMTFoundations.AiryDistribution.comparison_joint_probe
