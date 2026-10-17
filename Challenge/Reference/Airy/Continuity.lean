import Mathlib

import Challenge.Reference.Airy.Core
import Challenge.Reference.Airy.Bounds

namespace RMTFoundations.AiryContinuity

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
open RMTFoundations.Airy

/-- The copied entire-function API and the bounds API are definitionally the same Ai. -/
theorem airyAiReal_eq_Ai :
    RMTFoundations.Airy.airyAiReal = RMTFoundations.Airy.airyAiReal := rfl

/-- The full operator closure uses the same Ai. -/
theorem closure_airyAiReal_eq_Ai :
    RMTFoundations.Airy.airyAiReal = RMTFoundations.Airy.airyAiReal := rfl

/-- Reuse the stronger bound, including the origin. -/
theorem airyAiReal_superexponential_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
    |RMTFoundations.Airy.airyAiReal x| ≤
      C * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) := by
  rw [airyAiReal_eq_Ai]
  exact RMTFoundations.AiryBounds.Ai_superexponential_bound

theorem airyHankelShiftKernel_eq_Ai_kernel (s : ℝ /- [definition] -/) :
    airyHankelShiftKernel s = RMTFoundations.Airy.airyHankelShiftKernel s := rfl

noncomputable abbrev airyKernelLp : ℝ → Lp ℝ 2 (halfLineMeasure.prod halfLineMeasure) :=
  RMTFoundations.AiryBounds.Ai_kernelLp

theorem airyKernelLp_continuous : Continuous airyKernelLp :=
  RMTFoundations.AiryBounds.Ai_kernelLp_continuous

/-- Linearity in the kernel, proved from actual integrable slices. -/
theorem kernelOperator_sub (K L : ℝ × ℝ → ℝ /- [definition] -/)
    (hK : MemLp K 2 (halfLineMeasure.prod halfLineMeasure) /- [standing] -/ )
    (hL : MemLp L 2 (halfLineMeasure.prod halfLineMeasure) /- [standing] -/ ) :
    kernelOperator (hK.sub hL) = kernelOperator hK - kernelOperator hL := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (hK.sub hL) f,
    kernelOperator_apply_ae hK f, kernelOperator_apply_ae hL f,
    integrable_kernelFun_slice_ae hK f, integrable_kernelFun_slice_ae hL f,
    Lp.coeFn_sub (kernelOperator hK f) (kernelOperator hL f)] with x hsub h1 h2 hi1 hi2 hf
  rw [sub_apply, hf, hsub]
  simp only [Pi.sub_apply, h1, h2, kernelIntegralFun, sub_mul]
  exact integral_sub hi1 hi2

theorem hsENorm_airyHankelShift_sub_le (s t : ℝ /- [definition] -/) :
    hsENorm (airyHankelShift s - airyHankelShift t) ≤
      edist (airyKernelLp s) (airyKernelLp t) := by
  have h := hsENorm_kernelOperator_le
    ((memLp_airyHankelShiftKernel s).sub (memLp_airyHankelShiftKernel t))
  rw [kernelOperator_sub _ _ (memLp_airyHankelShiftKernel s)
    (memLp_airyHankelShiftKernel t)] at h
  simpa only [airyHankelShift, airyKernelLp, RMTFoundations.AiryBounds.Ai_kernelLp,
    Lp.edist_toLp_toLp, airyHankelShiftKernel_eq_Ai_kernel] using h

/-- Continuity in the Hilbert--Schmidt metric for every real cutoff. -/
theorem tendsto_hsENorm_airyHankelShift_sub (t : ℝ /- [definition] -/) :
    Tendsto (fun s => hsENorm (airyHankelShift s - airyHankelShift t)) (𝓝 t) (𝓝 0) := by
  have h := (airyKernelLp_continuous.tendsto t).edist
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => airyKernelLp t) (𝓝 t) (𝓝 (airyKernelLp t)))
  simp only [edist_self] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun s =>
      hsENorm_airyHankelShift_sub_le s t)

theorem tendsto_hsNorm_airyHankelShift_sub (t : ℝ /- [definition] -/) :
    Tendsto (fun s => hsNorm (airyHankelShift s - airyHankelShift t)) (𝓝 t) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_hsENorm_airyHankelShift_sub t)
  simpa only [hsNorm, ENNReal.toReal_zero, Function.comp_def] using h

/-- The canonical nonzero Ai and a unit vector witness simultaneous nondegeneracy. -/
theorem continuity_joint_probe (s : ℝ /- [definition] -/) :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      ‖shiftedUnitVector s‖ = 1 ∧
      IsHilbertSchmidt (airyHankelShift s) ∧ IsTraceClass (airyKernelShift s) := by
  refine ⟨?_, shiftedUnitVector_norm s, isHilbertSchmidt_airyHankelShift s,
    isTraceClass_airyKernelShift s⟩
  rw [airyAiReal_eq_Ai]
  exact RMTFoundations.AiryBounds.Ai_kernel_inhabitation.1

/-- Endomorphisms of the fixed positive-half-line real Hilbert space. -/
noncomputable abbrev AiryOp := Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure

noncomputable def hsProductSum (l : List (AiryOp × AiryOp) /- [definition] -/ ) : AiryOp :=
  (l.map fun p => p.1 ∘L p.2).sum

noncomputable def hsProductCost (l : List (AiryOp × AiryOp) /- [definition] -/ ) : ℝ≥0∞ :=
  (l.map fun p => hsENorm p.1 * hsENorm p.2).sum

/-- The projective trace-ideal enorm: infimum of the costs of finite HS-product
presentations. Infinite costs need no extra proof fields. This is independent of
any Hilbert basis because each hsENorm is basis independent. -/
noncomputable def traceENorm (T : AiryOp /- [definition] -/) : ℝ≥0∞ :=
  ⨅ l : List (AiryOp × AiryOp), ⨅ (_ : T = hsProductSum l), hsProductCost l

noncomputable def traceNorm (T : AiryOp /- [definition] -/) : ℝ := (traceENorm T).toReal

theorem traceENorm_le_presentation (T : AiryOp /- [definition] -/)
    (l : List (AiryOp × AiryOp) /- [definition] -/ )
    (h : T = hsProductSum l /- [standing] -/) : traceENorm T ≤ hsProductCost l :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

theorem traceENorm_zero : traceENorm (0 : AiryOp) = 0 := by
  apply le_antisymm _ zero_le
  simpa [hsProductSum, hsProductCost] using traceENorm_le_presentation 0 [] (by
    simp [hsProductSum])

theorem traceENorm_comp_le (A B : AiryOp /- [definition] -/) :
    traceENorm (A ∘L B) ≤ hsENorm A * hsENorm B := by
  simpa [hsProductSum, hsProductCost] using traceENorm_le_presentation (A ∘L B) [(A, B)]
    (by simp [hsProductSum])

theorem traceENorm_add_le (S T : AiryOp /- [definition] -/) :
    traceENorm (S + T) ≤ traceENorm S + traceENorm T := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro l hl m hm
  have hsum : S + T = hsProductSum (l ++ m) := by
    simp only [hsProductSum, List.map_append, List.sum_append] at hl hm ⊢
    rw [hl, hm]
  simpa [hsProductCost, List.map_append, List.sum_append] using
    traceENorm_le_presentation (S + T) (l ++ m) hsum

/-- The trace gauge dominates the genuine operator norm; it cannot collapse
nonzero operators to zero. -/
theorem enorm_le_traceENorm (T : AiryOp /- [definition] -/) : ‖T‖ₑ ≤ traceENorm T := by
  apply le_iInf
  intro l
  apply le_iInf
  intro hl
  rw [hl]
  clear hl T
  induction l with
  | nil => simp [hsProductSum, hsProductCost, enorm]
  | cons p l ih =>
      simp only [hsProductSum, hsProductCost, List.map_cons, List.sum_cons] at ih ⊢
      have hadd : ‖p.1 ∘L p.2 + hsProductSum l‖ₑ ≤
          ‖p.1 ∘L p.2‖ₑ + ‖hsProductSum l‖ₑ := by
        simpa only [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm] using
          ENNReal.ofReal_le_ofReal (norm_add_le (p.1 ∘L p.2) (hsProductSum l))
      exact hadd.trans (add_le_add
        ((ContinuousLinearMap.opENorm_comp_le p.1 p.2).trans (mul_le_mul
          (opENorm_le_sumSq_rpow_half p.1 (canonicalBasis ℝ _))
          (opENorm_le_sumSq_rpow_half p.2 (canonicalBasis ℝ _)) zero_le zero_le)) ih)

theorem traceENorm_eq_zero_iff (T : AiryOp /- [definition] -/) :
    traceENorm T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hx := enorm_le_traceENorm T
    rw [h] at hx
    have hz : ‖T‖ₑ = 0 := le_antisymm hx zero_le
    have hn := congrArg ENNReal.toReal hz
    exact norm_eq_zero.mp (by simpa only [toReal_enorm, ENNReal.toReal_zero] using hn)
  · intro h
    simpa [h] using traceENorm_zero

theorem traceENorm_airyKernelShift_ne_top (s : ℝ /- [definition] -/) :
    traceENorm (airyKernelShift s) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (isHilbertSchmidt_airyHankelShift s)
    (isHilbertSchmidt_airyHankelShift s)) (traceENorm_comp_le _ _)

theorem airyKernelShift_sub_factorization (s t : ℝ /- [definition] -/) :
    airyKernelShift s - airyKernelShift t =
      (airyHankelShift s - airyHankelShift t) ∘L airyHankelShift s +
        airyHankelShift t ∘L (airyHankelShift s - airyHankelShift t) := by
  change airyHankelShift s * airyHankelShift s - airyHankelShift t * airyHankelShift t =
    (airyHankelShift s - airyHankelShift t) * airyHankelShift s +
      airyHankelShift t * (airyHankelShift s - airyHankelShift t)
  rw [sub_mul, mul_sub, sub_add_sub_cancel]

theorem traceENorm_airyKernelShift_sub_le (s t : ℝ /- [definition] -/) :
    traceENorm (airyKernelShift s - airyKernelShift t) ≤
      hsENorm (airyHankelShift s - airyHankelShift t) *
        (‖airyKernelLp s‖ₑ + ‖airyKernelLp t‖ₑ) := by
  have hsize : ∀ u : ℝ, hsENorm (airyHankelShift u) ≤ ‖airyKernelLp u‖ₑ := by
    intro u
    have h := hsENorm_kernelOperator_le (memLp_airyHankelShiftKernel u)
    simpa only [airyHankelShift, airyKernelLp, RMTFoundations.AiryBounds.Ai_kernelLp,
      Lp.enorm_toLp, airyHankelShiftKernel_eq_Ai_kernel] using h
  rw [airyKernelShift_sub_factorization]
  calc traceENorm ((airyHankelShift s - airyHankelShift t) ∘L airyHankelShift s +
      airyHankelShift t ∘L (airyHankelShift s - airyHankelShift t))
      ≤ traceENorm ((airyHankelShift s - airyHankelShift t) ∘L airyHankelShift s) +
        traceENorm (airyHankelShift t ∘L (airyHankelShift s - airyHankelShift t)) :=
          traceENorm_add_le _ _
    _ ≤ hsENorm (airyHankelShift s - airyHankelShift t) * hsENorm (airyHankelShift s) +
      hsENorm (airyHankelShift t) * hsENorm (airyHankelShift s - airyHankelShift t) :=
        add_le_add (traceENorm_comp_le _ _) (traceENorm_comp_le _ _)
    _ ≤ hsENorm (airyHankelShift s - airyHankelShift t) * ‖airyKernelLp s‖ₑ +
      ‖airyKernelLp t‖ₑ * hsENorm (airyHankelShift s - airyHankelShift t) :=
        by gcongr <;> exact hsize _
    _ = hsENorm (airyHankelShift s - airyHankelShift t) *
      (‖airyKernelLp s‖ₑ + ‖airyKernelLp t‖ₑ) := by rw [mul_add, mul_comm ‖airyKernelLp t‖ₑ]

theorem traceENorm_airyKernelShift_sub_ne_top (s t : ℝ /- [definition] -/) :
    traceENorm (airyKernelShift s - airyKernelShift t) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top
    ((isHilbertSchmidt_airyHankelShift s).sub (isHilbertSchmidt_airyHankelShift t))
    (ENNReal.add_ne_top.mpr ⟨enorm_ne_top, enorm_ne_top⟩))
    (traceENorm_airyKernelShift_sub_le s t)

/-- Actual continuity in the projective trace-ideal metric, for all real levels. -/
theorem tendsto_traceENorm_airyKernelShift_sub (t : ℝ /- [definition] -/) :
    Tendsto (fun s => traceENorm (airyKernelShift s - airyKernelShift t)) (𝓝 t) (𝓝 0) := by
  have hsize : Tendsto (fun s => ‖airyKernelLp s‖ₑ + ‖airyKernelLp t‖ₑ)
      (𝓝 t) (𝓝 (‖airyKernelLp t‖ₑ + ‖airyKernelLp t‖ₑ)) :=
    (airyKernelLp_continuous.tendsto t).enorm.add tendsto_const_nhds
  have hprod := ENNReal.Tendsto.mul (tendsto_hsENorm_airyHankelShift_sub t)
    (Or.inr (ENNReal.add_ne_top.mpr ⟨enorm_ne_top, enorm_ne_top⟩)) hsize
    (Or.inr ENNReal.zero_ne_top)
  simp only [zero_mul] at hprod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun s => traceENorm_airyKernelShift_sub_le s t)

theorem tendsto_traceNorm_airyKernelShift_sub (t : ℝ /- [definition] -/) :
    Tendsto (fun s => traceNorm (airyKernelShift s - airyKernelShift t)) (𝓝 t) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_traceENorm_airyKernelShift_sub t)
  simpa only [traceNorm, ENNReal.toReal_zero, Function.comp_def] using h

/-- The trace-ideal family assumptions and nonzero Hilbert space hold jointly. -/
theorem trace_continuity_joint_probe (s : ℝ /- [definition] -/) :
    ‖shiftedUnitVector s‖ = 1 ∧
      traceENorm (airyKernelShift s) ≠ ⊤ ∧
      traceENorm (airyKernelShift s - airyKernelShift (s - 1)) ≠ ⊤ :=
  ⟨shiftedUnitVector_norm s, traceENorm_airyKernelShift_ne_top s,
    traceENorm_airyKernelShift_sub_ne_top s (s - 1)⟩

theorem hsENorm_smul (c : ℝ /- [definition] -/) (T : AiryOp /- [definition] -/) :
    hsENorm (c • T) = ‖c‖ₑ * hsENorm T := by
  unfold hsENorm sumSq
  simp only [smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq']

theorem hsProductSum_smul (c : ℝ /- [definition] -/)
    (l : List (AiryOp × AiryOp) /- [definition] -/ ) :
    hsProductSum (l.map fun p => (c • p.1, p.2)) = c • hsProductSum l := by
  induction l with
  | nil =>
      change (0 : AiryOp) = c • (0 : AiryOp)
      apply ContinuousLinearMap.ext
      intro f
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_zero]
  | cons p l ih =>
      simp only [List.map_cons, hsProductSum, List.sum_cons] at ih ⊢
      rw [ih, ContinuousLinearMap.smul_comp, smul_add]

theorem hsProductCost_smul (c : ℝ /- [definition] -/)
    (l : List (AiryOp × AiryOp) /- [definition] -/ ) :
    hsProductCost (l.map fun p => (c • p.1, p.2)) = ‖c‖ₑ * hsProductCost l := by
  induction l with
  | nil => simp [hsProductCost]
  | cons p l ih =>
      simp only [List.map_cons, hsProductCost, List.sum_cons] at ih ⊢
      rw [ih, hsENorm_smul, mul_assoc, mul_add]

theorem traceENorm_smul_le (c : ℝ /- [definition] -/) (T : AiryOp /- [definition] -/)
    (hc : c ≠ 0 /- [standing] -/) : traceENorm (c • T) ≤ ‖c‖ₑ * traceENorm T := by
  unfold traceENorm
  rw [ENNReal.mul_iInf_of_ne (by simpa using hc) enorm_ne_top]
  apply le_iInf
  intro l
  rw [ENNReal.mul_iInf_of_ne (by simpa using hc) enorm_ne_top]
  apply le_iInf
  intro hl
  have h := traceENorm_le_presentation (c • T) (l.map fun p => (c • p.1, p.2)) (by
    rw [hsProductSum_smul, hl])
  simpa only [traceENorm, hsProductCost_smul] using h

theorem traceENorm_smul (c : ℝ /- [definition] -/) (T : AiryOp /- [definition] -/) :
    traceENorm (c • T) = ‖c‖ₑ * traceENorm T := by
  by_cases hc : c = 0
  · have hz : (0 : ℝ) • T = (0 : AiryOp) := by
      apply ContinuousLinearMap.ext
      intro f
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, zero_smul]
    rw [hc, hz, traceENorm_zero, enorm_zero, zero_mul]
  apply le_antisymm (traceENorm_smul_le c T hc)
  have h := traceENorm_smul_le c⁻¹ (c • T) (inv_ne_zero hc)
  rw [inv_smul_smul₀ hc, enorm_inv hc] at h
  have he : ‖c‖ₑ ≠ 0 := by simpa only [ne_eq, enorm_eq_zero] using hc
  have hm := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞) ≤ ‖c‖ₑ from zero_le)
  rw [← mul_assoc, ENNReal.mul_inv_cancel he enorm_ne_top, one_mul] at hm
  exact hm

theorem traceENorm_neg (T : AiryOp /- [definition] -/) : traceENorm (-T) = traceENorm T := by
  have hneg : (-1 : ℝ) • T = -T := by
    apply ContinuousLinearMap.ext
    intro f
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
    exact neg_one_smul ℝ (T f)
  simpa only [hneg, enorm_neg, enorm_one, one_mul] using traceENorm_smul (-1) T

/-- The ordinary operator topology also follows from the stronger trace estimate. -/
theorem continuous_airyKernelShift : Continuous airyKernelShift := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h : Tendsto (fun s => ‖airyKernelShift s - airyKernelShift t‖ₑ) (𝓝 t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_traceENorm_airyKernelShift_sub t) (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun s => enorm_le_traceENorm _)
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa only [Function.comp_def, ENNReal.toReal_zero, toReal_enorm] using hr

end RMTFoundations.AiryContinuity

#print axioms RMTFoundations.AiryContinuity.airyAiReal_eq_Ai
#print axioms RMTFoundations.AiryContinuity.closure_airyAiReal_eq_Ai
#print axioms RMTFoundations.AiryContinuity.airyAiReal_superexponential_bound
#print axioms RMTFoundations.AiryContinuity.airyHankelShiftKernel_eq_Ai_kernel
#print axioms RMTFoundations.AiryContinuity.airyKernelLp
#print axioms RMTFoundations.AiryContinuity.airyKernelLp_continuous
#print axioms RMTFoundations.AiryContinuity.kernelOperator_sub
#print axioms RMTFoundations.AiryContinuity.hsENorm_airyHankelShift_sub_le
#print axioms RMTFoundations.AiryContinuity.tendsto_hsENorm_airyHankelShift_sub
#print axioms RMTFoundations.AiryContinuity.tendsto_hsNorm_airyHankelShift_sub
#print axioms RMTFoundations.AiryContinuity.continuity_joint_probe
#print axioms RMTFoundations.AiryContinuity.AiryOp
#print axioms RMTFoundations.AiryContinuity.hsProductSum
#print axioms RMTFoundations.AiryContinuity.hsProductCost
#print axioms RMTFoundations.AiryContinuity.traceENorm
#print axioms RMTFoundations.AiryContinuity.traceNorm
#print axioms RMTFoundations.AiryContinuity.traceENorm_le_presentation
#print axioms RMTFoundations.AiryContinuity.traceENorm_zero
#print axioms RMTFoundations.AiryContinuity.traceENorm_comp_le
#print axioms RMTFoundations.AiryContinuity.traceENorm_add_le
#print axioms RMTFoundations.AiryContinuity.enorm_le_traceENorm
#print axioms RMTFoundations.AiryContinuity.traceENorm_eq_zero_iff
#print axioms RMTFoundations.AiryContinuity.traceENorm_airyKernelShift_ne_top
#print axioms RMTFoundations.AiryContinuity.airyKernelShift_sub_factorization
#print axioms RMTFoundations.AiryContinuity.traceENorm_airyKernelShift_sub_le
#print axioms RMTFoundations.AiryContinuity.traceENorm_airyKernelShift_sub_ne_top
#print axioms RMTFoundations.AiryContinuity.tendsto_traceENorm_airyKernelShift_sub
#print axioms RMTFoundations.AiryContinuity.tendsto_traceNorm_airyKernelShift_sub
#print axioms RMTFoundations.AiryContinuity.trace_continuity_joint_probe
#print axioms RMTFoundations.AiryContinuity.hsENorm_smul
#print axioms RMTFoundations.AiryContinuity.hsProductSum_smul
#print axioms RMTFoundations.AiryContinuity.hsProductCost_smul
#print axioms RMTFoundations.AiryContinuity.traceENorm_smul_le
#print axioms RMTFoundations.AiryContinuity.traceENorm_smul
#print axioms RMTFoundations.AiryContinuity.traceENorm_neg
#print axioms RMTFoundations.AiryContinuity.continuous_airyKernelShift
