import RMTFoundations.TracyWidom.HMPainleveWronskian
import RMTFoundations.TracyWidom.HMPainleveContinuation
import RMTFoundations.TracyWidom.HMAiryEnvelope
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMGreenRepresentation
open Set Filter MeasureTheory
open scoped Topology
/-- A differentiable convex function with a finite right limit has nonpositive slope. -/
theorem convex_derivative_nonpos
    (f : ℝ → ℝ /- [definition] -/)
    (a l : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hc : ConvexOn ℝ (Ici a) f /- [standing] -/)
    (hl : Tendsto f atTop (𝓝 l) /- [standing] -/)
    (s : ℝ /- [definition] -/)
    (hs : a ≤ s /- [standing] -/)
    : deriv f s ≤ 0 := by
  have ht : Tendsto (fun t : ℝ => (f t-f s)/(t-s)) atTop (𝓝 0) := by
    have hn := hl.sub_const (f s)
    have hi : Tendsto (fun t : ℝ => (t-s)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (by
        apply tendsto_atTop.mpr
        intro b
        filter_upwards [eventually_ge_atTop (b+s)] with t ht
        linarith)
    simpa only [mul_zero,div_eq_mul_inv] using hn.mul hi
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop s] with t hst
  have h := hc.deriv_le_slope hs (hs.trans hst.le) hst (hf s)
  simpa only [slope_def_field] using h
/-- The derivative also tends to zero; no derivative asymptotic is assumed. -/
theorem convex_derivative_atTop_zero
    (f : ℝ → ℝ /- [definition] -/)
    (a l : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hc : ConvexOn ℝ (Ici a) f /- [standing] -/)
    (hl : Tendsto f atTop (𝓝 l) /- [standing] -/)
    : Tendsto (deriv f) atTop (𝓝 0) := by
  have hsub : Tendsto (fun t : ℝ => t-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with t ht
    linarith
  have hlow : Tendsto (fun t => f t-f (t-1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using hl.sub (hl.comp hsub)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (a+1)] with t ht
    have h := hc.slope_le_deriv (show a ≤ t-1 by linarith)
      (show a ≤ t by linarith) (show t-1<t by linarith) (hf t)
    simpa only [slope_def_field,show t-(t-1)=(1:ℝ) by ring,div_one] using h
  · filter_upwards [eventually_ge_atTop a] with t ht
    exact convex_derivative_nonpos f a l hf hc hl t ht
/-- A second-derivative sign constructs the convexity used above. -/
theorem nonnegative_second_derivative_boundary
    (f : ℝ → ℝ /- [definition] -/)
    (a l : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hdf : Differentiable ℝ (deriv f) /- [standing] -/)
    (hdd : ∀ s ≥ a, 0 ≤ deriv (deriv f) s /- [standing] -/)
    (hl : Tendsto f atTop (𝓝 l) /- [standing] -/)
    : (∀ s ≥ a, deriv f s ≤ 0) ∧ Tendsto (deriv f) atTop (𝓝 0) := by
  have hc : ConvexOn ℝ (Ici a) f := convexOn_of_deriv2_nonneg'
    (convex_Ici a) hf.differentiableOn hdf.differentiableOn
    (fun s hs => hdd s hs)
  exact ⟨fun s hs => convex_derivative_nonpos f a l hf hc hl s hs,
    convex_derivative_atTop_zero f a l hf hc hl⟩

open RMTFoundations.Airy RMTFoundations.TracyWidom.HMAiryEnvelope
/-- Relative Airy normalization constructs positivity and a bounded relative envelope. -/
theorem normalized_positive_tail
    (q : ℝ → ℝ /- [definition] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : ∃ a : ℝ, 1 ≤ a ∧ ∀ s ≥ a, 0 < q s ∧ |q s/airyAiReal s| ≤ 2 := by
  have hp := hn.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  have hb := (continuous_abs.tendsto 1 |>.comp hn).eventually_lt_const
    (by norm_num : |(1:ℝ)|<2)
  obtain ⟨a,ha⟩ := ((hp.and hb).and (eventually_ge_atTop (1:ℝ))).exists_forall_of_atTop
  refine ⟨max a 1,le_max_right _ _,fun s hs => ?_⟩
  have h := ha s ((le_max_left _ _).trans hs)
  have hA : 0 < airyAiReal s := airyAiReal_pos_of_nonneg (by linarith [h.2])
  have hratio : 0 < q s/airyAiReal s := lt_trans (by norm_num) h.1.1
  exact ⟨(div_pos_iff_of_pos_right hA).mp hratio,h.1.2.le⟩
/-- Absolute decay follows from the normalization, with no derivative-decay premise. -/
theorem normalized_atTop_zero
    (q : ℝ → ℝ /- [definition] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : Tendsto q atTop (𝓝 0) := by
  have ht : Tendsto (fun s => (q s/airyAiReal s)*airyAiReal s) atTop (𝓝 0) := by
    simpa only [mul_zero] using hn.mul airyAi_atTop_zero
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  exact div_mul_cancel₀ (q s) (airyAiReal_pos_of_nonneg hs).ne'

/-- Classical PII plus Airy normalization constructs the zero derivative boundary. -/
theorem normalized_derivative_boundary
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : Tendsto (deriv q) atTop (𝓝 0) := by
  obtain ⟨a,ha,hpos⟩ := normalized_positive_tail q hn
  have hdf : Differentiable ℝ (deriv q) := fun s => (hqq s).differentiableAt
  have hdd : ∀ s ≥ a, 0 ≤ deriv (deriv q) s := by
    intro s hs
    rw [(hqq s).deriv]
    have hs0 : 0 ≤ s := by linarith
    have hq0 := (hpos s hs).1.le
    positivity
  exact (nonnegative_second_derivative_boundary q a 0 hq hdf hdd
    (normalized_atTop_zero q hn)).2
/-- The physical Airy Wronskian boundary vanishes for every normalized classical candidate. -/
theorem normalized_wronskian_boundary
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : Tendsto (fun s => airyAiReal s*deriv q s-deriv airyAiReal s*q s) atTop (𝓝 0) := by
  simpa only [mul_zero,zero_mul,sub_self] using
    (airyAi_atTop_zero.mul (normalized_derivative_boundary q hq hqq hn)).sub
      (airyAi_derivative_atTop_zero.mul (normalized_atTop_zero q hn))
/-- Both reduction-of-order integrations and absolute integrability are derived
from the equation and normalization. No representation or boundary assumption remains. -/
theorem normalized_nested_green_representation
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : ∃ a : ℝ, 1 ≤ a ∧ ∀ s ≥ a,
      0 < q s ∧ |q s/airyAiReal s| ≤ 2 ∧
      IntegrableOn (fun u => 2*airyAiReal u*(q u)^3) (Ioi s) ∧
      (∫ u in Ioi s, 2*airyAiReal u*(q u)^3) =
        -(airyAiReal s*deriv q s-deriv airyAiReal s*q s) ∧
      IntegrableOn (fun t => (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) (Ioi s) ∧
      q s/airyAiReal s = 1+
        ∫ t in Ioi s, (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2 := by
  obtain ⟨a,ha,hpos⟩ := normalized_positive_tail q hn
  let W : ℝ → ℝ := fun s => airyAiReal s*deriv q s-deriv airyAiReal s*q s
  let R : ℝ → ℝ := fun s => q s/airyAiReal s
  have hw := normalized_wronskian_boundary q hq hqq hn
  have hdW (t : ℝ) : HasDerivAt W (2*airyAiReal t*(q t)^3) t :=
    RMTFoundations.TracyWidom.HMPainleveWronskian.pii_airy_wronskian_derivative q t (hq t) (hqq t)
  have hp (t : ℝ) (ht : a ≤ t) : 0 ≤ 2*airyAiReal t*(q t)^3 := by
    have hA := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).le
    have hq0 := (hpos t ht).1.le
    positivity
  have hinner (s : ℝ) (hs : a ≤ s) :
      IntegrableOn (fun t => 2*airyAiReal t*(q t)^3) (Ioi s) ∧
      (∫ t in Ioi s, 2*airyAiReal t*(q t)^3) = -W s := by
    have hi := integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hdW t)
      (fun t ht => hp t (hs.trans ht.le)) hw
    have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hdW t)
      (fun t ht => hp t (hs.trans ht.le)) hw
    exact ⟨hi,by simpa only [zero_sub] using he⟩
  have hWneg (t : ℝ) (ht : a ≤ t) : W t ≤ 0 := by
    have hi : 0 ≤ ∫ u in Ioi t, 2*airyAiReal u*(q u)^3 :=
      integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hp u (ht.trans hu.le))
    rw [(hinner t ht).2] at hi
    linarith
  have hdR (t : ℝ) (ht : a ≤ t) : HasDerivAt R (W t/(airyAiReal t)^2) t := by
    have hnA := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).ne'
    convert! ((hq t).hasDerivAt).div (hasDerivAt_airyAiReal' t) hnA using 1 <;>
      dsimp [R,W] <;> ring
  have hRneg (t : ℝ) (ht : a ≤ t) : W t/(airyAiReal t)^2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hWneg t ht) (sq_nonneg _)
  refine ⟨a,ha,fun s hs => ?_⟩
  have hri := integrableOn_Ioi_deriv_of_nonpos' (fun t ht => hdR t (hs.trans ht))
    (fun t ht => hRneg t (hs.trans ht.le)) hn
  have hre := integral_Ioi_of_hasDerivAt_of_nonpos' (fun t ht => hdR t (hs.trans ht))
    (fun t ht => hRneg t (hs.trans ht.le)) hn
  have heq : (fun t => (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) =ᵐ[volume.restrict (Ioi s)]
      (fun t => -(W t/(airyAiReal t)^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [(hinner t (hs.trans ht.le)).2,neg_div]
  refine ⟨(hpos s hs).1,(hpos s hs).2,(hinner s hs).1,(hinner s hs).2,
    hri.neg.congr heq.symm,?_⟩
  rw [integral_congr_ae heq,integral_neg,hre]
  dsimp only [R]
  ring
/-- Every original classical-model binder is jointly instantiated on the actual
nonzero Fredholm solution, including the complete infinite-tail representation. -/
theorem normalized_green_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) ∧
      Tendsto (deriv q) atTop (𝓝 0) ∧
      Tendsto (fun s => airyAiReal s*deriv q s-deriv airyAiReal s*q s) atTop (𝓝 0) ∧
      ∃ a : ℝ, 1 ≤ a ∧ ∀ s ≥ a,
        0 < q s ∧ |q s/airyAiReal s| ≤ 2 ∧
        IntegrableOn (fun u => 2*airyAiReal u*(q u)^3) (Ioi s) ∧
        (∫ u in Ioi s, 2*airyAiReal u*(q u)^3) =
          -(airyAiReal s*deriv q s-deriv airyAiReal s*q s) ∧
        IntegrableOn (fun t => (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) (Ioi s) ∧
        q s/airyAiReal s = 1+
          ∫ t in Ioi s, (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2 := by
  obtain ⟨q,hnq,hq,hode,hasym,_,_⟩ :=
    RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  exact ⟨q,hnq,hq,hode,hasym,normalized_derivative_boundary q hq hode hasym,
    normalized_wronskian_boundary q hq hode hasym,
    normalized_nested_green_representation q hq hode hasym⟩
/-- The full convex-boundary binder lists are jointly realized on the actual
nonzero classical Fredholm solution, rather than an assumed auxiliary boundary law. -/
theorem convex_boundary_canonical_joint_probe :
    ∃ (q : ℝ → ℝ) (a : ℝ), q ≠ 0 ∧ 1 ≤ a ∧
      Differentiable ℝ q ∧ Differentiable ℝ (deriv q) ∧
      (∀ s ≥ a, 0 ≤ deriv (deriv q) s) ∧ ConvexOn ℝ (Ici a) q ∧
      Tendsto q atTop (𝓝 0) ∧
      (∀ s ≥ a, deriv q s ≤ 0) ∧ Tendsto (deriv q) atTop (𝓝 0) := by
  obtain ⟨q,hnq,hq,hqq,hn,_,_⟩ := RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  obtain ⟨a,ha,hpos⟩ := normalized_positive_tail q hn
  have hdf : Differentiable ℝ (deriv q) := fun s => (hqq s).differentiableAt
  have hdd : ∀ s ≥ a, 0 ≤ deriv (deriv q) s := by
    intro s hs
    rw [(hqq s).deriv]
    have hs0 : 0 ≤ s := by linarith
    have hq0 := (hpos s hs).1.le
    positivity
  have hc : ConvexOn ℝ (Ici a) q := convexOn_of_deriv2_nonneg' (convex_Ici a)
    hq.differentiableOn hdf.differentiableOn (fun s hs => hdd s hs)
  have hl := normalized_atTop_zero q hn
  have hb := nonnegative_second_derivative_boundary q a 0 hq hdf hdd hl
  exact ⟨q,a,hnq,ha,hq,hdf,hdd,hc,hl,hb⟩
end RMTFoundations.TracyWidom.HMGreenRepresentation
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.convex_derivative_nonpos
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.convex_derivative_atTop_zero
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.nonnegative_second_derivative_boundary
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_positive_tail
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_atTop_zero
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_derivative_boundary
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_wronskian_boundary
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_nested_green_representation
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_green_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HMGreenRepresentation.convex_boundary_canonical_joint_probe
