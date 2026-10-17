import RMTFoundations.TracyWidom.HMGreenRepresentation
import RMTFoundations.TracyWidom.HMAiryKernel
import RMTFoundations.TracyWidom.HMGreenFubini
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMVolterraRepresentation
open Set Filter MeasureTheory
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMGreenRepresentation RMTFoundations.TracyWidom.HMAiryKernel
/-- The Airy Green kernel written by reduction of order on the positive tail. -/
noncomputable def airyGreen (s u : ℝ /- [definition] -/)
    : ℝ := airyAiReal s*airyAiReal u*(∫ t in s..u,1/(airyAiReal t)^2)
/-- The arbitrary classical normalized candidate has the literal one-integral
Airy Green representation, with absolute integrability derived in the proof. -/
theorem normalized_single_green_representation
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hn : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : ∃ a : ℝ, 1 ≤ a ∧ ∀ s ≥ a,
      0 < q s ∧ |q s/airyAiReal s| ≤ 2 ∧
      IntegrableOn (fun u => airyGreen s u*(2*(q u)^3)) (Ioi s) ∧
      q s=airyAiReal s+∫ u in Ioi s,airyGreen s u*(2*(q u)^3) := by
  obtain ⟨a,ha,hQ⟩ := normalized_nested_green_representation q hq hqq hn
  let f : ℝ → ℝ := fun t => tailReciprocal t/2
  let g : ℝ → ℝ := fun t => 2*airyAiReal t*(q t)^3
  have hf : Continuous f := tailReciprocal_continuous.div_const 2
  have hg : Continuous g := (continuous_const.mul continuous_airyAiReal).mul (hq.continuous.pow 3)
  have hfEq (t : ℝ) (ht : a ≤ t) : f t=1/(airyAiReal t)^2 := by
    dsimp [f,tailReciprocal]
    rw [max_eq_right (ha.trans ht)]
    ring
  refine ⟨a,ha,fun s hs => ?_⟩
  have hgi : ∀ t ≥ s, IntegrableOn g (Ioi t) :=
    fun t ht => (hQ t (hs.trans ht)).2.2.1
  have hgp : ∀ t ≥ s, 0 ≤ g t := by
    intro t ht
    have hq0 := (hQ t (hs.trans ht)).1.le
    have hA0 := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).le
    dsimp [g]
    positivity
  have hfp : ∀ t ≥ s, 0 ≤ f t := by intro t ht;dsimp [f,tailReciprocal];positivity
  have houtereq : (fun t => f t*(∫ u in Ioi t,g u)) =ᵐ[volume.restrict (Ioi s)]
      (fun t => (∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hfEq t (hs.trans ht.le)]
    dsimp only [g]
    ring
  have hoi : IntegrableOn (fun t => f t*(∫ u in Ioi t,g u)) (Ioi s) :=
    (hQ s hs).2.2.2.2.1.congr houtereq.symm
  have hF := RMTFoundations.TracyWidom.HMGreenFubini.nested_tail_fubini f g s hf hg hfp hgp hgi hoi
  have hnorm : q s/airyAiReal s=1+∫ u in Ioi s,g u*(∫ t in s..u,f t) := by
    rw [← hF.2,integral_congr_ae houtereq]
    exact (hQ s hs).2.2.2.2.2
  have hphys : (fun u => airyAiReal s*(g u*(∫ t in s..u,f t))) =ᵐ[volume.restrict (Ioi s)]
      (fun u => airyGreen s u*(2*(q u)^3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hj : (∫ t in s..u,f t)=(∫ t in s..u,1/(airyAiReal t)^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu.le] at ht
      exact hfEq t (hs.trans ht.1)
    rw [hj]
    dsimp only [airyGreen,g]
    ring
  have hi := (hF.1.const_mul (airyAiReal s)).congr hphys
  refine ⟨(hQ s hs).1,(hQ s hs).2.1,hi,?_⟩
  have hA := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ s)).ne'
  have he := congrArg (fun x => airyAiReal s*x) hnorm
  rw [mul_div_cancel₀ _ hA,mul_add,mul_one,← integral_const_mul,
    integral_congr_ae hphys] at he
  exact he
/-- The actual nonzero Fredholm model supplies every original binder and the
literal infinite-tail Green representation together. -/
theorem single_green_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) ∧
      ∃ a : ℝ, 1 ≤ a ∧ ∀ s ≥ a,
        0 < q s ∧ |q s/airyAiReal s| ≤ 2 ∧
        IntegrableOn (fun u => airyGreen s u*(2*(q u)^3)) (Ioi s) ∧
        q s=airyAiReal s+∫ u in Ioi s,airyGreen s u*(2*(q u)^3) := by
  obtain ⟨q,hnq,hq,hqq,hn,_,_⟩ := RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  exact ⟨q,hnq,hq,hqq,hn,normalized_single_green_representation q hq hqq hn⟩
end RMTFoundations.TracyWidom.HMVolterraRepresentation
#print axioms RMTFoundations.TracyWidom.HMVolterraRepresentation.airyGreen
#print axioms RMTFoundations.TracyWidom.HMVolterraRepresentation.normalized_single_green_representation
#print axioms RMTFoundations.TracyWidom.HMVolterraRepresentation.single_green_all_binder_joint_probe
