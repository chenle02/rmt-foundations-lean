import RMTFoundations.TracyWidom.OrderFourFredholm
import RMTFoundations.TracyWidom.PlusLeftTail


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.AiryKernel RMTFoundations.TWLeftTail

theorem tendsto_TW4AiryR_atBot : Tendsto TW4AiryR atBot (𝓝 0) := by
  change Tendsto (fun s => (TW1R s+hankelDetPlus s)/2) atBot (𝓝 0)
  convert (TW1R_tendsto_atBot_zero_unconditional.add tendsto_hankelDetPlus_atBot).div_const 2 using 1 <;>
    first | rfl | norm_num | (funext s; rfl)

theorem tendsto_TW4R_atTop : Tendsto TW4R atTop (𝓝 1) := by
  apply tendsto_TW4AiryR_atTop.comp
  exact tendsto_id.const_mul_atTop (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))

theorem tendsto_TW4R_atBot : Tendsto TW4R atBot (𝓝 0) := by
  apply tendsto_TW4AiryR_atBot.comp
  exact tendsto_id.const_mul_atBot (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))

/-- Continuity and opposite endpoint limits give every interior level, without
requiring a monotonicity hypothesis. This does not construct a probability law. -/
theorem continuous_endpoints_level_exists
    (F : ℝ → ℝ /- [definition] -/)
    (hc : Continuous F /- [standing] -/)
    (h0 : Tendsto F atBot (𝓝 0) /- [standing] -/)
    (h1 : Tendsto F atTop (𝓝 1) /- [standing] -/)
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃ s : ℝ, F s = q := by
  have hleft : ∀ᶠ s : ℝ in atBot, F s < q ∧ s ≤ 0 :=
    (h0.eventually (gt_mem_nhds hq0)).and (eventually_le_atBot 0)
  have hright : ∀ᶠ s : ℝ in atTop, q < F s ∧ 0 ≤ s :=
    (h1.eventually (lt_mem_nhds hq1)).and (eventually_ge_atTop 0)
  obtain ⟨a,ha,haz⟩ := hleft.exists
  obtain ⟨b,hb,hbz⟩ := hright.exists
  obtain ⟨s,_,hs⟩ := intermediate_value_Icc (haz.trans hbz) hc.continuousOn ⟨ha.le,hb.le⟩
  exact ⟨s,hs⟩

theorem TW4R_level_exists
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃ s : ℝ, TW4R s = q :=
  continuous_endpoints_level_exists TW4R continuous_TW4R tendsto_TW4R_atBot
    tendsto_TW4R_atTop q hq0 hq1

theorem TW4R_half_level_exists : ∃ s : ℝ, TW4R s = 1/2 :=
  TW4R_level_exists (1/2) (by norm_num) (by norm_num)

/-- All endpoint and interior-level hypotheses hold jointly for the actual GSE
formula, including a nonzero Fredholm value. No monotonicity is assumed. -/
theorem TW4_endpoints_all_binder_joint_probe :
    Continuous TW4R ∧ Tendsto TW4R atBot (𝓝 0) ∧ Tendsto TW4R atTop (𝓝 1) ∧
      0 < TW4R 0 ∧ (0:ℝ)<1/2 ∧ (1/2:ℝ)<1 ∧
      (∃ s : ℝ, TW4R s = 1/2) :=
  ⟨continuous_TW4R,tendsto_TW4R_atBot,tendsto_TW4R_atTop,
    TW4R_positive 0,by norm_num,by norm_num,TW4R_half_level_exists⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.tendsto_TW4AiryR_atBot
#print axioms RMTFoundations.TracyWidom.tendsto_TW4R_atTop
#print axioms RMTFoundations.TracyWidom.tendsto_TW4R_atBot
#print axioms RMTFoundations.TracyWidom.continuous_endpoints_level_exists
#print axioms RMTFoundations.TracyWidom.TW4R_level_exists
#print axioms RMTFoundations.TracyWidom.TW4R_half_level_exists
#print axioms RMTFoundations.TracyWidom.TW4_endpoints_all_binder_joint_probe
