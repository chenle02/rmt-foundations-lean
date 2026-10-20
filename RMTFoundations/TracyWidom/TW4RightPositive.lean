import RMTFoundations.TracyWidom.TW4RightLogConcavity
import RMTFoundations.TracyWidom.TW4CoshDerivative
import RMTFoundations.TracyWidom.TWMidpointTail
import RMTFoundations.TracyWidom.TWCoshSign
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.IntegralRepresentations

/-- Physical midpoint comparison implies a strict GSE density sign at its original
shift. The genuine square-tail integrability is called inside the proof. -/
theorem TW4AirySlope_positive_of_physical_midpoint
    (s : ℝ) -- [definition]
    (hq : ∀ t, s ≤ t → 0 < resolventQ t) -- [standing]
    (hm : ∀ x, 0 ≤ x → resolventQ s*resolventQ (x+x+s) ≤
      (resolventQ (x+s))^2) -- [standing]
    : 0 < TW4AirySlope s := by
  have hi : IntegrableOn (fun x => (resolventQ (x+s))^2) (Ioi 0) := by
    have hbase := (integrable_indicator_iff measurableSet_Ioi).mpr
      (resolventQ_square_tail_integrals s).1
    have ht := hbase.comp_add_right s
    have he : (fun x => ((Ioi s).indicator (fun t => (resolventQ t)^2)) (x+s)) =
        (Ioi (0:ℝ)).indicator (fun x => (resolventQ (x+s))^2) := by
      funext x
      have hx : x+s ∈ Ioi s ↔ x ∈ Ioi (0:ℝ) := by
        simp only [mem_Ioi]
        constructor <;> intro h <;> linarith
      simp only [indicator_apply,hx]
    rw [he] at ht
    exact (integrable_indicator_iff measurableSet_Ioi).mp ht
  have hu := midpoint_square_tail_comparison_unshifted resolventQ s
    (fun t ht => (hq t ht).le) hi hm
  rw [(resolventQ_square_tail_integrals s).2.1] at hu
  have hQ : 0 < TWEndpointTail s := by
    have hn : 0 ≤ᵐ[volume.restrict (Ioi s)] resolventQ := by
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      exact fun t ht => (hq t ht.le).le
    apply (setIntegral_pos_iff_support_of_nonneg_ae hn (integrableOn_resolventQ s)).mpr
    have he : Function.support resolventQ ∩ Ioi s = Ioi s := by
      ext t
      simp only [mem_inter_iff,mem_Ioi,Function.mem_support]
      exact ⟨fun h => h.2,fun ht => ⟨(hq t ht.le).ne',ht⟩⟩
    rw [he]
    simp
  have hc := cosh_response_pos_of_half_tail_bound (resolventQ s) (resolventU s)
    (TWEndpointTail s) (hq s le_rfl) hQ hu
  rw [TW4AirySlope_eq_cosh_response]
  exact mul_pos (div_pos (Real.sqrt_pos.mpr (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s))
    (by norm_num)) hc

/-- A complete genuine right ray has positive raw GSE density, without a sign premise. -/
theorem eventually_TW4AirySlope_positive :
    ∀ᶠ s : ℝ in atTop, 0 < TW4AirySlope s := by
  obtain ⟨a,ha,hq,hm⟩ := exists_physical_endpoint_midpoint_tail
  filter_upwards [eventually_ge_atTop a] with s hs
  exact TW4AirySlope_positive_of_physical_midpoint s
    (fun t ht => hq t (hs.trans ht)) (hm s hs)

/-- The actual GSE Fredholm average is strictly increasing on some right ray. -/
theorem exists_TW4AiryR_strictMono_right_tail :
    ∃ a : ℝ, 0 ≤ a ∧ StrictMonoOn TW4AiryR (Ici a) ∧
      (∀ s, a ≤ s → 0 < TW4AirySlope s) ∧
      (∀ s, a ≤ s → TW4AiryR s < 1) := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 eventually_TW4AirySlope_positive
  let a := max 0 b
  have hpos (s : ℝ) (hs : a ≤ s) : 0 < TW4AirySlope s :=
    hb s ((le_max_right 0 b).trans hs)
  have hmono : StrictMonoOn TW4AiryR (Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici a) continuous_TW4AiryR.continuousOn
    intro s hs
    rw [(TW4AiryR_hasDerivAt s).deriv]
    exact hpos s (interior_subset hs)
  refine ⟨a,le_max_left _ _,hmono,hpos,?_⟩
  intro s hs
  have hlt : TW4AiryR s < TW4AiryR (s+1) := hmono hs (show a ≤ s+1 by linarith) (by linarith)
  have hupper : TW4AiryR (s+1) ≤ 1 := by
    apply ge_of_tendsto tendsto_TW4AiryR_atTop
    filter_upwards [eventually_ge_atTop (s+1)] with t ht
    exact hmono.monotoneOn (show a ≤ s+1 by linarith) (show a ≤ t by linarith) ht
  exact hlt.trans_le hupper

/-- All comparison, integrability, derivative and strict-monotonicity inputs are
jointly realized on actual nonzero Airy rows of the same certified right tail. -/
theorem right_GSE_density_all_binder_joint_probe :
    (∃ a s : ℝ, 0 ≤ a ∧ a ≤ s ∧ airyBoundaryVector s ≠ 0 ∧
      (∀ t, s ≤ t → 0 < resolventQ t) ∧
      (∀ x, 0 ≤ x → resolventQ s*resolventQ (x+x+s) ≤ (resolventQ (x+s))^2) ∧
      IntegrableOn resolventQ (Ioi s) ∧
      IntegrableOn (fun t => (resolventQ t)^2) (Ioi s) ∧
      0 < TW4AirySlope s) ∧
      (∃ a : ℝ, 0 ≤ a ∧ StrictMonoOn TW4AiryR (Ici a) ∧
        (∀ s, a ≤ s → 0 < TW4AirySlope s) ∧ (∀ s, a ≤ s → TW4AiryR s < 1)) := by
  obtain ⟨a,ha,hq,hm⟩ := exists_physical_endpoint_midpoint_tail
  exact ⟨⟨a,a,ha,le_rfl,airyBoundaryVector_ne_zero a,hq,hm a le_rfl,
    integrableOn_resolventQ a,(resolventQ_square_tail_integrals a).1,
    TW4AirySlope_positive_of_physical_midpoint a hq (hm a le_rfl)⟩,
    exists_TW4AiryR_strictMono_right_tail⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4AirySlope_positive_of_physical_midpoint
#print axioms RMTFoundations.TracyWidom.eventually_TW4AirySlope_positive
#print axioms RMTFoundations.TracyWidom.exists_TW4AiryR_strictMono_right_tail
#print axioms RMTFoundations.TracyWidom.right_GSE_density_all_binder_joint_probe
