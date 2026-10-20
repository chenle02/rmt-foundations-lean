import RMTFoundations.TracyWidom.HMNontrivialJets
import RMTFoundations.TracyWidom.TWLocalSignUpgrade
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPhysicalLocalSign
open Filter Set
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.HMNontrivialJets RMTFoundations.TracyWidom.TWLocalSignUpgrade
/-- The actual normalized Fredholm coordinate has no stationary zero. -/
theorem physical_no_double_zero
    (s : ℝ /- [definition] -/)
    : resolventQ s ≠ 0 ∨ deriv resolventQ s ≠ 0 := by
  apply normalized_no_double_zero resolventQ s
  · intro t
    exact (RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_resolventQ t).differentiableAt
  · exact RMTFoundations.TracyWidom.PhysicalPainleveII.hasDerivAt_deriv_resolventQ
  · exact RMTFoundations.TracyWidom.HMNormalization.resolventQ_relative_Airy_atTop
/-- A local nonnegative neighborhood suffices for strict physical positivity
at its center. The neighborhood is a visible premise, not a global sign claim. -/
theorem physical_positive_of_local_nonnegative
    (s : ℝ /- [definition] -/)
    (hn : ∀ᶠ t in 𝓝 s, 0 ≤ resolventQ t /- [standing] -/)
    : 0 < resolventQ s :=
  positive_of_local_nonnegative resolventQ s hn (physical_no_double_zero s)
/-- Every normalized classical candidate accepts the same literal local sign
bridge. No candidate's global nonnegativity is assumed or concluded. -/
theorem normalized_positive_of_local_nonnegative
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t /- [standing] -/)
    (ha : Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 1) /- [standing] -/)
    (hn : ∀ᶠ t in 𝓝 s, 0 ≤ q t /- [standing] -/)
    : 0 < q s :=
  positive_of_local_nonnegative q s hn (normalized_no_double_zero q s hq hqq ha)
/-- A genuine physical positive-tail point supplies every local-sign,
normalization and global classical binder by terms on the SAME nonzero model. -/
theorem physical_local_sign_all_binder_joint_probe :
    ∃ (q : ℝ → ℝ) (a s : ℝ),
      q=resolventQ ∧ q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t) ∧
      Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 1) ∧
      1 ≤ a ∧ s=a+1 ∧
      (∀ t ≥ a, 0 < q t) ∧ (∀ᶠ t in 𝓝 s, 0 ≤ q t) ∧
      (∀ t, q t ≠ 0 ∨ deriv q t ≠ 0) ∧ 0 < q s ∧ 0 < resolventQ s := by
  obtain ⟨q,hne,hq,hqq,ha,_,_⟩ :=
    RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  have he := RMTFoundations.TracyWidom.HMUniqueness.normalized_classical_eq_fredholm q hq hqq ha
  obtain ⟨a,ha1,hpos⟩ := RMTFoundations.TracyWidom.HMGreenRepresentation.normalized_positive_tail q ha
  have hn : ∀ᶠ t in 𝓝 (a+1), 0 ≤ q t := by
    filter_upwards [Ioi_mem_nhds (show a<a+1 by linarith)] with t ht
    exact (hpos t (le_of_lt ht)).1.le
  have hs := normalized_positive_of_local_nonnegative q (a+1) hq hqq ha hn
  have hphys : 0 < resolventQ (a+1) := by
    apply physical_positive_of_local_nonnegative (a+1)
    simpa only [he] using hn
  exact ⟨q,a,a+1,he,hne,hq,hqq,ha,ha1,rfl,(fun t ht => (hpos t ht).1),hn,
    fun t => normalized_no_double_zero q t hq hqq ha,hs,hphys⟩
end RMTFoundations.TracyWidom.HMPhysicalLocalSign
#print axioms RMTFoundations.TracyWidom.HMPhysicalLocalSign.physical_no_double_zero
#print axioms RMTFoundations.TracyWidom.HMPhysicalLocalSign.physical_positive_of_local_nonnegative
#print axioms RMTFoundations.TracyWidom.HMPhysicalLocalSign.normalized_positive_of_local_nonnegative
#print axioms RMTFoundations.TracyWidom.HMPhysicalLocalSign.physical_local_sign_all_binder_joint_probe
