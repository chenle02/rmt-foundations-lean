import RMTFoundations.TracyWidom.HMUniqueness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMNontrivialJets
open Filter Set
open scoped Topology
open RMTFoundations.TracyWidom.HMLinearODE RMTFoundations.Airy
/-- A nontrivial global classical PII solution cannot have a double zero.
This makes no global sign assertion. -/
theorem no_double_zero
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t /- [standing] -/)
    (hn : q ≠ 0 /- [standing] -/)
    : q s ≠ 0 ∨ deriv q s ≠ 0 := by
  by_contra h
  push_neg at h
  apply hn
  have hz : ∀ t : ℝ, HasDerivAt (deriv (fun _ : ℝ => (0:ℝ)))
      (t*0+2*0^3) t := by
    intro t
    simpa only [deriv_const', mul_zero, zero_pow (by norm_num : (3:ℕ)≠0), add_zero]
      using hasDerivAt_const t (0:ℝ)
  exact pii_initial_value_unique q (fun _ => 0) s hq (differentiable_const (0:ℝ)) hqq hz
    h.1 (by simpa using h.2)
/-- Airy normalization supplies nontriviality; it does not supply global sign. -/
theorem normalized_no_double_zero
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t /- [standing] -/)
    (hn : Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 1) /- [standing] -/)
    : q s ≠ 0 ∨ deriv q s ≠ 0 := by
  apply no_double_zero q s hq hqq
  intro he
  have hz : Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 0) := by
    simp only [he, Pi.zero_apply, zero_div]
    exact tendsto_const_nhds
  have hbad := tendsto_nhds_unique hz hn
  norm_num at hbad
/-- Every jet binder is realized jointly by the actual normalized nonzero
Fredholm solution; the same model supplies the entire real-line conclusion. -/
theorem canonical_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t) ∧
      Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 1) ∧
      (∀ s, q s ≠ 0 ∨ deriv q s ≠ 0) := by
  obtain ⟨q,hn,hq,hqq,ha,_,_⟩ := pii_global_all_binder_joint_probe
  exact ⟨q,hn,hq,hqq,ha,fun s => normalized_no_double_zero q s hq hqq ha⟩
end RMTFoundations.TracyWidom.HMNontrivialJets
#print axioms RMTFoundations.TracyWidom.HMNontrivialJets.no_double_zero
#print axioms RMTFoundations.TracyWidom.HMNontrivialJets.normalized_no_double_zero
#print axioms RMTFoundations.TracyWidom.HMNontrivialJets.canonical_all_binder_joint_probe
