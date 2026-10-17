import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HMAsymptotic
open Filter Set
open scoped Topology
/-- Relative normalization gives a nonvanishing denominator and a genuine
pointwise envelope eventually, without a prescribed tail floor. -/
theorem relative_normalization_envelope
    (q A : ℝ → ℝ /- [definition] -/)
    (hq : Tendsto (fun s => q s/A s) atTop (𝓝 1) /- [standing] -/)
    : ∃ a : ℝ, ∀ s ≥ a, A s ≠ 0 ∧ |q s| ≤ 2*|A s| := by
  have hp : ∀ᶠ s in atTop, (1/2:ℝ)<q s/A s := hq.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  have hb : ∀ᶠ s in atTop, |q s/A s|<2 :=
    (continuous_abs.tendsto 1 |>.comp hq).eventually_lt_const (by norm_num : |(1:ℝ)|<2)
  obtain ⟨a,ha⟩ := (hp.and hb).exists_forall_of_atTop
  refine ⟨a,fun s hs => ?_⟩
  have hA : A s ≠ 0 := by
    intro he
    have := (ha s hs).1
    simp [he] at this
    linarith
  refine ⟨hA,?_⟩
  calc
    |q s| = |q s/A s| *|A s| := by rw [← abs_mul,div_mul_cancel₀ _ hA]
    _ ≤ 2*|A s| := mul_le_mul_of_nonneg_right (ha s hs).2.le (abs_nonneg _)
/-- Two identically normalized candidates have relative difference tending to zero. -/
theorem relative_difference_atTop
    (q r A : ℝ → ℝ /- [definition] -/)
    (hq : Tendsto (fun s => q s/A s) atTop (𝓝 1) /- [standing] -/)
    (hr : Tendsto (fun s => r s/A s) atTop (𝓝 1) /- [standing] -/)
    : Tendsto (fun s => (q s-r s)/A s) atTop (𝓝 0) := by
  simpa only [← sub_div,sub_self] using hq.sub hr
/-- A nonzero exponentially decaying model realizes every envelope binder. -/
theorem envelope_joint_probe :
    (fun s : ℝ => Real.exp (-s)) 0 ≠ 0 ∧
    Tendsto (fun s : ℝ => Real.exp (-s)/Real.exp (-s)) atTop (𝓝 1) ∧
    ∃ a : ℝ, ∀ s ≥ a, Real.exp (-s) ≠ 0 ∧ |Real.exp (-s)| ≤ 2*|Real.exp (-s)| := by
  have hn : Tendsto (fun s : ℝ => Real.exp (-s)/Real.exp (-s)) atTop (𝓝 1) := by
    simpa only [div_self (Real.exp_ne_zero _)] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1))
  exact ⟨by norm_num,hn,relative_normalization_envelope _ _ hn⟩
/-- Joint probe supplies both independently written normalization binders
by terms on a genuine nonzero decaying example. -/
theorem relative_difference_joint_probe :
    Real.exp (0:ℝ) ≠ 0 ∧
    Tendsto (fun s : ℝ => Real.exp (-s)/Real.exp (-s)) atTop (𝓝 1) ∧
    Tendsto (fun s : ℝ => Real.exp (-s)/Real.exp (-s)) atTop (𝓝 1) ∧
    Tendsto (fun s : ℝ => (Real.exp (-s)-Real.exp (-s))/Real.exp (-s)) atTop (𝓝 0) := by
  have hn := envelope_joint_probe.2.1
  exact ⟨Real.exp_ne_zero 0,hn,hn,
    relative_difference_atTop (fun s => Real.exp (-s)) (fun s => Real.exp (-s))
      (fun s => Real.exp (-s)) hn hn⟩
end RMTFoundations.TracyWidom.HMAsymptotic
#print axioms RMTFoundations.TracyWidom.HMAsymptotic.relative_normalization_envelope
#print axioms RMTFoundations.TracyWidom.HMAsymptotic.relative_difference_atTop
#print axioms RMTFoundations.TracyWidom.HMAsymptotic.envelope_joint_probe

#print axioms RMTFoundations.TracyWidom.HMAsymptotic.relative_difference_joint_probe
