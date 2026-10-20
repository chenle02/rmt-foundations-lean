import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.TWLocalSignUpgrade
open Filter Set
open scoped Topology
/-- Local nonnegativity plus a nonzero value/slope jet excludes touching zero. -/
theorem positive_of_local_nonnegative
    (f : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hn : ∀ᶠ t in 𝓝 s, 0 ≤ f t /- [standing] -/)
    (hj : f s ≠ 0 ∨ deriv f s ≠ 0 /- [standing] -/)
    : 0 < f s := by
  have hnonneg : 0 ≤ f s := hn.self_of_nhds
  by_contra h
  have hz : f s = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hm : IsLocalMin f s := by
    filter_upwards [hn] with t ht
    simpa only [hz] using ht
  have hd : deriv f s = 0 := hm.deriv_eq_zero
  rcases hj with hv | hv
  · exact hv hz
  · exact hv hd
/-- Global nonnegativity upgrades by the same local argument. The hypothesis
is explicit and is never asserted for the physical PII coordinate here. -/
theorem positive_of_nonnegative
    (f : ℝ → ℝ /- [definition] -/)
    (hn : ∀ t, 0 ≤ f t /- [standing] -/)
    (hj : ∀ t, f t ≠ 0 ∨ deriv f t ≠ 0 /- [standing] -/)
    : ∀ t, 0 < f t := by
  intro t
  exact positive_of_local_nonnegative f t (Eventually.of_forall hn) (hj t)
/-- Nonconstant exponential values and nonzero slopes realize all local and
global sign-upgrade binders simultaneously. -/
theorem sign_upgrade_all_binder_joint_probe :
    ∃ f : ℝ → ℝ, f 0=1 ∧ deriv f 0=1 ∧
      (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≠ 0 ∨ deriv f t ≠ 0) ∧
      (∀ s, ∀ᶠ t in 𝓝 s, 0 ≤ f t) ∧ (∀ s, 0 < f s) := by
  have hn : ∀ t : ℝ, 0 ≤ Real.exp t := fun t => (Real.exp_pos t).le
  have hj : ∀ t : ℝ, Real.exp t ≠ 0 ∨ deriv Real.exp t ≠ 0 :=
    fun t => Or.inl (Real.exp_ne_zero t)
  refine ⟨Real.exp,by norm_num,?_,hn,hj,
    fun _ => Eventually.of_forall hn,positive_of_nonnegative Real.exp hn hj⟩
  rw [(Real.hasDerivAt_exp 0).deriv]
  norm_num
end RMTFoundations.TracyWidom.TWLocalSignUpgrade
#print axioms RMTFoundations.TracyWidom.TWLocalSignUpgrade.positive_of_local_nonnegative
#print axioms RMTFoundations.TracyWidom.TWLocalSignUpgrade.positive_of_nonnegative
#print axioms RMTFoundations.TracyWidom.TWLocalSignUpgrade.sign_upgrade_all_binder_joint_probe
