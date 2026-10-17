import RMTFoundations.Airy.Damping
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Filter Asymptotics
open scoped Topology Asymptotics

/-- Asymptotic equivalence to a nonnegative model supplies arbitrarily sharp relative bounds. -/
theorem rightTail_relative_bounds_of_isEquivalent
    (f g : ℝ → ℝ /- [definition] -/)
    (hfg : f ~[atTop] g /- [standing] -/)
    (hg : ∀ᶠ s in atTop, 0 ≤ g s /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ s in atTop, (1-ε)*g s ≤ f s ∧ f s ≤ (1+ε)*g s := by
  have hb := hfg.isLittleO.bound hε
  filter_upwards [hb,hg] with s hs hgs
  simp only [Pi.sub_apply,Real.norm_eq_abs,abs_of_nonneg hgs] at hs
  have h := abs_le.mp hs
  constructor <;> nlinarith

/-- Every relative-bound binder has a common positive, nonzero exponential instance. -/
theorem rightTail_relative_bounds_joint_probe :
    ∃ f g : ℝ → ℝ, f ~[atTop] g ∧ (∀ᶠ s in atTop, 0 ≤ g s) ∧
      0 < (1/2 : ℝ) ∧ 0 < g 0 ∧
      (∀ᶠ s in atTop, (1-(1/2 : ℝ))*g s ≤ f s ∧ f s ≤ (1+(1/2 : ℝ))*g s) := by
  let g : ℝ → ℝ := fun s => Real.exp (-s)
  have hp : ∀ᶠ s in atTop, 0 ≤ g s := Eventually.of_forall (fun s => (Real.exp_pos _).le)
  exact ⟨g,g,IsEquivalent.refl,hp,by norm_num,Real.exp_pos _,
    rightTail_relative_bounds_of_isEquivalent g g IsEquivalent.refl hp (1/2) (by norm_num)⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.rightTail_relative_bounds_of_isEquivalent
#print axioms RMTFoundations.TracyWidom.rightTail_relative_bounds_joint_probe
