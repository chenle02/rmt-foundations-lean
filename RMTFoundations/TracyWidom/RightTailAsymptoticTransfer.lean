import RMTFoundations.Airy.Damping
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Filter Asymptotics
open scoped Topology Asymptotics

/-- A vanishing trace with quadratic tail error determines the leading tail asymptotic. -/
theorem rightTail_asymptotic_of_quadratic_error
    (f t g : ℝ → ℝ /- [definition] -/)
    (ht : Tendsto t atTop (𝓝 0) /- [standing] -/)
    (hg : t ~[atTop] g /- [standing] -/)
    (herr : ∀ᶠ s in atTop, |f s - t s| ≤ (t s)^2 / 2 /- [standing] -/) :
    f ~[atTop] g := by
  apply IsEquivalent.trans (v := t) _ hg
  change (fun s => f s - t s) =o[atTop] t
  apply IsLittleO.of_bound
  intro c hc
  have hsmall := ht.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < 2*c by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hc))
  filter_upwards [herr, hsmall] with s hs hsm
  simp only [Real.norm_eq_abs]
  calc
    |f s - t s| ≤ (t s)^2/2 := hs
    _ ≤ c * |t s| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (t s)]

/-- All premises hold jointly for a positive exponential trace and nonzero tail. -/
theorem rightTail_asymptotic_quadratic_joint_probe :
    ∃ f t g : ℝ → ℝ,
      (∀ s, 0 < t s) ∧ Tendsto t atTop (𝓝 0) ∧ t ~[atTop] g ∧
      (∀ᶠ s in atTop, |f s-t s| ≤ (t s)^2/2) ∧ 0 < f 0 ∧ f ~[atTop] g := by
  let t : ℝ → ℝ := fun s => Real.exp (-s)
  let f : ℝ → ℝ := fun s => t s - (t s)^2/2
  have ht : Tendsto t atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have he : t ~[atTop] t := IsEquivalent.refl
  have herr : ∀ᶠ s in atTop, |f s-t s| ≤ (t s)^2/2 := by
    apply Eventually.of_forall
    intro s
    dsimp [f]
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  refine ⟨f,t,t,fun s => Real.exp_pos _,ht,he,herr,?_,
    rightTail_asymptotic_of_quadratic_error f t t ht he herr⟩
  norm_num [f,t]

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.rightTail_asymptotic_of_quadratic_error
#print axioms RMTFoundations.TracyWidom.rightTail_asymptotic_quadratic_joint_probe
