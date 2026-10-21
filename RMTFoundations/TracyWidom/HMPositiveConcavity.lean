import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPositiveConcavity
open Set
/-- A differentiable positive function concave on an infinite right ray
has a nonnegative derivative there. -/
theorem positive_concave_deriv_nonnegative
    (f : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hp : ∀ t ≥ a, 0 < f t /- [standing] -/)
    (hc : ConcaveOn ℝ (Ici a) f /- [standing] -/)
    (hx : a ≤ x /- [standing] -/)
    : 0 ≤ deriv f x := by
  by_contra hn
  have hd : deriv f x < 0 := lt_of_not_ge hn
  let d := (f x+1)/(-deriv f x)
  have hdp : 0 < d := div_pos (by linarith [hp x hx]) (neg_pos.mpr hd)
  have hxy : x < x+d := by linarith
  have hy : a ≤ x+d := by linarith
  have hs := hc.slope_le_deriv hx hy hxy (hf x)
  rw [slope_def_field] at hs
  have hm := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
  have he : deriv f x*d = -(f x+1) := by
    dsimp [d]
    field_simp [ne_of_lt hd]
  have hypos := hp (x+d) hy
  nlinarith
/-- A positive twice differentiable function on a right ray cannot have its
second derivative bounded above by a fixed negative multiple of itself forever.
This is a generic calculus conclusion; no physical PII sign is a hidden premise. -/
theorem positive_relative_curvature_hit
    (f : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (k : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hff : Differentiable ℝ (deriv f) /- [standing] -/)
    (hp : ∀ t ≥ a, 0 < f t /- [standing] -/)
    (hk : 0 < k /- [standing] -/)
    : ∃ t ≥ a, -k*f t < deriv (deriv f) t := by
  by_contra hn
  push_neg at hn
  have hc : ConcaveOn ℝ (Ici a) f := by
    apply concaveOn_of_deriv2_nonpos' (convex_Ici a) hf.differentiableOn
      hff.differentiableOn
    intro t ht
    change deriv (deriv f) t ≤ 0
    have hh := hn t ht
    nlinarith [hp t ht]
  have hg : ∀ t ≥ a, 0 ≤ deriv f t :=
    fun t ht => positive_concave_deriv_nonnegative f a t hf hp hc ht
  have hm : MonotoneOn f (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a) hf.continuous.continuousOn
      hf.differentiableOn
    intro t ht
    exact hg t (interior_subset ht)
  let b := a + (deriv f a+1)/(k*f a)
  have hab : a < b := by
    dsimp [b]
    have hh : 0 < (deriv f a+1)/(k*f a) :=
      div_pos (by linarith [hg a le_rfl]) (mul_pos hk (hp a le_rfl))
    linarith
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope (deriv f) hab
    hff.continuous.continuousOn hff.differentiableOn
  have hca : a ≤ c := hc.1.le
  have hcb : c ≤ b := hc.2.le
  have hbound : deriv (deriv f) c ≤ -k*f a := by
    have hfca := hm (show a ∈ Ici a from le_refl a) (show c ∈ Ici a from hca) hca
    have hh := hn c hca
    nlinarith
  rw [he] at hbound
  have hmul := (div_le_iff₀ (sub_pos.mpr hab)).mp hbound
  have hid : k*f a*(b-a) = deriv f a+1 := by
    dsimp [b]
    field_simp [(hp a le_rfl).ne', hk.ne']
    ring
  have hgb := hg b hab.le
  nlinarith
/-- The affine function t+2 supplies every positive-concavity binder jointly,
and both its value and derivative at the chosen point are nonzero. -/
theorem positive_concavity_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a x : ℝ), Differentiable ℝ f ∧
      (∀ t ≥ a, 0 < f t) ∧ ConcaveOn ℝ (Ici a) f ∧ a ≤ x ∧
      f x=3 ∧ deriv f x=1 ∧ 0 ≤ deriv f x := by
  let f : ℝ → ℝ := fun t => t+2
  have hf : Differentiable ℝ f := by dsimp [f]; fun_prop
  have hp : ∀ t ≥ (0:ℝ), 0 < f t := by intro t ht; dsimp [f]; linarith
  have hc : ConcaveOn ℝ (Ici (0:ℝ)) f := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy r s hr hs hrs
    change r*(x+2)+s*(y+2) ≤ (r*x+s*y)+2
    nlinarith
  have hd : deriv f 1=1 := by simpa [f] using ((hasDerivAt_id (1:ℝ)).add_const 2).deriv
  exact ⟨f,0,1,hf,hp,hc,by norm_num,by norm_num [f],hd,
    positive_concave_deriv_nonnegative f 0 1 hf hp hc (by norm_num)⟩
/-- exp supplies every relative-curvature binder jointly with nonzero value,
slope and curvature. -/
theorem positive_curvature_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a k t : ℝ), Differentiable ℝ f ∧
      Differentiable ℝ (deriv f) ∧ (∀ z ≥ a, 0 < f z) ∧ 0 < k ∧
      a ≤ t ∧ -k*f t < deriv (deriv f) t ∧
      (∃ z ≥ a, -k*f z < deriv (deriv f) z) := by
  have hf : Differentiable ℝ Real.exp := Real.differentiable_exp
  have hff : Differentiable ℝ (deriv Real.exp) := by simpa using hf
  have hp : ∀ z ≥ (0:ℝ), 0 < Real.exp z := fun z _ => Real.exp_pos z
  have hh : -(1:ℝ)*Real.exp 1 < deriv (deriv Real.exp) 1 := by
    simp only [Real.deriv_exp]
    nlinarith [Real.exp_pos (1:ℝ)]
  exact ⟨Real.exp,0,1,1,hf,hff,hp,by norm_num,by norm_num,hh,
    positive_relative_curvature_hit Real.exp 0 1 hf hff hp (by norm_num)⟩
end RMTFoundations.TracyWidom.HMPositiveConcavity
#print axioms RMTFoundations.TracyWidom.HMPositiveConcavity.positive_concave_deriv_nonnegative
#print axioms RMTFoundations.TracyWidom.HMPositiveConcavity.positive_relative_curvature_hit
#print axioms RMTFoundations.TracyWidom.HMPositiveConcavity.positive_concavity_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HMPositiveConcavity.positive_curvature_all_binder_joint_probe
