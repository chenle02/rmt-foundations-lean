import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.PositiveCubicCurvature
open Set Filter
/-- A globally differentiable positive function cannot satisfy a uniform
positive quadratic lower bound for its derivative on an infinite right ray. -/
theorem positive_quadratic_deriv_hit
    (f : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hp : ∀ t ≥ a, 0 < f t /- [standing] -/)
    (hc : 0 < c /- [standing] -/)
    : ∃ t ≥ a, deriv f t < c*(f t)^2 := by
  by_contra hn
  push Not at hn
  let g : ℝ → ℝ := fun t => (f t)⁻¹
  have hg : DifferentiableOn ℝ g (Ici a) := by
    intro t ht
    exact ((hf t).inv (hp t ht).ne').differentiableWithinAt
  have hgd : ∀ t ≥ a, deriv g t ≤ -c := by
    intro t ht
    rw [show deriv g t = -deriv f t/(f t)^2 from
      deriv_fun_inv'' (hf t) (hp t ht).ne']
    apply (div_le_iff₀ (sq_pos_of_pos (hp t ht))).mpr
    nlinarith [hn t ht]
  let b := a+(g a+1)/c
  have hga : 0 < g a := inv_pos.mpr (hp a le_rfl)
  have hab : a < b := by
    dsimp [b]
    linarith [div_pos (show 0 < g a+1 by linarith) hc]
  have hg' : DifferentiableOn ℝ g (Icc a b) := hg.mono Icc_subset_Ici_self
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope g hab
    hg'.continuousOn (hg'.mono Ioo_subset_Icc_self)
  have hbound := hgd t ht.1.le
  rw [he] at hbound
  have hmul := (div_le_iff₀ (sub_pos.mpr hab)).mp hbound
  have hid : c*(b-a)=g a+1 := by
    dsimp [b]
    field_simp [hc.ne'] <;> ring
  have hgb : 0 < g b := inv_pos.mpr (hp b hab.le)
  nlinarith
/-- exp at a=0, c=1 has nonzero value and slope and satisfies all
hypotheses jointly; its derivative is below its square at t=1. -/
theorem quadratic_deriv_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a c t : ℝ), Differentiable ℝ f ∧
      (∀ z ≥ a, 0 < f z) ∧ 0 < c ∧ a ≤ t ∧
      f 0=1 ∧ deriv f 0=1 ∧ deriv f t < c*(f t)^2 ∧
      (∃ z ≥ a, deriv f z < c*(f z)^2) := by
  have hp : ∀ z ≥ (0:ℝ), 0 < Real.exp z := fun z _ => Real.exp_pos z
  have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
  have hb : deriv Real.exp 1 < (1:ℝ)*(Real.exp 1)^2 := by
    simp only [Real.deriv_exp,one_mul]
    nlinarith [Real.exp_pos (1:ℝ)]
  exact ⟨Real.exp,0,1,1,Real.differentiable_exp,hp,by norm_num,by norm_num,
    by simp,by simp,hb,positive_quadratic_deriv_hit Real.exp 0 1
      Real.differentiable_exp hp (by norm_num)⟩
/-- A positive, globally twice differentiable function tending to infinity
cannot have its second derivative bounded below by a positive cubic forever.
The proof uses monotonicity of the elementary energy and the reciprocal obstruction. -/
theorem positive_cubic_curvature_hit
    (f : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (k : ℝ /- [definition] -/)
    (hf : Differentiable ℝ f /- [standing] -/)
    (hff : Differentiable ℝ (deriv f) /- [standing] -/)
    (hp : ∀ t ≥ a, 0 < f t /- [standing] -/)
    (hTop : Tendsto f atTop atTop /- [standing] -/)
    (hk : 0 < k /- [standing] -/)
    : ∃ t ≥ a, deriv (deriv f) t < k*(f t)^3 := by
  by_contra hn
  push Not at hn
  have hdm : MonotoneOn (deriv f) (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a) hff.continuous.continuousOn
      hff.differentiableOn
    intro t ht
    have hta : a ≤ t := interior_subset ht
    exact le_trans (le_of_lt (mul_pos hk (pow_pos (hp t hta) 3))) (hn t hta)
  obtain ⟨b,hba,hfb⟩ := ((eventually_gt_atTop a).and (hTop.eventually_gt_atTop (f a))).exists
  obtain ⟨u,hu,hue⟩ := exists_deriv_eq_slope f hba
    hf.continuous.continuousOn hf.differentiableOn
  have hua : a ≤ u := hu.1.le
  have hdu : 0 < deriv f u := by
    rw [hue]
    exact div_pos (sub_pos.mpr hfb) (sub_pos.mpr hba)
  have hd : ∀ t ≥ u, 0 < deriv f t := by
    intro t ht
    exact lt_of_lt_of_le hdu (hdm hua (le_trans hua ht) ht)
  let E : ℝ → ℝ := fun t => (deriv f t)^2-(k/2)*(f t)^4
  have hEd : ∀ t, HasDerivAt E
      (2*deriv f t*(deriv (deriv f) t-k*(f t)^3)) t := by
    intro t
    have hd1 : HasDerivAt (fun x => (deriv f x)^2)
        (2*deriv f t*deriv (deriv f) t) t := by
      simpa using ((hff t).hasDerivAt.fun_pow 2)
    have hd2 : HasDerivAt (fun x => (k/2)*(f x)^4)
        ((k/2)*(4*(f t)^3*deriv f t)) t := by
      simpa using (((hf t).hasDerivAt.fun_pow 4).const_mul (k/2))
    have H : HasDerivAt E
        (2*deriv f t*deriv (deriv f) t-(k/2)*(4*(f t)^3*deriv f t)) t :=
      hd1.fun_sub hd2
    convert H using 1 <;> ring
  have hE : Differentiable ℝ E := fun t => (hEd t).differentiableAt
  have hEm : MonotoneOn E (Ici u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici u) hE.continuous.continuousOn
      hE.differentiableOn
    intro t ht
    have htu : u ≤ t := interior_subset ht
    rw [(hEd t).deriv]
    exact mul_nonneg (mul_nonneg (by norm_num) (hd t htu).le)
      (sub_nonneg.mpr (hn t (le_trans hua htu)))
  have h4Top : Tendsto (fun t => (f t)^4) atTop atTop :=
    (tendsto_pow_atTop (show (4:ℕ)≠0 by decide)).comp hTop
  obtain ⟨d,hdu',hfloor⟩ := ((eventually_ge_atTop u).and
    (h4Top.eventually_gt_atTop (-4*E u/k))).exists
  have hfloormul : -4*E u < (f d)^4*k := (div_lt_iff₀ hk).mp hfloor
  have hfm : MonotoneOn f (Ici u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici u) hf.continuous.continuousOn
      hf.differentiableOn
    intro t ht
    exact (hd t (interior_subset ht)).le
  let c := Real.sqrt (k/4)
  have hcp : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c^2=k/4 := Real.sq_sqrt (by linarith)
  have hpd : ∀ t ≥ d, 0 < f t := fun t ht => hp t (le_trans hua (le_trans hdu' ht))
  obtain ⟨t,ht,hlt⟩ := positive_quadratic_deriv_hit f d c hf hpd hcp
  have htu := le_trans hdu' ht
  have hEt := hEm (show u ∈ Ici u from le_refl u) htu htu
  have hft : f d ≤ f t := hfm hdu' htu ht
  have hf4 : (f d)^4 ≤ (f t)^4 := pow_le_pow_left₀
    (hp d (le_trans hua hdu')).le hft 4
  have hpos : 0 < E u+(k/4)*(f t)^4 := by
    have hm := mul_le_mul_of_nonneg_left hf4 (show 0 ≤ k by linarith)
    nlinarith [hfloormul]
  have hs : (c*(f t)^2)^2 ≤ (deriv f t)^2 := by
    dsimp [E] at hEt hpos
    have hid : (c*(f t)^2)^2=(k/4)*(f t)^4 := by
      calc
        (c*(f t)^2)^2=c^2*(f t)^4 := by ring
        _=(k/4)*(f t)^4 := by rw [hc2]
    rw [hid]
    nlinarith
  have hcft : 0 ≤ c*(f t)^2 := mul_nonneg hcp.le (sq_nonneg (f t))
  have hl : c*(f t)^2 ≤ deriv f t :=
    (sq_le_sq₀ hcft (hd t htu).le).mp hs
  linarith
/-- The unbounded exp law instantiates every cubic-curvature binder,
with its nonzero value, slope and curvature at zero stated explicitly. -/
theorem cubic_curvature_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a k t : ℝ), Differentiable ℝ f ∧
      Differentiable ℝ (deriv f) ∧ (∀ z ≥ a, 0 < f z) ∧
      Tendsto f atTop atTop ∧ 0 < k ∧ a ≤ t ∧
      f 0=1 ∧ deriv f 0=1 ∧ deriv (deriv f) 0=1 ∧
      deriv (deriv f) t < k*(f t)^3 ∧
      (∃ z ≥ a, deriv (deriv f) z < k*(f z)^3) := by
  have hf : Differentiable ℝ Real.exp := Real.differentiable_exp
  have hff : Differentiable ℝ (deriv Real.exp) := by simpa using hf
  have hp : ∀ z ≥ (0:ℝ), 0 < Real.exp z := fun z _ => Real.exp_pos z
  have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
  have hb : deriv (deriv Real.exp) 1 < (1:ℝ)*(Real.exp 1)^3 := by
    simp only [Real.deriv_exp,one_mul]
    have hh : Real.exp 1 < (Real.exp 1)^2 := by nlinarith
    nlinarith [mul_pos (sq_pos_of_pos (Real.exp_pos (1:ℝ))) (sub_pos.mpr he)]
  exact ⟨Real.exp,0,1,1,hf,hff,hp,Real.tendsto_exp_atTop,by norm_num,
    by norm_num,by simp,by simp,by simp,hb,
    positive_cubic_curvature_hit Real.exp 0 1 hf hff hp Real.tendsto_exp_atTop (by norm_num)⟩
end RMTFoundations.TracyWidom.PositiveCubicCurvature
#print axioms RMTFoundations.TracyWidom.PositiveCubicCurvature.positive_quadratic_deriv_hit
#print axioms RMTFoundations.TracyWidom.PositiveCubicCurvature.quadratic_deriv_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.PositiveCubicCurvature.positive_cubic_curvature_hit
#print axioms RMTFoundations.TracyWidom.PositiveCubicCurvature.cubic_curvature_all_binder_joint_probe
