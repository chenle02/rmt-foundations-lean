import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPositiveRatioBarrier
open Set Filter
open scoped Topology

/-- A continuous function at a local minimum has nonnegative second derivative.
The second derivative is the ordinary total `deriv`, including its zero fallback. -/
theorem local_min_second_deriv_nonnegative
    (f : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hc : ContinuousAt f s /- [standing] -/)
    (hm : IsLocalMin f s /- [standing] -/)
    : 0 ≤ deriv (deriv f) s := by
  by_contra h
  have hn : deriv (deriv f) s < 0 := lt_of_not_ge h
  have hx : IsLocalMax f s := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 s] (fun _ => f s) := by
    filter_upwards [hm,hx] with t ht hu
    exact le_antisymm hu ht
  have hz := he.deriv.deriv_eq
  have hz0 : deriv (deriv f) s = 0 := by simpa using hz
  linarith

/-- The squared positive ratio is smoother to differentiate than its square root. -/
noncomputable def squaredRatio
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    : ℝ := (y t)^2/t

theorem squaredRatio_hasDerivAt
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (ht : t ≠ 0 /- [standing] -/)
    : HasDerivAt (squaredRatio y)
      (2*y t*deriv y t/t-(y t)^2/t^2) t := by
  convert! ((hy t).hasDerivAt.pow 2).fun_div (hasDerivAt_id t) ht using 1
  simp only [Pi.pow_apply,id_eq]
  field_simp [ht]
  ring

theorem squaredRatio_deriv
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (ht : t ≠ 0 /- [standing] -/)
    : deriv (squaredRatio y) t = 2*y t*deriv y t/t-(y t)^2/t^2 :=
  (squaredRatio_hasDerivAt y t hy ht).deriv

/-- Literal reflected-PII at one point supplies the second ratio derivative.
No global PII or physical sign assumption is present. -/
theorem squaredRatio_second_deriv
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : t ≠ 0 /- [standing] -/)
    : deriv (deriv (squaredRatio y)) t =
      2*((deriv y t)^2+y t*(y t*(2*(y t)^2-t)))/t -
        4*y t*deriv y t/t^2 + 2*(y t)^2/t^3 := by
  have he : deriv (squaredRatio y) =ᶠ[𝓝 t]
      (fun u => 2*y u*deriv y u/u-(y u)^2/u^2) := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    exact squaredRatio_deriv y u hy hu
  have hd := (((((hy t).hasDerivAt.const_mul 2).fun_mul hyy).fun_div
    (hasDerivAt_id t) ht).fun_sub
      (((hy t).hasDerivAt.pow 2).fun_div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht)))
  rw [he.deriv_eq]
  convert! hd.deriv using 1
  simp only [Pi.pow_apply,id_eq]
  field_simp [ht]
  ring

/-- At a local ratio minimum, the pointwise reflected-PII jet lies strictly
above the coarse square-root threshold. -/
theorem squaredRatio_local_min_above_quarter
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 1 ≤ t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMin (squaredRatio y) t /- [standing] -/)
    : 1/4 < squaredRatio y t := by
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ht0.ne'
  have hd := hm.hasDerivAt_eq_zero (squaredRatio_hasDerivAt y t hy htne)
  have hjet : 2*t*deriv y t=y t := by
    field_simp at hd
    nlinarith
  have hsecond := squaredRatio_second_deriv y t hy hyy htne
  have hstationary : deriv (deriv (squaredRatio y)) t =
      (2*(y t)^2/t)*(2*(y t)^2-t+1/(4*t^2)) := by
    rw [hsecond]
    field_simp
    nlinarith [sq_nonneg (2*t*deriv y t-y t)]
  have hn := local_min_second_deriv_nonnegative (squaredRatio y) t
    (squaredRatio_hasDerivAt y t hy htne).continuousAt hm
  rw [hstationary] at hn
  by_contra h
  have hsmall : (y t)^2 ≤ t/4 := by
    have hb : squaredRatio y t ≤ 1/4 := le_of_not_gt h
    dsimp only [squaredRatio] at hb
    nlinarith [(div_le_iff₀ ht0).mp hb]
  have hb : 1/(4*t^2) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*t^2) (by norm_num : (0:ℝ)<4)).2
    nlinarith
  have hnegative : 2*(y t)^2-t+1/(4*t^2)<0 := by linarith
  have hfactor : 0 < 2*(y t)^2/t := by positivity
  exact (not_le_of_gt (mul_neg_of_pos_of_neg hfactor hnegative)) hn

/-- Literal adapter for the unsquared positive ratio y(t)/sqrt(t). -/
theorem positiveRatio_local_min_above_half
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 1 ≤ t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMin (fun u => y u/Real.sqrt u) t /- [standing] -/)
    : 1/2 < y t/Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < y t/Real.sqrt t := div_pos hp (Real.sqrt_pos.mpr ht0)
  have he : ∀ u : ℝ, 0 ≤ u → squaredRatio y u = (y u/Real.sqrt u)^2 := by
    intro u hu
    simp only [squaredRatio,div_pow,Real.sq_sqrt hu]
  have hmsq : IsLocalMin (squaredRatio y) t := by
    filter_upwards [hm,eventually_gt_nhds ht0] with u hmu hu
    rw [he t ht0.le,he u hu.le]
    nlinarith
  have hq := squaredRatio_local_min_above_quarter y t hy hyy ht hp hmsq
  rw [he t ht0.le] at hq
  nlinarith

/-- The compact minimum principle transfers a local-minimum barrier between
two hits. Its premise only constrains local minima, not the values on the interval. -/
theorem threshold_between_hits
    (f : ℝ → ℝ /- [definition] -/)
    (a b c : ℝ /- [definition] -/)
    (hab : a ≤ b /- [standing] -/)
    (hf : ContinuousOn f (Icc a b) /- [standing] -/)
    (ha : c ≤ f a /- [standing] -/)
    (hb : c ≤ f b /- [standing] -/)
    (hmin : ∀ s ∈ Ioo a b, IsLocalMin f s → c < f s /- [standing] -/)
    : ∀ s ∈ Icc a b, c ≤ f s := by
  intro s hs
  by_contra h
  have hlow : f s < c := lt_of_not_ge h
  obtain ⟨z,hz,hzmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf
  have hzlow : f z < c := (hzmin hs).trans_lt hlow
  have haz : a < z := by
    have hza : a ≤ z := hz.1
    by_contra h
    have he : z=a := le_antisymm (le_of_not_gt h) hza
    rw [he] at hzlow
    exact (not_lt_of_ge ha) hzlow
  have hzb : z < b := by
    have hzb : z ≤ b := hz.2
    by_contra h
    have he : z=b := le_antisymm hzb (le_of_not_gt h)
    rw [he] at hzlow
    exact (not_lt_of_ge hb) hzlow
  have hlocal : IsLocalMin f z := hzmin.isLocalMin (Icc_mem_nhds haz hzb)
  exact (not_lt_of_gt (hmin z ⟨haz,hzb⟩ hlocal)) hzlow

/-- A nonconstant positive polynomial realizes the reflected PII jet at one
point and a genuine local ratio minimum. It is not a global PII solution. -/
noncomputable def jetProbe
    (t : ℝ /- [definition] -/)
    : ℝ := 1+(t-1)/2+(t-1)^2/2

theorem jetProbe_hasDerivAt
    (t : ℝ /- [definition] -/)
    : HasDerivAt jetProbe (1/2+(t-1)) t := by
  have hd := ((hasDerivAt_const t (1:ℝ)).fun_add
    (((hasDerivAt_id t).sub_const 1).div_const 2)).fun_add
    ((((hasDerivAt_id t).sub_const 1).pow 2).div_const 2)
  convert! hd using 1
  simp only [id_eq]
  ring

theorem jetProbe_deriv : deriv jetProbe = fun t => 1/2+(t-1) :=
  funext (fun t => (jetProbe_hasDerivAt t).deriv)

theorem local_calculus_all_binder_joint_probe :
    ∃ (y : ℝ → ℝ) (t : ℝ),
      Differentiable ℝ y ∧
      HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t ∧
      1 ≤ t ∧ 0 < y t ∧ t ≠ 0 ∧
      IsLocalMin (squaredRatio y) t ∧
      IsLocalMin (fun u => y u/Real.sqrt u) t ∧
      HasDerivAt (squaredRatio y) (2*y t*deriv y t/t-(y t)^2/t^2) t ∧
      0 < deriv (deriv (squaredRatio y)) t ∧
      1/4 < squaredRatio y t ∧ 1/2 < y t/Real.sqrt t := by
  have hy : Differentiable ℝ jetProbe := fun t => (jetProbe_hasDerivAt t).differentiableAt
  have hyy : HasDerivAt (deriv jetProbe) (jetProbe 1*(2*(jetProbe 1)^2-1)) 1 := by
    rw [jetProbe_deriv]
    convert! (hasDerivAt_const (1:ℝ) (1/2:ℝ)).fun_add ((hasDerivAt_id (1:ℝ)).sub_const 1) using 1
    norm_num [jetProbe]
  have hd := squaredRatio_hasDerivAt jetProbe 1 hy (by norm_num)
  have hz : deriv (squaredRatio jetProbe) 1=0 := by
    rw [hd.deriv,jetProbe_deriv]
    norm_num [jetProbe]
  have hsecond : deriv (deriv (squaredRatio jetProbe)) 1 = 5/2 := by
    rw [squaredRatio_second_deriv jetProbe 1 hy hyy (by norm_num),jetProbe_deriv]
    norm_num [jetProbe]
  have hp : 0 < deriv (deriv (squaredRatio jetProbe)) 1 := by rw [hsecond]; norm_num
  have hm := isLocalMin_of_deriv_deriv_pos hp hz hd.continuousAt
  have hpositive : ∀ u : ℝ, 0 < jetProbe u := by
    intro u
    dsimp only [jetProbe]
    nlinarith [sq_nonneg (u-1/2)]
  have hratio : IsLocalMin (fun u => jetProbe u/Real.sqrt u) 1 := by
    filter_upwards [hm,eventually_gt_nhds (by norm_num : (0:ℝ)<1)] with u hu hu0
    have hr : 0 < jetProbe u/Real.sqrt u := div_pos (hpositive u) (Real.sqrt_pos.mpr hu0)
    have hw : squaredRatio jetProbe u = (jetProbe u/Real.sqrt u)^2 := by
      simp only [squaredRatio,div_pow,Real.sq_sqrt hu0.le]
    rw [show squaredRatio jetProbe 1=1 by norm_num [squaredRatio,jetProbe],hw] at hu
    rw [show jetProbe 1/Real.sqrt 1=1 by norm_num [jetProbe]]
    nlinarith
  exact ⟨jetProbe,1,hy,hyy,by norm_num,by norm_num [jetProbe],by norm_num,
    hm,hratio,hd,hp,squaredRatio_local_min_above_quarter jetProbe 1 hy hyy
      (by norm_num) (by norm_num [jetProbe]) hm,
    positiveRatio_local_min_above_half jetProbe 1 hy hyy
      (by norm_num) (by norm_num [jetProbe]) hratio⟩

/-- The compact threshold bridge has all binders inhabited by a nonconstant
positive exponential on an interval with two distinct endpoints. -/
theorem threshold_bridge_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a b c : ℝ), a < b ∧ c > 0 ∧
      ContinuousOn f (Icc a b) ∧ c ≤ f a ∧ c ≤ f b ∧
      (∀ s ∈ Ioo a b, IsLocalMin f s → c < f s) ∧
      (∀ s ∈ Icc a b, c ≤ f s) := by
  have hmin : ∀ s ∈ Ioo (0:ℝ) 1, IsLocalMin Real.exp s → 1 < Real.exp s := by
    intro s hs _
    exact Real.one_lt_exp_iff.mpr hs.1
  have ha : (1:ℝ) ≤ Real.exp 0 := by norm_num
  have hb : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  exact ⟨Real.exp,0,1,1,by norm_num,by norm_num,Real.continuous_exp.continuousOn,
    ha,hb,hmin,threshold_between_hits Real.exp 0 1 1 (by norm_num)
      Real.continuous_exp.continuousOn ha hb hmin⟩

end RMTFoundations.TracyWidom.HMPositiveRatioBarrier
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.local_min_second_deriv_nonnegative
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.squaredRatio
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.squaredRatio_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.squaredRatio_deriv
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.squaredRatio_second_deriv
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.squaredRatio_local_min_above_quarter
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.positiveRatio_local_min_above_half
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.threshold_between_hits
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.jetProbe
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.jetProbe_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.jetProbe_deriv
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.local_calculus_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioBarrier.threshold_bridge_all_binder_joint_probe
