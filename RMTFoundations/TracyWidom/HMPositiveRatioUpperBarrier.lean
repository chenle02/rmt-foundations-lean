import RMTFoundations.TracyWidom.HMPositiveRatioBarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier
open Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.HMPositiveRatioBarrier

/-- A continuous function at a local maximum has nonpositive second derivative. -/
theorem local_max_second_deriv_nonpositive
    (f : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hc : ContinuousAt f s /- [standing] -/)
    (hm : IsLocalMax f s /- [standing] -/)
    : deriv (deriv f) s ≤ 0 := by
  have hn := local_min_second_deriv_nonnegative (fun u => -f u) s hc.neg hm.neg
  have he : deriv (fun u => -f u) = fun u => -deriv f u := by
    funext u
    exact deriv.fun_neg
  rw [he,deriv.fun_neg] at hn
  linarith

/-- A pointwise reflected-PII jet at a positive local ratio maximum lies
strictly below the limiting squared-ratio threshold. No global PII is assumed. -/
theorem squaredRatio_local_max_below_half
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 1 ≤ t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMax (squaredRatio y) t /- [standing] -/)
    : squaredRatio y t < 1/2 := by
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
  have hn := local_max_second_deriv_nonpositive (squaredRatio y) t
    (squaredRatio_hasDerivAt y t hy htne).continuousAt hm
  rw [hstationary] at hn
  by_contra h
  have hbig : t/2 ≤ (y t)^2 := by
    have hb : 1/2 ≤ squaredRatio y t := le_of_not_gt h
    dsimp only [squaredRatio] at hb
    nlinarith [(le_div_iff₀ ht0).mp hb]
  have hpositive : 0 < 2*(y t)^2-t+1/(4*t^2) := by
    have hr : 0 < 1/(4*t^2) := by positivity
    linarith
  have hfactor : 0 < 2*(y t)^2/t := by positivity
  exact (not_le_of_gt (mul_pos hfactor hpositive)) hn

/-- Literal local-maximum adapter for the positive unsquared ratio. -/
theorem positiveRatio_local_max_below_sqrt_half
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 1 ≤ t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMax (fun u => y u/Real.sqrt u) t /- [standing] -/)
    : y t/Real.sqrt t < Real.sqrt (1/2) := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < y t/Real.sqrt t := div_pos hp (Real.sqrt_pos.mpr ht0)
  have hyn : ∀ᶠ u in 𝓝 t, 0 < y u :=
    (hy t).continuousAt.eventually (eventually_gt_nhds hp)
  have he : ∀ u : ℝ, 0 ≤ u → squaredRatio y u = (y u/Real.sqrt u)^2 := by
    intro u hu
    simp only [squaredRatio,div_pow,Real.sq_sqrt hu]
  have hmsq : IsLocalMax (squaredRatio y) t := by
    filter_upwards [hm,hyn,eventually_gt_nhds ht0] with u hmu hyu hu
    rw [he t ht0.le,he u hu.le]
    have hru : 0 < y u/Real.sqrt u := div_pos hyu (Real.sqrt_pos.mpr hu)
    exact (sq_le_sq₀ hru.le hr0.le).mpr hmu
  have hb := squaredRatio_local_max_below_half y t hy hyy ht hp hmsq
  rw [he t ht0.le] at hb
  have hsq : (Real.sqrt (1/2:ℝ))^2=1/2 := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (1/2:ℝ)
  nlinarith

/-- Negation converts the already proved compact minimum bridge into an
upper threshold bridge between two lower hits. -/
theorem upper_threshold_between_hits
    (f : ℝ → ℝ /- [definition] -/)
    (a b c : ℝ /- [definition] -/)
    (hab : a ≤ b /- [standing] -/)
    (hf : ContinuousOn f (Icc a b) /- [standing] -/)
    (ha : f a ≤ c /- [standing] -/)
    (hb : f b ≤ c /- [standing] -/)
    (hmax : ∀ s ∈ Ioo a b, IsLocalMax f s → f s < c /- [standing] -/)
    : ∀ s ∈ Icc a b, f s ≤ c := by
  have hn : ∀ s ∈ Icc a b, -c ≤ -f s := by
    apply threshold_between_hits (fun u => -f u) a b (-c) hab hf.neg
    · linarith
    · linarith
    · intro s hs hm
      have hms : IsLocalMax f s := by simpa only [neg_neg] using hm.neg
      have hx := hmax s hs hms
      linarith
  intro s hs
  exact neg_le_neg_iff.mp (hn s hs)

/-- Nonconstant polynomial with positive value and the genuine reflected-PII
jet at one, producing a local maximum instead of a global PII model. -/
noncomputable def upperJetProbe
    (t : ℝ /- [definition] -/)
    : ℝ := 1/4+(t-1)/8-(7/64)*(t-1)^2

theorem upperJetProbe_hasDerivAt
    (t : ℝ /- [definition] -/)
    : HasDerivAt upperJetProbe (1/8-(7/32)*(t-1)) t := by
  have hd := ((hasDerivAt_const t (1/4:ℝ)).fun_add
    (((hasDerivAt_id t).sub_const 1).div_const 8)).fun_sub
    ((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (7/64))
  convert! hd using 1
  simp only [id_eq]
  ring

theorem upperJetProbe_deriv : deriv upperJetProbe = fun t => 1/8-(7/32)*(t-1) :=
  funext (fun t => (upperJetProbe_hasDerivAt t).deriv)

theorem upper_local_calculus_all_binder_joint_probe :
    ∃ (y : ℝ → ℝ) (t : ℝ),
      Differentiable ℝ y ∧
      HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t ∧
      1 ≤ t ∧ 0 < y t ∧ t ≠ 0 ∧
      IsLocalMax (squaredRatio y) t ∧
      IsLocalMax (fun u => y u/Real.sqrt u) t ∧
      deriv (deriv (squaredRatio y)) t = -5/64 ∧
      squaredRatio y t < 1/2 ∧ y t/Real.sqrt t < Real.sqrt (1/2) := by
  have hy : Differentiable ℝ upperJetProbe := fun t => (upperJetProbe_hasDerivAt t).differentiableAt
  have hyy : HasDerivAt (deriv upperJetProbe)
      (upperJetProbe 1*(2*(upperJetProbe 1)^2-1)) 1 := by
    rw [upperJetProbe_deriv]
    convert! (hasDerivAt_const (1:ℝ) (1/8:ℝ)).fun_sub
      (((hasDerivAt_id (1:ℝ)).sub_const 1).const_mul (7/32)) using 1
    norm_num [upperJetProbe]
  have hd := squaredRatio_hasDerivAt upperJetProbe 1 hy (by norm_num)
  have hz : deriv (squaredRatio upperJetProbe) 1=0 := by
    rw [hd.deriv,upperJetProbe_deriv]
    norm_num [upperJetProbe]
  have hsecond : deriv (deriv (squaredRatio upperJetProbe)) 1 = -5/64 := by
    rw [squaredRatio_second_deriv upperJetProbe 1 hy hyy (by norm_num),upperJetProbe_deriv]
    norm_num [upperJetProbe]
  have hn : deriv (deriv (squaredRatio upperJetProbe)) 1 < 0 := by rw [hsecond]; norm_num
  have hm := isLocalMax_of_deriv_deriv_neg hn hz hd.continuousAt
  have hratio : IsLocalMax (fun u => upperJetProbe u/Real.sqrt u) 1 := by
    have hpositive : ∀ᶠ u in 𝓝 (1:ℝ), 0 < upperJetProbe u :=
      (upperJetProbe_hasDerivAt 1).continuousAt.eventually
        (eventually_gt_nhds (by norm_num [upperJetProbe] : 0 < upperJetProbe 1))
    filter_upwards [hm,hpositive,eventually_gt_nhds (by norm_num : (0:ℝ)<1)] with u hu hyp hu0
    have hr : 0 < upperJetProbe u/Real.sqrt u := div_pos hyp (Real.sqrt_pos.mpr hu0)
    have hw : squaredRatio upperJetProbe u = (upperJetProbe u/Real.sqrt u)^2 := by
      simp only [squaredRatio,div_pow,Real.sq_sqrt hu0.le]
    rw [show squaredRatio upperJetProbe 1=1/16 by norm_num [squaredRatio,upperJetProbe],hw] at hu
    rw [show upperJetProbe 1/Real.sqrt 1=1/4 by norm_num [upperJetProbe]]
    nlinarith
  exact ⟨upperJetProbe,1,hy,hyy,by norm_num,by norm_num [upperJetProbe],by norm_num,
    hm,hratio,hsecond,squaredRatio_local_max_below_half upperJetProbe 1 hy hyy
      (by norm_num) (by norm_num [upperJetProbe]) hm,
    positiveRatio_local_max_below_sqrt_half upperJetProbe 1 hy hyy
      (by norm_num) (by norm_num [upperJetProbe]) hratio⟩

/-- Every compact upper-threshold binder is realized on a strictly positive,
nonconstant decreasing exponential and two distinct endpoints. -/
theorem upper_threshold_bridge_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a b c : ℝ), a < b ∧ c > 0 ∧
      ContinuousOn f (Icc a b) ∧ f a ≤ c ∧ f b ≤ c ∧
      (∀ s ∈ Ioo a b, IsLocalMax f s → f s < c) ∧
      (∀ s ∈ Icc a b, f s ≤ c) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have ha : f 0 ≤ (1:ℝ) := by norm_num [f]
  have hb : f 1 ≤ (1:ℝ) := Real.exp_le_one_iff.mpr (by norm_num)
  have hmax : ∀ s ∈ Ioo (0:ℝ) 1, IsLocalMax f s → f s < 1 := by
    intro s hs _
    exact Real.exp_lt_one_iff.mpr (by linarith [hs.1])
  exact ⟨f,0,1,1,by norm_num,by norm_num,hf.continuousOn,ha,hb,hmax,
    upper_threshold_between_hits f 0 1 1 (by norm_num) hf.continuousOn ha hb hmax⟩

end RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.local_max_second_deriv_nonpositive
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.squaredRatio_local_max_below_half
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.positiveRatio_local_max_below_sqrt_half
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upper_threshold_between_hits
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upperJetProbe
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upperJetProbe_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upperJetProbe_deriv
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upper_local_calculus_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier.upper_threshold_bridge_all_binder_joint_probe
