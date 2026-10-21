import RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier
import RMTFoundations.TracyWidom.PositiveCubicCurvature
import RMTFoundations.TracyWidom.PositiveSquareFloor
import RMTFoundations.TracyWidom.CanonicalPainleveWitness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMGlobalSquaredUpper
open Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.HMPositiveRatioBarrier RMTFoundations.TracyWidom.HMPositiveRatioUpperBarrier

/-- A nonzero continuous function has constant sign on a right ray. -/
theorem positive_on_ray_of_positive_base
    (f : ℝ → ℝ) -- [definition]
    (a : ℝ) -- [definition]
    (hf : Continuous f) -- [standing]
    (hn : ∀ t ≥ a, f t ≠ 0) -- [standing]
    (ha : 0 < f a) -- [standing]
    : ∀ t ≥ a, 0 < f t := by
  intro t ht
  by_contra hp
  have htneg : f t < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hn t ht)
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc' ht hf.continuousOn ⟨htneg.le,ha.le⟩
  exact hn z hz.1 hzero

/-- Negating a reflected Painleve II solution preserves its equation. -/
theorem neg_reflected_jet
    (y : ℝ → ℝ) -- [definition]
    (hyy : ∀ t, HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t) -- [standing]
    : ∀ t, HasDerivAt (deriv (fun u => -y u))
        ((-y t)*(2*(-y t)^2-t)) t := by
  intro t
  have he : deriv (fun u => -y u) = fun u => -deriv y u := by
    funext u
    exact deriv.fun_neg
  rw [he]
  convert! (hyy t).fun_neg using 1 <;> ring

/-- Above any squared ratio strictly larger than one half, a positive reflected
PII solution would have a positive cubic curvature forever, which is impossible. -/
theorem positive_reflected_floor_impossible
    (y : ℝ → ℝ) -- [definition]
    (a g : ℝ) -- [definition]
    (hy : Differentiable ℝ y) -- [standing]
    (hyy : ∀ t, HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t) -- [standing]
    (hp : ∀ t ≥ a, 0 < y t) -- [standing]
    (hg : 1/2 < g) -- [standing]
    (hfloor : ∀ t ≥ a, g*t ≤ (y t)^2) -- [standing]
    : False := by
  have hg0 : 0 < g := by linarith
  have hk : 0 < 2-1/g := by
    have hh := (div_lt_iff₀ hg0).mpr (show (1:ℝ)<2*g by linarith)
    linarith
  have hTop := RMTFoundations.TracyWidom.PositiveSquareFloor.positive_square_floor_tendsto y a g hp hg0 hfloor
  obtain ⟨t,ht,hbad⟩ := RMTFoundations.TracyWidom.PositiveCubicCurvature.positive_cubic_curvature_hit
    y a (2-1/g) hy (fun t => (hyy t).differentiableAt) hp hTop hk
  rw [(hyy t).deriv] at hbad
  have hid : y t*(2*(y t)^2-t)-(2-1/g)*(y t)^3 =
      (y t/g)*((y t)^2-g*t) := by field_simp [hg0.ne']; ring
  have hn : 0 ≤ y t*(2*(y t)^2-t)-(2-1/g)*(y t)^3 := by
    rw [hid]
    exact mul_nonneg (div_nonneg (hp t ht).le hg0.le) (sub_nonneg.mpr (hfloor t ht))
  linarith

/-- Every global real reflected PII solution has arbitrarily late hits below
each squared-ratio threshold larger than one half. No sign is assumed. -/
theorem reflected_squared_ratio_low_hit
    (y : ℝ → ℝ) -- [definition]
    (a g : ℝ) -- [definition]
    (hy : Differentiable ℝ y) -- [standing]
    (hyy : ∀ t, HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t) -- [standing]
    (hg : 1/2 < g) -- [standing]
    : ∃ t ≥ max a 1, squaredRatio y t < g := by
  by_contra hn
  push Not at hn
  let b := max a 1
  have hb : 1 ≤ b := le_max_right _ _
  have hg0 : 0 < g := by linarith
  have hfloor : ∀ t ≥ b, g*t ≤ (y t)^2 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    exact (le_div_iff₀ ht0).mp (hn t ht)
  have hne : ∀ t ≥ b, y t ≠ 0 := by
    intro t ht he
    have hh := hfloor t ht
    rw [he] at hh
    have ht0 : 0 < t := by linarith
    have hp := mul_pos hg0 ht0
    norm_num at hh
    linarith
  rcases lt_or_gt_of_ne (hne b le_rfl) with hneg | hpos
  · have hpn : ∀ t ≥ b, 0 < -y t := positive_on_ray_of_positive_base
      (fun t => -y t) b hy.continuous.neg
      (fun t ht => neg_ne_zero.mpr (hne t ht)) (by linarith)
    exact positive_reflected_floor_impossible (fun t => -y t) b g hy.neg
      (neg_reflected_jet y hyy) hpn hg (by simpa only [neg_sq] using hfloor)
  · exact positive_reflected_floor_impossible y b g hy hyy
      (positive_on_ray_of_positive_base y b hy.continuous hne hpos) hg hfloor

/-- The squared local-maximum barrier is independent of the sign of y. -/
theorem squared_ratio_local_max_below_half_without_sign
    (y : ℝ → ℝ) -- [definition]
    (t : ℝ) -- [definition]
    (hy : Differentiable ℝ y) -- [standing]
    (hyy : ∀ u, HasDerivAt (deriv y) (y u*(2*(y u)^2-u)) u) -- [standing]
    (ht : 1 ≤ t) -- [standing]
    (hm : IsLocalMax (squaredRatio y) t) -- [standing]
    : squaredRatio y t < 1/2 := by
  by_cases hz : y t = 0
  · norm_num [squaredRatio,hz]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have he : squaredRatio (fun u => -y u) = squaredRatio y := by
      funext u
      simp only [squaredRatio,neg_sq]
    have hn := squaredRatio_local_max_below_half (fun u => -y u) t hy.neg
      (neg_reflected_jet y hyy t) ht (by linarith) (by simpa only [he] using hm)
    simpa only [he] using hn
  · exact squaredRatio_local_max_below_half y t hy (hyy t) ht hpos hm

/-- Global real reflected PII solutions obey the sharp squared limsup upper
bound, formulated as an eventual threshold for every g greater than one half. -/
theorem reflected_squared_ratio_eventually_le
    (y : ℝ → ℝ) -- [definition]
    (hy : Differentiable ℝ y) -- [standing]
    (hyy : ∀ t, HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t) -- [standing]
    (g : ℝ) -- [definition]
    (hg : 1/2 < g) -- [standing]
    : ∀ᶠ t in atTop, squaredRatio y t ≤ g := by
  obtain ⟨a,ha,hga⟩ := reflected_squared_ratio_low_hit y 1 g hy hyy hg
  filter_upwards [eventually_ge_atTop a] with t ht
  obtain ⟨b,hb,hgb⟩ := reflected_squared_ratio_low_hit y t g hy hyy hg
  have htb : t ≤ b := le_trans (le_max_left _ _) hb
  have ha1 : 1 ≤ a := by simpa using ha
  have hc : ContinuousOn (squaredRatio y) (Icc a b) := by
    intro u hu
    exact (squaredRatio_hasDerivAt y u hy (by linarith [hu.1])).continuousAt.continuousWithinAt
  exact upper_threshold_between_hits (squaredRatio y) a b g (le_trans ht htb)
    hc hga.le hgb.le (fun u hu hm =>
      lt_trans (squared_ratio_local_max_below_half_without_sign y u hy hyy
        (by linarith [hu.1]) hm) hg) t ⟨ht,htb⟩

/-- Reflecting the argument reverses the sign of the first derivative. -/
theorem reflected_hasDerivAt
    (q : ℝ → ℝ) -- [definition]
    (hq : Differentiable ℝ q) -- [standing]
    (t : ℝ) -- [definition]
    : HasDerivAt (fun u => q (-u)) (-deriv q (-t)) t := by
  convert! (hq (-t)).hasDerivAt.comp t ((hasDerivAt_id t).neg) using 1 <;> simp

/-- The global PII equation reflects to y''=y(2y²-t), with no sign premise. -/
theorem reflected_pii_jet
    (q : ℝ → ℝ) -- [definition]
    (hq : Differentiable ℝ q) -- [standing]
    (hqq : ∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t) -- [standing]
    : ∀ t, HasDerivAt (deriv (fun u => q (-u)))
      (q (-t)*(2*(q (-t))^2-t)) t := by
  have he : deriv (fun u => q (-u)) = fun u => -deriv q (-u) :=
    funext (fun u => (reflected_hasDerivAt q hq u).deriv)
  intro t
  rw [he]
  convert! ((hqq (-t)).comp t ((hasDerivAt_id t).neg)).fun_neg using 1 <;> simp <;> ring


/-- The sharp squared limsup upper bound for every global classical PII
solution in the original coordinate. No global positivity hypothesis is used. -/
theorem pii_squared_ratio_eventually_le
    (q : ℝ → ℝ) -- [definition]
    (hq : Differentiable ℝ q) -- [standing]
    (hqq : ∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t) -- [standing]
    (g : ℝ) -- [definition]
    (hg : 1/2 < g) -- [standing]
    : ∀ᶠ t in atTop, (q (-t))^2/t ≤ g := by
  exact reflected_squared_ratio_eventually_le (fun t => q (-t))
    (fun t => (reflected_hasDerivAt q hq t).differentiableAt)
    (reflected_pii_jet q hq hqq) g hg

/-- The sharp upper bound at the actual physical Fredholm coordinate. -/
theorem resolventQ_squared_ratio_eventually_le
    (g : ℝ) -- [definition]
    (hg : 1/2 < g) -- [standing]
    : ∀ᶠ t in atTop, (RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ (-t))^2/t ≤ g := by
  exact pii_squared_ratio_eventually_le RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ
    (fun t => (RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_resolventQ t).differentiableAt)
    RMTFoundations.TracyWidom.PhysicalPainleveII.hasDerivAt_deriv_resolventQ g hg

/-- The actual normalized nonzero canonical Fredholm model supplies every
binder of the global sharp-upper theorem, jointly, for every threshold. -/
theorem physical_upper_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, q = RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ ∧
      q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ t, HasDerivAt (deriv q) (t*q t+2*(q t)^3) t) ∧
      Tendsto (fun t => q t/RMTFoundations.Airy.airyAiReal t) atTop (𝓝 1) ∧
      (∀ g : ℝ, 1/2 < g → ∀ᶠ t in atTop, (q (-t))^2/t ≤ g) ∧
      (∀ a g : ℝ, 1/2 < g → ∃ t ≥ max a 1, (q (-t))^2/t < g) := by
  rcases RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_classical_tracyWidom_witness with
    ⟨_,_,_,_,q,hphysical,hq,_,_,_,_,hqq,hAiry,_⟩
  have hn : q ≠ 0 := by
    intro he
    have hz : Tendsto (fun t => q t/RMTFoundations.Airy.airyAiReal t) atTop (𝓝 0) := by
      simp only [he,Pi.zero_apply,zero_div]
      exact tendsto_const_nhds
    have hh := tendsto_nhds_unique hz hAiry
    norm_num at hh
  refine ⟨q,hphysical,hn,hq,hqq,hAiry,(fun g hg => pii_squared_ratio_eventually_le q hq hqq g hg),?_⟩
  intro a g hg
  exact reflected_squared_ratio_low_hit (fun t => q (-t)) a g
    (fun t => (reflected_hasDerivAt q hq t).differentiableAt)
    (reflected_pii_jet q hq hqq) hg

end RMTFoundations.TracyWidom.HMGlobalSquaredUpper

#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.positive_on_ray_of_positive_base
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.neg_reflected_jet
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.positive_reflected_floor_impossible
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.reflected_squared_ratio_low_hit
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.squared_ratio_local_max_below_half_without_sign
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.reflected_squared_ratio_eventually_le
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.reflected_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.reflected_pii_jet
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.pii_squared_ratio_eventually_le
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.resolventQ_squared_ratio_eventually_le
#print axioms RMTFoundations.TracyWidom.HMGlobalSquaredUpper.physical_upper_all_binder_joint_probe
