import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ODEMaximumPrinciple
open Set Filter Topology Real

/-- A twice differentiable function cannot have a positive interior maximum
when its second derivative is strictly positive wherever the function is positive. -/
theorem no_positive_local_max
    (w v d : ℝ → ℝ /- [definition] -/)
    (hw : ∀ t, HasDerivAt w (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (d t) t /- [standing] -/)
    (a x : ℝ /- [definition] -/)
    (hx : a < x /- [standing] -/)
    (hd : ∀ t, a < t → 0 < w t → 0 < d t /- [standing] -/)
    (hm : IsLocalMax w x /- [standing] -/)
    (hp : 0 < w x /- [standing] -/) : False := by
  have hc : Continuous w := continuous_iff_continuousAt.mpr fun t => (hw t).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun t => (hv t).continuousAt
  have hzero : v x = 0 := hm.hasDerivAt_eq_zero (hw x)
  have hna : ∀ᶠ t in 𝓝 x, a < t := Ioi_mem_nhds hx
  have hn : ∀ᶠ t in 𝓝 x, a < t ∧ 0 < w t ∧ w t ≤ w x :=
    hna.and ((hc.continuousAt.eventually (Ioi_mem_nhds hp)).and hm)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  let y : ℝ := x+ε/2
  have hxy : x < y := by dsimp [y]; linarith
  have hb (t : ℝ) (ht : t ∈ Icc x y) : a < t ∧ 0 < w t ∧ w t ≤ w x := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have h : 0 ≤ t-x := sub_nonneg.mpr ht.1
    rw [abs_of_nonneg h]
    dsimp [y] at ht
    linarith [ht.2]
  have hmono : StrictMonoOn v (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x y) hvc.continuousOn
    intro t ht
    rw [(hv t).deriv]
    have H := hb t (interior_subset ht)
    exact hd t H.1 H.2.1
  have hwmono : StrictMonoOn w (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x y) hc.continuousOn
    intro t ht
    have ht' : t ∈ Ioo x y := by simpa only [interior_Icc] using ht
    rw [(hw t).deriv,←hzero]
    exact hmono ⟨le_rfl,hxy.le⟩ ⟨ht'.1.le,ht'.2.le⟩ ht'.1
  have H := hwmono ⟨le_rfl,hxy.le⟩ ⟨hxy.le,le_rfl⟩ hxy
  exact (not_lt_of_ge (hb y ⟨hxy.le,le_rfl⟩).2.2) H

/-- Half-line maximum principle, with the actual infinite-tail limit retained. -/
theorem halfline_nonpos
    (w v d : ℝ → ℝ /- [definition] -/)
    (hw : ∀ t, HasDerivAt w (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (d t) t /- [standing] -/)
    (a : ℝ /- [definition] -/)
    (ha : w a ≤ 0 /- [standing] -/)
    (hd : ∀ t, a < t → 0 < w t → 0 < d t /- [standing] -/)
    (htail : Tendsto w atTop (𝓝 0) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : a ≤ x /- [standing] -/) : w x ≤ 0 := by
  by_contra H
  have hp : 0 < w x := lt_of_not_ge H
  obtain ⟨b,hb⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds hp))
  let B : ℝ := max b (x+1)
  have hxB : x < B := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hB : w B < w x := hb B (le_max_left _ _)
  have hc : Continuous w := continuous_iff_continuousAt.mpr fun t => (hw t).continuousAt
  obtain ⟨z,hz,hm⟩ := (isCompact_Icc (a := a) (b := B)).exists_isMaxOn
    ⟨x,hx,hxB.le⟩ hc.continuousOn
  have hpz : 0 < w z := hp.trans_le (hm ⟨hx,hxB.le⟩)
  have haz : a < z := by
    rcases hz.1.eq_or_lt with h | h
    · subst z; exact False.elim ((not_lt_of_ge ha) hpz)
    · exact h
  have hzB : z < B := by
    rcases hz.2.lt_or_eq with h | h
    · exact h
    · subst z; exact False.elim ((not_lt_of_ge (hm ⟨hx,hxB.le⟩)) hB)
  have hlocal : IsLocalMax w z := hm.isLocalMax (Icc_mem_nhds haz hzB)
  exact no_positive_local_max w v d hw hv a z haz hd hlocal hpz

/-- Upper exponential comparison without a sign premise on the solution. -/
theorem exponential_upper
    (u v q : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (a c A : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hA : 0 ≤ A /- [standing] -/)
    (ha : u a ≤ A /- [standing] -/)
    (hq : ∀ t, a ≤ t → c^2 ≤ q t /- [standing] -/)
    (htail : Tendsto u atTop (𝓝 0) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : a ≤ x /- [standing] -/) : u x ≤ A*exp (-c*(x-a)) := by
  let E : ℝ → ℝ := fun t => A*exp (-c*(t-a))
  have hE (t : ℝ) : HasDerivAt E (-c*E t) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul (-c)).exp.const_mul A using 1 <;>
      simp only [E,Function.comp_def,id_eq] <;> ring
  have hE2 (t : ℝ) : HasDerivAt (fun t => v t+c*E t)
      (q t*u t-c^2*E t) t := by
    convert! (hv t).add ((hE t).const_mul c) using 1 <;> ring
  have hEt : Tendsto E atTop (𝓝 0) := by
    have hta : Tendsto (fun t : ℝ => t-a) atTop atTop := by
      simpa only [sub_eq_add_neg,id_eq] using
        tendsto_atTop_add_const_right atTop (-a) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
    have H := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hta.atTop_mul_const hc)
    convert H.const_mul A using 1
    · funext t; dsimp [E,Function.comp_def]; congr 2; ring
    · simp
  have H := halfline_nonpos (fun t => u t-E t) (fun t => v t+c*E t)
    (fun t => q t*u t-c^2*E t)
    (fun t => by convert! (hu t).sub (hE t) using 1 <;> ring)
    hE2 a (by simpa [E] using sub_nonpos.mpr ha) (by
      intro t ht hp
      have he : 0 ≤ E t := by dsimp [E]; positivity
      have hqt := hq t ht.le
      have hqpos : 0 < q t := lt_of_lt_of_le (sq_pos_of_pos hc) hqt
      have hd : q t*u t-c^2*E t = q t*(u t-E t)+(q t-c^2)*E t := by ring
      rw [hd]
      exact add_pos_of_pos_of_nonneg (mul_pos hqpos hp)
        (mul_nonneg (sub_nonneg.mpr hqt) he))
    (by simpa only [sub_zero] using htail.sub hEt) x hx
  exact sub_nonpos.mp H

/-- A decaying real oscillator above a positive potential floor has an absolute
exponential envelope, with no positivity or weighted-derivative tail assumption. -/
theorem absolute_exponential_tail
    (u v q : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (a c : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hq : ∀ t, a ≤ t → c^2 ≤ q t /- [standing] -/)
    (htail : Tendsto u atTop (𝓝 0) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : a ≤ x /- [standing] -/) : |u x| ≤ |u a| *exp (-c*(x-a)) := by
  have hupp := exponential_upper u v q hu hv a c |u a| hc (abs_nonneg _) (le_abs_self _) hq htail x hx
  have hlow := exponential_upper (fun t => -u t) (fun t => -v t) q
    (fun t => (hu t).neg)
    (fun t => by convert! (hv t).neg using 1 <;> ring)
    a c |u a| hc (abs_nonneg _) (neg_le_abs _) hq
    (by simpa only [neg_zero] using htail.neg) x hx
  exact abs_le.mpr ⟨by linarith,hupp⟩

/-- Complete nondegenerate all-binder control, with both signs and growing amplitudes. -/
theorem exponential_all_binder_joint_probe (n : ℕ /- [definition] -/)
    (σ : ℝ /- [definition] -/)
    (hσ : σ=1 ∨ σ = -1 /- [standing] -/) :
    ∃ u v q : ℝ → ℝ,
      u 0 ≠ 0 ∧ (∀ t, HasDerivAt u (v t) t) ∧
      (∀ t, HasDerivAt v (q t*u t) t) ∧
      (∀ t, 0 ≤ t → (1:ℝ)^2 ≤ q t) ∧ Tendsto u atTop (𝓝 0) ∧
      (∀ x, 0 ≤ x → |u x| ≤ |u 0| *exp (-1*(x-0))) := by
  let u : ℝ → ℝ := fun t => σ*((n+1:ℕ):ℝ)*exp (-2*t)
  let v : ℝ → ℝ := fun t => -2*u t
  have hu (t : ℝ) : HasDerivAt u (v t) t := by
    convert! (((hasDerivAt_id t).const_mul (-2)).exp).const_mul (σ*((n+1:ℕ):ℝ)) using 1 <;>
      simp only [u,v,Function.comp_def,id_eq] <;> ring
  have hv (t : ℝ) : HasDerivAt v (4*u t) t := by
    convert! (hu t).const_mul (-2) using 1 <;> simp only [v] <;> ring
  have ht : Tendsto u atTop (𝓝 0) := by
    have H : Tendsto (fun t : ℝ => exp (-2*t)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,neg_mul,mul_neg,mul_comm] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.atTop_mul_const (show (0:ℝ)<2 by norm_num))
    simpa only [u,mul_zero] using H.const_mul (σ*((n+1:ℕ):ℝ))
  refine ⟨u,v,fun _ => 4,?_,hu,hv,?_,ht,?_⟩
  · have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    dsimp [u]
    simp only [mul_zero,exp_zero,mul_one]
    exact mul_ne_zero hσ0 (by positivity)
  · intro t ht; norm_num
  · intro x hx; exact absolute_exponential_tail u v (fun _ => 4) hu hv 0 1
      (by norm_num) (by intro t ht; norm_num) ht x hx

/-- Uniform boundary control is propagated uniformly, with its quantifier
visible. This lemma does not assert the boundary control for Hermite modes. -/
theorem family_absolute_exponential_tail
    (u v q : ℕ → ℝ → ℝ /- [definition] -/)
    (hu : ∀ n t, HasDerivAt (u n) (v n t) t /- [standing] -/)
    (hv : ∀ n t, HasDerivAt (v n) (q n t*u n t) t /- [standing] -/)
    (a c A : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hq : ∀ n t, a ≤ t → c^2 ≤ q n t /- [standing] -/)
    (htail : ∀ n, Tendsto (u n) atTop (𝓝 0) /- [standing] -/)
    (hseed : ∀ n, |u n a| ≤ A /- [standing] -/) :
    ∀ n x, a ≤ x → |u n x| ≤ A*exp (-c*(x-a)) := by
  intro n x hx
  exact (absolute_exponential_tail (u n) (v n) (q n) (hu n) (hv n)
    a c hc (hq n) (htail n) x hx).trans
      (mul_le_mul_of_nonneg_right (hseed n) (exp_pos _).le)

/-- Complete nondegenerate FAMILY witness, with uniform amplitude 2 and a
strictly positive potential; every dimension uses an actual decaying solution. -/
theorem uniform_family_all_binder_joint_probe :
    ∃ u v q : ℕ → ℝ → ℝ,
      (∀ n, u n 0 ≠ 0) ∧ (∀ n t, HasDerivAt (u n) (v n t) t) ∧
      (∀ n t, HasDerivAt (v n) (q n t*u n t) t) ∧
      (∀ n t, 0 ≤ t → (1:ℝ)^2 ≤ q n t) ∧
      (∀ n, Tendsto (u n) atTop (𝓝 0)) ∧
      (∀ n, |u n 0| ≤ 2) ∧
      (∀ n x, 0 ≤ x → |u n x| ≤ 2*exp (-1*(x-0))) := by
  let A : ℕ → ℝ := fun n => 1+1/((n+1:ℕ):ℝ)
  let u : ℕ → ℝ → ℝ := fun n t => A n*exp (-2*t)
  let v : ℕ → ℝ → ℝ := fun n t => -2*u n t
  have hAp (n : ℕ) : 0 < A n := by dsimp [A]; positivity
  have hAb (n : ℕ) : A n ≤ 2 := by
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
    have hd : 1/((n+1:ℕ):ℝ) ≤ (1:ℝ) := (div_le_one (by positivity)).mpr hn
    dsimp [A]; linarith
  have hu (n : ℕ) (t : ℝ) : HasDerivAt (u n) (v n t) t := by
    convert! (((hasDerivAt_id t).const_mul (-2)).exp).const_mul (A n) using 1 <;>
      simp only [u,v,Function.comp_def,id_eq] <;> ring
  have hv (n : ℕ) (t : ℝ) : HasDerivAt (v n) (4*u n t) t := by
    convert! (hu n t).const_mul (-2) using 1 <;> simp only [v] <;> ring
  have ht (n : ℕ) : Tendsto (u n) atTop (𝓝 0) := by
    have H : Tendsto (fun t : ℝ => exp (-2*t)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,neg_mul,mul_neg,mul_comm] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.atTop_mul_const (show (0:ℝ)<2 by norm_num))
    simpa only [u,mul_zero] using H.const_mul (A n)
  have hs (n : ℕ) : |u n 0| ≤ 2 := by simpa [u,abs_of_pos (hAp n)] using hAb n
  refine ⟨u,v,fun _ _ => 4,?_,hu,hv,?_,ht,hs,?_⟩
  · intro n; simpa [u] using (hAp n).ne'
  · intro n t ht; norm_num
  · exact family_absolute_exponential_tail u v (fun _ _ => 4) hu hv 0 1 2
      (by norm_num) (by intro n t ht; norm_num) ht hs

end RMTFoundations.TracyWidom.ODEMaximumPrinciple

#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.no_positive_local_max
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.halfline_nonpos
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.exponential_upper
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.absolute_exponential_tail
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.exponential_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.family_absolute_exponential_tail
#print axioms RMTFoundations.TracyWidom.ODEMaximumPrinciple.uniform_family_all_binder_joint_probe
