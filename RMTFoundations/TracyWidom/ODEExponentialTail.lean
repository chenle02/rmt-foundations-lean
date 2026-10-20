import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ODEExponentialTail
open Set Filter Real Topology

/-- Differentiating the weighted outgoing component uses the exact ODE. -/
theorem outgoing_derivative
    (u v q : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (c x : ℝ /- [definition] -/) :
    HasDerivAt (fun t => exp (-c*t)*(v t+c*u t))
      (exp (-c*x)*(q x-c^2)*u x) x := by
  convert! (((hasDerivAt_id x).const_mul (-c)).exp).mul
    ((hv x).add ((hu x).const_mul c)) using 1 <;>
    simp only [Function.comp_def,Pi.add_apply,id_eq] <;> ring

/-- For a positive decaying solution above a positive potential floor,
the growing outgoing component has the correct nonpositive sign. -/
theorem outgoing_nonpos
    (u v q : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (a c : ℝ /- [definition] -/)
    (hpos : ∀ t, a ≤ t → 0 ≤ u t /- [standing] -/)
    (hq : ∀ t, a ≤ t → c^2 ≤ q t /- [standing] -/)
    (htail : Tendsto (fun t => exp (-c*t)*(v t+c*u t)) atTop (𝓝 0) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : a ≤ x /- [standing] -/) : v x+c*u x ≤ 0 := by
  let f : ℝ → ℝ := fun t => exp (-c*t)*(v t+c*u t)
  have hd (t : ℝ) : HasDerivAt f (exp (-c*t)*(q t-c^2)*u t) t :=
    outgoing_derivative u v q hu hv c t
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hm : MonotoneOn f (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a) hc.continuousOn
    · intro t ht; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      have hta : a ≤ t := interior_subset ht
      exact mul_nonneg (mul_nonneg (exp_pos _).le (sub_nonneg.mpr (hq t hta))) (hpos t hta)
  have hle : f x ≤ 0 := ge_of_tendsto htail (by
    filter_upwards [eventually_ge_atTop x] with t ht
    exact hm hx (hx.trans ht) ht)
  apply le_of_mul_le_mul_left ?_ (exp_pos (-c*x))
  simpa only [mul_zero] using hle

/-- Relative exponential envelope; all constants are uniform in any external
index once the hypotheses are supplied uniformly. -/
theorem relative_exponential_tail
    (u v q : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (a c : ℝ /- [definition] -/)
    (hpos : ∀ t, a ≤ t → 0 ≤ u t /- [standing] -/)
    (hq : ∀ t, a ≤ t → c^2 ≤ q t /- [standing] -/)
    (htail : Tendsto (fun t => exp (-c*t)*(v t+c*u t)) atTop (𝓝 0) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : a ≤ x /- [standing] -/) : u x ≤ u a*exp (-c*(x-a)) := by
  have hd (t : ℝ) : HasDerivAt (fun t => exp (c*t)*u t)
      (exp (c*t)*(v t+c*u t)) t := by
    convert! (((hasDerivAt_id t).const_mul c).exp).mul (hu t) using 1 <;>
      simp only [Function.comp_def,id_eq] <;> ring
  have hc : Continuous (fun t => exp (c*t)*u t) :=
    continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hm : AntitoneOn (fun t => exp (c*t)*u t) (Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn
    · intro t ht; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
        (outgoing_nonpos u v q hu hv a c hpos hq htail t (interior_subset ht))
  have H := hm (le_refl a) hx hx
  apply (mul_le_mul_iff_of_pos_left (exp_pos (c*x))).mp
  have he : exp (c*x)*exp (-c*(x-a))=exp (c*a) := by
    rw [←exp_add]; congr 1; ring
  calc
    exp (c*x)*u x ≤ exp (c*a)*u a := H
    _ = exp (c*x)*(u a*exp (-c*(x-a))) := by
      calc
        exp (c*a)*u a = (exp (c*x)*exp (-c*(x-a)))*u a := by rw [he]
        _ = _ := by ring

/-- Complete joint example with positive nonconstant growing-index solutions,
strictly positive potential and a genuine infinite-tail limit. -/
theorem exponential_tail_joint_probe (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/) :
    ((n+1:ℕ):ℝ)*exp (-2*x) ≤ ((n+1:ℕ):ℝ)*exp (-x) := by
  let u : ℝ → ℝ := fun t => ((n+1:ℕ):ℝ)*exp (-2*t)
  let v : ℝ → ℝ := fun t => -2*(((n+1:ℕ):ℝ)*exp (-2*t))
  have hu (t : ℝ) : HasDerivAt u (v t) t := by
    convert! (((hasDerivAt_id t).const_mul (-2)).exp).const_mul ((n+1:ℕ):ℝ) using 1 <;>
      simp only [u,v,Function.comp_def,id_eq] <;> ring
  have hv (t : ℝ) : HasDerivAt v (4*u t) t := by
    convert! (hu t).const_mul (-2) using 1 <;> simp only [u,v] <;> ring
  have ht : Tendsto (fun t => exp (-1*t)*(v t+1*u t)) atTop (𝓝 0) := by
    have H := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<3))
    convert H.const_mul (-((n+1:ℕ):ℝ)) using 1
    · funext t
      dsimp [u,v,Function.comp_def]
      rw [show -2*(((n+1:ℕ):ℝ)*exp (-2*t))+1*(((n+1:ℕ):ℝ)*exp (-2*t)) =
        -((n+1:ℕ):ℝ)*exp (-2*t) by ring]
      rw [mul_left_comm,←exp_add]
      congr 2 <;> ring
    · simp
  have H := relative_exponential_tail u v (fun _ => 4) hu hv 0 1
    (by intro t ht; dsimp [u]; positivity) (by intro t ht; norm_num) ht x hx
  simpa [u] using H
end RMTFoundations.TracyWidom.ODEExponentialTail

#print axioms RMTFoundations.TracyWidom.ODEExponentialTail.outgoing_derivative
#print axioms RMTFoundations.TracyWidom.ODEExponentialTail.outgoing_nonpos
#print axioms RMTFoundations.TracyWidom.ODEExponentialTail.relative_exponential_tail
#print axioms RMTFoundations.TracyWidom.ODEExponentialTail.exponential_tail_joint_probe
