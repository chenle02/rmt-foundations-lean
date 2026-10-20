import RMTFoundations.TracyWidom.HermiteCubicSaddle
import RMTFoundations.TracyWidom.HermiteCircleEnvelope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCircleCoordinate
open Complex Filter Topology
open RMTFoundations.TracyWidom.HermiteCubicSaddle RMTFoundations.TracyWidom.HermiteCircleEnvelope
open RMTFoundations.TracyWidom.HermiteSaddleSource

/-- The coordinate on the actual positive-radius Cauchy circle, after theta=d*t. -/
noncomputable def circleCoordinate (N : ℕ /- [definition] -/)
    (β t : ℝ /- [definition] -/) : ℂ :=
  (((1-β*saddleScale N : ℝ) : ℂ)*
    Complex.exp ((saddleScale N : ℂ)*Complex.I*t)-1)/(saddleScale N : ℂ)

lemma circle_coordinate_source (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β t : ℝ /- [definition] -/) :
    saddleCoordinate N (circleCoordinate N β t) =
      (circleRadius N β : ℂ)*Complex.exp ((saddleScale N*t : ℝ)*Complex.I) := by
  have hd : (saddleScale N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (saddle_scale_pos N hN))
  unfold saddleCoordinate circleCoordinate circleRadius
  push_cast
  rw [mul_div_cancel₀ _ hd]
  have ha : (saddleScale N : ℂ)*Complex.I*t = (saddleScale N : ℂ)*t*Complex.I := by ring
  rw [ha]
  ring

lemma circle_coordinate_decomposition (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β t : ℝ /- [definition] -/) :
    circleCoordinate N β t =
      (Complex.exp ((saddleScale N : ℂ)*Complex.I*t)-1)/(saddleScale N : ℂ) -
      (β : ℂ)*Complex.exp ((saddleScale N : ℂ)*Complex.I*t) := by
  have hd : (saddleScale N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (saddle_scale_pos N hN))
  unfold circleCoordinate
  push_cast
  field_simp
  ring

lemma circle_coordinate_tendsto (β t : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => circleCoordinate (n+1) β t) atTop
      (𝓝 (-(β : ℂ)+Complex.I*t)) := by
  have hd : Tendsto (fun n : ℕ => (saddleScale (n+1) : ℂ)) atTop (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp saddle_scale_tendsto
  have hdn : Tendsto (fun n : ℕ => (saddleScale (n+1) : ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd,Filter.Eventually.of_forall ?_⟩
    intro n
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (saddle_scale_pos (n+1) (by omega)))
  have hf : HasDerivAt (fun z : ℂ => Complex.exp (z*(Complex.I*t)))
      (Complex.I*t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (Complex.I*t)).cexp
  have hs := hf.tendsto_slope_zero.comp hdn
  have hq : Tendsto (fun n : ℕ =>
      (Complex.exp ((saddleScale (n+1) : ℂ)*Complex.I*t)-1)/(saddleScale (n+1) : ℂ))
      atTop (𝓝 (Complex.I*t)) := by
    simpa [Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hs
  have he : Tendsto (fun n : ℕ => Complex.exp ((saddleScale (n+1) : ℂ)*Complex.I*t))
      atTop (𝓝 1) := by
    simpa [Function.comp_def] using Complex.continuous_exp.continuousAt.tendsto.comp
      ((hd.mul_const Complex.I).mul_const (t : ℂ))
  have hh := hq.sub (he.const_mul (β : ℂ))
  simp only [mul_one] at hh
  convert hh using 1
  · funext n
    exact circle_coordinate_decomposition _ (by omega) β t
  · ring

lemma circle_coordinate_zero (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β : ℝ /- [definition] -/) :
    circleCoordinate N β 0 = -(β : ℂ) := by
  rw [circle_coordinate_decomposition N hN]
  simp

lemma circle_domain_exhausts (t : ℝ /- [definition] -/) :
    ∀ᶠ n : ℕ in atTop, |saddleScale (n+1)*t| < Real.pi := by
  have h : Tendsto (fun n : ℕ => |saddleScale (n+1)*t|) atTop (𝓝 0) := by
    simpa using (saddle_scale_tendsto.mul_const t).abs
  exact h.eventually (gt_mem_nhds Real.pi_pos)

/-- Moving-coordinate version of the proved compact cubic phase estimate. -/
theorem circle_phase_tendsto (β x t : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => saddlePhase (n+1) x (circleCoordinate (n+1) β t)) atTop
      (𝓝 ((x : ℂ)*(-(β : ℂ)+Complex.I*t)-(-(β : ℂ)+Complex.I*t)^3/3)) := by
  let u : ℂ := -(β : ℂ)+Complex.I*t
  let R : ℝ := ‖u‖+1
  have hu := circle_coordinate_tendsto β t
  have hb : ∀ᶠ n : ℕ in atTop, ‖circleCoordinate (n+1) β t‖ ≤ R := by
    filter_upwards [hu.norm.eventually (gt_mem_nhds (show ‖u‖ < R by dsimp [R]; linarith))]
      with n hn
    exact hn.le
  have herr : Tendsto (fun n : ℕ =>
      saddlePhase (n+1) x (circleCoordinate (n+1) β t) -
      ((x : ℂ)*circleCoordinate (n+1) β t-(circleCoordinate (n+1) β t)^3/3))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hb,saddle_phase_locally_uniform R (by dsimp [R]; positivity) ε hε]
      with n hn he
    simpa only [dist_zero_right] using he x (circleCoordinate (n+1) β t) hn
  have hc := (hu.const_mul (x : ℂ)).sub ((hu.pow 3).div_const (3 : ℂ))
  have ha := herr.add hc
  simpa only [sub_add_cancel,zero_add] using ha

theorem circle_exp_tendsto (β x t : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => Complex.exp (saddlePhase (n+1) x (circleCoordinate (n+1) β t)))
      atTop (𝓝 (Complex.exp ((x : ℂ)*(-(β : ℂ)+Complex.I*t)-
        (-(β : ℂ)+Complex.I*t)^3/3))) :=
  Complex.continuous_exp.continuousAt.tendsto.comp (circle_phase_tendsto β x t)

/-- Complete nondegenerate growing source example, with no asymptotic binder. -/
theorem circle_coordinate_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < saddleScale (n+1) ∧
      circleCoordinate (n+1) 1 0 = -1 ∧
      saddleCoordinate (n+1) (circleCoordinate (n+1) 1 1) =
        (circleRadius (n+1) 1 : ℂ)*Complex.exp ((saddleScale (n+1) : ℂ)*Complex.I)) ∧
    Tendsto (fun n : ℕ => circleCoordinate (n+1) 1 1) atTop (𝓝 (-1+Complex.I)) ∧
    (∀ᶠ n : ℕ in atTop, |saddleScale (n+1)| < Real.pi) ∧
    Tendsto (fun n : ℕ => Complex.exp (saddlePhase (n+1) 1 (circleCoordinate (n+1) 1 1)))
      atTop (𝓝 (Complex.exp ((-1+Complex.I)-(-1+Complex.I)^3/3))) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,fun n => ?_,?_,?_,?_⟩
  · exact ⟨saddle_scale_pos _ (by omega),by simpa using circle_coordinate_zero (n+1) (by omega) 1,
      by simpa using circle_coordinate_source (n+1) (by omega) 1 1⟩
  · simpa using circle_coordinate_tendsto 1 1
  · simpa using circle_domain_exhausts 1
  · simpa using circle_exp_tendsto 1 1 1
end RMTFoundations.TracyWidom.HermiteCircleCoordinate

#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circleCoordinate
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_coordinate_source
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_coordinate_decomposition
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_coordinate_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_coordinate_zero
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_domain_exhausts
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_phase_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_exp_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCircleCoordinate.circle_coordinate_joint_probe
