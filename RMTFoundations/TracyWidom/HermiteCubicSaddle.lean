import RMTFoundations.TracyWidom.HermiteEdgeScale
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCubicSaddle
open Filter Topology Complex
open RMTFoundations.TracyWidom.HermiteEdgeScale

/-- The principal-log remainder after the actual cubic coalescing-saddle term. -/
noncomputable def logRemainder (z : ℂ /- [definition] -/) : ℂ :=
  Complex.log (1+z)-z+z^2/2-z^3/3

lemma log_remainder_zero : logRemainder 0 = 0 := by simp [logRemainder]

lemma log_remainder_has_deriv (z : ℂ /- [definition] -/)
    (hz : ‖z‖ < 1 /- [standing] -/) :
    HasDerivAt logRemainder (-z^3/(1+z)) z := by
  have hm := Complex.mem_slitPlane_of_norm_lt_one hz
  have hn := Complex.slitPlane_ne_zero hm
  have h := ((((hasDerivAt_id z).const_add 1).clog hm).sub (hasDerivAt_id z)).add
    (((hasDerivAt_id z).pow 2).div_const 2)
  have hh := h.sub (((hasDerivAt_id z).pow 3).div_const 3)
  apply hh.congr_deriv
  simp only [id_eq]
  field_simp [hn]
  <;> ring

/-- Complex fourth-order remainder, proved on the whole closed half-radius disk.
The branch premise is derived throughout the disk rather than assumed. -/
theorem log_remainder_bound (z : ℂ /- [definition] -/)
    (hz : ‖z‖ ≤ 1/2 /- [standing] -/) :
    ‖logRemainder z‖ ≤ 2*‖z‖^4 := by
  have hd : ∀ y ∈ Metric.closedBall (0 : ℂ) ‖z‖,
      HasDerivWithinAt logRemainder (-y^3/(1+y)) (Metric.closedBall 0 ‖z‖) y := by
    intro y hy
    have hy' : ‖y‖ ≤ ‖z‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    exact (log_remainder_has_deriv y (by linarith)).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall (0 : ℂ) ‖z‖,
      ‖-y^3/(1+y)‖ ≤ 2*‖z‖^3 := by
    intro y hy
    have hy' : ‖y‖ ≤ ‖z‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hl : 1/2 ≤ ‖(1 : ℂ)+y‖ := by
      have hh : 1-‖y‖ ≤ ‖(1 : ℂ)+y‖ := by
        simpa only [norm_one,norm_neg,sub_neg_eq_add] using norm_sub_norm_le (1 : ℂ) (-y)
      linarith
    rw [norm_div, norm_neg, norm_pow]
    calc
      _ ≤ ‖z‖^3 / (1/2) := by gcongr
      _ = _ := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x := (0 : ℂ)) (y := z) hd hb
    (convex_closedBall (0 : ℂ) ‖z‖)
    (Metric.mem_closedBall_self (norm_nonneg z))
    (by simp [Metric.mem_closedBall, dist_eq_norm])
  simpa only [log_remainder_zero, sub_zero, mul_assoc, ← pow_succ] using h

noncomputable def saddleScale (N : ℕ /- [definition] -/) : ℝ :=
  (N : ℝ)^(-1/3 : ℝ)

lemma saddle_scale_pos (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : 0 < saddleScale N := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

lemma saddle_scale_cube (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : (N : ℝ)*(saddleScale N)^3 = 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [saddleScale, ← Real.rpow_mul_natCast hn.le]
  norm_num
  rw [Real.rpow_neg_one]
  exact mul_inv_cancel₀ (ne_of_gt hn)

/-- Literal rescaled coalescing-saddle phase after subtracting its constant. -/
noncomputable def saddlePhase (N : ℕ /- [definition] -/)
    (x u : ℂ /- [definition] -/) : ℂ :=
  x*u+(N : ℂ)*((saddleScale N : ℂ)*u-((saddleScale N : ℂ)*u)^2/2-
    Complex.log (1+(saddleScale N : ℂ)*u))

/-- Exact cubic term and signed remainder, no asymptotic premise. -/
lemma saddle_phase_cubic_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x u : ℂ /- [definition] -/) :
    saddlePhase N x u-(x*u-u^3/3) =
      -(N : ℂ)*logRemainder ((saddleScale N : ℂ)*u) := by
  have hc : (N : ℂ)*(saddleScale N : ℂ)^3 = 1 := by
    exact_mod_cast saddle_scale_cube N hN
  unfold saddlePhase logRemainder
  linear_combination -(u^3/3)*hc

/-- Quantitative uniform complex cubic phase approximation on bounded scaled windows. -/
theorem saddle_phase_compact_error (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hsmall : saddleScale N*R ≤ 1/2 /- [standing] -/)
    (x u : ℂ /- [definition] -/)
    (hu : ‖u‖ ≤ R /- [standing] -/) :
    ‖saddlePhase N x u-(x*u-u^3/3)‖ ≤ 2*saddleScale N*R^4 := by
  have hd := (saddle_scale_pos N hN).le
  have hn : (0 : ℝ) ≤ N := by positivity
  have hnrm : ‖(saddleScale N : ℂ)*u‖ = saddleScale N*‖u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
  have hz : ‖(saddleScale N : ℂ)*u‖ ≤ 1/2 := by rw [hnrm]; nlinarith
  rw [saddle_phase_cubic_identity N hN, norm_mul, norm_neg, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)*(2*‖(saddleScale N : ℂ)*u‖^4) := by
      exact mul_le_mul_of_nonneg_left (log_remainder_bound _ hz) hn
    _ ≤ (N : ℝ)*(2*(saddleScale N*R)^4) := by rw [hnrm]; gcongr
    _ = _ := by linear_combination (2*saddleScale N*R^4)*(saddle_scale_cube N hN)

lemma saddle_scale_tendsto :
    Tendsto (fun n : ℕ => saddleScale (n+1)) atTop (𝓝 0) := by
  simpa [saddleScale,Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/3 by norm_num)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Uniform on every bounded complex u-window, with x arbitrary and all branch conditions supplied. -/
theorem saddle_phase_locally_uniform (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x u : ℂ, ‖u‖ ≤ R →
      ‖saddlePhase (n+1) x u-(x*u-u^3/3)‖ < ε := by
  have hsmalllim : Tendsto (fun n : ℕ => saddleScale (n+1)*R) atTop (𝓝 0) := by
    simpa using saddle_scale_tendsto.mul_const R
  have hsmall : ∀ᶠ n : ℕ in atTop, saddleScale (n+1)*R < 1/2 :=
    hsmalllim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have herr : ∀ᶠ n : ℕ in atTop, 2*saddleScale (n+1)*R^4 < ε := by
    have hl := (saddle_scale_tendsto.const_mul 2).mul_const (R^4)
    have hh : Tendsto (fun n : ℕ => 2*saddleScale (n+1)*R^4) atTop (𝓝 0) := by simpa using hl
    exact hh.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall,herr] with n hs he x u hu
  exact lt_of_le_of_lt (saddle_phase_compact_error (n+1) (by omega) R hR hs.le x u hu) he

/-- Pointwise consequence of the proved compact phase convergence. -/
theorem saddle_phase_tendsto (x u : ℂ /- [definition] -/) :
    Tendsto (fun n : ℕ => saddlePhase (n+1) x u) atTop (𝓝 (x*u-u^3/3)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [saddle_phase_locally_uniform ‖u‖ (norm_nonneg u) ε hε] with n hn
  simpa only [dist_eq_norm] using hn x u (le_refl ‖u‖)

/-- The exact finite denominator remaining after the contour Jacobian. -/
noncomputable def saddleIntegrand (N : ℕ /- [definition] -/)
    (x u : ℂ /- [definition] -/) : ℂ :=
  Complex.exp (saddlePhase N x u)/(1+(saddleScale N : ℂ)*u)

/-- Actual cubic rescaled integrand converges, including its denominator.
This is not an interchange of an integral and a limit. -/
theorem saddle_integrand_tendsto (x u : ℂ /- [definition] -/) :
    Tendsto (fun n : ℕ => saddleIntegrand (n+1) x u) atTop
      (𝓝 (Complex.exp (x*u-u^3/3))) := by
  have hp := Complex.continuous_exp.continuousAt.tendsto.comp (saddle_phase_tendsto x u)
  have hd : Tendsto (fun n : ℕ => (saddleScale (n+1) : ℂ)) atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp saddle_scale_tendsto
  have he : Tendsto (fun n : ℕ => (1 : ℂ)+(saddleScale (n+1) : ℂ)*u) atTop (𝓝 1) := by
    simpa using (hd.mul_const u).const_add 1
  have hq := hp.div he (by norm_num : (1 : ℂ) ≠ 0)
  convert hq using 1
  · funext n
    rfl
  · simp only [div_one]

/-- Every finite premise is satisfied by a growing literal N and nonzero complex saddle coordinate.
The locally uniform assertion uses no assumed limit. -/
theorem cubic_saddle_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < saddleScale (n+1) ∧
      (n+1 : ℝ)*(saddleScale (n+1))^3 = 1 ∧
      let u : ℂ := Complex.I/4
      u ≠ 0 ∧ ‖logRemainder u‖ ≤ 2*‖u‖^4) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      0 < saddleScale (n+1) ∧ saddleScale (n+1)*3 ≤ 1/2 ∧
      ∀ x u : ℂ, ‖u‖ ≤ 3 →
        ‖saddlePhase (n+1) x u-(x*u-u^3/3)‖ < ε) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩, ?_, ?_⟩
  · intro n
    refine ⟨saddle_scale_pos (n+1) (by omega), ?_, ?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using saddle_scale_cube (n+1) (by omega)
    · dsimp only
      refine ⟨div_ne_zero Complex.I_ne_zero (by norm_num),log_remainder_bound _ ?_⟩
      norm_num [norm_div]
  · intro ε hε
    have hslim : Tendsto (fun n : ℕ => saddleScale (n+1)*3) atTop (𝓝 0) := by
      simpa using saddle_scale_tendsto.mul_const 3
    have hs : ∀ᶠ n : ℕ in atTop, saddleScale (n+1)*3 < 1/2 :=
      hslim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
    filter_upwards [hs,saddle_phase_locally_uniform 3 (by norm_num) ε hε] with n hn he
    exact ⟨saddle_scale_pos _ (by omega),hn.le,he⟩
/-- Nonzero pointwise-integrand witness on the same unbounded dimension family. -/
theorem saddle_integrand_joint_probe :
    (∀ n : ℕ, 0 < saddleScale (n+1) ∧ saddleIntegrand (n+1) 1 Complex.I ≠ 0) ∧
    Tendsto (fun n : ℕ => saddleIntegrand (n+1) 1 Complex.I) atTop
      (𝓝 (Complex.exp (Complex.I-Complex.I^3/3))) := by
  refine ⟨fun n => ?_,by simpa using saddle_integrand_tendsto 1 Complex.I⟩
  have hw : (1 : ℂ)+(saddleScale (n+1) : ℂ)*Complex.I ≠ 0 := by
    intro hh
    have hp := congrArg Complex.re hh
    simp [Complex.mul_re] at hp
  exact ⟨saddle_scale_pos (n+1) (by omega),
    div_ne_zero (Complex.exp_ne_zero _) hw⟩
end RMTFoundations.TracyWidom.HermiteCubicSaddle

#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.logRemainder
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.log_remainder_zero
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.log_remainder_has_deriv
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.log_remainder_bound
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddleScale
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_scale_pos
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_scale_cube
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddlePhase
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_phase_cubic_identity
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_phase_compact_error
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_scale_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_phase_locally_uniform
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_phase_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddleIntegrand
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_integrand_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.cubic_saddle_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteCubicSaddle.saddle_integrand_joint_probe
