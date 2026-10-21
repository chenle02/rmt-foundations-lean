import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.PerturbedAiryStability
open Set Real Filter Topology

/-- Quantitative stability for second-order scalar ODEs. The inhomogeneous
coefficient forcing is bounded using the reference solution only. -/
theorem coefficient_stability
    (u v g h q r : ℝ → ℝ /- [definition] -/)
    (a b δ K η M : ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t * u t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t * g t) t /- [standing] -/)
    (hK : 1 ≤ K /- [standing] -/)
    (hη : 0 ≤ η /- [standing] -/)
    (hM : 0 ≤ M /- [standing] -/)
    (hq : ∀ t ∈ Icc a b, |q t| ≤ K /- [standing] -/)
    (hqr : ∀ t ∈ Icc a b, |q t - r t| ≤ η /- [standing] -/)
    (hgb : ∀ t ∈ Icc a b, |g t| ≤ M /- [standing] -/)
    (ha : max |u a - g a| |v a - h a| ≤ δ /- [standing] -/) :
    ∀ t ∈ Icc a b, max |u t - g t| |v t - h t| ≤
      gronwallBound δ K (η * M) (t-a) := by
  let f : ℝ → ℝ × ℝ := fun t => (u t - g t, v t - h t)
  let f' : ℝ → ℝ × ℝ := fun t => (v t - h t, q t * u t - r t * g t)
  have hd (t : ℝ) : HasDerivAt f (f' t) t :=
    ((hu t).sub (hg t)).prodMk ((hv t).sub (hh t))
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hn (t : ℝ) : ‖f t‖ = max |u t-g t| |v t-h t| := by
    simp [f, Prod.norm_def, Real.norm_eq_abs]
  have hn' (t : ℝ) : ‖f' t‖ = max |v t-h t| |q t*u t-r t*g t| := by
    simp [f', Prod.norm_def, Real.norm_eq_abs]
  have hb (t : ℝ) (ht : t ∈ Ico a b) : ‖f' t‖ ≤ K * ‖f t‖ + η * M := by
    have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have hfn : 0 ≤ ‖f t‖ := norm_nonneg _
    have hK0 : 0 ≤ K := by linarith
    have hh0 : |v t - h t| ≤ ‖f t‖ := by rw [hn]; exact le_max_right _ _
    have hu0 : |u t - g t| ≤ ‖f t‖ := by rw [hn]; exact le_max_left _ _
    rw [hn']
    apply max_le
    · nlinarith [mul_nonneg hη hM]
    · calc
        |q t*u t-r t*g t| = |q t*(u t-g t)+(q t-r t)*g t| := by congr 1; ring
        _ ≤ |q t*(u t-g t)| + |(q t-r t)*g t| := abs_add_le _ _
        _ = |q t| * |u t-g t| + |q t-r t| * |g t| := by rw [abs_mul,abs_mul]
        _ ≤ K * ‖f t‖ + η * M := by
          exact add_le_add
            (mul_le_mul (hq t ht') hu0 (abs_nonneg _) hK0)
            (mul_le_mul (hqr t ht') (hgb t ht') (abs_nonneg _) hη)
  have H := norm_le_gronwallBound_of_norm_deriv_right_le (δ := δ) (a := a) (b := b) hc.continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) (by simpa only [hn] using ha) hb
  intro t ht
  simpa only [hn] using H t ht

/-- A single Cauchy datum at zero controls both directions of a compact interval. -/
theorem coefficient_stability_symmetric
    (u v g h q r : ℝ → ℝ /- [definition] -/)
    (R δ K η M : ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t * u t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t * g t) t /- [standing] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hδ : 0 ≤ δ /- [standing] -/)
    (hK : 1 ≤ K /- [standing] -/)
    (hη : 0 ≤ η /- [standing] -/)
    (hM : 0 ≤ M /- [standing] -/)
    (hq : ∀ t, |t| ≤ R → |q t| ≤ K /- [standing] -/)
    (hqr : ∀ t, |t| ≤ R → |q t - r t| ≤ η /- [standing] -/)
    (hgb : ∀ t, |t| ≤ R → |g t| ≤ M /- [standing] -/)
    (ha : max |u 0 - g 0| |v 0 - h 0| ≤ δ /- [standing] -/) :
    ∀ t, |t| ≤ R → max |u t - g t| |v t - h t| ≤
      gronwallBound δ K (η*M) R := by
  have hb := gronwallBound_mono hδ (mul_nonneg hη hM) (show 0 ≤ K by linarith)
  intro t ht
  by_cases h0 : 0 ≤ t
  · have H := coefficient_stability u v g h q r 0 R δ K η M hu hv hg hh hK hη hM
      (fun x hx => hq x (by rw [abs_of_nonneg hx.1]; exact hx.2))
      (fun x hx => hqr x (by rw [abs_of_nonneg hx.1]; exact hx.2))
      (fun x hx => hgb x (by rw [abs_of_nonneg hx.1]; exact hx.2)) ha
    have Ht : max |u t-g t| |v t-h t| ≤ gronwallBound δ K (η*M) t := by
      simpa using H t ⟨h0,(abs_le.mp ht).2⟩
    exact Ht.trans (hb (abs_le.mp ht).2)
  · have ht0 : 0 ≤ -t := by linarith
    have ud (x : ℝ) : HasDerivAt (fun x => u (-x)) (-v (-x)) x := by
      simpa only [Function.comp_def,mul_neg,mul_one] using (hu (-x)).comp x (hasDerivAt_neg x)
    have vd (x : ℝ) : HasDerivAt (fun x => -v (-x)) (q (-x)*u (-x)) x := by
      simpa only [Function.comp_def,mul_neg,mul_one,neg_neg,Pi.neg_apply] using ((hv (-x)).comp x (hasDerivAt_neg x)).fun_neg
    have gd (x : ℝ) : HasDerivAt (fun x => g (-x)) (-h (-x)) x := by
      simpa only [Function.comp_def,mul_neg,mul_one] using (hg (-x)).comp x (hasDerivAt_neg x)
    have hd (x : ℝ) : HasDerivAt (fun x => -h (-x)) (r (-x)*g (-x)) x := by
      simpa only [Function.comp_def,mul_neg,mul_one,neg_neg,Pi.neg_apply] using ((hh (-x)).comp x (hasDerivAt_neg x)).fun_neg
    have hneg (c d : ℝ) : |-c - -d| = |c-d| := by
      rw [show -c - -d = -(c-d) by ring,abs_neg]
    have H := coefficient_stability (fun x => u (-x)) (fun x => -v (-x))
      (fun x => g (-x)) (fun x => -h (-x)) (fun x => q (-x)) (fun x => r (-x))
      0 R δ K η M ud vd gd hd hK hη hM
      (fun x hx => hq (-x) (by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2))
      (fun x hx => hqr (-x) (by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2))
      (fun x hx => hgb (-x) (by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2))
      (by simpa only [neg_zero,hneg] using ha)
    have Ht := H (-t) ⟨ht0,by linarith [(abs_le.mp ht).1]⟩
    simp only [neg_neg,hneg,sub_zero] at Ht
    exact Ht.trans (hb (by linarith [(abs_le.mp ht).1]))

/-- Vanishing coefficient and Cauchy-data errors imply compact C1 convergence.
The generic implication has a complete nonzero joint witness below. -/
theorem coefficient_stability_locally_uniform
    (u v q : ℕ → ℝ → ℝ /- [definition] -/)
    (g h r : ℝ → ℝ /- [definition] -/)
    (δ η : ℕ → ℝ /- [definition] -/)
    (R K M : ℝ /- [definition] -/)
    (hu : ∀ n t, HasDerivAt (u n) (v n t) t /- [standing] -/)
    (hv : ∀ n t, HasDerivAt (v n) (q n t*u n t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t*g t) t /- [standing] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hK : 1 ≤ K /- [standing] -/)
    (hM : 0 ≤ M /- [standing] -/)
    (hδ : ∀ n, 0 ≤ δ n /- [standing] -/)
    (hη : ∀ n, 0 ≤ η n /- [standing] -/)
    (hq : ∀ n t, |t| ≤ R → |q n t| ≤ K /- [standing] -/)
    (hqr : ∀ n t, |t| ≤ R → |q n t-r t| ≤ η n /- [standing] -/)
    (hgb : ∀ t, |t| ≤ R → |g t| ≤ M /- [standing] -/)
    (ha : ∀ n, max |u n 0-g 0| |v n 0-h 0| ≤ δ n /- [standing] -/)
    (hδlim : Tendsto δ atTop (𝓝 0) /- [standing] -/)
    (hηlim : Tendsto η atTop (𝓝 0) /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ t, |t| ≤ R → max |u n t-g t| |v n t-h t| < ε := by
  have hK0 : K ≠ 0 := by linarith
  have hlim : Tendsto (fun n => gronwallBound (δ n) K (η n*M) R) atTop (𝓝 0) := by
    simp only [gronwallBound,if_neg hK0]
    have H := (hδlim.mul_const (exp (K*R))).add
      (((hηlim.mul_const M).div_const K).mul_const (exp (K*R)-1))
    simpa using H
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn t ht
  exact lt_of_le_of_lt (coefficient_stability_symmetric (u n) (v n) g h (q n) r
    R (δ n) K (η n) M (hu n) (hv n) hg hh hR (hδ n) hK (hη n) hM
    (hq n) (hqr n) hgb (ha n) t ht) hn

/-- Complete joint witness for the convergence theorem. The approximants are
nonzero exponentials with genuinely different initial values at every finite n. -/
theorem convergence_joint_probe (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ t, |t| ≤ 1 →
      max |(1+((n+1:ℕ):ℝ)^(-1:ℝ))*exp t-exp t|
        |(1+((n+1:ℕ):ℝ)^(-1:ℝ))*exp t-exp t| < ε := by
  let δ : ℕ → ℝ := fun n => ((n+1:ℕ):ℝ)^(-1:ℝ)
  have hδ (n : ℕ) : 0 ≤ δ n := by dsimp [δ]; positivity
  have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto δ atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0:ℝ)<1 by norm_num)).comp hn
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (fun t => (1+δ n)*exp t)
      ((1+δ n)*exp t) t := (hasDerivAt_exp t).const_mul _
  exact coefficient_stability_locally_uniform
    (fun n t => (1+δ n)*exp t) (fun n t => (1+δ n)*exp t) (fun _ _ => 1)
    exp exp (fun _ => 1) δ (fun _ => 0) 1 1 (exp 1)
    hd (by simpa using hd) hasDerivAt_exp (by simpa using hasDerivAt_exp)
    (by norm_num) (by norm_num) (exp_pos _).le hδ (by intro n; norm_num)
    (by intro n t ht; norm_num) (by intro n t ht; norm_num)
    (by intro t ht; rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (abs_le.mp ht).2)
    (by intro n; simpa [exp_zero,abs_of_nonneg (hδ n)] using (le_rfl : δ n ≤ δ n))
    hlim tendsto_const_nhds ε hε

/-- All analytic inputs supplied jointly on a nonzero growing exponential family. -/
theorem coefficient_stability_joint_probe (n : ℕ /- [definition] -/) :
    ∀ t ∈ Icc (0:ℝ) 1,
      max |((n+2:ℕ):ℝ)*exp t-exp t| |((n+2:ℕ):ℝ)*exp t-exp t| ≤
        gronwallBound (n+1) 1 0 t := by
  have hd (t : ℝ) : HasDerivAt (fun x => ((n+2:ℕ):ℝ)*exp x)
      (((n+2:ℕ):ℝ)*exp t) t := (Real.hasDerivAt_exp t).const_mul _
  have H := coefficient_stability
    (fun t => ((n+2:ℕ):ℝ)*exp t) (fun t => ((n+2:ℕ):ℝ)*exp t)
    exp exp (fun _ => 1) (fun _ => 1) 0 1 (n+1) 1 0 (exp 1)
    hd (by simpa using hd) Real.hasDerivAt_exp (by simpa using Real.hasDerivAt_exp)
    (by norm_num) (by norm_num) (exp_pos _).le
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    (by intro t ht; rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr ht.2)
    (by
      have hc : ((n+2:ℕ):ℝ)-1 = (n:ℝ)+1 := by push_cast; ring
      simp only [exp_zero,mul_one,max_self]
      rw [hc,abs_of_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity)])
  simpa using H
end RMTFoundations.TracyWidom.PerturbedAiryStability

#print axioms RMTFoundations.TracyWidom.PerturbedAiryStability.coefficient_stability
#print axioms RMTFoundations.TracyWidom.PerturbedAiryStability.coefficient_stability_symmetric
#print axioms RMTFoundations.TracyWidom.PerturbedAiryStability.coefficient_stability_locally_uniform
#print axioms RMTFoundations.TracyWidom.PerturbedAiryStability.convergence_joint_probe
#print axioms RMTFoundations.TracyWidom.PerturbedAiryStability.coefficient_stability_joint_probe
