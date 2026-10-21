import RMTFoundations.TracyWidom.HermiteKernelLimit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HermiteFredholmLimit
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TracyWidom.HermiteKernelLimit RMTFoundations.TracyWidom.HermiteKernelIntegral
open RMTFoundations.TracyWidom.HermiteEdgeKernel RMTFoundations.TracyWidom.HermiteEdgeODE RMTFoundations.TracyWidom.GUEHermite

/-- The true scaled Hermite projection has a common full-halfline exponential bound. -/
theorem scaledKernel_shift_uniform_bound (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |scaledKernel (n+2) (x+s) (y+s)| ≤
        C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y) := by
  obtain ⟨D,hD,hb⟩ := adjacentPair_shift_uniform_bound s
  refine ⟨D^2,by positivity,?_⟩
  intro n x y hx hy
  have hi := adjacentPair_integrable (n+2) (by omega) (x+s) (y+s)
  have heint : (∫ u, Real.exp (-u) ∂halfLineMeasure) = 1 := by
    change (∫ u in Ioi (0:ℝ), Real.exp (-u)) = 1
    have hh := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
    simpa only [neg_one_mul,mul_zero,Real.exp_zero,neg_div,div_neg,div_one,neg_neg] using hh
  have hm : Integrable (fun u : ℝ =>
      (2*D^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u)) halfLineMeasure := by
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul _
  rw [scaledKernel_eq_adjacent_integral (n+2) (by omega) (x+s) (y+s),abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc (1/2:ℝ)*|∫ u, adjacentPair (n+2) (x+s) (y+s) u ∂halfLineMeasure|
      ≤ (1/2:ℝ)*∫ u, |adjacentPair (n+2) (x+s) (y+s) u| ∂halfLineMeasure :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (adjacentPair (n+2) (x+s) (y+s))) (by norm_num)
    _ ≤ (1/2:ℝ)*∫ u, (2*D^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u) ∂halfLineMeasure := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae hi.abs hm
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      exact hb (n+2) (by omega) x y u hx hy hu.le
    _ = D^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y) := by
      rw [integral_const_mul,heint]
      ring


theorem positiveExtension_half_bound
    (k : ℝ → ℝ → ℝ /- [definition] -/)
    (C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |k x y| ≤ C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y) /- [standing] -/) :
    ∀ x y : ℝ, |positiveExtension k x y| ≤
      C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y) := by
  intro x y
  unfold positiveExtension
  split_ifs with h
  · exact hb x y h.1 h.2
  · simp only [abs_zero]
    positivity

noncomputable def scaledHermiteKernel
    (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : ℝ → ℝ → ℝ :=
  positiveExtension (fun x y => scaledKernel (n+2) (x+s) (y+s))

theorem scaledHermiteKernel_measurable
    (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    Measurable (Function.uncurry (scaledHermiteKernel n s)) := by
  apply positiveExtension_measurable
  apply Continuous.measurable
  change Continuous (fun p : ℝ × ℝ => RMTFoundations.TracyWidom.HermiteEdgeScale.edgeScale (n+2)*
    ∑ k : Fin (n+2), hermiteMode k.val (RMTFoundations.TracyWidom.HermiteEdgeScale.edgePoint (n+2) (p.1+s))*
      hermiteMode k.val (RMTFoundations.TracyWidom.HermiteEdgeScale.edgePoint (n+2) (p.2+s)))
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro k _
  have hm : Continuous (hermiteMode k.val) := continuous_iff_continuousAt.mpr
    (fun x => (hermiteMode_hasDerivAt k.val x).continuousAt)
  unfold RMTFoundations.TracyWidom.HermiteEdgeScale.edgePoint
  apply Continuous.mul <;> apply hm.comp <;> fun_prop

/-- Fredholm-series passage for the literal finite-N Hermite projection, at every coupling.
This theorem makes no unproved finite-N matrix-eigenvalue probability identification. -/
theorem scaledHermiteKernel_fredholm_tendsto
    (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    Tendsto (fun n : ℕ => kernelFredholm halfLineMeasure (scaledHermiteKernel n s) z)
      atTop (𝓝 (kernelFredholm halfLineMeasure (K_fredholmKernel s) z)) := by
  obtain ⟨C,hC,hb⟩ := scaledKernel_shift_uniform_bound s
  apply kernelFredholm_tendsto_of_minor_bound halfLineMeasure atTop
    (fun n => scaledHermiteKernel n s) (K_fredholmKernel s)
    (fun x => Real.exp (-(1/2:ℝ)*x)) C hC.le
    ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).integrable_sq)
  · exact Eventually.of_forall fun n => scaledHermiteKernel_measurable n s
  · apply Eventually.of_forall
    intro n d x
    exact weighted_kernel_minor_bound_pow d (scaledHermiteKernel n s) C
      (fun u => Real.exp (-(1/2:ℝ)*u)) x hC.le (fun _ => Real.exp_nonneg _)
      (positiveExtension_half_bound _ C hC.le (hb n))
  · intro x y
    by_cases hxy : 0 ≤ x ∧ 0 ≤ y
    · simp only [scaledHermiteKernel,K_fredholmKernel,positiveExtension,if_pos hxy]
      exact scaledKernel_shift_tendsto s x y hxy.1 hxy.2
    · simp only [scaledHermiteKernel,K_fredholmKernel,positiveExtension,if_neg hxy]
      exact tendsto_const_nhds

/-- The one-time finite Hermite Fredholm determinants converge to the TW2R. -/
theorem scaledHermiteKernel_gap_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => (kernelFredholm halfLineMeasure (scaledHermiteKernel n s) (-1)).re)
      atTop (𝓝 (TW2R s)) := by
  have ht := scaledHermiteKernel_fredholm_tendsto s (-1)
  rw [K_fredholm_physical s (-1)] at ht
  simpa only [TW2,TW2R,Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

/-- Full asymptotic Fredholm joint example uses actual growing, nondegenerate Hermite data. -/
theorem fredholm_complete_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    (∀ n : ℕ, 0 < hermiteDensity (n+2) (fun i => (i.val : ℝ))) ∧
    (∀ n : ℕ, Measurable (Function.uncurry (scaledHermiteKernel n (-1)))) ∧
    (∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        |scaledKernel (n+2) (x-1) (y-1)| ≤ C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y)) ∧
      (∀ n : ℕ, ∀ x y : ℝ,
        |scaledHermiteKernel n (-1) x y| ≤ C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y)) ∧
      (∀ n d : ℕ, ∀ x : Fin d → ℝ, |kernelMinor (scaledHermiteKernel n (-1)) d x| ≤
        (Real.sqrt d*C)^d*∏ i, (Real.exp (-(1/2:ℝ)*x i))^2)) ∧
    Integrable (fun x : ℝ => (Real.exp (-(1/2:ℝ)*x))^2) halfLineMeasure ∧
    (∀ x y : ℝ, Tendsto (fun n : ℕ => scaledHermiteKernel n (-1) x y)
      atTop (𝓝 (K_fredholmKernel (-1) x y))) ∧
    Tendsto (fun n : ℕ => (kernelFredholm halfLineMeasure (scaledHermiteKernel n (-1)) (-1)).re)
      atTop (𝓝 (TW2R (-1))) := by
  obtain ⟨C,hC,hb⟩ := scaledKernel_shift_uniform_bound (-1)
  refine ⟨airyAiReal_zero_pos.ne',fun n => hermite_density_all_binder_joint_probe.2 (n+1),
    fun n => scaledHermiteKernel_measurable n (-1),⟨C,hC,?_,?_,?_⟩,
    (memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).integrable_sq,?_,
    scaledHermiteKernel_gap_tendsto (-1)⟩
  · intro n x y hx hy
    simpa only [sub_eq_add_neg] using hb n x y hx hy
  · intro n
    exact positiveExtension_half_bound _ C hC.le (hb n)
  · intro n d x
    exact weighted_kernel_minor_bound_pow d (scaledHermiteKernel n (-1)) C
      (fun u => Real.exp (-(1/2:ℝ)*u)) x hC.le (fun _ => Real.exp_nonneg _)
      (positiveExtension_half_bound _ C hC.le (hb n))
  · intro x y
    by_cases hxy : 0 ≤ x ∧ 0 ≤ y
    · simp only [scaledHermiteKernel,K_fredholmKernel,positiveExtension,if_pos hxy]
      exact scaledKernel_shift_tendsto (-1) x y hxy.1 hxy.2
    · simp only [scaledHermiteKernel,K_fredholmKernel,positiveExtension,if_neg hxy]
      exact tendsto_const_nhds

end RMTFoundations.TracyWidom.HermiteFredholmLimit

#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.scaledKernel_shift_uniform_bound
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.scaledHermiteKernel
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.scaledHermiteKernel_measurable
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.scaledHermiteKernel_fredholm_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.scaledHermiteKernel_gap_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.fredholm_complete_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteFredholmLimit.positiveExtension_half_bound
