import Challenge.Reference.Analysis.HalfPlane
import Challenge.Reference.Measure.StieltjesInversion
import Mathlib

namespace RMTFoundations.HerglotzBorelProof

open MeasureTheory Filter Topology Set Metric Real BoundedContinuousFunction

section Disk

variable {f : ℂ → ℂ /- [definition] -/ }

/-- `ζ ↦ f(rζ)` is differentiable on a neighbourhood of the closed unit disk. -/
theorem diffContOnCl_scale (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ )
    (hr1 : r < 1 /- [standing] -/ ) : DiffContOnCl ℂ (fun ζ => f ((r : ℂ) * ζ)) (ball 0 1) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball 0 one_ne_zero]
  refine hf.comp (differentiableOn_const _ |>.mul differentiableOn_id) fun ζ hζ => ?_
  rw [mem_closedBall, dist_zero_right] at hζ
  rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  nlinarith [norm_nonneg ζ]

/-- `θ ↦ P(e^{iθ}, w)` is continuous for `|w| < 1`. -/
theorem continuous_poissonKernel_circle {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) :
    Continuous fun θ : ℝ => poissonKernel 0 w (circleMap 0 1 θ) := by
  simp only [poissonKernel_def]
  refine Continuous.div (by fun_prop) (by fun_prop) fun θ h0 => ?_
  have hne : circleMap 0 1 θ - 0 - (w - 0) ≠ 0 := by
    intro h1
    have : circleMap 0 1 θ = w := by simpa [sub_eq_zero] using h1
    rw [mem_ball, dist_zero_right, ← this, norm_circleMap_zero, abs_one] at hw
    exact lt_irrefl _ hw
  exact hne (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))

/-- `θ ↦ f(r e^{iθ})` is continuous for `r < 1`. -/
theorem continuous_scale_circle (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ )
    (hr1 : r < 1 /- [standing] -/ ) : Continuous fun θ : ℝ => f ((r : ℂ) * circleMap 0 1 θ) := by
  refine hf.continuousOn.comp_continuous (continuous_const.mul (continuous_circleMap 0 1))
    fun θ => ?_
  rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
    norm_circleMap_zero, abs_one, mul_one]
  exact hr1

/-- **Poisson formula for the real part on the circle of radius `r < 1`**, written as an
interval integral in `θ`. -/
theorem re_poisson (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ ) (hr1 : r < 1 /- [standing] -/ )
    {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) :
    (f ((r : ℂ) * w)).re = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      poissonKernel 0 w (circleMap 0 1 θ) * (f ((r : ℂ) * circleMap 0 1 θ)).re := by
  have h := (diffContOnCl_scale hf hr0 hr1).circleAverage_poissonKernel_smul hw
  have h2 := congrArg Complex.re h
  rw [← h2, Real.circleAverage_def]
  have hint : IntervalIntegrable (fun θ => (poissonKernel 0 w • fun ζ => f ((r : ℂ) * ζ))
      (circleMap 0 1 θ)) volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_poissonKernel_circle hw).smul
      (continuous_scale_circle hf hr0 hr1)
  rw [Complex.real_smul, Complex.re_ofReal_mul]
  congr 1
  have := (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint).symm
  rw [Complex.reCLM_apply] at this
  rw [this]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show (poissonKernel 0 w (circleMap 0 1 θ) • f ((r : ℂ) * circleMap 0 1 θ)).re = _
  rw [Complex.real_smul, Complex.re_ofReal_mul]

/-- `0 ≤ P(e^{iθ}, w) ≤ (1 + |w|)/(1 - |w|)`. -/
theorem poisson_bounds {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) (θ : ℝ /- [definition] -/ ) :
    0 ≤ poissonKernel 0 w (circleMap 0 1 θ) ∧
      poissonKernel 0 w (circleMap 0 1 θ) ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere, dist_zero_right, norm_circleMap_zero, abs_one]
  have hP : poissonKernel 0 w (circleMap 0 1 θ)
      = ((circleMap 0 1 θ - 0 + (w - 0)) / ((circleMap 0 1 θ - 0) - (w - 0))).re := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
  have h1 := le_re_herglotzRieszKernel hz hw
  have h2 := re_herglotzRieszKernel_le hz hw
  simp only [sub_zero] at h1 h2 hP
  have hwn : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  rw [hP]
  refine ⟨le_trans (div_nonneg (by linarith) (by positivity)) h1, h2⟩

/-- The Poisson kernel as a bounded continuous function of `θ`. -/
noncomputable def poissonBCF {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun θ => poissonKernel 0 w (circleMap 0 1 θ),
    continuous_poissonKernel_circle hw⟩ ((1 + ‖w‖) / (1 - ‖w‖)) fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      obtain ⟨a1, a2⟩ := poisson_bounds hw x
      obtain ⟨b1, b2⟩ := poisson_bounds hw y
      rw [abs_le]; constructor <;> linarith

/-- Evaluation of `poissonBCF`. -/
theorem poissonBCF_apply {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) (θ : ℝ /- [definition] -/ ) :
    poissonBCF hw θ = poissonKernel 0 w (circleMap 0 1 θ) := rfl

variable (f) in
/-- The approximating measure on `[0, 2π]`: `(2π)⁻¹ Re f(r e^{iθ}) dθ`. -/
noncomputable def sig (r : ℝ /- [definition] -/ ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * π))).withDensity
    fun θ => ENNReal.ofReal ((2 * π)⁻¹ * (f ((r : ℂ) * circleMap 0 1 θ)).re)

/-- Integrals against `sig f r` are weighted `θ`-integrals. -/
theorem integral_sig (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ )
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ ) (hr1 : r < 1 /- [standing] -/ )
    (g : ℝ → ℝ /- [definition] -/ ) :
    ∫ θ, g θ ∂(sig f r) = ∫ θ in (0 : ℝ)..2 * π,
      (2 * π)⁻¹ * (f ((r : ℂ) * circleMap 0 1 θ)).re * g θ := by
  have hmeas : Measurable fun θ : ℝ =>
      ENNReal.ofReal ((2 * π)⁻¹ * (f ((r : ℂ) * circleMap 0 1 θ)).re) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Complex.measurable_re.comp
        (continuous_scale_circle hf hr0 hr1).measurable))
  rw [sig, integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  have hnn : 0 ≤ (2 * π)⁻¹ * (f ((r : ℂ) * circleMap 0 1 θ)).re := by
    refine mul_nonneg (by positivity) (hre _ ?_)
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, norm_circleMap_zero, abs_one, mul_one]
    exact hr1
  rw [ENNReal.toReal_ofReal hnn, smul_eq_mul]

/-- `∫ P(e^{iθ}, w) d(sig f r) = Re f(r w)`. -/
theorem integral_sig_poisson (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ )
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ ) (hr1 : r < 1 /- [standing] -/ )
    {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) :
    ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂(sig f r) = (f ((r : ℂ) * w)).re := by
  rw [integral_sig hf hre hr0 hr1, re_poisson hf hr0 hr1 hw, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  ring

/-- `sig f r` is finite. -/
theorem sig_finite (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ )
    (hr1 : r < 1 /- [standing] -/ ) :
    IsFiniteMeasure (sig f r) := by
  refine isFiniteMeasure_withDensity_ofReal ?_
  refine (Integrable.hasFiniteIntegral ?_)
  have hc : Continuous fun θ : ℝ => (2 * π)⁻¹ * (f ((r : ℂ) * circleMap 0 1 θ)).re :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_scale_circle hf hr0 hr1))
  exact (hc.integrableOn_Icc (a := 0) (b := 2 * π)).mono_set Ioc_subset_Icc_self

/-- `sig f r` is supported on `[0, 2π]`. -/
theorem sig_support {r : ℝ /- [definition] -/ } : sig f r (Icc 0 (2 * π))ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  have : (Icc 0 (2 * π))ᶜ ∩ Ioc 0 (2 * π) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨h1, h2⟩
    exact h1 ⟨h2.1.le, h2.2⟩
  rw [this, measure_empty]

/-- `sig f r` has mass `Re f(0)`. -/
theorem sig_mass (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ )
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re /- [standing] -/ ) {r : ℝ /- [definition] -/ } (hr0 : 0 < r /- [standing] -/ ) (hr1 : r < 1 /- [standing] -/ ) :
    (sig f r).real univ = (f 0).re := by
  haveI := sig_finite hf hr0 hr1
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hP : ∀ θ, poissonKernel 0 0 (circleMap 0 1 θ) = 1 := by
    intro θ
    have hn : ‖circleMap 0 1 θ‖ = 1 := by rw [norm_circleMap_zero, abs_one]
    simp [poissonKernel_def, hn]
  have := integral_sig_poisson hf hre hr0 hr1 h0
  simp only [hP, mul_zero, integral_const, smul_eq_mul, mul_one] at this
  exact this

omit f in
/-- A cluster point of a convergent map is its limit (Hausdorff). -/
theorem eq_of_mapClusterPt_of_tendsto {α X : Type* /- [definition] -/ } [TopologicalSpace X /- [definition] -/ ] [T2Space X /- [definition] -/ ]
    {u : α → X /- [definition] -/ } {F : Filter α /- [definition] -/ } {a b : X /- [definition] -/ } (h1 : MapClusterPt b F u /- [standing] -/ ) (h2 : Tendsto u F (𝓝 a) /- [standing] -/ ) :
    b = a :=
  eq_of_nhds_neBot (h1.clusterPt.mono h2)

/-- **Herglotz representation of the real part on the disk.** If `f` is holomorphic on
the unit disk with `Re f ≥ 0`, there is a finite measure `σ` on `[0, 2π]` with
`Re f(w) = ∫ P(e^{iθ}, w) dσ(θ)`. The measures `(2π)⁻¹ Re f(r e^{iθ}) dθ` lie in a
compact set of finite measures (mass `Re f(0)`, support `[0, 2π]`); `σ` is a cluster
point as `r ↑ 1`, and the Poisson formula passes to the limit. -/
theorem disk_herglotz (hf : DifferentiableOn ℂ f (ball 0 1) /- [standing] -/ )
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re /- [standing] -/ ) :
    ∃ σ : FiniteMeasure ℝ, (σ : Measure ℝ) (Icc 0 (2 * π))ᶜ = 0 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        (f w).re = ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂(σ : Measure ℝ) := by
  classical
  let Sig : ℝ → FiniteMeasure ℝ := fun r =>
    if h : 0 < r ∧ r < 1 then ⟨sig f r, sig_finite hf h.1 h.2⟩ else 0
  have hSig : ∀ r (h : 0 < r ∧ r < 1), ((Sig r : FiniteMeasure ℝ) : Measure ℝ) = sig f r := by
    intro r h
    have heq : Sig r = ⟨sig f r, sig_finite hf h.1 h.2⟩ := dite_eq_left h
    exact congrArg FiniteMeasure.toMeasure heq
  set C : NNReal := (f 0).re.toNNReal
  set Kset : Set (FiniteMeasure ℝ) := {μ | μ.mass ≤ C ∧ μ (Icc 0 (2 * π))ᶜ = 0}
  have hK : IsCompact Kset := isCompact_setOf_finiteMeasure_le_of_isCompact C isCompact_Icc
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr using hr
  have hle : map Sig (𝓝[<] (1 : ℝ)) ≤ 𝓟 Kset := by
    rw [le_principal_iff, mem_map]
    filter_upwards [hev] with r hr
    haveI := sig_finite hf hr.1 hr.2
    refine ⟨?_, ?_⟩
    · rw [FiniteMeasure.mass]
      have hm := sig_mass hf hre hr.1 hr.2
      have heq : Sig r = ⟨sig f r, sig_finite hf hr.1 hr.2⟩ := dite_eq_left hr
      rw [heq]
      show (sig f r univ).toNNReal ≤ C
      rw [measureReal_def] at hm
      rw [show C = (f 0).re.toNNReal from rfl, ← hm, ENNReal.toReal, Real.toNNReal_coe]
    · have heq : Sig r = ⟨sig f r, sig_finite hf hr.1 hr.2⟩ := dite_eq_left hr
      rw [heq]
      show (sig f r (Icc 0 (2 * π))ᶜ).toNNReal = 0
      rw [sig_support, ENNReal.toNNReal_zero]
  obtain ⟨σ, hσK, hcl⟩ := hK.exists_clusterPt hle
  refine ⟨σ, ?_, fun w hw => ?_⟩
  · have := hσK.2
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, this, ENNReal.coe_zero]
  · let T : FiniteMeasure ℝ → ℝ := fun μ => ∫ θ, poissonBCF hw θ ∂(μ : Measure ℝ)
    have hT : Continuous T := FiniteMeasure.continuous_integral_boundedContinuousFunction _
    have hmc : MapClusterPt σ (𝓝[<] (1 : ℝ)) Sig := hcl
    have h2 := hmc.continuousAt_comp hT.continuousAt
    have hlim : Tendsto (T ∘ Sig) (𝓝[<] (1 : ℝ)) (𝓝 (f w).re) := by
      have hcont : Tendsto (fun r : ℝ => (f ((r : ℂ) * w)).re) (𝓝[<] (1 : ℝ)) (𝓝 (f w).re) := by
        have hfw : ContinuousAt f w := hf.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)
        have hmul : Tendsto (fun r : ℝ => (r : ℂ) * w) (𝓝 (1 : ℝ)) (𝓝 w) := by
          have : Continuous fun r : ℝ => (r : ℂ) * w := by fun_prop
          simpa using this.tendsto 1
        exact (Complex.continuous_re.continuousAt.tendsto.comp
          (hfw.tendsto.comp (hmul.mono_left nhdsWithin_le_nhds)))
      refine hcont.congr' ?_
      filter_upwards [hev] with r hr
      simp only [Function.comp_apply, T, poissonBCF_apply]
      rw [hSig r hr, integral_sig_poisson hf hre hr.1 hr.2 hw]
    have := eq_of_mapClusterPt_of_tendsto h2 hlim
    rw [← this]
    rfl

end Disk

section Cayley

open Complex

/-- The Cayley map `w ↦ i(1 + w)/(1 - w)` from the disk to the upper half-plane. -/
noncomputable def cay (w : ℂ /- [definition] -/ ) : ℂ := I * (1 + w) / (1 - w)

/-- Its inverse `z ↦ (z - i)/(z + i)`. -/
noncomputable def invcay (z : ℂ /- [definition] -/ ) : ℂ := (z - I) / (z + I)

/-- `Im cay(w) = (1 - |w|²)/|1 - w|²`. -/
theorem cay_im (w : ℂ /- [definition] -/ ) (hw : w ≠ 1 /- [standing] -/ ) :
    (cay w).im = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [cay, Complex.div_im, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  have hd : (1 - w.re) * (1 - w.re) + (0 - w.im) * (0 - w.im) ≠ 0 := by
    have := Complex.normSq_pos.mpr hne
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at this
    linarith
  field_simp
  ring

/-- Points of the open disk are not `1`. -/
theorem norm_lt_one_of_ne {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) : w ≠ 1 := by
  intro h; rw [h, mem_ball, dist_zero_right, norm_one] at hw; exact lt_irrefl _ hw

/-- `cay` maps the disk into `ℂ⁺`. -/
theorem cay_mem_upper {w : ℂ /- [definition] -/ } (hw : w ∈ ball (0 : ℂ) 1 /- [standing] -/ ) : cay w ∈ RMTFoundations.AnalyticHalfPlane.upper := by
  show 0 < (cay w).im
  rw [cay_im w (norm_lt_one_of_ne hw)]
  have h1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have h2 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (norm_lt_one_of_ne hw)))
  have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  positivity

/-- `z + i ≠ 0` on `ℂ⁺`. -/
theorem add_I_ne {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) : z + I ≠ 0 := by
  intro h; have := congrArg Complex.im h
  simp at this; have hz' : 0 < z.im := hz; linarith

/-- `invcay` maps `ℂ⁺` into the disk. -/
theorem invcay_mem_ball {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) :
    invcay z ∈ ball (0 : ℂ) 1 := by
  have hz' : 0 < z.im := hz
  rw [mem_ball, dist_zero_right, invcay, norm_div, div_lt_one (norm_pos_iff.mpr (add_I_ne hz))]
  have h1 : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- `cay ∘ invcay = id` on `ℂ⁺`. -/
theorem cay_invcay {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) : cay (invcay z) = z := by
  have h := add_I_ne hz
  have h2 : (1 : ℂ) - (z - I) / (z + I) ≠ 0 := by
    rw [one_sub_div h]; simp only [ne_eq, div_eq_zero_iff, h, or_false]
    intro h3; have : (2 : ℂ) * I = 0 := by linear_combination h3
    simp at this
  rw [cay, invcay]
  field_simp
  ring

/-- `invcay ∘ cay = id` off `1`. -/
theorem invcay_cay {ζ : ℂ /- [definition] -/ } (hζ : ζ ≠ 1 /- [standing] -/ ) : invcay (cay ζ) = ζ := by
  have hne : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  have hp : I * (1 + ζ) / (1 - ζ) + I = 2 * I / (1 - ζ) := by field_simp; ring
  have hm : I * (1 + ζ) / (1 - ζ) - I = 2 * I * ζ / (1 - ζ) := by field_simp; ring
  rw [invcay, cay, hp, hm]
  field_simp

/-- `cay` maps the unit circle minus `1` into `ℝ`. -/
theorem cay_real {ζ : ℂ /- [definition] -/ } (hζn : ‖ζ‖ = 1 /- [standing] -/ ) (hζ : ζ ≠ 1 /- [standing] -/ ) : cay ζ = ((cay ζ).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [cay_im ζ hζ, hζn]; simp

/-- **The Poisson kernel under the Cayley map**: for `z ∈ ℂ⁺` and `|ζ| = 1`, `ζ ≠ 1`,
with `t = cay ζ ∈ ℝ`, `P(ζ, invcay z) = (1 + t²) Im z / ((t - Re z)² + (Im z)²)`. -/
theorem poisson_cayley {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) {ζ : ℂ /- [definition] -/ } (hζn : ‖ζ‖ = 1 /- [standing] -/ )
    (hζ : ζ ≠ 1 /- [standing] -/ ) :
    poissonKernel 0 (invcay z) ζ
      = (1 + (cay ζ).re ^ 2) * z.im / (((cay ζ).re - z.re) ^ 2 + z.im ^ 2) := by
  have hz' : 0 < z.im := hz
  set t := (cay ζ).re with ht
  have hT : cay ζ = (t : ℂ) := cay_real hζn hζ
  have hζe : ζ = invcay (t : ℂ) := by rw [← hT, invcay_cay hζ]
  have hzI := add_I_ne hz
  have htI : (t : ℂ) + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hdiff : ζ - invcay z = 2 * I * ((t : ℂ) - z) / (((t : ℂ) + I) * (z + I)) := by
    rw [hζe, invcay, invcay]; field_simp; ring
  have hnw : ‖invcay z‖ ^ 2 = (z.re ^ 2 + (z.im - 1) ^ 2) / (z.re ^ 2 + (z.im + 1) ^ 2) := by
    rw [invcay, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp; ring
  have hnd : ‖ζ - invcay z‖ ^ 2
      = 4 * ((t - z.re) ^ 2 + z.im ^ 2) / ((t ^ 2 + 1) * (z.re ^ 2 + (z.im + 1) ^ 2)) := by
    rw [hdiff, Complex.sq_norm, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_mul]
    simp [Complex.normSq_apply]
    ring
  simp only [poissonKernel_def]
  simp only [sub_zero]
  rw [hζn, hnw, hnd]
  have h1 : 0 < z.re ^ 2 + (z.im + 1) ^ 2 := by positivity
  have h2 : 0 < (t - z.re) ^ 2 + z.im ^ 2 := by positivity
  field_simp
  ring

/-- At `ζ = 1` the kernel is `Im z`. -/
theorem poisson_cayley_one {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) :
    poissonKernel 0 (invcay z) 1 = z.im := by
  have hw := invcay_mem_ball hz
  have h := cay_im (invcay z) (norm_lt_one_of_ne hw)
  rw [cay_invcay hz] at h
  rw [h]
  simp only [poissonKernel_def]
  simp only [sub_zero, norm_one, one_pow]

end Cayley

section Stieltjes

open RMTFoundations.Stieltjes (stieltjes)

/-- `stieltjes` is mathlib's `resolventTransform`. -/
theorem stieltjes_eq_resolventTransform (μ : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) :
    stieltjes μ z = resolventTransform μ z := by
  rw [stieltjes, resolventTransform_apply]
  congr 1
  funext t
  rw [resolvent, Ring.inverse_eq_inv, Algebra.algebraMap_eq_smul_one, Complex.real_smul,
    mul_one]

/-- The Stieltjes transform of a finite measure is holomorphic on `ℂ⁺`. -/
theorem stieltjes_differentiableOn (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] :
    DifferentiableOn ℂ (stieltjes μ) RMTFoundations.AnalyticHalfPlane.upper := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hnot : z ∉ algebraMap ℝ ℂ '' μ.support := by
    rintro ⟨t, -, ht⟩
    rw [Complex.coe_algebraMap] at ht
    have := congrArg Complex.im ht
    rw [Complex.ofReal_im] at this
    linarith
  have hd := (hasDerivAt_resolventTransform (A := ℂ) z hnot).differentiableAt
  have he : stieltjes μ = resolventTransform μ := funext (stieltjes_eq_resolventTransform μ)
  rw [he]
  exact hd.differentiableWithinAt

/-- `|S_μ(z)| ≤ μ(ℝ)/Im z`. -/
theorem norm_stieltjes_le (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (z : ℂ /- [definition] -/ ) (hz : 0 < z.im /- [standing] -/ ) :
    ‖stieltjes μ z‖ ≤ μ.real univ / z.im := by
  rw [stieltjes]
  have hb : ∀ t : ℝ, ‖((t : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := fun t => by
    rw [norm_inv]
    refine inv_anti₀ hz ?_
    have := Complex.abs_im_le_norm ((t : ℂ) - z)
    simp at this
    rwa [abs_of_pos hz] at this
  calc ‖∫ t, ((t : ℂ) - z)⁻¹ ∂μ‖ ≤ ∫ _t, z.im⁻¹ ∂μ :=
        norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall hb)
    _ = μ.real univ / z.im := by rw [integral_const, smul_eq_mul, div_eq_mul_inv]

end Stieltjes

section HalfPlane

open Complex

/-- The boundary parametrisation `θ ↦ cay(e^{iθ}) ∈ ℝ`. -/
noncomputable def tmap (θ : ℝ /- [definition] -/ ) : ℝ := (cay (circleMap 0 1 θ)).re

/-- The exceptional set `{θ : e^{iθ} = 1}` (the point at infinity). -/
def infSet : Set ℝ := {θ | circleMap 0 1 θ = 1}

/-- The exceptional set is measurable. -/
theorem measurableSet_infSet : MeasurableSet infSet :=
  (isClosed_singleton.preimage (continuous_circleMap 0 1)).measurableSet

/-- `tmap` is measurable. -/
theorem measurable_tmap : Measurable tmap := by
  unfold tmap cay
  exact Complex.measurable_re.comp ((measurable_const.mul (measurable_const.add
    (continuous_circleMap 0 1).measurable)).div (measurable_const.sub
    (continuous_circleMap 0 1).measurable))

/-- `|e^{iθ}| = 1`. -/
theorem norm_circleMap_one (θ : ℝ /- [definition] -/ ) : ‖circleMap 0 1 θ‖ = 1 := by
  rw [norm_circleMap_zero, abs_one]

open Classical in
/-- The kernel identity on the whole circle, split by the exceptional set. -/
theorem poisson_split {z : ℂ /- [definition] -/ } (hz : z ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) (θ : ℝ /- [definition] -/ ) :
    poissonKernel 0 (invcay z) (circleMap 0 1 θ)
      = if θ ∈ infSet then z.im
        else (1 + tmap θ ^ 2) * z.im / ((tmap θ - z.re) ^ 2 + z.im ^ 2) := by
  by_cases h : θ ∈ infSet
  · rw [if_pos h, show circleMap 0 1 θ = 1 from h, poisson_cayley_one hz]
  · rw [if_neg h]
    exact poisson_cayley hz (norm_circleMap_one θ) h

/-- `cay` is holomorphic on the disk. -/
theorem cay_differentiableOn : DifferentiableOn ℂ cay (ball 0 1) := by
  intro w hw
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm (norm_lt_one_of_ne hw))
  unfold cay
  exact (((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) hne).differentiableWithinAt

/-- **The imaginary part of a Herglotz function, represented through the disk.**
`Im F(z) = Im z · σ(∞) + ∫_{θ ∉ ∞} (1 + t²) Im z / ((t - Re z)² + (Im z)²) dσ(θ)`,
`t = tmap θ`, for a finite measure `σ`. -/
theorem im_rep {F : ℂ → ℂ /- [definition] -/ } (hF : DifferentiableOn ℂ F RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ )
    (him : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, 0 ≤ (F z).im /- [standing] -/ ) :
    ∃ σ : FiniteMeasure ℝ, ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper,
      (F z).im = z.im * (σ : Measure ℝ).real infSet
        + ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * z.im / ((tmap θ - z.re) ^ 2 + z.im ^ 2)
          ∂(σ : Measure ℝ) := by
  classical
  set f : ℂ → ℂ := fun w => -I * F (cay w) with hfdef
  have hf : DifferentiableOn ℂ f (ball 0 1) :=
    (differentiableOn_const _).mul (hF.comp cay_differentiableOn fun w hw => cay_mem_upper hw)
  have hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (f w).re := by
    intro w hw
    have : (f w).re = (F (cay w)).im := by simp [hfdef]
    rw [this]; exact him _ (cay_mem_upper hw)
  obtain ⟨σ, -, hσ⟩ := disk_herglotz hf hre
  refine ⟨σ, fun z hz => ?_⟩
  have hw := invcay_mem_ball hz
  have h1 : (F z).im = (f (invcay z)).re := by simp [hfdef, cay_invcay hz]
  rw [h1, hσ _ hw]
  have hint : Integrable (fun θ => poissonKernel 0 (invcay z) (circleMap 0 1 θ)) (σ : Measure ℝ) :=
    (poissonBCF hw).integrable (σ : Measure ℝ)
  rw [← integral_add_compl measurableSet_infSet hint]
  congr 1
  · rw [setIntegral_congr_fun measurableSet_infSet (g := fun _ => z.im) (fun θ hθ => by
      simp only; rw [poisson_split hz θ, if_pos hθ])]
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  · refine setIntegral_congr_fun measurableSet_infSet.compl fun θ hθ => ?_
    rw [poisson_split hz θ, if_neg hθ]

end HalfPlane

section Assemble

open Complex RMTFoundations.StieltjesInversion RMTFoundations.Stieltjes

/-- `(1+t²)(n+1)²/(t²+(n+1)²) → 1 + t²`. -/
theorem ratio_tendsto (t : ℝ /- [definition] -/ ) :
    Tendsto (fun n : ℕ => (1 + t ^ 2) * (((n : ℝ) + 1) ^ 2 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)))
      atTop (𝓝 (1 + t ^ 2)) := by
  have h1 : Tendsto (fun n : ℕ => t ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ 1 this)
    exact tendsto_const_nhds.div_atTop this
  have h2 : Tendsto (fun n : ℕ => (t ^ 2 / ((n : ℝ) + 1) ^ 2 + 1)⁻¹) atTop (𝓝 ((0 + 1)⁻¹)) :=
    (h1.add tendsto_const_nhds).inv₀ (by norm_num)
  rw [show ((0 : ℝ) + 1)⁻¹ = 1 by norm_num] at h2
  have h3 := h2.const_mul (1 + t ^ 2)
  rw [mul_one] at h3
  refine h3.congr fun n => ?_
  have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  congr 1
  field_simp

/-- `(1+t²)(n+1)²/(t²+(n+1)²) ≤ (n+1)² + 1`. -/
theorem ratio_le (t : ℝ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) :
    (1 + t ^ 2) * (((n : ℝ) + 1) ^ 2 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)) ≤ ((n : ℝ) + 1) ^ 2 + 1 := by
  have hn : (0 : ℝ) < t ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hn]
  nlinarith [sq_nonneg t, sq_nonneg ((n : ℝ) + 1)]

/-- **The Herglotz-Borel theorem, PROVED.** -/
theorem herglotzBorel : RMTFoundations.AnalyticHalfPlane.HerglotzBorel := by
  classical
  intro F M hF him hM
  obtain ⟨σ, hrep⟩ := im_rep hF him
  set σm : Measure ℝ := (σ : Measure ℝ) with hσm
  have hI : Complex.I ∈ RMTFoundations.AnalyticHalfPlane.upper := by show 0 < Complex.I.im; simp
  have hM0 : 0 ≤ M := by
    have := (norm_nonneg _).trans (hM _ hI); simpa using this
  -- the bound along the imaginary axis
  have hyI : ∀ y : ℝ, 0 < y → ((y : ℂ) * Complex.I) ∈ RMTFoundations.AnalyticHalfPlane.upper := fun y hy => by
    show 0 < ((y : ℂ) * Complex.I).im; simp [hy]
  have hkey : ∀ y : ℝ, 0 < y →
      y ^ 2 * σm.real infSet + ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * (y ^ 2 / (tmap θ ^ 2 + y ^ 2))
        ∂σm ≤ M := by
    intro y hy
    have hr := hrep _ (hyI y hy)
    have hre0 : ((y : ℂ) * Complex.I).re = 0 := by simp
    have him0 : ((y : ℂ) * Complex.I).im = y := by simp
    rw [hre0, him0] at hr
    have hb : y * (F ((y : ℂ) * Complex.I)).im ≤ M := by
      have h1 := hM _ (hyI y hy)
      rw [him0] at h1
      have h2 : (F ((y : ℂ) * Complex.I)).im ≤ ‖F ((y : ℂ) * Complex.I)‖ :=
        Complex.im_le_norm _
      calc y * (F ((y : ℂ) * Complex.I)).im ≤ y * (M / y) := by gcongr; linarith
        _ = M := by field_simp
    rw [hr] at hb
    have e : y * ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * y / ((tmap θ - 0) ^ 2 + y ^ 2) ∂σm
        = ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * (y ^ 2 / (tmap θ ^ 2 + y ^ 2)) ∂σm := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [sub_zero]; ring
    have : y * (y * σm.real infSet + ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * y
        / ((tmap θ - 0) ^ 2 + y ^ 2) ∂σm)
        = y ^ 2 * σm.real infSet + ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * (y ^ 2 / (tmap θ ^ 2 + y ^ 2))
          ∂σm := by rw [mul_add, e]; ring
    linarith
  have hnn : ∀ y : ℝ, 0 ≤ ∫ θ in infSetᶜ, (1 + tmap θ ^ 2) * (y ^ 2 / (tmap θ ^ 2 + y ^ 2)) ∂σm :=
    fun y => setIntegral_nonneg measurableSet_infSet.compl fun θ _ => by positivity
  -- no mass at infinity
  have hinf : σm.real infSet = 0 := by
    by_contra hne
    have hpos : 0 < σm.real infSet := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    set y := Real.sqrt ((M + 1) / σm.real infSet)
    have hy : 0 < y := Real.sqrt_pos.mpr (by positivity)
    have hy2 : y ^ 2 = (M + 1) / σm.real infSet := Real.sq_sqrt (by positivity)
    have := hkey y hy
    have := hnn y
    rw [hy2, div_mul_cancel₀ _ hpos.ne'] at *
    linarith
  -- the finite measure on the line
  set ρ : Measure ℝ := σm.restrict infSetᶜ with hρ
  set dens : ℝ → ENNReal := fun θ => ENNReal.ofReal (1 + tmap θ ^ 2) with hdens
  have hdm : Measurable dens :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_tmap.pow_const 2))
  have hlin : ∫⁻ θ, dens θ ∂ρ ≤ ENNReal.ofReal M := by
    set g : ℕ → ℝ → ℝ := fun n θ =>
      (1 + tmap θ ^ 2) * (((n : ℝ) + 1) ^ 2 / (tmap θ ^ 2 + ((n : ℝ) + 1) ^ 2)) with hg
    have hgm : ∀ n, Measurable (g n) := fun n => by
      simp only [hg]
      exact (measurable_const.add (measurable_tmap.pow_const 2)).mul
        (measurable_const.div (((measurable_tmap.pow_const 2)).add measurable_const))
    have hgn : ∀ n θ, 0 ≤ g n θ := fun n θ => by simp only [hg]; positivity
    have hgi : ∀ n, Integrable (g n) ρ := fun n =>
      Integrable.of_bound (hgm n).aestronglyMeasurable (((n : ℝ) + 1) ^ 2 + 1)
        (Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgn n θ)]; exact ratio_le _ n)
    have hlint : ∀ n, ∫⁻ θ, ENNReal.ofReal (g n θ) ∂ρ ≤ ENNReal.ofReal M := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (Eventually.of_forall (hgn n))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hkey ((n : ℝ) + 1) (by positivity)
      have h0 : 0 ≤ ((n : ℝ) + 1) ^ 2 * σm.real infSet := by positivity
      linarith
    have hfatou := lintegral_liminf_le (μ := ρ) (u := atTop)
      (f := fun n θ => ENNReal.ofReal (g n θ))
      (fun n => ENNReal.measurable_ofReal.comp (hgm n))
    have hlim : ∀ θ, liminf (fun n => ENNReal.ofReal (g n θ)) atTop = dens θ := by
      intro θ
      exact ((ENNReal.continuous_ofReal.tendsto _).comp (ratio_tendsto (tmap θ))).liminf_eq
    simp only [hlim] at hfatou
    refine hfatou.trans ?_
    exact liminf_le_of_frequently_le' (Frequently.of_forall hlint)
  set ν0 : Measure ℝ := ρ.withDensity dens with hν0
  set μ : Measure ℝ := ν0.map tmap with hμ
  have hμuniv : μ univ ≤ ENNReal.ofReal M := by
    rw [hμ, Measure.map_apply measurable_tmap MeasurableSet.univ, preimage_univ, hν0,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hlin
  haveI hμfin : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hμuniv ENNReal.ofReal_lt_top⟩
  have hμM : μ.real univ ≤ M := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hM0 hμuniv
  -- the imaginary parts agree
  have hImEq : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, (F z).im = (stieltjes μ z).im := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hs := stieltjes_im μ z.re z.im hz'
    rw [Complex.re_add_im] at hs
    rw [hs, hrep z hz, hinf, mul_zero, zero_add]
    have hcont : Continuous fun s : ℝ => z.im / ((s - z.re) ^ 2 + z.im ^ 2) := by
      refine continuous_const.div (by fun_prop) fun s => ?_
      have : 0 < z.im ^ 2 := by positivity
      positivity
    rw [hμ, integral_map measurable_tmap.aemeasurable hcont.aestronglyMeasurable, hν0,
      integral_withDensity_eq_integral_toReal_smul hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hdens, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  -- the holomorphic difference is a real constant, hence zero
  refine ⟨μ, hμfin, hμM, ?_⟩
  set H : ℂ → ℂ := fun z => F z - stieltjes μ z with hH
  have hopen : IsOpen RMTFoundations.AnalyticHalfPlane.upper := RMTFoundations.AnalyticHalfPlane.isOpen_upper
  have hHd : DifferentiableOn ℂ H RMTFoundations.AnalyticHalfPlane.upper := hF.sub (stieltjes_differentiableOn μ)
  have hHa : AnalyticOnNhd ℂ H RMTFoundations.AnalyticHalfPlane.upper := hHd.analyticOnNhd hopen
  have hconv : Convex ℝ RMTFoundations.AnalyticHalfPlane.upper := convex_halfSpace_im_gt 0
  have hHim : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, (H z).im = 0 := fun z hz => by
    simp only [hH, Complex.sub_im, hImEq z hz, sub_self]
  rcases hHa.is_constant_or_isOpen hconv.isPreconnected with ⟨c, hc⟩ | hop
  · -- the constant vanishes
    have hc0 : c = 0 := by
      by_contra hne
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
      set y := (2 * (M + μ.real univ) + 1) / ‖c‖
      have hy : 0 < y := by have := measureReal_nonneg (μ := μ) (s := univ); positivity
      have h1 := hc _ (hyI y hy)
      have hb1 := hM _ (hyI y hy)
      have hb2 := norm_stieltjes_le μ _ (hyI y hy)
      have him0 : ((y : ℂ) * Complex.I).im = y := by simp
      rw [him0] at hb1 hb2
      have : ‖c‖ ≤ M / y + μ.real univ / y := by
        rw [← h1]; exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
      rw [← add_div, le_div_iff₀ hy] at this
      have e : ‖c‖ * y = 2 * (M + μ.real univ) + 1 := by
        rw [show y = (2 * (M + μ.real univ) + 1) / ‖c‖ from rfl]
        field_simp
      have := measureReal_nonneg (μ := μ) (s := univ)
      linarith
    intro z hz
    have := hc z hz
    rw [hc0] at this
    exact sub_eq_zero.mp this
  · exfalso
    have himg := hop RMTFoundations.AnalyticHalfPlane.upper subset_rfl hopen
    have hmem : H Complex.I ∈ H '' RMTFoundations.AnalyticHalfPlane.upper := mem_image_of_mem H hI
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg _ hmem
    have hpt : H Complex.I + (ε / 2 : ℝ) * Complex.I ∈ H '' RMTFoundations.AnalyticHalfPlane.upper := by
      refine hball ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    obtain ⟨z, hz, hzeq⟩ := hpt
    have h1 := hHim z hz
    rw [hzeq] at h1
    have h2 := hHim _ hI
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at h1
    rw [h2] at h1
    linarith

end Assemble
end RMTFoundations.HerglotzBorelProof

#print axioms RMTFoundations.HerglotzBorelProof.diffContOnCl_scale
#print axioms RMTFoundations.HerglotzBorelProof.continuous_poissonKernel_circle
#print axioms RMTFoundations.HerglotzBorelProof.continuous_scale_circle
#print axioms RMTFoundations.HerglotzBorelProof.re_poisson
#print axioms RMTFoundations.HerglotzBorelProof.poisson_bounds
#print axioms RMTFoundations.HerglotzBorelProof.poissonBCF
#print axioms RMTFoundations.HerglotzBorelProof.poissonBCF_apply
#print axioms RMTFoundations.HerglotzBorelProof.sig
#print axioms RMTFoundations.HerglotzBorelProof.integral_sig
#print axioms RMTFoundations.HerglotzBorelProof.integral_sig_poisson
#print axioms RMTFoundations.HerglotzBorelProof.sig_finite
#print axioms RMTFoundations.HerglotzBorelProof.sig_support
#print axioms RMTFoundations.HerglotzBorelProof.sig_mass
#print axioms RMTFoundations.HerglotzBorelProof.eq_of_mapClusterPt_of_tendsto
#print axioms RMTFoundations.HerglotzBorelProof.disk_herglotz
#print axioms RMTFoundations.HerglotzBorelProof.cay
#print axioms RMTFoundations.HerglotzBorelProof.invcay
#print axioms RMTFoundations.HerglotzBorelProof.cay_im
#print axioms RMTFoundations.HerglotzBorelProof.norm_lt_one_of_ne
#print axioms RMTFoundations.HerglotzBorelProof.cay_mem_upper
#print axioms RMTFoundations.HerglotzBorelProof.add_I_ne
#print axioms RMTFoundations.HerglotzBorelProof.invcay_mem_ball
#print axioms RMTFoundations.HerglotzBorelProof.cay_invcay
#print axioms RMTFoundations.HerglotzBorelProof.invcay_cay
#print axioms RMTFoundations.HerglotzBorelProof.cay_real
#print axioms RMTFoundations.HerglotzBorelProof.poisson_cayley
#print axioms RMTFoundations.HerglotzBorelProof.poisson_cayley_one
#print axioms RMTFoundations.HerglotzBorelProof.stieltjes_eq_resolventTransform
#print axioms RMTFoundations.HerglotzBorelProof.stieltjes_differentiableOn
#print axioms RMTFoundations.HerglotzBorelProof.norm_stieltjes_le
#print axioms RMTFoundations.HerglotzBorelProof.tmap
#print axioms RMTFoundations.HerglotzBorelProof.infSet
#print axioms RMTFoundations.HerglotzBorelProof.measurableSet_infSet
#print axioms RMTFoundations.HerglotzBorelProof.measurable_tmap
#print axioms RMTFoundations.HerglotzBorelProof.norm_circleMap_one
#print axioms RMTFoundations.HerglotzBorelProof.poisson_split
#print axioms RMTFoundations.HerglotzBorelProof.cay_differentiableOn
#print axioms RMTFoundations.HerglotzBorelProof.im_rep
#print axioms RMTFoundations.HerglotzBorelProof.ratio_tendsto
#print axioms RMTFoundations.HerglotzBorelProof.ratio_le
#print axioms RMTFoundations.HerglotzBorelProof.herglotzBorel
