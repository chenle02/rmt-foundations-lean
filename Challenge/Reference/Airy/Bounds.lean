import Mathlib
import Challenge.Reference.Airy.Core

namespace RMTFoundations.AiryBounds

open RMTFoundations.Airy




open MeasureTheory Set Filter
open scoped Topology ENNReal


theorem Ai_contDiff (n : WithTop ℕ∞ /- [definition] -/) : ContDiff ℝ n RMTFoundations.Airy.airyAiReal :=
  (complex_analyticOnNhd_airyAi.contDiff (n := n)).real_of_complex

theorem Ai_continuous : Continuous RMTFoundations.Airy.airyAiReal := (Ai_contDiff 0).continuous

theorem Ai_ODE (x : ℝ /- [definition] -/) : iteratedDeriv 2 RMTFoundations.Airy.airyAiReal x = x * RMTFoundations.Airy.airyAiReal x :=
  iteratedDeriv_two_airyAiReal x

/-- A uniform superexponential bound including the origin. -/
theorem Ai_superexponential_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
    |RMTFoundations.Airy.airyAiReal x| ≤ C * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hC₁nn : 0 ≤ C₁ := by
    have h := hC₁ 1 le_rfl
    rw [Real.one_rpow, Real.one_rpow, mul_one] at h
    exact le_of_lt (pos_of_mul_pos_left ((airyAiReal_pos_of_nonneg zero_le_one).trans_le h)
      (Real.exp_pos _).le)
  have hc : Continuous (fun x : ℝ => |RMTFoundations.Airy.airyAiReal x| * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))) := by
    apply Ai_continuous.abs.mul
    apply Real.continuous_exp.comp
    exact continuous_const.mul (Real.continuous_rpow_const (by norm_num))
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hc.continuousOn
  let M := |RMTFoundations.Airy.airyAiReal x₀| * Real.exp (2 / 3 * x₀ ^ (3 / 2 : ℝ))
  let C := max (max 1 M) C₁
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C, hC, fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hm : |RMTFoundations.Airy.airyAiReal x| * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) ≤ M := hmax ⟨hx, hx1⟩
    calc |RMTFoundations.Airy.airyAiReal x| = (|RMTFoundations.Airy.airyAiReal x| * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))) *
        Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ ≤ C * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (Real.exp_pos _).le
  · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
    have hr : x ^ (-1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by norm_num)
    rw [abs_of_pos (airyAiReal_pos_of_nonneg hx)]
    calc RMTFoundations.Airy.airyAiReal x ≤ C₁ * x ^ (-1 / 4 : ℝ) * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) := hC₁ x hx1'
      _ ≤ C₁ * 1 * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hC₁nn) (Real.exp_pos _).le
      _ ≤ C * Real.exp (-(2 / 3 * x ^ (3 / 2 : ℝ))) := by
        simpa using mul_le_mul_of_nonneg_right (le_max_right (max 1 M) C₁) (Real.exp_pos _).le

/-- Every lower half-line has a single exponential dominator. -/
theorem Ai_halfline_exp_bound (a : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, a ≤ u → |RMTFoundations.Airy.airyAiReal u| ≤ C * Real.exp (-u) := by
  obtain ⟨C₁, hC₁, hb⟩ := Ai_superexponential_bound
  have hc : Continuous (fun u : ℝ => |RMTFoundations.Airy.airyAiReal u| * Real.exp u) := Ai_continuous.abs.mul Real.continuous_exp
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show min a 0 ≤ (9 / 4 : ℝ) by
      exact (min_le_right _ _).trans (by norm_num))) hc.continuousOn
  let M := |RMTFoundations.Airy.airyAiReal u₀| * Real.exp u₀
  let C := max (max 1 M) C₁
  refine ⟨C, lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (le_max_left _ _)), fun u hu => ?_⟩
  by_cases hu2 : u ≤ 9 / 4
  · have hm : |RMTFoundations.Airy.airyAiReal u| * Real.exp u ≤ M := hmax ⟨(min_le_left _ _).trans hu, hu2⟩
    calc |RMTFoundations.Airy.airyAiReal u| = (|RMTFoundations.Airy.airyAiReal u| * Real.exp u) * Real.exp (-u) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (-u) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ ≤ C * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (Real.exp_pos _).le
  · have hu2' : 9 / 4 < u := lt_of_not_ge hu2
    have hu0 : 0 < u := by linarith
    have hsqrt : (3 : ℝ) / 2 ≤ Real.sqrt u := by
      have h94 : Real.sqrt (9 / 4 : ℝ) = 3 / 2 := by
        rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 4) hu2'
      rw [h94] at h
      exact h.le
    have hr : u ^ (3 / 2 : ℝ) = Real.sqrt u * u := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add_one hu0.ne', Real.sqrt_eq_rpow]
    have he : Real.exp (-(2 / 3 * u ^ (3 / 2 : ℝ))) ≤ Real.exp (-u) := by
      apply Real.exp_le_exp.mpr
      rw [hr]
      have h := mul_le_mul_of_nonneg_right hsqrt hu0.le
      linarith
    calc |RMTFoundations.Airy.airyAiReal u| ≤ C₁ * Real.exp (-(2 / 3 * u ^ (3 / 2 : ℝ))) := hb u hu0.le
      _ ≤ C₁ * Real.exp (-u) := mul_le_mul_of_nonneg_left he hC₁.le
      _ ≤ C * Real.exp (-u) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le





open MeasureTheory Set Filter
open scoped Topology ENNReal


noncomputable def shiftedKernel (f : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/) (q : ℝ × ℝ /- [definition] -/) : ℝ := f (q.1 + q.2 + s)

theorem continuous_shiftedKernel (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/) (s : ℝ /- [definition] -/) :
    Continuous (shiftedKernel f s) := by
  exact hf.comp ((continuous_fst.add continuous_snd).add continuous_const)

theorem integrable_exp_square :
    Integrable (fun x : ℝ => (Real.exp (-x)) ^ 2) RMTFoundations.Airy.halfLineMeasure := by
  have h := integrableOn_exp_neg_Ioi (0 : ℝ)
  have hb : ∀ᵐ x ∂ RMTFoundations.Airy.halfLineMeasure, ‖Real.exp (-x)‖ ≤ (1 : ℝ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith [show (0 : ℝ) < x from hx])
  simpa [sq] using h.bdd_mul (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable hb

theorem integrable_quadrant_exp (C : ℝ /- [definition] -/) :
    Integrable (fun q : ℝ × ℝ => (C * Real.exp (-(q.1 + q.2))) ^ 2) RMTFoundations.Airy.quadrantMeasure := by
  have h := (integrable_exp_square.mul_prod integrable_exp_square).const_mul (C ^ 2)
  convert h using 1
  funext q
  rw [neg_add, Real.exp_add]
  ring

theorem integrable_shiftedKernel_sq (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (s C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hbound : ∀ u : ℝ, s ≤ u → |f u| ≤ C * Real.exp (-u) /- [standing] -/ ) :
    Integrable (fun q : ℝ × ℝ => shiftedKernel f s q ^ 2) RMTFoundations.Airy.quadrantMeasure := by
  apply Integrable.mono' (integrable_quadrant_exp (C * Real.exp (-s)))
  · exact (continuous_shiftedKernel f hf s).pow 2 |>.aestronglyMeasurable
  · have hpos : ∀ᵐ q ∂ RMTFoundations.Airy.quadrantMeasure, 0 < q.1 ∧ 0 < q.2 := by
      change ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
        q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hpos] with q hq
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb := hbound (q.1 + q.2 + s) (by linarith [hq.1, hq.2])
    have heq : C * Real.exp (-(q.1 + q.2 + s)) =
        (C * Real.exp (-s)) * Real.exp (-(q.1 + q.2)) := by
      rw [neg_add, Real.exp_add]
      ring
    rw [heq] at hb
    unfold shiftedKernel
    nlinarith [sq_abs (f (q.1 + q.2 + s)), abs_nonneg (f (q.1 + q.2 + s)),
      mul_nonneg (mul_nonneg hC (Real.exp_pos (-s)).le) (Real.exp_pos (-(q.1 + q.2))).le]

theorem memLp_shiftedKernel (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (s C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hbound : ∀ u : ℝ, s ≤ u → |f u| ≤ C * Real.exp (-u) /- [standing] -/ ) :
    MemLp (shiftedKernel f s) 2 RMTFoundations.Airy.quadrantMeasure := by
  exact (memLp_two_iff_integrable_sq
    (continuous_shiftedKernel f hf s).aestronglyMeasurable).mpr
    (integrable_shiftedKernel_sq f hf s C hC hbound)

/-- Nondegenerate joint satisfiability of every analytic premise above, for every shift. -/
theorem kernelBounds_inhabitation (s : ℝ /- [definition] -/) :
    Continuous (fun u : ℝ => Real.exp (-u)) ∧ (0 : ℝ) ≤ 1 ∧
    (∀ u : ℝ, s ≤ u → |Real.exp (-u)| ≤ 1 * Real.exp (-u)) ∧
    (Real.exp (-(1 + 1 + s)) ≠ 0) := by
  refine ⟨Real.continuous_exp.comp continuous_neg, zero_le_one, ?_, (Real.exp_pos _).ne'⟩
  intro u _
  simp [abs_of_pos (Real.exp_pos _)]


theorem ae_positive_quadrant : ∀ᵐ q ∂ RMTFoundations.Airy.quadrantMeasure, 0 < q.1 ∧ 0 < q.2 := by
  change ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
    q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

theorem abs_shiftedKernel_le (f : ℝ → ℝ /- [definition] -/)
    (a C s : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : a ≤ s /- [standing] -/)
    (hbound : ∀ u : ℝ, a ≤ u → |f u| ≤ C * Real.exp (-u) /- [standing] -/ )
    (q : ℝ × ℝ /- [definition] -/)
    (hq : 0 < q.1 ∧ 0 < q.2 /- [standing] -/) :
    |shiftedKernel f s q| ≤ (C * Real.exp (-a)) * Real.exp (-(q.1 + q.2)) := by
  have hb := hbound (q.1 + q.2 + s) (by linarith [hq.1, hq.2])
  calc |shiftedKernel f s q| ≤ C * Real.exp (-(q.1 + q.2 + s)) := hb
    _ ≤ C * Real.exp (-(q.1 + q.2 + a)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [neg_add, Real.exp_add]; ring

theorem tendsto_shiftedKernel_eLpNorm (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (s₀ C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hbound : ∀ u : ℝ, s₀ - 1 ≤ u → |f u| ≤ C * Real.exp (-u) /- [standing] -/ ) :
    Tendsto (fun s => eLpNorm (shiftedKernel f s - shiftedKernel f s₀) 2 RMTFoundations.Airy.quadrantMeasure)
      (𝓝 s₀) (𝓝 0) := by
  let D := C * Real.exp (-(s₀ - 1))
  let B : ℝ × ℝ → ℝ := fun q => (2 * D * Real.exp (-(q.1 + q.2))) ^ 2
  let F : ℝ → ℝ × ℝ → ℝ≥0∞ :=
    fun s q => ENNReal.ofReal ((shiftedKernel f s q - shiftedKernel f s₀ q) ^ 2)
  have hD : 0 ≤ D := mul_nonneg hC (Real.exp_pos _).le
  have hB : Integrable B RMTFoundations.Airy.quadrantMeasure := integrable_quadrant_exp (2 * D)
  have hfin : (∫⁻ q, ENNReal.ofReal (B q) ∂ RMTFoundations.Airy.quadrantMeasure) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => sq_nonneg _)).mp
      hB.hasFiniteIntegral).ne
  have hmeas : ∀ᶠ s in 𝓝 s₀, Measurable (F s) := by
    apply Eventually.of_forall
    intro s
    exact ENNReal.measurable_ofReal.comp
      (((continuous_shiftedKernel f hf s).sub (continuous_shiftedKernel f hf s₀)).pow 2).measurable
  have hdom : ∀ᶠ s in 𝓝 s₀, ∀ᵐ q ∂ RMTFoundations.Airy.quadrantMeasure, F s q ≤ ENNReal.ofReal (B q) := by
    filter_upwards [eventually_ge_nhds (show s₀ - 1 < s₀ by linarith)] with s hs
    filter_upwards [ae_positive_quadrant] with q hq
    apply ENNReal.ofReal_le_ofReal
    have h₁ := abs_shiftedKernel_le f (s₀ - 1) C s hC hs hbound q hq
    have h₂ := abs_shiftedKernel_le f (s₀ - 1) C s₀ hC (by linarith) hbound q hq
    have hab : |shiftedKernel f s q - shiftedKernel f s₀ q| ≤
        2 * D * Real.exp (-(q.1 + q.2)) := by
      calc |shiftedKernel f s q - shiftedKernel f s₀ q|
          ≤ |shiftedKernel f s q| + |shiftedKernel f s₀ q| := abs_sub _ _
        _ ≤ D * Real.exp (-(q.1 + q.2)) + D * Real.exp (-(q.1 + q.2)) := add_le_add h₁ h₂
        _ = _ := by ring
    dsimp [F, B]
    nlinarith [sq_abs (shiftedKernel f s q - shiftedKernel f s₀ q),
      abs_nonneg (shiftedKernel f s q - shiftedKernel f s₀ q),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD) (Real.exp_pos (-(q.1 + q.2))).le]
  have hlim : ∀ᵐ q ∂ RMTFoundations.Airy.quadrantMeasure, Tendsto (fun s => F s q) (𝓝 s₀) (𝓝 0) := by
    apply ae_of_all
    intro q
    have hc : Continuous (fun s : ℝ => ENNReal.ofReal
        ((f (q.1 + q.2 + s) - f (q.1 + q.2 + s₀)) ^ 2)) :=
      ENNReal.continuous_ofReal.comp
        (((hf.comp (continuous_const.add continuous_id)).sub continuous_const).pow 2)
    simpa [F, shiftedKernel] using hc.tendsto s₀
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (μ := RMTFoundations.Airy.quadrantMeasure) (f := fun _ => 0) (fun q => ENNReal.ofReal (B q)) hmeas hdom hfin hlim
  have ht' : Tendsto (fun s => (∫⁻ q, F s q ∂ RMTFoundations.Airy.quadrantMeasure) ^ (1 / 2 : ℝ)) (𝓝 s₀) (𝓝 0) := by
    simpa using ht.ennrpow_const (1 / 2 : ℝ)
  have heq : ∀ s, eLpNorm (shiftedKernel f s - shiftedKernel f s₀) 2 RMTFoundations.Airy.quadrantMeasure =
      (∫⁻ q, F s q ∂ RMTFoundations.Airy.quadrantMeasure) ^ (1 / 2 : ℝ) := by
    intro s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    · norm_num
      congr 1
      apply lintegral_congr
      intro q
      simp only [Pi.sub_apply, ENNReal.rpow_two, F]
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      congr 1
      rw [Real.norm_eq_abs, sq_abs]
    · exact ((continuous_shiftedKernel f hf s).sub
        (continuous_shiftedKernel f hf s₀)).aestronglyMeasurable
  exact ht'.congr (fun s => (heq s).symm)











theorem Ai_kernel_sq_integrable (s : ℝ /- [definition] -/) :
    Integrable (fun q => RMTFoundations.Airy.airyHankelShiftKernel s q ^ 2) RMTFoundations.Airy.quadrantMeasure := by
  obtain ⟨C, hC, hb⟩ := Ai_halfline_exp_bound s
  exact integrable_shiftedKernel_sq RMTFoundations.Airy.airyAiReal Ai_continuous s C hC.le hb

theorem Ai_kernel_memLp (s : ℝ /- [definition] -/) : MemLp (RMTFoundations.Airy.airyHankelShiftKernel s) 2 RMTFoundations.Airy.quadrantMeasure := by
  obtain ⟨C, hC, hb⟩ := Ai_halfline_exp_bound s
  exact memLp_shiftedKernel RMTFoundations.Airy.airyAiReal Ai_continuous s C hC.le hb

/-- This finite nonnegative double integral is the square of the kernel L² norm. -/
theorem Ai_double_integral_finite (s : ℝ /- [definition] -/) :
    (∫⁻ x, ∫⁻ t, ENNReal.ofReal (RMTFoundations.Airy.airyAiReal (x + t + s) ^ 2) ∂ RMTFoundations.Airy.halfLineMeasure ∂ RMTFoundations.Airy.halfLineMeasure) < ∞ := by
  have hi := (hasFiniteIntegral_iff_ofReal
    (ae_of_all RMTFoundations.Airy.quadrantMeasure fun q => sq_nonneg (RMTFoundations.Airy.airyHankelShiftKernel s q))).mp
    (Ai_kernel_sq_integrable s).hasFiniteIntegral
  have hm : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (RMTFoundations.Airy.airyHankelShiftKernel s q ^ 2)) :=
    ENNReal.measurable_ofReal.comp (continuous_shiftedKernel RMTFoundations.Airy.airyAiReal Ai_continuous s |>.pow 2).measurable
  rw [RMTFoundations.Airy.quadrantMeasure, lintegral_prod _ hm.aemeasurable] at hi
  exact hi

noncomputable def Ai_kernelLp (s : ℝ /- [definition] -/) : Lp ℝ 2 RMTFoundations.Airy.quadrantMeasure :=
  (Ai_kernel_memLp s).toLp (RMTFoundations.Airy.airyHankelShiftKernel s)

theorem Ai_kernelLp_continuous : Continuous Ai_kernelLp := by
  apply continuous_iff_continuousAt.mpr
  intro s₀
  obtain ⟨C, hC, hb⟩ := Ai_halfline_exp_bound (s₀ - 1)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' RMTFoundations.Airy.airyHankelShiftKernel Ai_kernel_memLp
    (RMTFoundations.Airy.airyHankelShiftKernel s₀) (Ai_kernel_memLp s₀)).mpr
    (tendsto_shiftedKernel_eLpNorm RMTFoundations.Airy.airyAiReal Ai_continuous s₀ C hC.le hb)

/-- RMTFoundations.Airy.airyAiReal and every shifted kernel are nondegenerate; analytic theorems assume no event. -/
theorem Ai_kernel_inhabitation :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧ RMTFoundations.Airy.airyHankelShiftKernel 0 (1, 1) ≠ 0 := by
  exact ⟨airyAiReal_zero_pos.ne', (airyAiReal_pos (by norm_num : (0 : ℝ) < 1 + 1 + 0)).ne'⟩




theorem H_integral_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure /- [definition] -/) :
    ∀ᵐ x ∂ RMTFoundations.Airy.halfLineMeasure, (RMTFoundations.Airy.airyHankelShift s f) x = ∫ t, RMTFoundations.Airy.airyAiReal (x + t + s) * f t ∂ RMTFoundations.Airy.halfLineMeasure :=
  kernelOperator_apply_ae (Ai_kernel_memLp s) f

theorem H_hilbertSchmidt (s : ℝ /- [definition] -/) : IsHilbertSchmidt (RMTFoundations.Airy.airyHankelShift s) :=
  isHilbertSchmidt_kernelOperator (Ai_kernel_memLp s)

theorem H_hsENorm_le (s : ℝ /- [definition] -/) :
    hsENorm (RMTFoundations.Airy.airyHankelShift s) ≤ eLpNorm (RMTFoundations.Airy.airyHankelShiftKernel s) 2 RMTFoundations.Airy.quadrantMeasure :=
  hsENorm_kernelOperator_le (Ai_kernel_memLp s)


end RMTFoundations.AiryBounds

#print axioms RMTFoundations.AiryBounds.Ai_contDiff
#print axioms RMTFoundations.AiryBounds.Ai_continuous
#print axioms RMTFoundations.AiryBounds.Ai_ODE
#print axioms RMTFoundations.AiryBounds.Ai_superexponential_bound
#print axioms RMTFoundations.AiryBounds.Ai_halfline_exp_bound
#print axioms RMTFoundations.AiryBounds.shiftedKernel
#print axioms RMTFoundations.AiryBounds.continuous_shiftedKernel
#print axioms RMTFoundations.AiryBounds.integrable_exp_square
#print axioms RMTFoundations.AiryBounds.integrable_quadrant_exp
#print axioms RMTFoundations.AiryBounds.integrable_shiftedKernel_sq
#print axioms RMTFoundations.AiryBounds.memLp_shiftedKernel
#print axioms RMTFoundations.AiryBounds.kernelBounds_inhabitation
#print axioms RMTFoundations.AiryBounds.ae_positive_quadrant
#print axioms RMTFoundations.AiryBounds.abs_shiftedKernel_le
#print axioms RMTFoundations.AiryBounds.tendsto_shiftedKernel_eLpNorm
#print axioms RMTFoundations.AiryBounds.Ai_kernel_sq_integrable
#print axioms RMTFoundations.AiryBounds.Ai_kernel_memLp
#print axioms RMTFoundations.AiryBounds.Ai_double_integral_finite
#print axioms RMTFoundations.AiryBounds.Ai_kernelLp
#print axioms RMTFoundations.AiryBounds.Ai_kernelLp_continuous
#print axioms RMTFoundations.AiryBounds.Ai_kernel_inhabitation
#print axioms RMTFoundations.AiryBounds.H_integral_apply_ae
#print axioms RMTFoundations.AiryBounds.H_hilbertSchmidt
#print axioms RMTFoundations.AiryBounds.H_hsENorm_le
