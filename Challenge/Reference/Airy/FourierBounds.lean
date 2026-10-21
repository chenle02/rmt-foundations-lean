import Mathlib
import Challenge.Reference.Airy.Core
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.AiryBounds

open MeasureTheory FourierTransform RMTFoundations.Airy
open Set Filter Complex
open scoped InnerProductSpace InnerProduct TemperedDistribution
open scoped SchwartzMap ENNReal Topology ContDiff

theorem fourier_integrable_schwartz_pairing
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    (∫ ξ : ℝ, (𝓕 f) ξ * φ ξ) = ∫ x : ℝ, f x * (𝓕 φ) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := f) (g := (φ : ℝ → ℂ))
    Real.continuous_fourierChar (by simpa only [innerₗ_apply_apply] using continuous_inner)
    hf φ.integrable
  rw [flip_innerₗ] at h
  simp only [smul_eq_mul] at h
  exact h

/-- Classical and L2 Fourier transforms agree for an L1 intersection L2 function.
No integrability of its classical Fourier transform is assumed. -/
theorem fourier_L1_L2_ae
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    ((𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hfcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq (f' := 𝓕 f)
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num))
    hfcont.locallyIntegrable
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  have hr : (∫ x : ℝ, (𝓕 φ) x * (h2.toLp f) x) = ∫ x : ℝ, f x * (𝓕 φ) x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have hq := fourier_integrable_schwartz_pairing f hf φ
  simp only [smul_eq_mul] at he
  have he' := he.symm.trans (hr.trans hq.symm)
  change (∫ x : ℝ, (g x : ℂ) * (𝓕 (h2.toLp f) : Lp ℂ 2 volume) x) =
    (∫ x : ℝ, (𝓕 f) x * (g x : ℂ)) at he'
  simpa only [Complex.real_smul, mul_comm] using he'

theorem fourier_L1_L2_memLp
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourier_L1_L2_ae f hf h2)).mp (Lp.memLp (𝓕 (h2.toLp f)))

theorem fourier_L1_L2_norm
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    ‖(fourier_L1_L2_memLp f hf h2).toLp (𝓕 f)‖ = ‖(h2.toLp f)‖ := by
  have he : (fourier_L1_L2_memLp f hf h2).toLp (𝓕 f) = 𝓕 (h2.toLp f) := by
    apply Lp.ext
    exact (fourier_L1_L2_memLp f hf h2).coeFn_toLp.trans
      (fourier_L1_L2_ae f hf h2).symm
  rw [he, Lp.norm_fourier_eq]


theorem inverse_fourier_integrable_schwartz_pairing
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    (∫ ξ : ℝ, (𝓕⁻ f) ξ * φ ξ) = ∫ x : ℝ, f x * (𝓕⁻ φ) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -innerₗ ℝ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := f) (g := (φ : ℝ → ℂ))
    Real.continuous_fourierChar (by fun_prop)
    hf φ.integrable
  have hn : (-innerₗ ℝ).flip = -innerₗ ℝ := by ext x y; simp [real_inner_comm]
  rw [hn] at h
  simp only [smul_eq_mul] at h
  have hs (x : ℝ) : (𝓕⁻ φ) x = (𝓕⁻ (φ : ℝ → ℂ)) x :=
    congrFun (SchwartzMap.fourierInv_coe φ) x
  simp_rw [hs]
  exact h

theorem inverse_fourier_L1_L2_ae
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    ((𝓕⁻ (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  have hfcont : Continuous (𝓕⁻ f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂.neg hf
  apply ae_eq_of_integral_contDiff_smul_eq (f' := 𝓕⁻ f)
    ((Lp.memLp (𝓕⁻ (h2.toLp f))).locallyIntegrable (by norm_num))
    hfcont.locallyIntegrable
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (Lp.fourierInv_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at he
  have hr : (∫ x : ℝ, (𝓕⁻ φ) x * (h2.toLp f) x) = ∫ x : ℝ, f x * (𝓕⁻ φ) x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have hq := inverse_fourier_integrable_schwartz_pairing f hf φ
  simp only [smul_eq_mul] at he
  have he' := he.symm.trans (hr.trans hq.symm)
  change (∫ x : ℝ, (g x : ℂ) * (𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume) x) =
    (∫ x : ℝ, (𝓕⁻ f) x * (g x : ℂ)) at he'
  simpa only [Complex.real_smul, mul_comm] using he'

theorem inverse_fourier_L1_L2_memLp
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) : MemLp (𝓕⁻ f) 2 :=
  (memLp_congr_ae (inverse_fourier_L1_L2_ae f hf h2)).mp (Lp.memLp (𝓕⁻ (h2.toLp f)))

theorem inverse_fourier_L1_L2_norm
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    ‖(inverse_fourier_L1_L2_memLp f hf h2).toLp (𝓕⁻ f)‖ = ‖(h2.toLp f)‖ := by
  have he : (inverse_fourier_L1_L2_memLp f hf h2).toLp (𝓕⁻ f) = 𝓕⁻ (h2.toLp f) := by
    apply Lp.ext
    exact (inverse_fourier_L1_L2_memLp f hf h2).coeFn_toLp.trans
      (inverse_fourier_L1_L2_ae f hf h2).symm
  rw [he, ← Lp.norm_fourier_eq (𝓕⁻ (h2.toLp f)), fourier_fourierInv_eq]

noncomputable def fourierPositivePhase (ξ x : ℝ /- [definition] -/) : ℂ :=
  Complex.exp (((2 * Real.pi * (ξ * x) : ℝ) : ℂ) * Complex.I)

theorem fourierPositivePhase_norm (ξ x : ℝ /- [definition] -/) :
    ‖fourierPositivePhase ξ x‖ = 1 := by
  simp [fourierPositivePhase, Complex.norm_exp]

theorem fourierPositivePhase_add (ξ x y : ℝ /- [definition] -/) :
    fourierPositivePhase ξ (x + y) = fourierPositivePhase ξ x * fourierPositivePhase ξ y := by
  unfold fourierPositivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem inverse_fourier_eq_positivePhase
    (m : ℝ → ℂ /- [definition] -/) (x : ℝ /- [definition] -/) :
    (𝓕⁻ m) x = ∫ ξ : ℝ, fourierPositivePhase ξ x * m ξ := by
  rw [Real.fourierInv_eq']
  simp only [fourierPositivePhase, Real.inner_apply, smul_eq_mul]

theorem fourier_neg_eq_positivePhase
    (f : ℝ → ℂ /- [definition] -/) (ξ : ℝ /- [definition] -/) :
    (𝓕 f) (-ξ) = ∫ x : ℝ, fourierPositivePhase ξ x * f x := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [fourierPositivePhase, Real.inner_apply, smul_eq_mul]
  congr 2
  congr 1
  ring

theorem inverse_fourier_kernel_apply
    (m f : ℝ → ℂ /- [definition] -/)
    (hm : Integrable m /- [standing] -/)
    (hf : Integrable f /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    (∫ y : ℝ, f y * (𝓕⁻ m) (x + y)) =
      (𝓕⁻ (fun ξ => m ξ * (𝓕 f) (-ξ))) x := by
  have hint : Integrable (fun p : ℝ × ℝ =>
      f p.1 * (fourierPositivePhase p.2 (x + p.1) * m p.2)) := by
    apply (hf.norm.mul_prod hm.norm).mono' ?_ ?_
    · have hc : Continuous (fun p : ℝ × ℝ => fourierPositivePhase p.2 (x + p.1)) := by
        unfold fourierPositivePhase
        fun_prop
      exact (hf.aestronglyMeasurable.comp_fst.mul
        (hc.aestronglyMeasurable.mul hm.aestronglyMeasurable.comp_snd))
    · exact ae_of_all _ (fun p => by simp only [norm_mul, fourierPositivePhase_norm, one_mul]; rfl)
  simp_rw [inverse_fourier_eq_positivePhase]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [fourier_neg_eq_positivePhase]
  simp_rw [fourierPositivePhase_add]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem fourier_neg_L1_L2_memLp
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    MemLp (fun ξ : ℝ => (𝓕 f) (-ξ)) 2 := by
  exact (fourier_L1_L2_memLp f hf h2).comp_measurePreserving
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).measurePreserving

theorem fourier_neg_L1_L2_norm
    (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/) :
    ‖(fourier_neg_L1_L2_memLp f hf h2).toLp (fun ξ : ℝ => (𝓕 f) (-ξ))‖ = ‖(h2.toLp f)‖ := by
  rw [Lp.norm_toLp]
  change (eLpNorm ((𝓕 f) ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ))) 2 volume).toReal = _
  rw [eLpNorm_comp_measurePreserving
    (fourier_L1_L2_memLp f hf h2).aestronglyMeasurable
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).measurePreserving]
  rw [← Lp.norm_toLp (𝓕 f) (fourier_L1_L2_memLp f hf h2)]
  exact fourier_L1_L2_norm f hf h2

theorem multiplier_fourier_integrable
    (m f : ℝ → ℂ /- [definition] -/)
    (hm : Integrable m /- [standing] -/)
    (hf : Integrable f /- [standing] -/) :
    Integrable (fun ξ => m ξ * (𝓕 f) (-ξ)) := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply (hm.norm.mul_const (∫ y : ℝ, ‖f y‖)).mono'
    (hm.aestronglyMeasurable.mul (hc.comp continuous_neg).aestronglyMeasurable)
  exact ae_of_all _ (fun ξ => by
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
        (innerₗ ℝ) f (-ξ)) (norm_nonneg _))

theorem multiplier_fourier_memLp
    (m f : ℝ → ℂ /- [definition] -/)
    (hm : AEStronglyMeasurable m volume /- [standing] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/)
    (C : ℝ /- [definition] -/)
    (hbound : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ C /- [standing] -/) :
    MemLp (fun ξ => m ξ * (𝓕 f) (-ξ)) 2 := by
  have hg := fourier_neg_L1_L2_memLp f hf h2
  apply hg.of_le_mul (hm.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with ξ hξ
  simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)

set_option maxHeartbeats 800000 in
theorem multiplier_fourier_norm_le
    (m f : ℝ → ℂ /- [definition] -/)
    (hm : AEStronglyMeasurable m volume /- [standing] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/)
    (C : ℝ /- [definition] -/)
    (hbound : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ C /- [standing] -/) :
    ‖(multiplier_fourier_memLp m f hm hf h2 C hbound).toLp (fun ξ => m ξ * (𝓕 f) (-ξ))‖ ≤ C * ‖(h2.toLp f)‖ := by
  rw [← fourier_neg_L1_L2_norm f hf h2]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hbound, (multiplier_fourier_memLp m f hm hf h2 C hbound).coeFn_toLp,
    (fourier_neg_L1_L2_memLp f hf h2).coeFn_toLp] with ξ hξ ha hb
  rw [ha, hb, norm_mul]
  exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)

/-- An inverse-Fourier kernel with bounded integrable multiplier is an L2 contraction
up to the multiplier bound. All convolution integrals are ordinary Bochner integrals. -/
theorem inverse_fourier_kernel_L2_bound
    (m f : ℝ → ℂ /- [definition] -/)
    (hm : Integrable m /- [standing] -/)
    (hf : Integrable f /- [standing] -/)
    (h2 : MemLp f 2 /- [standing] -/)
    (C : ℝ /- [definition] -/)
    (hbound : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ C /- [standing] -/) :
    ∃ hH : MemLp (fun x : ℝ => ∫ y : ℝ, f y * (𝓕⁻ m) (x + y)) 2,
      ‖hH.toLp (fun x : ℝ => ∫ y : ℝ, f y * (𝓕⁻ m) (x + y))‖ ≤ C * ‖(h2.toLp f)‖ := by
  have hmul := multiplier_fourier_memLp m f hm.aestronglyMeasurable hf h2 C hbound
  have hi := multiplier_fourier_integrable m f hm hf
  have hinv := inverse_fourier_L1_L2_memLp _ hi hmul
  have he : (fun x : ℝ => ∫ y : ℝ, f y * (𝓕⁻ m) (x + y)) =
      𝓕⁻ (fun ξ => m ξ * (𝓕 f) (-ξ)) := by
    funext x
    exact inverse_fourier_kernel_apply m f hm hf x
  rw [he]
  refine ⟨hinv, ?_⟩
  rw [inverse_fourier_L1_L2_norm _ hi hmul]
  exact multiplier_fourier_norm_le m f hm.aestronglyMeasurable hf h2 C hbound

open RMTFoundations.Airy
open Set

noncomputable def dampedHalfLineFunction
    (β : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) : ℝ → ℂ :=
  (Ioi 0).indicator (fun x => (Real.exp (-β * x) : ℂ) * (f x : ℂ))

theorem halfLine_damping_weight_memLp
    (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    MemLp (fun x : ℝ => Real.exp (-β * x)) 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrableOn_exp_mul_Ioi (a := -(2 * β)) (by linarith) 0
  apply h.congr
  exact ae_of_all _ (fun x => by
    change Real.exp (-(2 * β) * x) = Real.exp (-β * x) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring)

theorem halfLine_damped_memLp
    (β : ℝ /- [definition] -/)
    (hβ : 0 ≤ β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    MemLp (fun x : ℝ => (Real.exp (-β * x) : ℂ) * (f x : ℂ)) 2 halfLineMeasure := by
  apply (Lp.memLp f).of_le ?_ ?_
  · exact (by fun_prop : Continuous (fun x : ℝ => (Real.exp (-β * x) : ℂ))).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_real]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hx.le

theorem dampedHalfLine_memLp
    (β : ℝ /- [definition] -/)
    (hβ : 0 ≤ β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    MemLp (dampedHalfLineFunction β f) 2 := by
  exact (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr (halfLine_damped_memLp β hβ f)

theorem dampedHalfLine_integrable
    (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    Integrable (dampedHalfLineFunction β f) := by
  have hdom := (halfLine_damping_weight_memLp β hβ).integrable_mul (Lp.memLp f).norm
  have hi : Integrable (fun x : ℝ => (Real.exp (-β * x) : ℂ) * (f x : ℂ)) halfLineMeasure := by
    apply hdom.mono' ?_ ?_
    · exact (halfLine_damped_memLp β hβ.le f).aestronglyMeasurable
    · exact ae_of_all _ (fun x => by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        rfl)
  exact (integrable_indicator_iff measurableSet_Ioi).mpr hi

theorem dampedHalfLine_norm_le
    (β : ℝ /- [definition] -/)
    (hβ : 0 ≤ β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ‖(dampedHalfLine_memLp β hβ f).toLp (dampedHalfLineFunction β f)‖ ≤ ‖f‖ := by
  have hw := halfLine_damped_memLp β hβ f
  have he : ‖(dampedHalfLine_memLp β hβ f).toLp (dampedHalfLineFunction β f)‖ = ‖hw.toLp (fun x : ℝ => (Real.exp (-β * x) : ℂ) * (f x : ℂ))‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, dampedHalfLineFunction,
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet]
  rw [he]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hw.coeFn_toLp, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  rw [hx, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_real]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hxpos.le

theorem inverse_fourier_phase_shift
    (m : ℝ → ℂ /- [definition] -/)
    (s x : ℝ /- [definition] -/) :
    (𝓕⁻ (fun ξ => fourierPositivePhase ξ s * m ξ)) x = (𝓕⁻ m) (x + s) := by
  simp_rw [inverse_fourier_eq_positivePhase, fourierPositivePhase_add]
  apply integral_congr_ae
  exact ae_of_all _ (fun ξ => by ring)

theorem restrict_L2_norm_le
    (f : ℝ → ℂ /- [definition] -/)
    (hf : MemLp f 2 /- [standing] -/) :
    ‖(hf.restrict (Ioi 0)).toLp f‖ ≤ ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_restrict_le f 2 volume (Ioi 0))

end RMTFoundations.AiryBounds

#print axioms RMTFoundations.AiryBounds.fourier_integrable_schwartz_pairing
#print axioms RMTFoundations.AiryBounds.fourier_L1_L2_ae
#print axioms RMTFoundations.AiryBounds.fourier_L1_L2_memLp
#print axioms RMTFoundations.AiryBounds.fourier_L1_L2_norm
#print axioms RMTFoundations.AiryBounds.inverse_fourier_integrable_schwartz_pairing
#print axioms RMTFoundations.AiryBounds.inverse_fourier_L1_L2_ae
#print axioms RMTFoundations.AiryBounds.inverse_fourier_L1_L2_memLp
#print axioms RMTFoundations.AiryBounds.inverse_fourier_L1_L2_norm
#print axioms RMTFoundations.AiryBounds.fourierPositivePhase
#print axioms RMTFoundations.AiryBounds.fourierPositivePhase_norm
#print axioms RMTFoundations.AiryBounds.fourierPositivePhase_add
#print axioms RMTFoundations.AiryBounds.inverse_fourier_eq_positivePhase
#print axioms RMTFoundations.AiryBounds.fourier_neg_eq_positivePhase
#print axioms RMTFoundations.AiryBounds.inverse_fourier_kernel_apply
#print axioms RMTFoundations.AiryBounds.fourier_neg_L1_L2_memLp
#print axioms RMTFoundations.AiryBounds.fourier_neg_L1_L2_norm
#print axioms RMTFoundations.AiryBounds.multiplier_fourier_integrable
#print axioms RMTFoundations.AiryBounds.multiplier_fourier_memLp
#print axioms RMTFoundations.AiryBounds.multiplier_fourier_norm_le
#print axioms RMTFoundations.AiryBounds.inverse_fourier_kernel_L2_bound
#print axioms RMTFoundations.AiryBounds.dampedHalfLineFunction
#print axioms RMTFoundations.AiryBounds.halfLine_damping_weight_memLp
#print axioms RMTFoundations.AiryBounds.halfLine_damped_memLp
#print axioms RMTFoundations.AiryBounds.dampedHalfLine_memLp
#print axioms RMTFoundations.AiryBounds.dampedHalfLine_integrable
#print axioms RMTFoundations.AiryBounds.dampedHalfLine_norm_le
#print axioms RMTFoundations.AiryBounds.inverse_fourier_phase_shift
#print axioms RMTFoundations.AiryBounds.restrict_L2_norm_le
