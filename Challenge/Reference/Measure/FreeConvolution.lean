import Challenge.Reference.Measure.HerglotzBorel
import Challenge.Reference.Measure.StieltjesSupport
import Mathlib

namespace RMTFoundations.FreeConvolution

open MeasureTheory Filter Topology Set
open RMTFoundations.Stieltjes (stieltjes)

section Basic

/-- `μ` puts no mass outside `[-R, R]`. -/
def SupportedIn (μ : Measure ℝ /- [definition] -/ ) (R : ℝ /- [definition] -/ ) : Prop := μ (Icc (-R) R)ᶜ = 0

/-- The mean `∫ t dμ(t)`. -/
noncomputable def mean (μ : Measure ℝ /- [definition] -/ ) : ℝ := ∫ t, t ∂μ

/-- `F_μ(w) - w` with `F_μ = 1/G_μ = -1/S_μ`, the reciprocal Cauchy transform. -/
noncomputable def hfun (μ : Measure ℝ /- [definition] -/ ) (w : ℂ /- [definition] -/ ) : ℂ := -(stieltjes μ w)⁻¹ - w

/-- The auxiliary function `u(t) = ((t - w) S_μ(w))⁻¹ - 1`. -/
noncomputable def uf (μ : Measure ℝ /- [definition] -/ ) (w : ℂ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) : ℂ :=
  ((t : ℂ) - w)⁻¹ * (stieltjes μ w)⁻¹ - 1

theorem ae_mem {μ : Measure ℝ /- [definition] -/ } {R : ℝ /- [definition] -/ } (h : SupportedIn μ R /- [standing] -/ ) :
    ∀ᵐ t ∂μ, t ∈ Icc (-R) R :=
  ae_iff.2 h

theorem sub_ne {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (t : ℝ /- [definition] -/ ) : (t : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem im_le_norm_sub {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (t : ℝ /- [definition] -/ ) : w.im ≤ ‖(t : ℂ) - w‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) - w)
  simp at this
  rwa [abs_of_pos hw] at this

theorem re_le_norm_sub (w : ℂ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) : |t - w.re| ≤ ‖(t : ℂ) - w‖ := by
  have := Complex.abs_re_le_norm ((t : ℂ) - w)
  simpa using this

theorem continuous_inv_sub {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    Continuous fun t : ℝ => ((t : ℂ) - w)⁻¹ :=
  (Complex.continuous_ofReal.sub continuous_const).inv₀ (sub_ne hw)

theorem norm_inv_sub_le {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (t : ℝ /- [definition] -/ ) : ‖((t : ℂ) - w)⁻¹‖ ≤ w.im⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hw (im_le_norm_sub hw t)

theorem integrable_inv_sub (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    Integrable (fun t : ℝ => ((t : ℂ) - w)⁻¹) μ :=
  Integrable.of_bound (continuous_inv_sub hw).aestronglyMeasurable w.im⁻¹
    (Eventually.of_forall (norm_inv_sub_le hw))

theorem integrable_ofReal {μ : Measure ℝ /- [definition] -/ } [IsFiniteMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } (h : SupportedIn μ R /- [standing] -/ ) :
    Integrable (fun t : ℝ => (t : ℂ)) μ :=
  Integrable.of_bound Complex.continuous_ofReal.aestronglyMeasurable R
    ((ae_mem h).mono fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ht)

theorem integrable_id {μ : Measure ℝ /- [definition] -/ } [IsFiniteMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } (h : SupportedIn μ R /- [standing] -/ ) :
    Integrable (fun t : ℝ => t) μ :=
  Integrable.of_bound continuous_id.aestronglyMeasurable R
    ((ae_mem h).mono fun t ht => by rw [Real.norm_eq_abs]; exact abs_le.2 ht)

theorem abs_mean_le {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } (h : SupportedIn μ R /- [standing] -/ ) :
    |mean μ| ≤ R := by
  rw [mean, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le (integrable_const R)
    ((ae_mem h).mono fun t ht => by rw [Real.norm_eq_abs]; exact abs_le.2 ht)
  simpa using this

/-- `Im (t - w)⁻¹ = Im w · ‖(t - w)⁻¹‖²`. -/
theorem im_inv_sub (w : ℂ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) :
    (((t : ℂ) - w)⁻¹).im = w.im * ‖((t : ℂ) - w)⁻¹‖ ^ 2 := by
  rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

theorem im_stieltjes_nonneg (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    0 ≤ (stieltjes μ w).im := by
  have h := integral_im (integrable_inv_sub μ hw)
  simp only [RCLike.im_to_complex] at h
  rw [stieltjes, ← h]
  refine integral_nonneg fun t => ?_
  rw [im_inv_sub w]
  positivity

/-- `Im S_μ(w) = Im w ∫ ‖(t - w)⁻¹‖² dμ`. -/
theorem im_stieltjes_eq (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    (stieltjes μ w).im = w.im * ∫ t, ‖((t : ℂ) - w)⁻¹‖ ^ 2 ∂μ := by
  have h := integral_im (integrable_inv_sub μ hw)
  simp only [RCLike.im_to_complex] at h
  rw [stieltjes, ← h, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => im_inv_sub w t)

theorem im_stieltjes_pos (μ : Measure ℝ /- [definition] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ }
    (h : SupportedIn μ R /- [standing] -/ ) {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) : 0 < (stieltjes μ w).im := by
  rw [im_stieltjes_eq μ hw]
  refine mul_pos hw ?_
  have hb : ∀ᵐ t : ℝ ∂μ, (R + ‖w‖) ^ 2 ≠ 0 ∧ ((R + ‖w‖) ^ 2)⁻¹ ≤ ‖((t : ℂ) - w)⁻¹‖ ^ 2 := by
    filter_upwards [ae_mem h] with t ht
    have hR : 0 ≤ R := by linarith [ht.1, ht.2]
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hw (by
      have := Complex.abs_im_le_norm w; rw [abs_of_pos hw] at this; exact this)
    have hn : ‖(t : ℂ) - w‖ ≤ R + ‖w‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith [abs_le.2 ht]
    have hpos : 0 < ‖(t : ℂ) - w‖ := norm_pos_iff.2 (sub_ne hw t)
    refine ⟨by positivity, ?_⟩
    rw [norm_inv, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hn 2)
  have hint : Integrable (fun t : ℝ => ‖((t : ℂ) - w)⁻¹‖ ^ 2) μ :=
    Integrable.of_bound ((continuous_inv_sub hw).norm.pow 2).aestronglyMeasurable
      (w.im⁻¹ ^ 2) (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_le hw t) 2)
  have hle := integral_mono_ae (integrable_const _) hint (hb.mono fun t ht => ht.2)
  rw [integral_const, probReal_univ, one_smul] at hle
  have : 0 < ((R + ‖w‖) ^ 2)⁻¹ := by
    obtain ⟨t, ht⟩ := hb.exists
    exact inv_pos.2 (lt_of_le_of_ne (sq_nonneg _) (Ne.symm ht.1))
  linarith

theorem stieltjes_ne {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ }
    (h : SupportedIn μ R /- [standing] -/ ) {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) : stieltjes μ w ≠ 0 := by
  intro h0
  have := im_stieltjes_pos μ h hw
  rw [h0, Complex.zero_im] at this
  exact lt_irrefl _ this

end Basic


section HRep

theorem integrable_conj {ν : Measure ℝ /- [definition] -/ } {f : ℝ → ℂ /- [definition] -/ } (hf : Integrable f ν /- [standing] -/ ) :
    Integrable (fun t => (starRingEnd ℂ) (f t)) ν :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

variable {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } {w : ℂ /- [definition] -/ }

theorem R_nonneg (h : SupportedIn μ R /- [standing] -/ ) : 0 ≤ R := by
  obtain ⟨t, ht⟩ := (ae_mem h).exists
  linarith [ht.1, ht.2]

omit [IsProbabilityMeasure μ] in
theorem continuous_uf (hw : 0 < w.im /- [standing] -/ ) : Continuous (uf μ w) :=
  ((continuous_inv_sub hw).mul continuous_const).sub continuous_const

omit [IsProbabilityMeasure μ] in
theorem norm_uf_le (hw : 0 < w.im /- [standing] -/ ) (t : ℝ /- [definition] -/ ) :
    ‖uf μ w t‖ ≤ w.im⁻¹ * ‖(stieltjes μ w)⁻¹‖ + 1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_one]
  gcongr
  exact norm_inv_sub_le hw t

theorem integrable_uf (hw : 0 < w.im /- [standing] -/ ) : Integrable (uf μ w) μ :=
  Integrable.of_bound (continuous_uf hw).aestronglyMeasurable _
    (Eventually.of_forall (norm_uf_le hw))

theorem integrable_uf_mul (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) :
    Integrable (fun t : ℝ => uf μ w t * t) μ :=
  Integrable.of_bound ((continuous_uf hw).mul Complex.continuous_ofReal).aestronglyMeasurable
    ((w.im⁻¹ * ‖(stieltjes μ w)⁻¹‖ + 1) * R) ((ae_mem h).mono fun t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (norm_uf_le hw t) (abs_le.2 ht) (abs_nonneg _)
        (by positivity))

theorem integrable_normSq_uf (hw : 0 < w.im /- [standing] -/ ) :
    Integrable (fun t : ℝ => Complex.normSq (uf μ w t)) μ :=
  Integrable.of_bound (Complex.continuous_normSq.comp (continuous_uf hw)).aestronglyMeasurable
    ((w.im⁻¹ * ‖(stieltjes μ w)⁻¹‖ + 1) ^ 2) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), ← Complex.sq_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_uf_le hw t) 2)

theorem integral_uf (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) : ∫ t, uf μ w t ∂μ = 0 := by
  unfold uf
  rw [integral_sub ((integrable_inv_sub μ hw).mul_const _) (integrable_const _),
    integral_mul_const, integral_const, probReal_univ, one_smul]
  change stieltjes μ w * (stieltjes μ w)⁻¹ - 1 = 0
  rw [mul_inv_cancel₀ (stieltjes_ne h hw), sub_self]

theorem integral_uf_mul (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) :
    ∫ t, uf μ w t * t ∂μ = -(hfun μ w + mean μ) := by
  have hpt : ∀ t : ℝ, uf μ w t * t
      = (stieltjes μ w)⁻¹ + w * (stieltjes μ w)⁻¹ * ((t : ℂ) - w)⁻¹ - t := by
    intro t
    have hne := sub_ne hw t
    unfold uf
    field_simp
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun t : ℝ => (stieltjes μ w)⁻¹
      + w * (stieltjes μ w)⁻¹ * ((t : ℂ) - w)⁻¹) μ :=
    (integrable_const _).add ((integrable_inv_sub μ hw).const_mul _)
  rw [integral_sub i1 (integrable_ofReal h), integral_add (integrable_const _)
    ((integrable_inv_sub μ hw).const_mul _), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_complex_ofReal]
  change _ + _ * stieltjes μ w - _ = _
  rw [hfun, mean]
  field_simp [stieltjes_ne h hw]
  ring

theorem mul_uf (hw : 0 < w.im /- [standing] -/ ) (h : SupportedIn μ R /- [standing] -/ ) (t : ℝ /- [definition] -/ ) :
    ((t : ℂ) - w) * uf μ w t = (stieltjes μ w)⁻¹ - ((t : ℂ) - w) := by
  have hne := sub_ne hw t
  have hS := stieltjes_ne h hw
  unfold uf
  field_simp

/-- **`Im (F_μ(w) - w) = Im w ∫ |u|² dμ`.** -/
theorem im_hfun (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) :
    (hfun μ w).im = w.im * ∫ t, Complex.normSq (uf μ w t) ∂μ := by
  set S := stieltjes μ w
  set g : ℝ → ℂ := fun t => (starRingEnd ℂ) (uf μ w t) * (S⁻¹ + w)
    - (starRingEnd ℂ) (uf μ w t * t) with hg
  have hpt : ∀ t : ℝ, g t = ((t : ℂ) - w) * (Complex.normSq (uf μ w t) : ℂ) := by
    intro t
    rw [hg]
    simp only
    rw [Complex.normSq_eq_conj_mul_self, map_mul, Complex.conj_ofReal]
    have := mul_uf (μ := μ) hw h t
    linear_combination (-(starRingEnd ℂ) (uf μ w t)) * this
  have hgi : Integrable g μ := by
    have e : g = fun t => (starRingEnd ℂ) (uf μ w t) * (S⁻¹ + w)
        - (starRingEnd ℂ) (uf μ w t * t) := rfl
    rw [e]
    refine Integrable.sub ?_ ?_
    · exact (integrable_conj (integrable_uf (μ := μ) hw)).mul_const _
    · exact integrable_conj (integrable_uf_mul (μ := μ) h hw)
  have hint : ∫ t, g t ∂μ = (starRingEnd ℂ) (hfun μ w + mean μ) := by
    rw [hg]
    simp only
    rw [integral_sub ((integrable_conj (integrable_uf (μ := μ) hw)).mul_const _)
      (integrable_conj (integrable_uf_mul (μ := μ) h hw)), integral_mul_const]
    rw [integral_conj, integral_conj, integral_uf h hw, integral_uf_mul h hw]
    simp
  have him := integral_im hgi
  simp only [RCLike.im_to_complex] at him
  rw [hint] at him
  have hpt2 : ∀ t : ℝ, (g t).im = -(w.im * Complex.normSq (uf μ w t)) := by
    intro t
    rw [hpt t]
    simp
  simp_rw [hpt2] at him
  rw [integral_neg, integral_const_mul] at him
  have : ((starRingEnd ℂ) (hfun μ w + mean μ)).im = -(hfun μ w).im := by simp
  rw [this] at him
  linarith

theorem im_hfun_nonneg (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) : 0 ≤ (hfun μ w).im := by
  rw [im_hfun h hw]
  exact mul_nonneg hw.le (integral_nonneg fun t => Complex.normSq_nonneg _)

/-- **`|F_μ(w) - w + m| ≤ R²/Im w`**: the bound the Herglotz representation needs. -/
theorem norm_hfun_add_le (h : SupportedIn μ R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ ) :
    ‖hfun μ w + mean μ‖ ≤ R ^ 2 / w.im := by
  set H := hfun μ w + mean μ
  set A := ∫ t, Complex.normSq (uf μ w t) ∂μ
  have hH : ‖H‖ = ‖∫ t, uf μ w t * t ∂μ‖ := by rw [integral_uf_mul h hw, norm_neg]
  have hbd : ‖∫ t, uf μ w t * t ∂μ‖ ≤ ∫ t, (w.im * Complex.normSq (uf μ w t)
      + R ^ 2 / w.im) / 2 ∂μ := by
    refine norm_integral_le_of_norm_le
      (((integrable_normSq_uf (μ := μ) hw).const_mul _).add (integrable_const _) |>.div_const _)
      ((ae_mem h).mono fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.sq_norm]
    have h1 : |t| ≤ R := abs_le.2 ht
    have h3 : ‖uf μ w t‖ * |t| ≤ ‖uf μ w t‖ * R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have e : w.im * ‖uf μ w t‖ ^ 2 + R ^ 2 / w.im - 2 * (‖uf μ w t‖ * R)
        = (w.im * ‖uf μ w t‖ - R) ^ 2 / w.im := by
      field_simp
      ring
    have h4 : 0 ≤ (w.im * ‖uf μ w t‖ - R) ^ 2 / w.im := div_nonneg (sq_nonneg _) hw.le
    linarith
  have hA : ∫ t, (w.im * Complex.normSq (uf μ w t) + R ^ 2 / w.im) / 2 ∂μ
      = (w.im * A + R ^ 2 / w.im) / 2 := by
    rw [integral_div, integral_add ((integrable_normSq_uf (μ := μ) hw).const_mul _)
      (integrable_const _), integral_const_mul, integral_const, probReal_univ, one_smul]
  have him : H.im = w.im * A := by
    have : H.im = (hfun μ w).im := by simp [H]
    rw [this, im_hfun h hw]
  have hle : H.im ≤ ‖H‖ := (le_abs_self _).trans (Complex.abs_im_le_norm H)
  rw [hH]
  rw [hA] at hbd
  rw [hH] at hle
  rw [le_div_iff₀ hw]
  have : ‖∫ t, uf μ w t * t ∂μ‖ ≤ R ^ 2 / w.im := by linarith
  rwa [le_div_iff₀ hw] at this

end HRep

section Tail

variable {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } {w : ℂ /- [definition] -/ }

theorem norm_inv_sub_tail {s : ℝ /- [definition] -/ } (hs : s ∈ Icc (-R) R /- [standing] -/ )
    (hx : R < |w.re| /- [standing] -/ ) : ‖((s : ℂ) - w)⁻¹‖ ≤ 1 / (|w.re| - R) := by
  rw [norm_inv, one_div]
  refine inv_anti₀ (by linarith) ?_
  have h1 := re_le_norm_sub w s
  have h2 : |w.re| - R ≤ |s - w.re| := by
    have := abs_sub_abs_le_abs_sub w.re s
    rw [abs_sub_comm] at this
    linarith [abs_le.2 hs]
  linarith

/-- For `|Re w| ≥ 5R` and `t ∈ [-R, R]`, `|u(t)| ≤ 4R/(|Re w| - R)`. -/
theorem norm_uf_tail (h : SupportedIn μ R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ )
    (hx : 5 * R ≤ |w.re| /- [standing] -/ ) {t : ℝ /- [definition] -/ } (ht : t ∈ Icc (-R) R /- [standing] -/ ) :
    ‖uf μ w t‖ ≤ 4 * R / (|w.re| - R) := by
  set S := stieltjes μ w
  set q := ((t : ℂ) - w) * S with hq
  have hd : 0 < |w.re| - R := by linarith
  have hq1 : q - 1 = ∫ s, ((t : ℂ) - w) * ((s : ℂ) - w)⁻¹ - 1 ∂μ := by
    rw [integral_sub ((integrable_inv_sub μ hw).const_mul _) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
    rfl
  have hq1b : ‖q - 1‖ ≤ 2 * R / (|w.re| - R) := by
    rw [hq1]
    have := norm_integral_le_of_norm_le (integrable_const (2 * R / (|w.re| - R)))
      ((ae_mem h).mono fun s hs => by
        have hsne := sub_ne hw s
        have e : ((t : ℂ) - w) * ((s : ℂ) - w)⁻¹ - 1 = ((t : ℂ) - s) * ((s : ℂ) - w)⁻¹ := by
          field_simp
          ring
        show ‖((t : ℂ) - w) * ((s : ℂ) - w)⁻¹ - 1‖ ≤ 2 * R / (|w.re| - R)
        rw [e, norm_mul, div_eq_mul_one_div]
        have ht2 : ‖(t : ℂ) - s‖ ≤ 2 * R := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
        exact mul_le_mul ht2 (norm_inv_sub_tail hs (by linarith)) (norm_nonneg _)
          (by linarith))
      (μ := μ) (f := fun s : ℝ => ((t : ℂ) - w) * ((s : ℂ) - w)⁻¹ - 1)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hsmall : 2 * R / (|w.re| - R) ≤ 1 / 2 := by
    rw [div_le_iff₀ hd]; linarith
  have hqn : 1 / 2 ≤ ‖q‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - q)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hqn; linarith
  have hu : uf μ w t = (1 - q) / q := by
    rw [uf, ← mul_inv]
    change q⁻¹ - 1 = (1 - q) / q
    field_simp
  rw [hu, norm_div, norm_sub_rev]
  rw [div_le_iff₀ (by linarith)]
  calc ‖q - 1‖ ≤ 2 * R / (|w.re| - R) := hq1b
    _ = 4 * R / (|w.re| - R) * (1 / 2) := by ring
    _ ≤ 4 * R / (|w.re| - R) * ‖q‖ := by gcongr

theorem norm_hfun_add_tail (h : SupportedIn μ R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ )
    (hx : 5 * R ≤ |w.re| /- [standing] -/ ) :
    ‖hfun μ w + mean μ‖ ≤ 4 * R ^ 2 / (|w.re| - R) := by
  rw [← norm_neg, ← integral_uf_mul h hw]
  have := norm_integral_le_of_norm_le (integrable_const (4 * R ^ 2 / (|w.re| - R)))
    ((ae_mem h).mono fun t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have e : 4 * R ^ 2 / (|w.re| - R) = 4 * R / (|w.re| - R) * R := by ring
      rw [e]
      exact mul_le_mul (norm_uf_tail h hR hw hx ht) (abs_le.2 ht) (abs_nonneg _)
        (by have : 0 < |w.re| - R := by linarith
            positivity))
    (μ := μ) (f := fun t => uf μ w t * t)
  rwa [integral_const, probReal_univ, one_smul] at this

theorem im_hfun_tail (h : SupportedIn μ R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) (hw : 0 < w.im /- [standing] -/ )
    (hx : 5 * R ≤ |w.re| /- [standing] -/ ) :
    (hfun μ w).im ≤ w.im * (4 * R / (|w.re| - R)) ^ 2 := by
  rw [im_hfun h hw]
  refine mul_le_mul_of_nonneg_left ?_ hw.le
  have := integral_mono_ae (integrable_normSq_uf (μ := μ) hw)
    (integrable_const ((4 * R / (|w.re| - R)) ^ 2))
    ((ae_mem h).mono fun t ht => by
      show Complex.normSq (uf μ w t) ≤ (4 * R / (|w.re| - R)) ^ 2
      rw [← Complex.sq_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_uf_tail h hR hw hx ht) 2)
  rwa [integral_const, probReal_univ, one_smul] at this

end Tail

section CS

/-- Cauchy–Schwarz for real integrals, via the discriminant. -/
theorem sq_integral_mul_le {ν : Measure ℝ /- [definition] -/ } {f g : ℝ → ℝ /- [definition] -/ } (hff : Integrable (fun t => f t ^ 2) ν /- [standing] -/ )
    (hgg : Integrable (fun t => g t ^ 2) ν /- [standing] -/ ) (hfg : Integrable (fun t => f t * g t) ν /- [standing] -/ ) :
    (∫ t, f t * g t ∂ν) ^ 2 ≤ (∫ t, f t ^ 2 ∂ν) * ∫ t, g t ^ 2 ∂ν := by
  have key : ∀ x : ℝ, 0 ≤ (∫ t, f t ^ 2 ∂ν) * (x * x) + (2 * ∫ t, f t * g t ∂ν) * x
      + ∫ t, g t ^ 2 ∂ν := by
    intro x
    have hpt : ∀ t, (x * f t + g t) ^ 2 = x * x * f t ^ 2 + 2 * x * (f t * g t) + g t ^ 2 := by
      intro t; ring
    have hi : ∫ t, (x * f t + g t) ^ 2 ∂ν = (∫ t, f t ^ 2 ∂ν) * (x * x)
        + (2 * ∫ t, f t * g t ∂ν) * x + ∫ t, g t ^ 2 ∂ν := by
      simp_rw [hpt]
      have i1 : Integrable (fun t => x * x * f t ^ 2) ν := hff.const_mul _
      have i2 : Integrable (fun t => 2 * x * (f t * g t)) ν := hfg.const_mul _
      have i12 : Integrable (fun t => x * x * f t ^ 2 + 2 * x * (f t * g t)) ν := i1.add i2
      rw [integral_add i12 hgg, integral_add i1 i2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← hi]
    exact integral_nonneg fun t => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

variable (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ]

/-- **Nonexpansiveness of Stieltjes transforms**:
`|S(w) - S(wv)|² ≤ |w - wv|² (Im S(w)/Im w)(Im S(wv)/Im wv)`. -/
theorem stieltjes_contract {w wv : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (hwp : 0 < wv.im /- [standing] -/ ) :
    ‖stieltjes ν w - stieltjes ν wv‖ ^ 2
      ≤ ‖w - wv‖ ^ 2 * ((stieltjes ν w).im / w.im) * ((stieltjes ν wv).im / wv.im) := by
  have hdiff : stieltjes ν w - stieltjes ν wv
      = (w - wv) * ∫ t, ((t : ℂ) - w)⁻¹ * ((t : ℂ) - wv)⁻¹ ∂ν := by
    rw [stieltjes, stieltjes, ← integral_sub (integrable_inv_sub ν hw) (integrable_inv_sub ν hwp),
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have h1 := sub_ne hw t
    have h2 := sub_ne hwp t
    simp only
    field_simp
    ring
  set f : ℝ → ℝ := fun t => ‖((t : ℂ) - w)⁻¹‖
  set g : ℝ → ℝ := fun t => ‖((t : ℂ) - wv)⁻¹‖
  have cf : Continuous f := (continuous_inv_sub hw).norm
  have cg : Continuous g := (continuous_inv_sub hwp).norm
  have bf : ∀ t, ‖f t‖ ≤ w.im⁻¹ := fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact norm_inv_sub_le hw t
  have bg : ∀ t, ‖g t‖ ≤ wv.im⁻¹ := fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact norm_inv_sub_le hwp t
  have iff : Integrable (fun t => f t ^ 2) ν :=
    Integrable.of_bound (cf.pow 2).aestronglyMeasurable (w.im⁻¹ ^ 2)
      (Eventually.of_forall fun t => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (bf t) 2)
  have igg : Integrable (fun t => g t ^ 2) ν :=
    Integrable.of_bound (cg.pow 2).aestronglyMeasurable (wv.im⁻¹ ^ 2)
      (Eventually.of_forall fun t => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (bg t) 2)
  have ifg : Integrable (fun t => f t * g t) ν :=
    Integrable.of_bound (cf.mul cg).aestronglyMeasurable (w.im⁻¹ * wv.im⁻¹)
      (Eventually.of_forall fun t => by
        rw [norm_mul]; exact mul_le_mul (bf t) (bg t) (norm_nonneg _) (by positivity))
  have hnorm : ‖∫ t, ((t : ℂ) - w)⁻¹ * ((t : ℂ) - wv)⁻¹ ∂ν‖ ≤ ∫ t, f t * g t ∂ν :=
    norm_integral_le_of_norm_le ifg (Eventually.of_forall fun t => by rw [norm_mul])
  have hcs := sq_integral_mul_le iff igg ifg
  have hf2 : ∫ t, f t ^ 2 ∂ν = (stieltjes ν w).im / w.im := by
    rw [im_stieltjes_eq ν hw, mul_div_cancel_left₀ _ hw.ne']
  have hg2 : ∫ t, g t ^ 2 ∂ν = (stieltjes ν wv).im / wv.im := by
    rw [im_stieltjes_eq ν hwp, mul_div_cancel_left₀ _ hwp.ne']
  rw [hdiff, norm_mul, mul_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← hf2, ← hg2]
  refine le_trans ?_ hcs
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end CS

/-- The analytic properties of a shift `h = F_μ - id` used by the fixed-point argument. -/
structure ShiftBounds (h : ℂ → ℂ /- [definition] -/ ) (a M L B : ℝ /- [definition] -/ ) : Prop where
  /-- holomorphic on `ℂ⁺` -/
  diff : DifferentiableOn ℂ h RMTFoundations.AnalyticHalfPlane.upper
  /-- `Im h ≥ 0` -/
  im_nonneg : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, 0 ≤ (h w).im
  /-- `Im h(w) ≤ M/Im w` -/
  im_le : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, (h w).im ≤ M / w.im
  /-- `|h(w)| ≤ a + M/Im w` -/
  norm_le : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, ‖h w‖ ≤ a + M / w.im
  /-- the Schwarz-Pick type contraction inherited from a Stieltjes transform -/
  contract : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, ∀ v ∈ RMTFoundations.AnalyticHalfPlane.upper,
    ‖h w - h v‖ ^ 2 ≤ ‖w - v‖ ^ 2 * ((h w).im / w.im) * ((h v).im / v.im)
  /-- the tail bounds for `|Re w| ≥ L` -/
  tail : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, L ≤ |w.re| → ‖h w‖ ≤ B ∧ (h w).im ≤ w.im / 4
  /-- `M ≥ 0` -/
  M_nonneg : 0 ≤ M

section Shift

variable {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ }

theorem hfun_differentiableOn (h : SupportedIn μ R /- [standing] -/ ) : DifferentiableOn ℂ (hfun μ) RMTFoundations.AnalyticHalfPlane.upper := by
  have h1 := (RMTFoundations.HerglotzBorelProof.stieltjes_differentiableOn μ).inv
    (fun w hw => stieltjes_ne h hw)
  exact h1.neg.sub differentiableOn_id

/-- **The Nevanlinna representation of `F_μ - id`**, from the proved Herglotz theorem:
`F_μ(w) - w + m = S_ν(w)` for a finite measure `ν` of mass at most `R²`. -/
theorem hfun_rep (h : SupportedIn μ R /- [standing] -/ ) : ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
    ν.real univ ≤ R ^ 2 ∧ ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, hfun μ w + mean μ = stieltjes ν w := by
  refine RMTFoundations.HerglotzBorelProof.herglotzBorel (fun w => hfun μ w + mean μ) (R ^ 2)
    ((hfun_differentiableOn h).add_const _) (fun w hw => ?_) (fun w hw => ?_)
  · have : (hfun μ w + mean μ).im = (hfun μ w).im := by simp
    rw [this]; exact im_hfun_nonneg h hw
  · exact norm_hfun_add_le h hw

theorem shiftBounds_hfun (h : SupportedIn μ R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    ShiftBounds (hfun μ) R (R ^ 2) (9 * R) (2 * R) := by
  have him : ∀ w, (hfun μ w + mean μ).im = (hfun μ w).im := fun w => by simp
  have hm := abs_mean_le h
  obtain ⟨ν, hν, -, hrep⟩ := hfun_rep h
  refine ⟨hfun_differentiableOn h, fun w hw => im_hfun_nonneg h hw, fun w hw => ?_,
    fun w hw => ?_, fun w hw v hv => ?_, fun w hw hx => ?_, sq_nonneg R⟩
  · rw [← him]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (norm_hfun_add_le h hw))
  · have e : hfun μ w = (hfun μ w + mean μ) - (mean μ : ℂ) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [norm_hfun_add_le h hw]
  · have e : hfun μ w - hfun μ v = stieltjes ν w - stieltjes ν v := by
      rw [← hrep w hw, ← hrep v hv]; ring
    rw [e, ← him w, ← him v, hrep w hw, hrep v hv]
    exact stieltjes_contract ν hw hv
  · have hwp : 0 < w.im := hw
    have hx5 : 5 * R ≤ |w.re| := by linarith
    have hd : 8 * R ≤ |w.re| - R := by linarith
    refine ⟨?_, ?_⟩
    · have e : hfun μ w = (hfun μ w + mean μ) - (mean μ : ℂ) := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_hfun_add_tail h hR hwp hx5
      have h2 : 4 * R ^ 2 / (|w.re| - R) ≤ R := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    · refine (im_hfun_tail h hR hwp hx5).trans ?_
      have h2 : 4 * R / (|w.re| - R) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have h3 : 0 ≤ 4 * R / (|w.re| - R) := by
        have : 0 < |w.re| - R := by linarith
        positivity
      have : (4 * R / (|w.re| - R)) ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith

end Shift

section FixedPoint

/-- One half-step `w ↦ z + h(w)` of the subordination iteration. -/
def Tm (h : ℂ → ℂ /- [standing] -/ ) (z w : ℂ /- [definition] -/ ) : ℂ := z + h w

/-- The subordination map `w ↦ z + h₂(z + h₁(w))`; its fixed point is `ω₁(z)`. -/
def fm (h1 h2 : ℂ → ℂ /- [standing] -/ ) (z w : ℂ /- [definition] -/ ) : ℂ := Tm h2 z (Tm h1 z w)

/-- The orbit of `z` under `fm`. -/
def orb (h1 h2 : ℂ → ℂ /- [standing] -/ ) (z : ℂ /- [definition] -/ ) : ℕ → ℂ
  | 0 => z
  | n + 1 => fm h1 h2 z (orb h1 h2 z n)

/-- The limit of the orbit: the subordination function `ω₁(z)`. -/
noncomputable def om1 (h1 h2 : ℂ → ℂ /- [standing] -/ ) (z : ℂ /- [definition] -/ ) : ℂ := limUnder atTop (orb h1 h2 z)

/-- `D(a, b) = |a - b|²/(Im a Im b)`, the quantity the iteration contracts. -/
noncomputable def Dq (a b : ℂ /- [definition] -/ ) : ℝ := ‖a - b‖ ^ 2 / (a.im * b.im)

/-- The per-half-step contraction factor `M/(η² + M)`. -/
noncomputable def kf (M η : ℝ /- [definition] -/ ) : ℝ := M / (η ^ 2 + M)

theorem kf_nonneg {M η : ℝ /- [definition] -/ } (hM : 0 ≤ M /- [standing] -/ ) : 0 ≤ kf M η := by
  unfold kf; positivity

theorem kf_lt_one {M η : ℝ /- [definition] -/ } (hM : 0 ≤ M /- [standing] -/ ) (hη : 0 < η /- [standing] -/ ) : kf M η < 1 := by
  unfold kf
  rw [div_lt_one (by positivity)]
  nlinarith

theorem kf_anti {M η η₁ : ℝ /- [definition] -/ } (hM : 0 ≤ M /- [standing] -/ ) (hη₁ : 0 < η₁ /- [standing] -/ ) (h : η₁ ≤ η /- [standing] -/ ) :
    kf M η ≤ kf M η₁ := by
  unfold kf
  exact div_le_div_of_nonneg_left hM (by positivity) (by nlinarith)

variable {h : ℂ → ℂ /- [standing] -/ } {a M L B : ℝ /- [definition] -/ }

theorem Tm_im (z w : ℂ /- [definition] -/ ) : (Tm h z w).im = z.im + (h w).im := by simp [Tm]

theorem Tm_im_ge (hs : ShiftBounds h a M L B /- [standing] -/ ) {z w : ℂ /- [definition] -/ } (hw : w ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) :
    z.im ≤ (Tm h z w).im := by
  rw [Tm_im]; linarith [hs.im_nonneg w hw]

theorem Tm_mem (hs : ShiftBounds h a M L B /- [standing] -/ ) {z w : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hw : w ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) :
    Tm h z w ∈ RMTFoundations.AnalyticHalfPlane.upper :=
  lt_of_lt_of_le hz (Tm_im_ge hs hw)

theorem Tm_im_le (hs : ShiftBounds h a M L B /- [standing] -/ ) {z w : ℂ /- [definition] -/ } (hw : w ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ )
    (hzw : z.im ≤ w.im /- [standing] -/ ) (hz : 0 < z.im /- [standing] -/ ) :
    (Tm h z w).im ≤ z.im + M / z.im := by
  rw [Tm_im]
  have := hs.im_le w hw
  have : M / w.im ≤ M / z.im := div_le_div_of_nonneg_left hs.M_nonneg hz hzw
  linarith

/-- **One half-step contracts `D` by `kf M (Im z)`**. -/
theorem Dq_Tm (hs : ShiftBounds h a M L B /- [standing] -/ ) {z w v : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ )
    (hw : z.im ≤ w.im /- [standing] -/ ) (hv : z.im ≤ v.im /- [standing] -/ ) :
    Dq (Tm h z w) (Tm h z v) ≤ kf M z.im ^ 2 * Dq w v := by
  have hw0 : w ∈ RMTFoundations.AnalyticHalfPlane.upper := lt_of_lt_of_le hz hw
  have hv0 : v ∈ RMTFoundations.AnalyticHalfPlane.upper := lt_of_lt_of_le hz hv
  have hw0p : 0 < w.im := hw0
  have hv0p : 0 < v.im := hv0
  set η := z.im
  set s := (h w).im
  set sv := (h v).im
  have hs0 : 0 ≤ s := hs.im_nonneg w hw0
  have hs0v : 0 ≤ sv := hs.im_nonneg v hv0
  have hk : ∀ {u : ℂ}, η ≤ u.im → 0 ≤ (h u).im → (h u).im ≤ M / u.im →
      (h u).im / (η + (h u).im) ≤ kf M η := by
    intro u hu h0 hle
    have hu0 : 0 < u.im := lt_of_lt_of_le hz hu
    rw [div_le_iff₀ (by linarith), kf, div_mul_eq_mul_div,
      le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hz 2) hs.M_nonneg)]
    have h1 : (h u).im * u.im ≤ M := by rwa [le_div_iff₀ hu0] at hle
    have h2 : (h u).im * η ≤ (h u).im * u.im := mul_le_mul_of_nonneg_left hu h0
    nlinarith
  have k1 := hk hw hs0 (hs.im_le w hw0)
  have k2 := hk hv hs0v (hs.im_le v hv0)
  have hc := hs.contract w hw0 v hv0
  have e1 : (Tm h z w).im = η + s := Tm_im z w
  have e2 : (Tm h z v).im = η + sv := Tm_im z v
  have e3 : Tm h z w - Tm h z v = h w - h v := by simp [Tm]
  unfold Dq
  rw [e1, e2, e3]
  have hp1 : 0 < η + s := by linarith
  have hp2 : 0 < η + sv := by linarith
  calc ‖h w - h v‖ ^ 2 / ((η + s) * (η + sv))
      ≤ ‖w - v‖ ^ 2 * (s / w.im) * (sv / v.im) / ((η + s) * (η + sv)) := by gcongr
    _ = ‖w - v‖ ^ 2 / (w.im * v.im) * (s / (η + s)) * (sv / (η + sv)) := by
        field_simp
    _ ≤ ‖w - v‖ ^ 2 / (w.im * v.im) * kf M η * kf M η := by
        have hD : 0 ≤ ‖w - v‖ ^ 2 / (w.im * v.im) := by positivity
        have hq1 : 0 ≤ s / (η + s) := by positivity
        have hk0 := kf_nonneg (η := η) hs.M_nonneg
        gcongr
    _ = kf M η ^ 2 * (‖w - v‖ ^ 2 / (w.im * v.im)) := by ring

variable {h1 h2 : ℂ → ℂ /- [standing] -/ } {a1 M1 a2 M2 : ℝ /- [definition] -/ }

theorem fm_im_ge (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z w : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hw : w ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) : z.im ≤ (fm h1 h2 z w).im :=
  Tm_im_ge hs2 (Tm_mem hs1 hz hw)

theorem Dq_fm (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z w v : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hw : z.im ≤ w.im /- [standing] -/ ) (hv : z.im ≤ v.im /- [standing] -/ ) :
    Dq (fm h1 h2 z w) (fm h1 h2 z v) ≤ (kf M1 z.im * kf M2 z.im) ^ 2 * Dq w v := by
  have hw0 : w ∈ RMTFoundations.AnalyticHalfPlane.upper := lt_of_lt_of_le hz hw
  have hv0 : v ∈ RMTFoundations.AnalyticHalfPlane.upper := lt_of_lt_of_le hz hv
  have a := Dq_Tm hs1 hz hw hv
  have b := Dq_Tm hs2 hz (Tm_im_ge hs1 hw0) (Tm_im_ge hs1 hv0)
  have hk2 : 0 ≤ kf M2 z.im ^ 2 := sq_nonneg _
  calc Dq (fm h1 h2 z w) (fm h1 h2 z v)
      ≤ kf M2 z.im ^ 2 * Dq (Tm h1 z w) (Tm h1 z v) := b
    _ ≤ kf M2 z.im ^ 2 * (kf M1 z.im ^ 2 * Dq w v) := mul_le_mul_of_nonneg_left a hk2
    _ = (kf M1 z.im * kf M2 z.im) ^ 2 * Dq w v := by ring

theorem orb_im_ge (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (n : ℕ /- [definition] -/ ) : z.im ≤ (orb h1 h2 z n).im := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact fm_im_ge hs1 hs2 hz (lt_of_lt_of_le hz ih)

theorem orb_mem (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (n : ℕ /- [definition] -/ ) : orb h1 h2 z n ∈ RMTFoundations.AnalyticHalfPlane.upper :=
  lt_of_lt_of_le hz (orb_im_ge hs1 hs2 hz n)

theorem orb_im_le (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (n : ℕ /- [definition] -/ ) : (orb h1 h2 z n).im ≤ z.im + M2 / z.im := by
  cases n with
  | zero =>
    show z.im ≤ z.im + M2 / z.im
    have : 0 ≤ M2 / z.im := div_nonneg hs2.M_nonneg hz.le
    linarith
  | succ n =>
    have hw := orb_mem hs1 hs2 hz n
    exact Tm_im_le hs2 (Tm_mem hs1 hz hw) (Tm_im_ge hs1 hw) hz

theorem Dq_orb (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    Dq (orb h1 h2 z (n + 1)) (orb h1 h2 z n)
      ≤ ((kf M1 z.im * kf M2 z.im) ^ 2) ^ n * Dq (orb h1 h2 z 1) (orb h1 h2 z 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := Dq_fm hs1 hs2 hz (orb_im_ge hs1 hs2 hz (n + 1)) (orb_im_ge hs1 hs2 hz n)
    calc Dq (orb h1 h2 z (n + 2)) (orb h1 h2 z (n + 1))
        ≤ (kf M1 z.im * kf M2 z.im) ^ 2 * Dq (orb h1 h2 z (n + 1)) (orb h1 h2 z n) := this
      _ ≤ (kf M1 z.im * kf M2 z.im) ^ 2 * (((kf M1 z.im * kf M2 z.im) ^ 2) ^ n
          * Dq (orb h1 h2 z 1) (orb h1 h2 z 0)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ((kf M1 z.im * kf M2 z.im) ^ 2) ^ (n + 1) * Dq (orb h1 h2 z 1) (orb h1 h2 z 0) := by
          ring

/-- The contraction ratio on `Im z ≥ η₁`. -/
noncomputable def cRat (M1 M2 η₁ : ℝ /- [definition] -/ ) : ℝ := kf M1 η₁ * kf M2 η₁

/-- The geometric constant on `Im z ≥ η₁`, `Im z ≤ Z`. -/
noncomputable def cCst (a2 M2 η₁ Z : ℝ /- [definition] -/ ) : ℝ := (Z + M2 / η₁) * ((a2 + M2 / η₁) / η₁)

theorem cRat_lt_one (hM1 : 0 ≤ M1 /- [standing] -/ ) (hM2 : 0 ≤ M2 /- [standing] -/ ) {η₁ : ℝ /- [definition] -/ } (hη₁ : 0 < η₁ /- [standing] -/ ) :
    cRat M1 M2 η₁ < 1 := by
  unfold cRat
  have := kf_lt_one hM1 hη₁
  have := kf_lt_one hM2 hη₁
  have := kf_nonneg (η := η₁) hM1
  have := kf_nonneg (η := η₁) hM2
  nlinarith

theorem cRat_nonneg (hM1 : 0 ≤ M1 /- [standing] -/ ) (hM2 : 0 ≤ M2 /- [standing] -/ ) (η₁ : ℝ /- [definition] -/ ) : 0 ≤ cRat M1 M2 η₁ :=
  mul_nonneg (kf_nonneg hM1) (kf_nonneg hM2)

/-- **The orbit is geometrically Cauchy, uniformly on `η₁ ≤ Im z ≤ Z`.** -/
theorem orb_dist (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z : ℂ /- [definition] -/ } {η₁ Z : ℝ /- [definition] -/ } (hη₁ : 0 < η₁ /- [standing] -/ ) (hz1 : η₁ ≤ z.im /- [standing] -/ ) (hzZ : z.im ≤ Z /- [standing] -/ ) (ha2 : 0 ≤ a2 /- [standing] -/ )
    (n : ℕ /- [definition] -/ ) :
    dist (orb h1 h2 z n) (orb h1 h2 z (n + 1)) ≤ cCst a2 M2 η₁ Z * cRat M1 M2 η₁ ^ n := by
  have hz : 0 < z.im := lt_of_lt_of_le hη₁ hz1
  have hM1 := hs1.M_nonneg
  have hM2 := hs2.M_nonneg
  set r := kf M1 z.im * kf M2 z.im
  have hr0 : 0 ≤ r := mul_nonneg (kf_nonneg hM1) (kf_nonneg hM2)
  have hr1 : r ≤ cRat M1 M2 η₁ :=
    mul_le_mul (kf_anti hM1 hη₁ hz1) (kf_anti hM2 hη₁ hz1) (kf_nonneg hM2) (kf_nonneg hM1)
  set D0 := Dq (orb h1 h2 z 1) (orb h1 h2 z 0)
  -- the first step
  have hstep : ‖orb h1 h2 z 1 - orb h1 h2 z 0‖ ≤ a2 + M2 / η₁ := by
    have e : orb h1 h2 z 1 - orb h1 h2 z 0 = h2 (Tm h1 z z) := by
      rw [show orb h1 h2 z 1 = fm h1 h2 z z from rfl, show orb h1 h2 z 0 = z from rfl]
      simp [fm, Tm]
    rw [e]
    have hm := Tm_mem hs1 hz (show z ∈ RMTFoundations.AnalyticHalfPlane.upper from hz)
    refine (hs2.norm_le _ hm).trans ?_
    have : M2 / (Tm h1 z z).im ≤ M2 / η₁ :=
      div_le_div_of_nonneg_left hM2 hη₁ (hz1.trans (Tm_im_ge hs1 hz))
    linarith
  have hD0 : D0 ≤ ((a2 + M2 / η₁) / η₁) ^ 2 := by
    have h1i := orb_im_ge hs1 hs2 hz 1
    unfold D0 Dq
    rw [div_le_iff₀ (by
      have : 0 < (orb h1 h2 z 1).im := lt_of_lt_of_le hz h1i
      exact mul_pos this hz)]
    have hq : 0 ≤ a2 + M2 / η₁ := by positivity
    have hsq : ‖orb h1 h2 z 1 - orb h1 h2 z 0‖ ^ 2 ≤ (a2 + M2 / η₁) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hstep 2
    have hden : η₁ ^ 2 ≤ (orb h1 h2 z 1).im * (orb h1 h2 z 0).im := by
      have : (orb h1 h2 z 0).im = z.im := rfl
      rw [this, sq]
      exact mul_le_mul (hz1.trans h1i) hz1 hη₁.le (by linarith)
    calc ‖orb h1 h2 z 1 - orb h1 h2 z 0‖ ^ 2 ≤ (a2 + M2 / η₁) ^ 2 := hsq
      _ = ((a2 + M2 / η₁) / η₁) ^ 2 * η₁ ^ 2 := by field_simp
      _ ≤ ((a2 + M2 / η₁) / η₁) ^ 2 * ((orb h1 h2 z 1).im * (orb h1 h2 z 0).im) := by gcongr
  have hY : ∀ k, (orb h1 h2 z k).im ≤ Z + M2 / η₁ := by
    intro k
    have := orb_im_le hs1 hs2 hz k
    have : M2 / z.im ≤ M2 / η₁ := div_le_div_of_nonneg_left hM2 hη₁ hz1
    linarith
  have hDn := Dq_orb hs1 hs2 hz n
  have hC0 : 0 ≤ cCst a2 M2 η₁ Z := by
    unfold cCst
    have : 0 ≤ Z + M2 / η₁ := by
      have : 0 ≤ M2 / η₁ := div_nonneg hM2 hη₁.le
      linarith
    positivity
  rw [dist_comm, dist_eq_norm, ← pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg hC0 (pow_nonneg (cRat_nonneg hM1 hM2 η₁) n)) two_ne_zero]
  have hi1 : 0 < (orb h1 h2 z (n + 1)).im := lt_of_lt_of_le hz (orb_im_ge hs1 hs2 hz _)
  have hi0 : 0 < (orb h1 h2 z n).im := lt_of_lt_of_le hz (orb_im_ge hs1 hs2 hz _)
  have hnorm : ‖orb h1 h2 z (n + 1) - orb h1 h2 z n‖ ^ 2
      = Dq (orb h1 h2 z (n + 1)) (orb h1 h2 z n)
        * ((orb h1 h2 z (n + 1)).im * (orb h1 h2 z n).im) := by
    unfold Dq; field_simp
  rw [hnorm]
  have hprod : (orb h1 h2 z (n + 1)).im * (orb h1 h2 z n).im ≤ (Z + M2 / η₁) ^ 2 := by
    rw [sq]; exact mul_le_mul (hY _) (hY _) hi0.le (by linarith [hY n])
  have hDn0 : 0 ≤ Dq (orb h1 h2 z (n + 1)) (orb h1 h2 z n) := by unfold Dq; positivity
  have hrn : (r ^ 2) ^ n ≤ (cRat M1 M2 η₁ ^ 2) ^ n :=
    pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ hr0 hr1 2) n
  have hD00 : 0 ≤ D0 := by
    unfold D0 Dq
    exact div_nonneg (sq_nonneg _)
      (mul_pos (lt_of_lt_of_le hz (orb_im_ge hs1 hs2 hz 1)) hz).le
  calc Dq (orb h1 h2 z (n + 1)) (orb h1 h2 z n)
        * ((orb h1 h2 z (n + 1)).im * (orb h1 h2 z n).im)
      ≤ ((r ^ 2) ^ n * D0) * (Z + M2 / η₁) ^ 2 :=
        mul_le_mul hDn hprod (by positivity) (by positivity)
    _ ≤ ((cRat M1 M2 η₁ ^ 2) ^ n * ((a2 + M2 / η₁) / η₁) ^ 2) * (Z + M2 / η₁) ^ 2 := by
        gcongr
    _ = (cCst a2 M2 η₁ Z * cRat M1 M2 η₁ ^ n) ^ 2 := by unfold cCst; ring

theorem orb_tendsto (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (ha2 : 0 ≤ a2 /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    Tendsto (orb h1 h2 z) atTop (𝓝 (om1 h1 h2 z)) := by
  have hc : CauchySeq (orb h1 h2 z) :=
    cauchySeq_of_le_geometric _ _ (cRat_lt_one hs1.M_nonneg hs2.M_nonneg hz)
      (orb_dist hs1 hs2 hz le_rfl le_rfl ha2)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨l, hl⟩

theorem om1_im_ge (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (ha2 : 0 ≤ a2 /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : z.im ≤ (om1 h1 h2 z).im :=
  ge_of_tendsto ((Complex.continuous_im.tendsto _).comp (orb_tendsto hs1 hs2 ha2 hz))
    (Eventually.of_forall fun n => orb_im_ge hs1 hs2 hz n)

theorem om1_mem (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (ha2 : 0 ≤ a2 /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : om1 h1 h2 z ∈ RMTFoundations.AnalyticHalfPlane.upper :=
  lt_of_lt_of_le hz (om1_im_ge hs1 hs2 ha2 hz)

theorem continuousAt_fm (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z w : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hw : w ∈ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ ) : ContinuousAt (fm h1 h2 z) w := by
  have c1 : ContinuousAt h1 w :=
    (hs1.diff.differentiableAt (RMTFoundations.AnalyticHalfPlane.isOpen_upper.mem_nhds hw)).continuousAt
  have hm := Tm_mem hs1 hz hw
  have c2 : ContinuousAt h2 (Tm h1 z w) :=
    (hs2.diff.differentiableAt (RMTFoundations.AnalyticHalfPlane.isOpen_upper.mem_nhds hm)).continuousAt
  have c3 : ContinuousAt (Tm h1 z) w := continuousAt_const.add c1
  exact continuousAt_const.add (c2.comp c3)

/-- **The fixed point**: `ω₁ = z + h₂(z + h₁(ω₁))`. -/
theorem om1_fixed (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (ha2 : 0 ≤ a2 /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : fm h1 h2 z (om1 h1 h2 z) = om1 h1 h2 z := by
  have ht := orb_tendsto hs1 hs2 ha2 hz
  have t1 : Tendsto (fun n => fm h1 h2 z (orb h1 h2 z n)) atTop
      (𝓝 (fm h1 h2 z (om1 h1 h2 z))) :=
    (continuousAt_fm hs1 hs2 hz (om1_mem hs1 hs2 ha2 hz)).tendsto.comp ht
  have t2 : Tendsto (fun n => fm h1 h2 z (orb h1 h2 z n)) atTop (𝓝 (om1 h1 h2 z)) :=
    ht.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique t1 t2

/-- **Uniqueness of the fixed point** in `{Im w ≥ Im z}`. -/
theorem fixed_unique (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    {z w v : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hw : z.im ≤ w.im /- [standing] -/ ) (hv : z.im ≤ v.im /- [standing] -/ )
    (hfw : fm h1 h2 z w = w /- [standing] -/ ) (hfv : fm h1 h2 z v = v /- [standing] -/ ) : w = v := by
  have hD := Dq_fm hs1 hs2 hz hw hv
  rw [hfw, hfv] at hD
  have hr := cRat_lt_one hs1.M_nonneg hs2.M_nonneg hz
  have hr0 := cRat_nonneg hs1.M_nonneg hs2.M_nonneg z.im
  have hr2 : (kf M1 z.im * kf M2 z.im) ^ 2 < 1 := by
    unfold cRat at hr hr0
    nlinarith
  have hD0 : 0 ≤ Dq w v := by
    unfold Dq
    have : 0 < w.im := lt_of_lt_of_le hz hw
    have : 0 < v.im := lt_of_lt_of_le hz hv
    positivity
  have hDz : Dq w v = 0 := by nlinarith
  unfold Dq at hDz
  have hw0 : 0 < w.im := lt_of_lt_of_le hz hw
  have hv0 : 0 < v.im := lt_of_lt_of_le hz hv
  rw [div_eq_zero_iff] at hDz
  rcases hDz with h0 | h0
  · have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h0
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · exfalso; have : 0 < w.im * v.im := mul_pos hw0 hv0; linarith

end FixedPoint

section Holo

variable {h1 h2 : ℂ → ℂ /- [standing] -/ } {a1 M1 a2 M2 L B : ℝ /- [definition] -/ }

theorem orb_differentiableOn (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (n : ℕ /- [definition] -/ ) : DifferentiableOn ℂ (fun z => orb h1 h2 z n) RMTFoundations.AnalyticHalfPlane.upper := by
  induction n with
  | zero => exact differentiableOn_id
  | succ n ih =>
    have g1 : DifferentiableOn ℂ (fun z => h1 (orb h1 h2 z n)) RMTFoundations.AnalyticHalfPlane.upper :=
      hs1.diff.comp ih (fun z hz => orb_mem hs1 hs2 hz n)
    have g2 : DifferentiableOn ℂ (fun z => z + h1 (orb h1 h2 z n)) RMTFoundations.AnalyticHalfPlane.upper :=
      differentiableOn_id.add g1
    have g3 : DifferentiableOn ℂ (fun z => h2 (z + h1 (orb h1 h2 z n))) RMTFoundations.AnalyticHalfPlane.upper :=
      hs2.diff.comp g2 (fun z hz => Tm_mem hs1 hz (orb_mem hs1 hs2 hz n))
    exact differentiableOn_id.add g3

theorem orb_tendstoUniformlyOn (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ )
    (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ ) (ha2 : 0 ≤ a2 /- [standing] -/ ) (K : Set ℂ /- [definition] -/ ) (hKU : K ⊆ RMTFoundations.AnalyticHalfPlane.upper /- [standing] -/ )
    (hK : IsCompact K /- [standing] -/ ) :
    TendstoUniformlyOn (fun n z => orb h1 h2 z n) (om1 h1 h2) atTop K := by
  rcases K.eq_empty_or_nonempty with he | hne
  · rw [he]; exact tendstoUniformlyOn_empty
  obtain ⟨z₁, hz₁K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨z₂, -, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_im.continuousOn
  set η₁ := z₁.im
  set Z := z₂.im
  have hη₁ : 0 < η₁ := hKU hz₁K
  have hr1 := cRat_lt_one hs1.M_nonneg hs2.M_nonneg hη₁
  have hr0 := cRat_nonneg hs1.M_nonneg hs2.M_nonneg η₁
  have hbound : ∀ z ∈ K, ∀ n, dist (orb h1 h2 z n) (om1 h1 h2 z)
      ≤ cCst a2 M2 η₁ Z * cRat M1 M2 η₁ ^ n / (1 - cRat M1 M2 η₁) := by
    intro z hz n
    exact dist_le_of_le_geometric_of_tendsto _ _ hr1
      (orb_dist hs1 hs2 hη₁ (hmin hz) (hmax hz) ha2)
      (orb_tendsto hs1 hs2 ha2 (hKU hz)) n
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => cCst a2 M2 η₁ Z * cRat M1 M2 η₁ ^ n
      / (1 - cRat M1 M2 η₁)) atTop (𝓝 (cCst a2 M2 η₁ Z * 0 / (1 - cRat M1 M2 η₁))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _).div_const _
  rw [mul_zero, zero_div] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm]
  exact lt_of_le_of_lt (hbound z hz n) hn

/-- **`ω₁` is holomorphic on `ℂ⁺`.** -/
theorem om1_differentiableOn (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ )
    (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ ) (ha2 : 0 ≤ a2 /- [standing] -/ ) :
    DifferentiableOn ℂ (om1 h1 h2) RMTFoundations.AnalyticHalfPlane.upper := by
  have hloc : TendstoLocallyUniformlyOn (fun n z => orb h1 h2 z n) (om1 h1 h2) atTop RMTFoundations.AnalyticHalfPlane.upper :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact RMTFoundations.AnalyticHalfPlane.isOpen_upper).2
      fun K hKU hK => orb_tendstoUniformlyOn hs1 hs2 ha2 K hKU hK
  exact hloc.differentiableOn (Eventually.of_forall fun n => orb_differentiableOn hs1 hs2 n)
    RMTFoundations.AnalyticHalfPlane.isOpen_upper

/-- **Far from the supports the subordination functions stay near `z`** and
`Im ω₁ ≤ (4/3) Im z`. -/
theorem om1_tail (hs1 : ShiftBounds h1 a1 M1 L B /- [standing] -/ ) (hs2 : ShiftBounds h2 a2 M2 L B /- [standing] -/ )
    (ha2 : 0 ≤ a2 /- [standing] -/ ) (hB : 0 ≤ B /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) (hx : L + B ≤ |z.re| /- [standing] -/ ) :
    ‖om1 h1 h2 z - z‖ ≤ B ∧ ‖Tm h1 z (om1 h1 h2 z) - z‖ ≤ B
      ∧ L ≤ |(om1 h1 h2 z).re| ∧ L ≤ |(Tm h1 z (om1 h1 h2 z)).re|
      ∧ (om1 h1 h2 z).im ≤ 4 / 3 * z.im := by
  have hre : ∀ w : ℂ, ‖w - z‖ ≤ B → L ≤ |w.re| := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
      have := Complex.abs_re_le_norm (w - z); simpa using this
    have h2 := abs_sub_abs_le_abs_sub z.re w.re
    rw [abs_sub_comm] at h2
    linarith
  have hstep : ∀ w ∈ RMTFoundations.AnalyticHalfPlane.upper, ‖w - z‖ ≤ B → ‖Tm h1 z w - z‖ ≤ B ∧ ‖fm h1 h2 z w - z‖ ≤ B := by
    intro w hw hwz
    have e1 : Tm h1 z w - z = h1 w := by simp [Tm]
    have b1 : ‖Tm h1 z w - z‖ ≤ B := by rw [e1]; exact (hs1.tail w hw (hre w hwz)).1
    have e2 : fm h1 h2 z w - z = h2 (Tm h1 z w) := by simp [fm, Tm]
    refine ⟨b1, ?_⟩
    rw [e2]
    exact (hs2.tail _ (Tm_mem hs1 hz hw) (hre _ b1)).1
  have horb : ∀ n, ‖orb h1 h2 z n - z‖ ≤ B := by
    intro n
    induction n with
    | zero => show ‖z - z‖ ≤ B; rw [sub_self, norm_zero]; exact hB
    | succ n ih => exact (hstep _ (orb_mem hs1 hs2 hz n) ih).2
  have hlim : ‖om1 h1 h2 z - z‖ ≤ B :=
    le_of_tendsto (((continuous_id.sub continuous_const).norm.tendsto _).comp
      (orb_tendsto hs1 hs2 ha2 hz)) (Eventually.of_forall horb)
  have hmem := om1_mem hs1 hs2 ha2 hz
  have h2b := (hstep _ hmem hlim).1
  refine ⟨hlim, h2b, hre _ hlim, hre _ h2b, ?_⟩
  set w1 := om1 h1 h2 z
  set w2 := Tm h1 z w1
  have hw2 : w2 ∈ RMTFoundations.AnalyticHalfPlane.upper := Tm_mem hs1 hz hmem
  have hfix : Tm h2 z w2 = w1 := om1_fixed hs1 hs2 ha2 hz
  have i1 : w1.im = z.im + (h2 w2).im := by rw [← hfix, Tm_im]
  have i2 : w2.im = z.im + (h1 w1).im := Tm_im z w1
  have t1 := (hs2.tail w2 hw2 (hre _ h2b)).2
  have t2 := (hs1.tail w1 hmem (hre _ hlim)).2
  linarith

end Holo

section Unique

theorem tendsto_real_iInter {ν : Measure ℝ /- [definition] -/ } [IsFiniteMeasure ν /- [standing] -/ ] {s : ℕ → Set ℝ /- [definition] -/ }
    (hs : ∀ n, MeasurableSet (s n) /- [standing] -/ ) (hm : Antitone s /- [standing] -/ ) :
    Tendsto (fun n => ν.real (s n)) atTop (𝓝 (ν.real (⋂ n, s n))) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_measure_iInter_atTop (fun n => (hs n).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩)

/-- `ε_n = 1/(n+1)`. -/
noncomputable def eps (n : ℕ /- [definition] -/ ) : ℝ := 1 / ((n : ℝ) + 1)

theorem eps_pos (n : ℕ /- [definition] -/ ) : 0 < eps n := by unfold eps; positivity

theorem eps_anti : Antitone eps := by
  intro m n hmn
  unfold eps
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

theorem iInter_eps {x : ℝ /- [definition] -/ } {s : ℕ → Set ℝ /- [definition] -/ } (hsub : ∀ n, s n ⊆ Icc (x - eps n) (x + eps n) /- [standing] -/ )
    (hx : ∀ n, x ∈ s n /- [standing] -/ ) : ⋂ n, s n = {x} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  refine ⟨fun hy => ?_, fun hy n => hy ▸ hx n⟩
  by_contra hne
  have hpos : 0 < |y - x| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  have := hsub n (hy n)
  have : |y - x| ≤ eps n := abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  unfold eps at this
  linarith

/-- `ν(a, b) + ν{a}/2 + ν{b}/2`, the quantity Stieltjes inversion recovers. -/
noncomputable def Dval (ν : Measure ℝ /- [definition] -/ ) (a b : ℝ /- [definition] -/ ) : ℝ :=
  ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2

theorem Dval_eq {ν ν' : Measure ℝ /- [definition] -/ } [IsFiniteMeasure ν /- [standing] -/ ] [IsFiniteMeasure ν' /- [standing] -/ ]
    (h : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, stieltjes ν z = stieltjes ν' z /- [standing] -/ ) {a b : ℝ /- [definition] -/ } (hab : a < b /- [standing] -/ ) :
    Dval ν a b = Dval ν' a b := by
  have T1 := RMTFoundations.StieltjesInversion.tendsto_interval_im ν a b hab
  have T2 := RMTFoundations.StieltjesInversion.tendsto_interval_im ν' a b hab
  have T1b : Tendsto (fun η : ℝ => ∫ x in a..b,
      (stieltjes ν' ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * (ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2))) := by
    refine T1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    congr 1
    funext x
    rw [h _ (show (0 : ℝ) < ((x : ℂ) + (η : ℂ) * Complex.I).im by simpa using hη)]
  have := tendsto_nhds_unique T1b T2
  exact mul_left_cancel₀ Real.pi_ne_zero this

theorem Dval_le (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] {a b : ℝ /- [definition] -/ } (hab : a < b /- [standing] -/ ) :
    ν.real (Ioo a b) ≤ Dval ν a b ∧ Dval ν a b ≤ ν.real (Icc a b) := by
  have h1 : ν.real (Ioc a b) = ν.real (Ioo a b) + ν.real {b} := by
    rw [← Set.Ioo_union_right hab, measureReal_union (by simp) (measurableSet_singleton b)]
  have h2 : ν.real (Icc a b) = ν.real (Ioc a b) + ν.real {a} := by
    rw [← Set.Ioc_union_left hab.le, measureReal_union (by simp) (measurableSet_singleton a)]
  have ha := measureReal_nonneg (μ := ν) (s := {a})
  have hb := measureReal_nonneg (μ := ν) (s := {b})
  unfold Dval
  constructor <;> linarith

theorem tendsto_Dval_atom (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (x : ℝ /- [definition] -/ ) :
    Tendsto (fun n => Dval ν (x - eps n) (x + eps n)) atTop (𝓝 (ν.real {x})) := by
  have hanti1 : Antitone fun n => Ioo (x - eps n) (x + eps n) := fun m n hmn =>
    Ioo_subset_Ioo (by linarith [eps_anti hmn]) (by linarith [eps_anti hmn])
  have hanti2 : Antitone fun n => Icc (x - eps n) (x + eps n) := fun m n hmn =>
    Icc_subset_Icc (by linarith [eps_anti hmn]) (by linarith [eps_anti hmn])
  have t1 := tendsto_real_iInter (ν := ν) (fun n => measurableSet_Ioo) hanti1
  have t2 := tendsto_real_iInter (ν := ν) (fun n => measurableSet_Icc) hanti2
  rw [iInter_eps (fun n => Ioo_subset_Icc_self)
    (fun n => ⟨by linarith [eps_pos n], by linarith [eps_pos n]⟩)] at t1
  rw [iInter_eps (fun n => subset_rfl)
    (fun n => ⟨by linarith [eps_pos n], by linarith [eps_pos n]⟩)] at t2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le t1 t2
    (fun n => (Dval_le ν (by linarith [eps_pos n])).1)
    (fun n => (Dval_le ν (by linarith [eps_pos n])).2)

/-- **A finite measure is determined by its Stieltjes transform on `ℂ⁺`.** -/
theorem measure_eq_of_stieltjes {ν ν' : Measure ℝ /- [definition] -/ } [IsFiniteMeasure ν /- [standing] -/ ] [IsFiniteMeasure ν' /- [standing] -/ ]
    (h : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, stieltjes ν z = stieltjes ν' z /- [standing] -/ ) : ν = ν' := by
  have hatom : ∀ x, ν.real {x} = ν'.real {x} := by
    intro x
    have t1 := tendsto_Dval_atom ν x
    have t2 := tendsto_Dval_atom ν' x
    refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
    exact (Dval_eq h (by linarith [eps_pos n])).symm
  have hIoo : ∀ a b, a < b → ν.real (Ioo a b) = ν'.real (Ioo a b) := by
    intro a b hab
    have := Dval_eq h hab
    unfold Dval at this
    rw [hatom a, hatom b] at this
    linarith
  have huniv : ν.real univ = ν'.real univ := by
    have t1 := RMTFoundations.StieltjesSupport.tendsto_iy_stieltjes ν
    have t2 := RMTFoundations.StieltjesSupport.tendsto_iy_stieltjes ν'
    have t1b : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * stieltjes ν' ((y : ℂ) * Complex.I))
        atTop (𝓝 (-(ν.real univ : ℂ))) := by
      refine t1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      rw [h _ (show (0 : ℝ) < ((y : ℂ) * Complex.I).im by simpa using hy)]
    have := tendsto_nhds_unique t1b t2
    have := congrArg Complex.re this
    simpa using this
  refine Measure.ext_of_Ioc_finite ν ν' ?_ fun a b hab => ?_
  · rw [measureReal_def, measureReal_def] at huniv
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 huniv
  · have e : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] →
        μ.real (Ioc a b) = μ.real (Ioo a b) + μ.real {b} := by
      intro μ _
      rw [← Set.Ioo_union_right hab, measureReal_union (by simp) (measurableSet_singleton b)]
    have hr : ν.real (Ioc a b) = ν'.real (Ioc a b) := by
      rw [e ν, e ν', hIoo a b hab, hatom b]
    rw [measureReal_def, measureReal_def] at hr
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hr

end Unique

section Endpoint

/-- **The upper support endpoint** `sup supp μ = inf {x : μ(x, ∞) = 0}`. -/
noncomputable def rightEndpoint (μ : Measure ℝ /- [definition] -/ ) : ℝ := sInf {x : ℝ | μ (Ioi x) = 0}

variable {μ : Measure ℝ /- [definition] -/ } {R : ℝ /- [definition] -/ }

theorem mem_endpointSet (h : SupportedIn μ R /- [standing] -/ ) : R ∈ {x : ℝ | μ (Ioi x) = 0} :=
  measure_mono_null (fun y hy => by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
    exact Or.inr hy) h

theorem endpointSet_bdd [IsProbabilityMeasure μ /- [standing] -/ ] (h : SupportedIn μ R /- [standing] -/ ) :
    ∀ x ∈ {x : ℝ | μ (Ioi x) = 0}, -R ≤ x := by
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  have hsub : Icc (-R) R ⊆ Ioi x := fun y hy => lt_of_lt_of_le hlt hy.1
  have h1 : μ (Icc (-R) R) = 0 := measure_mono_null hsub hx
  have h2 : μ (Icc (-R) R) + μ (Icc (-R) R)ᶜ = μ univ := measure_add_measure_compl measurableSet_Icc
  rw [h1, h, measure_univ] at h2
  simp at h2

theorem rightEndpoint_le (h : SupportedIn μ R /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ] : rightEndpoint μ ≤ R :=
  csInf_le ⟨-R, endpointSet_bdd h⟩ (mem_endpointSet h)

theorem neg_le_rightEndpoint (h : SupportedIn μ R /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ] :
    -R ≤ rightEndpoint μ :=
  le_csInf ⟨R, mem_endpointSet h⟩ (endpointSet_bdd h)

/-- No mass above the endpoint. -/
theorem measure_Ioi_rightEndpoint (h : SupportedIn μ R /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ] :
    μ (Ioi (rightEndpoint μ)) = 0 := by
  have hcov : Ioi (rightEndpoint μ) = ⋃ n : ℕ, Ioi (rightEndpoint μ + eps n) := by
    ext y
    simp only [Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨n, by unfold eps; linarith⟩
    · rintro ⟨n, hn⟩; linarith [eps_pos n]
  rw [hcov]
  refine measure_iUnion_null fun n => ?_
  obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt ⟨R, mem_endpointSet h⟩
    (show rightEndpoint μ < rightEndpoint μ + eps n by linarith [eps_pos n])
  exact measure_mono_null (Ioi_subset_Ioi hxlt.le) hx

/-- Mass arbitrarily close below the endpoint. -/
theorem measure_Ioi_pos_of_lt (h : SupportedIn μ R /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ] {x : ℝ /- [definition] -/ }
    (hx : x < rightEndpoint μ /- [standing] -/ ) : 0 < μ (Ioi x) := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have : rightEndpoint μ ≤ x :=
    csInf_le ⟨-R, endpointSet_bdd h⟩ (show x ∈ {x : ℝ | μ (Ioi x) = 0} from h0)
  linarith

end Endpoint

section FreeConvolution

theorem norm_mul_stieltjes_add_one {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ }
    (h : SupportedIn μ R /- [standing] -/ ) {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    ‖w * stieltjes μ w + 1‖ ≤ R / w.im := by
  have e : w * stieltjes μ w + 1 = ∫ t, (t : ℂ) * ((t : ℂ) - w)⁻¹ ∂μ := by
    have hpt : ∀ t : ℝ, (t : ℂ) * ((t : ℂ) - w)⁻¹ = 1 + w * ((t : ℂ) - w)⁻¹ := by
      intro t
      have := sub_ne hw t
      field_simp
      ring
    simp_rw [hpt]
    rw [integral_add (integrable_const _) ((integrable_inv_sub μ hw).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    rw [stieltjes]
    ring
  rw [e]
  have := norm_integral_le_of_norm_le (integrable_const (R / w.im))
    ((ae_mem h).mono fun t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
      exact mul_le_mul (abs_le.2 ht) (norm_inv_sub_le hw t) (norm_nonneg _)
        (by linarith [ht.1, ht.2]))
    (μ := μ) (f := fun t : ℝ => (t : ℂ) * ((t : ℂ) - w)⁻¹)
  rwa [integral_const, probReal_univ, one_smul] at this

theorem im_stieltjes_tail {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ }
    (h : SupportedIn μ R /- [standing] -/ ) {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (hx : R < |w.re| /- [standing] -/ ) :
    (stieltjes μ w).im ≤ w.im * (1 / (|w.re| - R)) ^ 2 := by
  rw [im_stieltjes_eq μ hw]
  refine mul_le_mul_of_nonneg_left ?_ hw.le
  have hint : Integrable (fun t : ℝ => ‖((t : ℂ) - w)⁻¹‖ ^ 2) μ :=
    Integrable.of_bound ((continuous_inv_sub hw).norm.pow 2).aestronglyMeasurable
      (w.im⁻¹ ^ 2) (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_le hw t) 2)
  have := integral_mono_ae hint (integrable_const ((1 / (|w.re| - R)) ^ 2))
    ((ae_mem h).mono fun t ht =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_tail ht hx) 2)
  rwa [integral_const, probReal_univ, one_smul] at this

/-- The subordination function `ω₁(z)` of `μ₁ ⊞ μ₂`: the fixed point of
`w ↦ z + h₂(z + h₁(w))`, `h_j = F_{μ_j} - id`. -/
noncomputable def omega1 (μ1 μ2 : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) : ℂ := om1 (hfun μ1) (hfun μ2) z

/-- The second subordination function `ω₂(z) = z + h₁(ω₁(z))`. -/
noncomputable def omega2 (μ1 μ2 : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) : ℂ := z + hfun μ1 (omega1 μ1 μ2 z)

/-- `ν` is **the free additive convolution** `μ₁ ⊞ μ₂`: a finite measure whose Stieltjes
transform is `S_{μ₁} ∘ ω₁` on `ℂ⁺` (Biane / Belinschi–Bercovici subordination). -/
def IsFreeConv (μ1 μ2 ν : Measure ℝ /- [definition] -/ ) : Prop :=
  IsFiniteMeasure ν ∧ ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, stieltjes ν z = stieltjes μ1 (omega1 μ1 μ2 z)

open Classical in
/-- **`μ₁ ⊞ μ₂`**, defined by subordination; `0` when no representing measure exists (never,
for compactly supported probability measures: `freeConv_isFreeConv`). -/
noncomputable def freeConv (μ1 μ2 : Measure ℝ /- [definition] -/ ) : Measure ℝ :=
  if h : ∃ ν, IsFreeConv μ1 μ2 ν then h.choose else 0

variable {μ1 μ2 : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ1 /- [standing] -/ ] [IsProbabilityMeasure μ2 /- [standing] -/ ] {R : ℝ /- [definition] -/ }

/-- **The subordination equations** `F_{μ₁}(ω₁) = F_{μ₂}(ω₂) = ω₁ + ω₂ - z`,
`Im ω_j ≥ Im z`. -/
theorem subordination (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) {z : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) :
    z.im ≤ (omega1 μ1 μ2 z).im ∧ z.im ≤ (omega2 μ1 μ2 z).im
      ∧ -(stieltjes μ1 (omega1 μ1 μ2 z))⁻¹ = omega1 μ1 μ2 z + omega2 μ1 μ2 z - z
      ∧ -(stieltjes μ2 (omega2 μ1 μ2 z))⁻¹ = omega1 μ1 μ2 z + omega2 μ1 μ2 z - z := by
  have hs1 := shiftBounds_hfun h1 hR
  have hs2 := shiftBounds_hfun h2 hR
  have hge := om1_im_ge hs1 hs2 hR.le hz
  have hmem := om1_mem hs1 hs2 hR.le hz
  have hfix := om1_fixed hs1 hs2 hR.le hz
  refine ⟨hge, Tm_im_ge hs1 hmem, ?_, ?_⟩
  · simp only [omega2, omega1, hfun]; ring
  · have e : omega1 μ1 μ2 z = z + hfun μ2 (omega2 μ1 μ2 z) := hfix.symm
    have e2 : -(stieltjes μ2 (omega2 μ1 μ2 z))⁻¹ = hfun μ2 (omega2 μ1 μ2 z) + omega2 μ1 μ2 z := by
      simp only [hfun]; ring
    rw [e2]
    linear_combination (-1 : ℂ) * e

/-- `S_{μ₁}(ω₁(z)) = S_{μ₂}(ω₂(z))`. -/
theorem stieltjes_omega_eq (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ )
    {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    stieltjes μ1 (omega1 μ1 μ2 z) = stieltjes μ2 (omega2 μ1 μ2 z) := by
  obtain ⟨-, -, e1, e2⟩ := subordination h1 h2 hR hz
  rw [← e2, neg_inj, inv_inj] at e1
  exact e1

theorem omega1_differentiableOn (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    DifferentiableOn ℂ (omega1 μ1 μ2) RMTFoundations.AnalyticHalfPlane.upper :=
  om1_differentiableOn (shiftBounds_hfun h1 hR) (shiftBounds_hfun h2 hR) hR.le

theorem exists_isFreeConv (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    ∃ ν, IsFreeConv μ1 μ2 ν := by
  have hs1 := shiftBounds_hfun h1 hR
  have hs2 := shiftBounds_hfun h2 hR
  have hmem : ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, omega1 μ1 μ2 z ∈ RMTFoundations.AnalyticHalfPlane.upper := fun z hz => om1_mem hs1 hs2 hR.le hz
  obtain ⟨ν, hν, -, hS⟩ := RMTFoundations.HerglotzBorelProof.herglotzBorel
    (fun z => stieltjes μ1 (omega1 μ1 μ2 z)) 1
    ((RMTFoundations.HerglotzBorelProof.stieltjes_differentiableOn μ1).comp
      (omega1_differentiableOn h1 h2 hR) hmem)
    (fun z hz => im_stieltjes_nonneg μ1 (hmem z hz))
    (fun z hz => by
      refine (RMTFoundations.HerglotzBorelProof.norm_stieltjes_le μ1 _ (hmem z hz)).trans ?_
      rw [probReal_univ]
      exact div_le_div_of_nonneg_left zero_le_one hz (om1_im_ge hs1 hs2 hR.le hz))
  exact ⟨ν, hν, fun z hz => (hS z hz).symm⟩

theorem isFreeConv_prob (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ )
    {ν : Measure ℝ /- [definition] -/ } (hν : IsFreeConv μ1 μ2 ν /- [standing] -/ ) : IsProbabilityMeasure ν := by
  obtain ⟨hfin, hS⟩ := hν
  have hs1 := shiftBounds_hfun h1 hR
  have hs2 := shiftBounds_hfun h2 hR
  have hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * stieltjes ν ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1)) := by
    have hbd : ∀ᶠ y : ℝ in atTop, ‖((y : ℂ) * Complex.I) * stieltjes ν ((y : ℂ) * Complex.I)
        - (-1)‖ ≤ R / y + (R + R ^ 2 / y) / y := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      set z : ℂ := (y : ℂ) * Complex.I
      have hz : 0 < z.im := by simp [z, hy]
      have hzim : z.im = y := by simp [z]
      obtain ⟨g1, g2, -, -⟩ := subordination h1 h2 hR hz
      set w := omega1 μ1 μ2 z
      have hw : 0 < w.im := lt_of_lt_of_le hz g1
      have hfix : w = z + hfun μ2 (omega2 μ1 μ2 z) := (om1_fixed hs1 hs2 hR.le hz).symm
      rw [hS z hz]
      have e : z * stieltjes μ1 w - (-1) = (w * stieltjes μ1 w + 1)
          - hfun μ2 (omega2 μ1 μ2 z) * stieltjes μ1 w := by
        rw [hfix]; ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have b1 : ‖w * stieltjes μ1 w + 1‖ ≤ R / y := by
        refine (norm_mul_stieltjes_add_one h1 hw).trans ?_
        rw [← hzim]; exact div_le_div_of_nonneg_left hR.le hz g1
      have b2 : ‖hfun μ2 (omega2 μ1 μ2 z)‖ ≤ R + R ^ 2 / y := by
        refine (hs2.norm_le _ (lt_of_lt_of_le hz g2)).trans ?_
        have : R ^ 2 / (omega2 μ1 μ2 z).im ≤ R ^ 2 / y := by
          rw [← hzim]; exact div_le_div_of_nonneg_left (sq_nonneg R) hz g2
        linarith
      have b3 : ‖stieltjes μ1 w‖ ≤ 1 / y := by
        refine (RMTFoundations.HerglotzBorelProof.norm_stieltjes_le μ1 _ hw).trans ?_
        rw [probReal_univ, ← hzim]; exact div_le_div_of_nonneg_left zero_le_one hz g1
      rw [norm_mul]
      have : ‖hfun μ2 (omega2 μ1 μ2 z)‖ * ‖stieltjes μ1 w‖ ≤ (R + R ^ 2 / y) * (1 / y) :=
        mul_le_mul b2 b3 (norm_nonneg _) (by positivity)
      rw [mul_one_div] at this
      linarith
    have hlim0 : Tendsto (fun y : ℝ => R / y + (R + R ^ 2 / y) / y) atTop (𝓝 0) := by
      have t1 : Tendsto (fun y : ℝ => R / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have t2 : Tendsto (fun y : ℝ => R + R ^ 2 / y) atTop (𝓝 (R + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
      have t3 : Tendsto (fun y : ℝ => (R + R ^ 2 / y) / y) atTop (𝓝 0) :=
        t2.div_atTop tendsto_id
      simpa using t1.add t3
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbd hlim0
  have ht := RMTFoundations.StieltjesSupport.tendsto_iy_stieltjes ν
  have heq := tendsto_nhds_unique hlim ht
  have hr : ν.real univ = 1 := by
    have := congrArg Complex.re heq
    simp at this
    linarith
  constructor
  rw [measureReal_def] at hr
  exact (ENNReal.toReal_eq_one_iff _).1 hr

theorem isFreeConv_support (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ )
    {ν : Measure ℝ /- [definition] -/ } (hν : IsFreeConv μ1 μ2 ν /- [standing] -/ ) : SupportedIn ν (11 * R) := by
  obtain ⟨hfin, hS⟩ := hν
  have hs1 := shiftBounds_hfun h1 hR
  have hs2 := shiftBounds_hfun h2 hR
  refine RMTFoundations.StieltjesSupport.support_of_im_small ν (11 * R) (1 / (48 * R ^ 2)) fun x η hη hx => ?_
  set z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  have hz : 0 < z.im := by simp [z, hη]
  have hzre : z.re = x := by simp [z]
  have hzim : z.im = η := by simp [z]
  rw [hS z hz]
  obtain ⟨-, -, hre1, -, him1⟩ := om1_tail hs1 hs2 hR.le (by linarith : (0 : ℝ) ≤ 2 * R) hz
    (by rw [hzre]; linarith)
  have hw : 0 < (omega1 μ1 μ2 z).im := om1_mem hs1 hs2 hR.le hz
  refine ⟨im_stieltjes_nonneg μ1 hw, ?_⟩
  have hre : 9 * R ≤ |(omega1 μ1 μ2 z).re| := hre1
  refine (im_stieltjes_tail h1 hw (by linarith)).trans ?_
  have hd : 8 * R ≤ |(omega1 μ1 μ2 z).re| - R := by linarith
  have hq : (1 / (|(omega1 μ1 μ2 z).re| - R)) ^ 2 ≤ 1 / (64 * R ^ 2) := by
    rw [div_pow, one_pow]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have him : (omega1 μ1 μ2 z).im ≤ 4 / 3 * η := by rw [← hzim]; exact him1
  calc (omega1 μ1 μ2 z).im * (1 / (|(omega1 μ1 μ2 z).re| - R)) ^ 2
      ≤ (4 / 3 * η) * (1 / (64 * R ^ 2)) :=
        mul_le_mul him hq (by positivity) (by linarith)
    _ = 1 / (48 * R ^ 2) * η := by field_simp; ring

theorem freeConv_isFreeConv (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    IsFreeConv μ1 μ2 (freeConv μ1 μ2) := by
  have hex := exists_isFreeConv h1 h2 hR
  rw [freeConv, dif_pos hex]
  exact hex.choose_spec

/-- **Uniqueness**: every representing measure is `freeConv μ₁ μ₂`. -/
theorem isFreeConv_unique (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ )
    {ν : Measure ℝ /- [definition] -/ } (hν : IsFreeConv μ1 μ2 ν /- [standing] -/ ) : ν = freeConv μ1 μ2 := by
  have hF := freeConv_isFreeConv h1 h2 hR
  haveI := hν.1
  haveI := hF.1
  exact measure_eq_of_stieltjes fun z hz => by rw [hν.2 z hz, hF.2 z hz]

/-- **`μ₁ ⊞ μ₂` is a compactly supported probability measure whose Stieltjes transform is
`S_{μ₁} ∘ ω₁ = S_{μ₂} ∘ ω₂`.** -/
theorem freeConv_spec (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    IsProbabilityMeasure (freeConv μ1 μ2) ∧ SupportedIn (freeConv μ1 μ2) (11 * R)
      ∧ ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, stieltjes (freeConv μ1 μ2) z = stieltjes μ1 (omega1 μ1 μ2 z)
        ∧ stieltjes (freeConv μ1 μ2) z = stieltjes μ2 (omega2 μ1 μ2 z) := by
  have hF := freeConv_isFreeConv h1 h2 hR
  refine ⟨isFreeConv_prob h1 h2 hR hF, isFreeConv_support h1 h2 hR hF, fun z hz =>
    ⟨hF.2 z hz, ?_⟩⟩
  rw [hF.2 z hz, stieltjes_omega_eq h1 h2 hR hz]

theorem freeConv_isProb (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) :
    IsProbabilityMeasure (freeConv μ1 μ2) :=
  (freeConv_spec h1 h2 hR).1

end FreeConvolution

section Semicircle

/-- The principal square root `w^{1/2}`. -/
noncomputable def csqrt (w : ℂ /- [definition] -/ ) : ℂ := w ^ (1 / 2 : ℂ)

theorem csqrt_sq (w : ℂ /- [definition] -/ ) : csqrt w ^ 2 = w := by
  rw [csqrt, ← Complex.cpow_nat_mul]
  norm_num

/-- `Re w^{1/2} = √((|w| + Re w)/2)`: continuous on all of `ℂ`, including the cut. -/
theorem re_sq (w : ℂ /- [definition] -/ ) : (csqrt w).re = Real.sqrt ((‖w‖ + w.re) / 2) := by
  by_cases hw : w = 0
  · subst hw
    rw [csqrt, Complex.zero_cpow (by norm_num)]
    simp
  rw [csqrt, Complex.cpow_def, if_neg hw, Complex.exp_re]
  have h1 : (Complex.log w * (1 / 2 : ℂ)).re = Real.log ‖w‖ / 2 := by
    simp [Complex.log_re]; ring
  have h2 : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
    simp [Complex.log_im]; ring
  rw [h1, h2, Real.cos_half (by linarith [Complex.neg_pi_lt_arg w]) (Complex.arg_le_pi w),
    Complex.cos_arg hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have he : Real.exp (Real.log ‖w‖ / 2) = Real.sqrt ‖w‖ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    ring_nf
  rw [he, ← Real.sqrt_mul hn.le]
  congr 1
  field_simp

theorem re_sq_nonneg (w : ℂ /- [definition] -/ ) : 0 ≤ (csqrt w).re := by
  rw [re_sq]; exact Real.sqrt_nonneg _

theorem continuous_re_sq : Continuous fun w : ℂ => (csqrt w).re := by
  simp_rw [re_sq]
  fun_prop

theorem re_sq_le (w : ℂ /- [definition] -/ ) : (csqrt w).re ≤ 1 + ‖w‖ := by
  rw [re_sq]
  have h1 : (‖w‖ + w.re) / 2 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; linarith
  have h2 : Real.sqrt ((‖w‖ + w.re) / 2) ≤ Real.sqrt ‖w‖ := Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt ‖w‖ ≤ 1 + ‖w‖ := by
    rcases le_or_gt ‖w‖ 1 with h | h
    · have : Real.sqrt ‖w‖ ≤ 1 := by
        rw [Real.sqrt_le_one]; exact h
      linarith [norm_nonneg w]
    · have : Real.sqrt ‖w‖ ≤ ‖w‖ := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      linarith
  linarith

theorem re_sq_ofReal (v : ℝ /- [definition] -/ ) : (csqrt (v : ℂ)).re = Real.sqrt v := by
  rw [re_sq, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h]; ring_nf
  · rw [abs_of_neg h, Real.sqrt_eq_zero'.2 (by linarith), Real.sqrt_eq_zero'.2 h.le]

variable {s : ℝ /- [definition] -/ }

/-- `c² - z²`, the radicand of the semicircle transform with `c² = 4s`. -/
def rad (s : ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) : ℂ := 4 * (s : ℂ) - z ^ 2

theorem rad_mem_slitPlane (hs : 0 < s /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : rad s z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hx : z.re = 0
  · left
    have : (rad s z).re = 4 * s - (z.re ^ 2 - z.im ^ 2) := by
      simp [rad, pow_two, Complex.mul_re]
    rw [this, hx]; nlinarith
  · right
    have : (rad s z).im = -(2 * z.re * z.im) := by
      simp [rad, pow_two, Complex.mul_im]
      ring
    rw [this]
    have : z.re * z.im ≠ 0 := mul_ne_zero hx hz.ne'
    intro h; apply this; linarith

/-- **The semicircle Stieltjes transform** `g_s(z) = (-z + i√(4s - z²))/(2s)`. -/
noncomputable def gsc (s : ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) : ℂ := (-z + Complex.I * csqrt (rad s z)) / (2 * s)

theorem gsc_quad (hs : 0 < s /- [standing] -/ ) (z : ℂ /- [definition] -/ ) : (s : ℂ) * gsc s z ^ 2 + z * gsc s z + 1 = 0 := by
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set u := csqrt (rad s z)
  have h : u ^ 2 = 4 * (s : ℂ) - z ^ 2 := csqrt_sq (rad s z)
  have hI := Complex.I_sq
  have key : (-z + Complex.I * u) ^ 2 + 2 * z * (-z + Complex.I * u) + 4 * s = 0 := by
    linear_combination u ^ 2 * hI - h
  have e : (s : ℂ) * gsc s z ^ 2 + z * gsc s z + 1
      = ((-z + Complex.I * u) ^ 2 + 2 * z * (-z + Complex.I * u) + 4 * s) / (4 * s) := by
    unfold gsc
    field_simp
    ring
  rw [e, key, zero_div]

/-- `Re √(4s - z²) > Im z` on `ℂ⁺`. -/
theorem re_sq_gt (hs : 0 < s /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : z.im < (csqrt (rad s z)).re := by
  set u := csqrt (rad s z)
  have hu : u ^ 2 = rad s z := csqrt_sq _
  have ha : 0 ≤ u.re := re_sq_nonneg _
  have hre : u.re ^ 2 - u.im ^ 2 = 4 * s - (z.re ^ 2 - z.im ^ 2) := by
    have := congrArg Complex.re hu
    simp [rad, pow_two, Complex.mul_re] at this
    nlinarith [this]
  have him : u.re * u.im = -(z.re * z.im) := by
    have := congrArg Complex.im hu
    simp [rad, pow_two, Complex.mul_im] at this
    nlinarith [this]
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0] at him
    have hx : z.re = 0 := by
      have : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hz.ne'
    rw [← h0, hx] at hre
    nlinarith
  · have hb : z.re ^ 2 ≤ u.im ^ 2 := by
      have e : (u.re * u.im) ^ 2 = (z.re * z.im) ^ 2 := by rw [him]; ring
      have h1 : u.re ^ 2 * z.re ^ 2 ≤ z.im ^ 2 * z.re ^ 2 := by
        have : u.re ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ ha hle 2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have h2 : u.re ^ 2 * z.re ^ 2 ≤ u.re ^ 2 * u.im ^ 2 := by nlinarith
      have h3 : 0 < u.re ^ 2 := by positivity
      exact le_of_mul_le_mul_left h2 h3
    have : u.re ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ ha hle 2
    nlinarith

theorem gsc_im (z : ℂ /- [definition] -/ ) : (gsc s z).im = (-z.im + (csqrt (rad s z)).re) / (2 * s) := by
  unfold gsc
  rw [show (2 * (s : ℂ)) = ((2 * s : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
  simp

theorem gsc_im_pos (hs : 0 < s /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : 0 < (gsc s z).im := by
  rw [gsc_im]
  have := re_sq_gt hs hz
  exact div_pos (by linarith) (by linarith)

theorem gsc_differentiableOn (hs : 0 < s /- [standing] -/ ) : DifferentiableOn ℂ (gsc s) RMTFoundations.AnalyticHalfPlane.upper := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun z => csqrt (rad s z)) z := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) (rad s z) :=
      (Complex.hasStrictDerivAt_cpow_const (rad_mem_slitPlane hs hz)).hasDerivAt.differentiableAt
    have hr : DifferentiableAt ℂ (rad s) z := by unfold rad; fun_prop
    exact hd.comp z hr
  unfold gsc
  exact ((differentiableAt_id.neg.add (h1.const_mul _)).div_const _).differentiableWithinAt

theorem gsc_mul (hs : 0 < s /- [standing] -/ ) (z : ℂ /- [definition] -/ ) : gsc s z * (z + s * gsc s z) = -1 := by
  linear_combination gsc_quad hs z

theorem norm_gsc_le (hs : 0 < s /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) : ‖gsc s z‖ ≤ 1 / z.im := by
  have hm := gsc_mul hs z
  have hi : z.im ≤ (z + s * gsc s z).im := by
    have : (z + s * gsc s z).im = z.im + s * (gsc s z).im := by simp
    rw [this]; nlinarith [gsc_im_pos hs hz]
  have hn : z.im ≤ ‖z + s * gsc s z‖ :=
    hi.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hn1 : ‖gsc s z‖ * ‖z + s * gsc s z‖ = 1 := by
    rw [← norm_mul, hm, norm_neg, norm_one]
  rw [le_div_iff₀ hz]
  calc ‖gsc s z‖ * z.im ≤ ‖gsc s z‖ * ‖z + s * gsc s z‖ :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = 1 := hn1

end Semicircle

section SemicircleMeasure

variable {s : ℝ /- [definition] -/ }

/-- `ν` represents the semicircle transform `g_s`. -/
def IsSC (s : ℝ /- [definition] -/ ) (ν : Measure ℝ /- [definition] -/ ) : Prop :=
  IsFiniteMeasure ν ∧ ∀ z ∈ RMTFoundations.AnalyticHalfPlane.upper, stieltjes ν z = gsc s z

theorem exists_isSC (hs : 0 < s /- [standing] -/ ) : ∃ ν, IsSC s ν := by
  obtain ⟨ν, hν, -, hS⟩ := RMTFoundations.HerglotzBorelProof.herglotzBorel (gsc s) 1 (gsc_differentiableOn hs)
    (fun z hz => (gsc_im_pos hs hz).le) (fun z hz => norm_gsc_le hs hz)
  exact ⟨ν, hν, fun z hz => (hS z hz).symm⟩

open Classical in
/-- **The semicircle law of variance `s`**, the measure whose Stieltjes transform is `g_s`
(constructed by the proved Herglotz theorem, not by integrating its density). -/
noncomputable def semicircle (s : ℝ /- [definition] -/ ) : Measure ℝ :=
  if h : ∃ ν, IsSC s ν then h.choose else 0

theorem semicircle_isSC (hs : 0 < s /- [standing] -/ ) : IsSC s (semicircle s) := by
  rw [semicircle, dif_pos (exists_isSC hs)]
  exact (exists_isSC hs).choose_spec

theorem semicircle_finite (hs : 0 < s /- [standing] -/ ) : IsFiniteMeasure (semicircle s) :=
  (semicircle_isSC hs).1

theorem stieltjes_semicircle (hs : 0 < s /- [standing] -/ ) {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    stieltjes (semicircle s) z = gsc s z :=
  (semicircle_isSC hs).2 z hz

/-- The semicircle density `√(4s - x²)/(2πs)` (zero off `[-2√s, 2√s]`). -/
noncomputable def scDens (s x : ℝ /- [definition] -/ ) : ℝ := Real.sqrt (4 * s - x ^ 2) / (2 * Real.pi * s)

theorem scDens_nonneg (hs : 0 < s /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : 0 ≤ scDens s x := by
  unfold scDens; positivity

theorem continuous_scDens (s : ℝ /- [definition] -/ ) : Continuous (scDens s) := by
  unfold scDens; fun_prop

theorem sc_boundary (hs : 0 < s /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : Tendsto (fun η : ℝ =>
    (stieltjes (semicircle s) ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * scDens s x)) := by
  have hc : Continuous fun η : ℝ =>
      (-η + (csqrt (rad s ((x : ℂ) + (η : ℂ) * Complex.I))).re) / (2 * s) := by
    have : Continuous fun η : ℝ => rad s ((x : ℂ) + (η : ℂ) * Complex.I) := by
      unfold rad; fun_prop
    exact ((continuous_neg.add (continuous_re_sq.comp this)).div_const _)
  have h0 : (-(0 : ℝ) + (csqrt (rad s ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))).re) / (2 * s)
      = Real.pi * scDens s x := by
    have e : rad s ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((4 * s - x ^ 2 : ℝ) : ℂ) := by
      simp [rad]
    rw [e, re_sq_ofReal, scDens]
    field_simp
    ring
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [h0] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hz : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  rw [stieltjes_semicircle hs hz, gsc_im]
  simp

theorem sc_bound (hs : 0 < s /- [standing] -/ ) (a b : ℝ /- [definition] -/ ) : ∃ C, ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc a b,
    |(stieltjes (semicircle s) ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C := by
  refine ⟨(2 + 4 * s + (|a| + |b| + 1) ^ 2) / (2 * s), ?_⟩
  have hev : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), η < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [hev, self_mem_nhdsWithin] with η h1 h0 x hx
  have h0p : (0 : ℝ) < η := h0
  set z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  have hz : 0 < z.im := by simpa [z] using h0p
  rw [stieltjes_semicircle hs hz, gsc_im, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * s)]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have hr0 := re_sq_nonneg (rad s z)
  have hr1 := re_sq_le (rad s z)
  have hzim : z.im = η := by simp [z]
  have hxab : |x| ≤ |a| + |b| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [hx.2, le_abs_self b, abs_nonneg a]
    · rw [abs_of_neg h]; linarith [hx.1, neg_abs_le a, abs_nonneg b]
  have hzn : ‖z‖ ≤ |a| + |b| + 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos h0p]
    linarith
  have hrad : ‖rad s z‖ ≤ 4 * s + (|a| + |b| + 1) ^ 2 := by
    unfold rad
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have : ‖z‖ ^ 2 ≤ (|a| + |b| + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
    norm_num
    linarith
  rw [hzim]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_pos h0p, abs_of_nonneg hr0]
  linarith

theorem sc_Ioo (hs : 0 < s /- [standing] -/ ) {a b : ℝ /- [definition] -/ } (hab : a < b /- [standing] -/ ) :
    (semicircle s).real (Ioo a b) = ∫ x in a..b, scDens s x := by
  haveI := semicircle_finite hs
  exact RMTFoundations.StieltjesInversion.stieltjes_density (semicircle s) (a - 1) (b + 1) (scDens s)
    (fun x _ => sc_boundary hs x) (fun aa bb _ _ => sc_bound hs aa bb) a b (by linarith) hab
    (by linarith)

theorem sc_atom (hs : 0 < s /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : (semicircle s).real {x} = 0 := by
  haveI := semicircle_finite hs
  obtain ⟨C, hC⟩ := sc_bound hs (x - 1) (x + 1)
  exact RMTFoundations.StieltjesInversion.atom_zero (semicircle s) x 1 C one_pos (scDens s)
    (fun y _ => sc_boundary hs y) hC

theorem sc_Ioc (hs : 0 < s /- [standing] -/ ) {a b : ℝ /- [definition] -/ } (hab : a < b /- [standing] -/ ) :
    (semicircle s).real (Ioc a b) = ∫ x in a..b, scDens s x := by
  haveI := semicircle_finite hs
  rw [← Set.Ioo_union_right hab, measureReal_union (by simp) (measurableSet_singleton b),
    sc_Ioo hs hab, sc_atom hs b, add_zero]

/-- **The semicircle law has density `scDens s`**: it is `Lebesgue.withDensity scDens`. -/
theorem semicircle_eq_withDensity (hs : 0 < s /- [standing] -/ ) :
    semicircle s = volume.withDensity (fun x => ENNReal.ofReal (scDens s x)) := by
  haveI := semicircle_finite hs
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [withDensity_apply _ measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le hab.le, ← sc_Ioc hs hab, ofReal_measureReal]
  · exact (continuous_scDens s).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact Eventually.of_forall fun x => scDens_nonneg hs x

/-- The edge `c = 2√s`. -/
noncomputable def scEdge (s : ℝ /- [definition] -/ ) : ℝ := 2 * Real.sqrt s

theorem scEdge_sq (hs : 0 < s /- [standing] -/ ) : scEdge s ^ 2 = 4 * s := by
  unfold scEdge; rw [mul_pow, Real.sq_sqrt hs.le]; ring

theorem scEdge_pos (hs : 0 < s /- [standing] -/ ) : 0 < scEdge s := by unfold scEdge; positivity

theorem scDens_eq_zero (hs : 0 < s /- [standing] -/ ) {x : ℝ /- [definition] -/ } (hx : scEdge s ≤ |x| /- [standing] -/ ) : scDens s x = 0 := by
  unfold scDens
  rw [Real.sqrt_eq_zero'.2, zero_div]
  have := scEdge_sq hs
  have h2 : scEdge s ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (scEdge_pos hs).le hx 2
  rw [sq_abs] at h2
  linarith

theorem scDens_pos (hs : 0 < s /- [standing] -/ ) {x : ℝ /- [definition] -/ } (hx : |x| < scEdge s /- [standing] -/ ) : 0 < scDens s x := by
  unfold scDens
  have := scEdge_sq hs
  have h2 : |x| ^ 2 < scEdge s ^ 2 := pow_lt_pow_left₀ hx (abs_nonneg x) two_ne_zero
  rw [sq_abs] at h2
  exact div_pos (Real.sqrt_pos.2 (by linarith)) (by positivity)

theorem sc_Ioo_zero (hs : 0 < s /- [standing] -/ ) {a b : ℝ /- [definition] -/ } (hab : a < b /- [standing] -/ )
    (h0 : ∀ x ∈ Icc a b, scEdge s ≤ |x| /- [standing] -/ ) : (semicircle s).real (Ioo a b) = 0 := by
  rw [sc_Ioo hs hab]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
    rw [Set.uIcc_of_le hab.le] at hx
    exact scDens_eq_zero hs (h0 x hx))]
  simp

theorem semicircle_supported (hs : 0 < s /- [standing] -/ ) : SupportedIn (semicircle s) (scEdge s) := by
  haveI := semicircle_finite hs
  have hc := scEdge_pos hs
  have hright : semicircle s (Ioi (scEdge s)) = 0 := by
    have hcov : Ioi (scEdge s) ⊆ ⋃ n : ℕ, Ioo (scEdge s) (scEdge s + n + 1) := by
      intro x hx
      obtain ⟨n, hn⟩ := exists_nat_gt (x - scEdge s)
      exact Set.mem_iUnion.2 ⟨n, hx, by linarith⟩
    refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
    have := sc_Ioo_zero hs (show scEdge s < scEdge s + n + 1 by linarith) (fun x hx => by
      rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.1)
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
  have hleft : semicircle s (Iio (-scEdge s)) = 0 := by
    have hcov : Iio (-scEdge s) ⊆ ⋃ n : ℕ, Ioo (-scEdge s - n - 1) (-scEdge s) := by
      intro x hx
      obtain ⟨n, hn⟩ := exists_nat_gt (-scEdge s - x)
      exact Set.mem_iUnion.2 ⟨n, by linarith, hx⟩
    refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
    have := sc_Ioo_zero hs (show -scEdge s - n - 1 < -scEdge s by linarith) (fun x hx => by
      rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2])
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
  have hc2 : (Icc (-scEdge s) (scEdge s))ᶜ ⊆ Iio (-scEdge s) ∪ Ioi (scEdge s) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hc2 (measure_union_null hleft hright)

theorem semicircle_prob (hs : 0 < s /- [standing] -/ ) : IsProbabilityMeasure (semicircle s) := by
  haveI := semicircle_finite hs
  have hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * stieltjes (semicircle s)
      ((y : ℂ) * Complex.I)) atTop (𝓝 (-1)) := by
    have hbd : ∀ᶠ y : ℝ in atTop, ‖((y : ℂ) * Complex.I) * stieltjes (semicircle s)
        ((y : ℂ) * Complex.I) - (-1)‖ ≤ s / y ^ 2 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hz : 0 < ((y : ℂ) * Complex.I).im := by simp [hy]
      rw [stieltjes_semicircle hs hz]
      have e : ((y : ℂ) * Complex.I) * gsc s ((y : ℂ) * Complex.I) - (-1)
          = -((s : ℂ) * gsc s ((y : ℂ) * Complex.I) ^ 2) := by
        linear_combination gsc_quad hs ((y : ℂ) * Complex.I)
      rw [e, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      have hg := norm_gsc_le hs hz
      have hzi : ((y : ℂ) * Complex.I).im = y := by simp
      rw [hzi] at hg
      have : ‖gsc s ((y : ℂ) * Complex.I)‖ ^ 2 ≤ (1 / y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
      calc s * ‖gsc s ((y : ℂ) * Complex.I)‖ ^ 2 ≤ s * (1 / y) ^ 2 :=
            mul_le_mul_of_nonneg_left this hs.le
        _ = s / y ^ 2 := by ring
    have h0 : Tendsto (fun y : ℝ => s / y ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbd h0
  have heq := tendsto_nhds_unique hlim (RMTFoundations.StieltjesSupport.tendsto_iy_stieltjes (semicircle s))
  have hr : (semicircle s).real univ = 1 := by
    have := congrArg Complex.re heq
    simp at this
    linarith
  constructor
  rw [measureReal_def] at hr
  exact (ENNReal.toReal_eq_one_iff _).1 hr

/-- **The right endpoint of the semicircle law is `2√s`.** -/
theorem rightEndpoint_semicircle (hs : 0 < s /- [standing] -/ ) : rightEndpoint (semicircle s) = scEdge s := by
  haveI := semicircle_prob hs
  have hsup := semicircle_supported hs
  refine le_antisymm (rightEndpoint_le hsup) ?_
  by_contra hlt
  rw [not_le] at hlt
  set E := rightEndpoint (semicircle s)
  have hc := scEdge_pos hs
  set a := max E 0
  have ha : a < scEdge s := max_lt hlt hc
  have hpos : 0 < (semicircle s).real (Ioo a (scEdge s)) := by
    rw [sc_Ioo hs ha]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_scDens s).intervalIntegrable _ _) (fun x hx => scDens_pos hs ?_) ha
    have h0 : 0 < x := lt_of_le_of_lt (le_max_right E 0) hx.1
    rw [abs_of_pos h0]; exact hx.2
  have hnull : semicircle s (Ioo a (scEdge s)) = 0 :=
    measure_mono_null (fun x hx => lt_of_le_of_lt (le_max_left E 0) hx.1)
      (measure_Ioi_rightEndpoint hsup)
  rw [measureReal_def, hnull] at hpos
  simp at hpos

/-- `hfun` of the semicircle law is `s · g_s`. -/
theorem hfun_semicircle (hs : 0 < s /- [standing] -/ ) {w : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) :
    hfun (semicircle s) w = s * gsc s w := by
  rw [hfun, stieltjes_semicircle hs hw]
  have hm := gsc_mul hs w
  have hne : gsc s w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; norm_num at hm
  field_simp
  linear_combination (-1 : ℂ) * hm

/-- **Root uniqueness**: `g_s(w)` is the only root of `s x² + w x + 1` in `ℂ⁺`. -/
theorem eq_gsc_of_root (hs : 0 < s /- [standing] -/ ) {w x : ℂ /- [definition] -/ } (hw : 0 < w.im /- [standing] -/ ) (hx : 0 < x.im /- [standing] -/ )
    (hroot : (s : ℂ) * x ^ 2 + w * x + 1 = 0 /- [standing] -/ ) : x = gsc s w := by
  set y := gsc s w
  have hy : 0 < y.im := gsc_im_pos hs hw
  have hry := gsc_quad hs w
  by_contra hne
  have hsum : (s : ℂ) * (x + y) + w = 0 := by
    have h1 : (x - y) * ((s : ℂ) * (x + y) + w) = 0 := by linear_combination hroot - hry
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hprod : (s : ℂ) * (x * y) = 1 := by linear_combination hsum * x - hroot
  have hre := congrArg Complex.re hprod
  have him := congrArg Complex.im hprod
  simp [Complex.mul_re, Complex.mul_im] at hre him
  have him2 : x.re * y.im = -(x.im * y.re) := by
    rcases him with h | h
    · exact absurd h hs.ne'
    · linarith
  have hpos : 0 < x.re * y.re - x.im * y.im := by
    have : s * (x.re * y.re - x.im * y.im) = 1 := by linarith
    by_contra hle
    push Not at hle
    nlinarith
  have k1 : (x.re * y.re - x.im * y.im) * y.im = -x.im * (y.re ^ 2 + y.im ^ 2) := by
    linear_combination y.re * him2
  have k2 : 0 < (x.re * y.re - x.im * y.im) * y.im := mul_pos hpos hy
  have k3 : 0 ≤ x.im * (y.re ^ 2 + y.im ^ 2) := by positivity
  linarith

end SemicircleMeasure

section SemicircleFacts

theorem SupportedIn.mono {μ : Measure ℝ /- [definition] -/ } {r R : ℝ /- [definition] -/ } (h : SupportedIn μ r /- [standing] -/ ) (hrR : r ≤ R /- [standing] -/ ) :
    SupportedIn μ R :=
  measure_mono_null (compl_subset_compl.2 (Icc_subset_Icc (by linarith) hrR)) h

/-- `iy (iy S_μ(iy) + 1) → -mean μ`. -/
theorem tendsto_mean {μ : Measure ℝ /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ] {R : ℝ /- [definition] -/ } (h : SupportedIn μ R /- [standing] -/ ) :
    Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * (((y : ℂ) * Complex.I)
      * stieltjes μ ((y : ℂ) * Complex.I) + 1)) atTop (𝓝 (-(mean μ : ℂ))) := by
  have hrw : ∀ y : ℝ, 0 < y → ((y : ℂ) * Complex.I) * (((y : ℂ) * Complex.I)
      * stieltjes μ ((y : ℂ) * Complex.I) + 1)
      = ∫ t, ((y : ℂ) * Complex.I) * ((t : ℂ) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹) ∂μ := by
    intro y hy
    have hw : 0 < ((y : ℂ) * Complex.I).im := by simp [hy]
    rw [integral_const_mul]
    congr 1
    have hpt : ∀ t : ℝ, (t : ℂ) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹
        = 1 + (y : ℂ) * Complex.I * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹ := by
      intro t
      have := sub_ne hw t
      field_simp
      ring
    simp_rw [hpt]
    rw [integral_add (integrable_const _) ((integrable_inv_sub μ hw).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul, stieltjes]
    ring
  have hmean : (-(mean μ : ℂ)) = ∫ t, -(t : ℂ) ∂μ := by
    rw [integral_neg, integral_complex_ofReal, mean]
  rw [hmean]
  refine Tendsto.congr' (f₁ := fun y : ℝ => ∫ t, ((y : ℂ) * Complex.I)
      * ((t : ℂ) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹) ∂μ) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (hrw y hy).symm
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => R) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hw : 0 < ((y : ℂ) * Complex.I).im := by simp [hy]
    exact (continuous_const.mul (Complex.continuous_ofReal.mul
      (continuous_inv_sub hw))).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hw : 0 < ((y : ℂ) * Complex.I).im := by simp [hy]
    filter_upwards [ae_mem h] with t ht
    have hyim : ((y : ℂ) * Complex.I).im = y := by simp
    have hb := norm_inv_sub_le hw t
    rw [hyim] at hb
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    calc y * (|t| * ‖((t : ℂ) - (y : ℂ) * Complex.I)⁻¹‖) ≤ y * (R * y⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (abs_le.2 ht) hb (norm_nonneg _)
            (by linarith [ht.1, ht.2])) hy.le
      _ = R := by field_simp
  · refine Eventually.of_forall fun t => ?_
    have hkey : ∀ y : ℝ, 0 < y → ((y : ℂ) * Complex.I)
        * ((t : ℂ) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹)
        = (t : ℂ) * ((t : ℂ) / ((y : ℂ) * Complex.I) - 1)⁻¹ := by
      intro y hy
      have hyI : (y : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') Complex.I_ne_zero
      rw [div_sub_one hyI, inv_div]
      ring
    have h1 : Tendsto (fun y : ℝ => (t : ℂ) / ((y : ℂ) * Complex.I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun y : ℝ => ‖(t : ℂ) / ((y : ℂ) * Complex.I)‖) =ᶠ[atTop] fun y => |t| / y := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
      exact Tendsto.congr' this.symm (tendsto_const_nhds.div_atTop tendsto_id)
    have h2 := ((h1.sub tendsto_const_nhds).inv₀ (show (0 : ℂ) - 1 ≠ 0 by norm_num)).const_mul
      (t : ℂ)
    rw [show (t : ℂ) * ((0 : ℂ) - 1)⁻¹ = -(t : ℂ) by norm_num] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (hkey y hy).symm

variable {s : ℝ /- [definition] -/ }

theorem semicircle_mean (hs : 0 < s /- [standing] -/ ) : mean (semicircle s) = 0 := by
  haveI := semicircle_prob hs
  have ht := tendsto_mean (semicircle_supported hs)
  have hz : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * (((y : ℂ) * Complex.I)
      * stieltjes (semicircle s) ((y : ℂ) * Complex.I) + 1)) atTop (𝓝 0) := by
    have hbd : ∀ᶠ y : ℝ in atTop, ‖((y : ℂ) * Complex.I) * (((y : ℂ) * Complex.I)
        * stieltjes (semicircle s) ((y : ℂ) * Complex.I) + 1)‖ ≤ s / y := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hz : 0 < ((y : ℂ) * Complex.I).im := by simp [hy]
      rw [stieltjes_semicircle hs hz]
      have e : ((y : ℂ) * Complex.I) * gsc s ((y : ℂ) * Complex.I) + 1
          = -((s : ℂ) * gsc s ((y : ℂ) * Complex.I) ^ 2) := by
        linear_combination gsc_quad hs ((y : ℂ) * Complex.I)
      rw [e]
      simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, abs_of_pos hs, abs_of_pos hy]
      have hg := norm_gsc_le hs hz
      have hzi : ((y : ℂ) * Complex.I).im = y := by simp
      rw [hzi] at hg
      have h2 : ‖gsc s ((y : ℂ) * Complex.I)‖ ^ 2 ≤ (1 / y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
      calc y * (s * ‖gsc s ((y : ℂ) * Complex.I)‖ ^ 2) ≤ y * (s * (1 / y) ^ 2) := by gcongr
        _ = s / y := by field_simp
    have h0 : Tendsto (fun y : ℝ => s / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbd h0
  have heq := tendsto_nhds_unique ht hz
  have := congrArg Complex.re heq
  simpa using this

/-- **`sc(a) ⊞ sc(b) = sc(a + b)`**, from the subordination definition. -/
theorem freeConv_semicircle {a b : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) (hb : 0 < b /- [standing] -/ ) :
    freeConv (semicircle a) (semicircle b) = semicircle (a + b) := by
  haveI := semicircle_prob ha
  haveI := semicircle_prob hb
  have hab : 0 < a + b := add_pos ha hb
  set R := scEdge a + scEdge b
  have hR : 0 < R := add_pos (scEdge_pos ha) (scEdge_pos hb)
  have h1 : SupportedIn (semicircle a) R :=
    (semicircle_supported ha).mono (by linarith [scEdge_pos hb])
  have h2 : SupportedIn (semicircle b) R :=
    (semicircle_supported hb).mono (by linarith [scEdge_pos ha])
  have hs1 := shiftBounds_hfun h1 hR
  have hs2 := shiftBounds_hfun h2 hR
  refine (isFreeConv_unique h1 h2 hR ⟨semicircle_finite hab, fun z hz => ?_⟩).symm
  have hzp : 0 < z.im := hz
  set G := gsc (a + b) z
  have hG : 0 < G.im := gsc_im_pos hab hzp
  set w1 := z + b * G
  set w2 := z + a * G
  have hw1 : z.im ≤ w1.im := by
    have : w1.im = z.im + b * G.im := by simp [w1]
    rw [this]; nlinarith
  have hw2 : 0 < w2.im := by
    have : w2.im = z.im + a * G.im := by simp [w2]
    rw [this]; nlinarith
  have hq := gsc_quad hab z
  have e1 : gsc a w1 = G := (eq_gsc_of_root ha (lt_of_lt_of_le hzp hw1) hG (by
    simp only [w1]; push_cast at hq ⊢; linear_combination hq)).symm
  have e2 : gsc b w2 = G := (eq_gsc_of_root hb hw2 hG (by
    simp only [w2]; push_cast at hq ⊢; linear_combination hq)).symm
  have hfix : fm (hfun (semicircle a)) (hfun (semicircle b)) z w1 = w1 := by
    simp only [fm, Tm]
    rw [hfun_semicircle ha (lt_of_lt_of_le hzp hw1), e1]
    rw [hfun_semicircle hb hw2, e2]
  have hom : omega1 (semicircle a) (semicircle b) z = w1 :=
    fixed_unique hs1 hs2 hzp (om1_im_ge hs1 hs2 hR.le hzp) hw1 (om1_fixed hs1 hs2 hR.le hzp) hfix
  rw [stieltjes_semicircle hab hzp, hom, stieltjes_semicircle ha (lt_of_lt_of_le hzp hw1), e1]

/-- The edge coefficient `√(2c)/(2πs)` of the semicircle density at `c = 2√s`. -/
noncomputable def scCoef (s : ℝ /- [definition] -/ ) : ℝ := Real.sqrt (2 * scEdge s) / (2 * Real.pi * s)

/-- **The square-root edge of the semicircle density**:
`|ρ_s(E) - scCoef · √(c - E)| ≤ (c - E)/(2πs)` for `-c < E < c`. -/
theorem sc_edge_asymptotic (hs : 0 < s /- [standing] -/ ) {E : ℝ /- [definition] -/ } (hE : E ∈ Ioo (-scEdge s) (scEdge s) /- [standing] -/ ) :
    |scDens s E - scCoef s * Real.sqrt (scEdge s - E)|
      ≤ 1 / (2 * Real.pi * s) * (scEdge s - E) := by
  set c := scEdge s
  have hc := scEdge_pos hs
  have hc2 := scEdge_sq hs
  have hr0 : 0 ≤ c - E := by linarith [hE.2]
  have hp0 : 0 ≤ c + E := by linarith [hE.1]
  set p := Real.sqrt (c + E)
  set q := Real.sqrt (2 * c)
  set r := Real.sqrt (c - E)
  have hp : p ^ 2 = c + E := Real.sq_sqrt hp0
  have hq : q ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hr : r ^ 2 = c - E := Real.sq_sqrt hr0
  have hpn : 0 ≤ p := Real.sqrt_nonneg _
  have hqp : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hrn : 0 ≤ r := Real.sqrt_nonneg _
  have hdens : scDens s E = r * p / (2 * Real.pi * s) := by
    unfold scDens
    congr 1
    rw [show 4 * s - E ^ 2 = (c - E) * (c + E) by nlinarith, Real.sqrt_mul hr0]
  have hpq : p ≤ q := Real.sqrt_le_sqrt (by linarith [hE.2])
  have hrq : r ≤ q := Real.sqrt_le_sqrt (by linarith [hE.1])
  have hdiff : (q - p) * (q + p) = r ^ 2 := by nlinarith
  have hkey : r * (q - p) ≤ r ^ 2 := by
    have h1 : q - p ≤ r ^ 2 / q := by
      rw [le_div_iff₀ hqp]
      nlinarith
    have h2 : r * (q - p) ≤ r * (r ^ 2 / q) := mul_le_mul_of_nonneg_left h1 hrn
    have h3 : r * (r ^ 2 / q) ≤ r ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hqp]
      nlinarith [sq_nonneg r]
    linarith
  have hpos : 0 < 2 * Real.pi * s := by positivity
  rw [hdens, scCoef, ← hr]
  rw [show r * p / (2 * Real.pi * s) - q / (2 * Real.pi * s) * r
      = -(r * (q - p)) / (2 * Real.pi * s) by ring]
  rw [abs_div, abs_neg, abs_of_pos hpos, abs_of_nonneg (mul_nonneg hrn (by linarith)),
    div_le_iff₀ hpos]
  field_simp
  linarith

/-- **Two-sided edge bounds** `√c/(2πs) √(c - x) ≤ ρ_s(x) ≤ √(2c)/(2πs) √(c - x)` on `(0, c)`. -/
theorem sc_density_bounds (hs : 0 < s /- [standing] -/ ) {x : ℝ /- [definition] -/ } (hx : x ∈ Ioo 0 (scEdge s) /- [standing] -/ ) :
    Real.sqrt (scEdge s) / (2 * Real.pi * s) * Real.sqrt (scEdge s - x) ≤ scDens s x
      ∧ scDens s x ≤ scCoef s * Real.sqrt (scEdge s - x) := by
  set c := scEdge s
  have hc2 := scEdge_sq hs
  have hr0 : 0 ≤ c - x := by linarith [hx.2]
  have hdens : scDens s x = Real.sqrt (c - x) * Real.sqrt (c + x) / (2 * Real.pi * s) := by
    unfold scDens
    congr 1
    rw [show 4 * s - x ^ 2 = (c - x) * (c + x) by nlinarith, Real.sqrt_mul hr0]
  have hpos : 0 < 2 * Real.pi * s := by positivity
  have h1 : Real.sqrt c ≤ Real.sqrt (c + x) := Real.sqrt_le_sqrt (by linarith [hx.1])
  have h2 : Real.sqrt (c + x) ≤ Real.sqrt (2 * c) := Real.sqrt_le_sqrt (by linarith [hx.2])
  have hr := Real.sqrt_nonneg (c - x)
  rw [hdens, scCoef]
  constructor
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 hr
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos, mul_comm (Real.sqrt (2 * c))]
    exact mul_le_mul_of_nonneg_left h2 hr

end SemicircleFacts
end RMTFoundations.FreeConvolution

#print axioms RMTFoundations.FreeConvolution.SupportedIn
#print axioms RMTFoundations.FreeConvolution.mean
#print axioms RMTFoundations.FreeConvolution.hfun
#print axioms RMTFoundations.FreeConvolution.uf
#print axioms RMTFoundations.FreeConvolution.ae_mem
#print axioms RMTFoundations.FreeConvolution.sub_ne
#print axioms RMTFoundations.FreeConvolution.im_le_norm_sub
#print axioms RMTFoundations.FreeConvolution.re_le_norm_sub
#print axioms RMTFoundations.FreeConvolution.continuous_inv_sub
#print axioms RMTFoundations.FreeConvolution.norm_inv_sub_le
#print axioms RMTFoundations.FreeConvolution.integrable_inv_sub
#print axioms RMTFoundations.FreeConvolution.integrable_ofReal
#print axioms RMTFoundations.FreeConvolution.integrable_id
#print axioms RMTFoundations.FreeConvolution.abs_mean_le
#print axioms RMTFoundations.FreeConvolution.im_inv_sub
#print axioms RMTFoundations.FreeConvolution.im_stieltjes_nonneg
#print axioms RMTFoundations.FreeConvolution.im_stieltjes_eq
#print axioms RMTFoundations.FreeConvolution.im_stieltjes_pos
#print axioms RMTFoundations.FreeConvolution.stieltjes_ne
#print axioms RMTFoundations.FreeConvolution.integrable_conj
#print axioms RMTFoundations.FreeConvolution.R_nonneg
#print axioms RMTFoundations.FreeConvolution.continuous_uf
#print axioms RMTFoundations.FreeConvolution.norm_uf_le
#print axioms RMTFoundations.FreeConvolution.integrable_uf
#print axioms RMTFoundations.FreeConvolution.integrable_uf_mul
#print axioms RMTFoundations.FreeConvolution.integrable_normSq_uf
#print axioms RMTFoundations.FreeConvolution.integral_uf
#print axioms RMTFoundations.FreeConvolution.integral_uf_mul
#print axioms RMTFoundations.FreeConvolution.mul_uf
#print axioms RMTFoundations.FreeConvolution.im_hfun
#print axioms RMTFoundations.FreeConvolution.im_hfun_nonneg
#print axioms RMTFoundations.FreeConvolution.norm_hfun_add_le
#print axioms RMTFoundations.FreeConvolution.norm_inv_sub_tail
#print axioms RMTFoundations.FreeConvolution.norm_uf_tail
#print axioms RMTFoundations.FreeConvolution.norm_hfun_add_tail
#print axioms RMTFoundations.FreeConvolution.im_hfun_tail
#print axioms RMTFoundations.FreeConvolution.sq_integral_mul_le
#print axioms RMTFoundations.FreeConvolution.stieltjes_contract
#print axioms RMTFoundations.FreeConvolution.ShiftBounds
#print axioms RMTFoundations.FreeConvolution.hfun_differentiableOn
#print axioms RMTFoundations.FreeConvolution.hfun_rep
#print axioms RMTFoundations.FreeConvolution.shiftBounds_hfun
#print axioms RMTFoundations.FreeConvolution.Tm
#print axioms RMTFoundations.FreeConvolution.fm
#print axioms RMTFoundations.FreeConvolution.orb
#print axioms RMTFoundations.FreeConvolution.om1
#print axioms RMTFoundations.FreeConvolution.Dq
#print axioms RMTFoundations.FreeConvolution.kf
#print axioms RMTFoundations.FreeConvolution.kf_nonneg
#print axioms RMTFoundations.FreeConvolution.kf_lt_one
#print axioms RMTFoundations.FreeConvolution.kf_anti
#print axioms RMTFoundations.FreeConvolution.Tm_im
#print axioms RMTFoundations.FreeConvolution.Tm_im_ge
#print axioms RMTFoundations.FreeConvolution.Tm_mem
#print axioms RMTFoundations.FreeConvolution.Tm_im_le
#print axioms RMTFoundations.FreeConvolution.Dq_Tm
#print axioms RMTFoundations.FreeConvolution.fm_im_ge
#print axioms RMTFoundations.FreeConvolution.Dq_fm
#print axioms RMTFoundations.FreeConvolution.orb_im_ge
#print axioms RMTFoundations.FreeConvolution.orb_mem
#print axioms RMTFoundations.FreeConvolution.orb_im_le
#print axioms RMTFoundations.FreeConvolution.Dq_orb
#print axioms RMTFoundations.FreeConvolution.cRat
#print axioms RMTFoundations.FreeConvolution.cCst
#print axioms RMTFoundations.FreeConvolution.cRat_lt_one
#print axioms RMTFoundations.FreeConvolution.cRat_nonneg
#print axioms RMTFoundations.FreeConvolution.orb_dist
#print axioms RMTFoundations.FreeConvolution.orb_tendsto
#print axioms RMTFoundations.FreeConvolution.om1_im_ge
#print axioms RMTFoundations.FreeConvolution.om1_mem
#print axioms RMTFoundations.FreeConvolution.continuousAt_fm
#print axioms RMTFoundations.FreeConvolution.om1_fixed
#print axioms RMTFoundations.FreeConvolution.fixed_unique
#print axioms RMTFoundations.FreeConvolution.orb_differentiableOn
#print axioms RMTFoundations.FreeConvolution.orb_tendstoUniformlyOn
#print axioms RMTFoundations.FreeConvolution.om1_differentiableOn
#print axioms RMTFoundations.FreeConvolution.om1_tail
#print axioms RMTFoundations.FreeConvolution.tendsto_real_iInter
#print axioms RMTFoundations.FreeConvolution.eps
#print axioms RMTFoundations.FreeConvolution.eps_pos
#print axioms RMTFoundations.FreeConvolution.eps_anti
#print axioms RMTFoundations.FreeConvolution.iInter_eps
#print axioms RMTFoundations.FreeConvolution.Dval
#print axioms RMTFoundations.FreeConvolution.Dval_eq
#print axioms RMTFoundations.FreeConvolution.Dval_le
#print axioms RMTFoundations.FreeConvolution.tendsto_Dval_atom
#print axioms RMTFoundations.FreeConvolution.measure_eq_of_stieltjes
#print axioms RMTFoundations.FreeConvolution.rightEndpoint
#print axioms RMTFoundations.FreeConvolution.mem_endpointSet
#print axioms RMTFoundations.FreeConvolution.endpointSet_bdd
#print axioms RMTFoundations.FreeConvolution.rightEndpoint_le
#print axioms RMTFoundations.FreeConvolution.neg_le_rightEndpoint
#print axioms RMTFoundations.FreeConvolution.measure_Ioi_rightEndpoint
#print axioms RMTFoundations.FreeConvolution.measure_Ioi_pos_of_lt
#print axioms RMTFoundations.FreeConvolution.norm_mul_stieltjes_add_one
#print axioms RMTFoundations.FreeConvolution.im_stieltjes_tail
#print axioms RMTFoundations.FreeConvolution.omega1
#print axioms RMTFoundations.FreeConvolution.omega2
#print axioms RMTFoundations.FreeConvolution.IsFreeConv
#print axioms RMTFoundations.FreeConvolution.freeConv
#print axioms RMTFoundations.FreeConvolution.subordination
#print axioms RMTFoundations.FreeConvolution.stieltjes_omega_eq
#print axioms RMTFoundations.FreeConvolution.omega1_differentiableOn
#print axioms RMTFoundations.FreeConvolution.exists_isFreeConv
#print axioms RMTFoundations.FreeConvolution.isFreeConv_prob
#print axioms RMTFoundations.FreeConvolution.isFreeConv_support
#print axioms RMTFoundations.FreeConvolution.freeConv_isFreeConv
#print axioms RMTFoundations.FreeConvolution.isFreeConv_unique
#print axioms RMTFoundations.FreeConvolution.freeConv_spec
#print axioms RMTFoundations.FreeConvolution.freeConv_isProb
#print axioms RMTFoundations.FreeConvolution.csqrt
#print axioms RMTFoundations.FreeConvolution.csqrt_sq
#print axioms RMTFoundations.FreeConvolution.re_sq
#print axioms RMTFoundations.FreeConvolution.re_sq_nonneg
#print axioms RMTFoundations.FreeConvolution.continuous_re_sq
#print axioms RMTFoundations.FreeConvolution.re_sq_le
#print axioms RMTFoundations.FreeConvolution.re_sq_ofReal
#print axioms RMTFoundations.FreeConvolution.rad
#print axioms RMTFoundations.FreeConvolution.rad_mem_slitPlane
#print axioms RMTFoundations.FreeConvolution.gsc
#print axioms RMTFoundations.FreeConvolution.gsc_quad
#print axioms RMTFoundations.FreeConvolution.re_sq_gt
#print axioms RMTFoundations.FreeConvolution.gsc_im
#print axioms RMTFoundations.FreeConvolution.gsc_im_pos
#print axioms RMTFoundations.FreeConvolution.gsc_differentiableOn
#print axioms RMTFoundations.FreeConvolution.gsc_mul
#print axioms RMTFoundations.FreeConvolution.norm_gsc_le
#print axioms RMTFoundations.FreeConvolution.IsSC
#print axioms RMTFoundations.FreeConvolution.exists_isSC
#print axioms RMTFoundations.FreeConvolution.semicircle
#print axioms RMTFoundations.FreeConvolution.semicircle_isSC
#print axioms RMTFoundations.FreeConvolution.semicircle_finite
#print axioms RMTFoundations.FreeConvolution.stieltjes_semicircle
#print axioms RMTFoundations.FreeConvolution.scDens
#print axioms RMTFoundations.FreeConvolution.scDens_nonneg
#print axioms RMTFoundations.FreeConvolution.continuous_scDens
#print axioms RMTFoundations.FreeConvolution.sc_boundary
#print axioms RMTFoundations.FreeConvolution.sc_bound
#print axioms RMTFoundations.FreeConvolution.sc_Ioo
#print axioms RMTFoundations.FreeConvolution.sc_atom
#print axioms RMTFoundations.FreeConvolution.sc_Ioc
#print axioms RMTFoundations.FreeConvolution.semicircle_eq_withDensity
#print axioms RMTFoundations.FreeConvolution.scEdge
#print axioms RMTFoundations.FreeConvolution.scEdge_sq
#print axioms RMTFoundations.FreeConvolution.scEdge_pos
#print axioms RMTFoundations.FreeConvolution.scDens_eq_zero
#print axioms RMTFoundations.FreeConvolution.scDens_pos
#print axioms RMTFoundations.FreeConvolution.sc_Ioo_zero
#print axioms RMTFoundations.FreeConvolution.semicircle_supported
#print axioms RMTFoundations.FreeConvolution.semicircle_prob
#print axioms RMTFoundations.FreeConvolution.rightEndpoint_semicircle
#print axioms RMTFoundations.FreeConvolution.hfun_semicircle
#print axioms RMTFoundations.FreeConvolution.eq_gsc_of_root
#print axioms RMTFoundations.FreeConvolution.SupportedIn.mono
#print axioms RMTFoundations.FreeConvolution.tendsto_mean
#print axioms RMTFoundations.FreeConvolution.semicircle_mean
#print axioms RMTFoundations.FreeConvolution.freeConv_semicircle
#print axioms RMTFoundations.FreeConvolution.scCoef
#print axioms RMTFoundations.FreeConvolution.sc_edge_asymptotic
#print axioms RMTFoundations.FreeConvolution.sc_density_bounds
