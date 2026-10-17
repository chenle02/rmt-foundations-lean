import RMTFoundations.TracyWidom.HMAiryEnvelope
import RMTFoundations.TracyWidom.HMAirySmallness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMAiryKernel
open Set MeasureTheory Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMAiryEnvelope
noncomputable def relativeGreen (s u : ℝ /- [definition] -/)
    : ℝ := (airyAiReal u)^4 * ∫ t in s..u, 2/(airyAiReal t)^2
/-- Reciprocal-square Airy primitive derivative on the positive tail. -/
theorem reciprocal_square_derivative
    (t : ℝ /- [definition] -/)
    (ht : 1 ≤ t /- [standing] -/)
    : HasDerivAt (fun x => 1/(airyAiReal x)^2)
      (-2*deriv airyAiReal t/(airyAiReal t)^3) t := by
  have hn := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).ne'
  convert! (hasDerivAt_const t (1:ℝ)).div ((hasDerivAt_airyAiReal' t).pow 2)
    (pow_ne_zero 2 hn) using 1 <;> simp only [Pi.pow_apply] <;> field_simp <;> ring
/-- The Airy logarithmic derivative controls the reciprocal-square primitive. -/
theorem reciprocal_square_derivative_lower
    (t : ℝ /- [definition] -/)
    (ht : 1 ≤ t /- [standing] -/)
    : 2/(airyAiReal t)^2 ≤ -2*deriv airyAiReal t/(airyAiReal t)^3 := by
  have hp := airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)
  have hn := airyAi_derivative_add_nonpos t ht
  apply (div_le_div_iff₀ (pow_pos hp 2) (pow_pos hp 3)).mpr
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (airyAiReal t)) hn]
/-- The genuine reduction-of-order Green kernel is positive and dominated by Ai squared. -/
theorem relativeGreen_bounds
    (s u : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/)
    (hu : s ≤ u /- [standing] -/)
    : 0 ≤ relativeGreen s u ∧ relativeGreen s u ≤ (airyAiReal u)^2 := by
  have hp (t : ℝ) (ht : t ∈ Icc s u) : 0 < airyAiReal t :=
    airyAiReal_pos_of_nonneg (by linarith [ht.1])
  have hc : ContinuousOn (fun t => 2/(airyAiReal t)^2) (Icc s u) :=
    continuousOn_const.div (continuous_airyAiReal.pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hp t ht).ne')
  have hdc : ContinuousOn (fun t => -2*deriv airyAiReal t/(airyAiReal t)^3) (Icc s u) :=
    (continuousOn_const.mul continuous_deriv_airyAiReal.continuousOn).div
      (continuous_airyAiReal.pow 3).continuousOn (fun t ht => pow_ne_zero 3 (hp t ht).ne')
  have hi : IntervalIntegrable (fun t => 2/(airyAiReal t)^2) volume s u := hc.intervalIntegrable_of_Icc hu
  have hdi : IntervalIntegrable (fun t => -2*deriv airyAiReal t/(airyAiReal t)^3) volume s u := hdc.intervalIntegrable_of_Icc hu
  have hmono := intervalIntegral.integral_mono_on hu hi hdi
    (fun t ht => reciprocal_square_derivative_lower t (hs.trans ht.1))
  have hftc : (∫ t in s..u, -2*deriv airyAiReal t/(airyAiReal t)^3) =
      1/(airyAiReal u)^2-1/(airyAiReal s)^2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hdi
    intro t ht
    rw [uIcc_of_le hu] at ht
    exact reciprocal_square_derivative t (hs.trans ht.1)
  rw [hftc] at hmono
  have hint0 : 0 ≤ ∫ t in s..u, 2/(airyAiReal t)^2 :=
    intervalIntegral.integral_nonneg_of_forall hu (fun t => by positivity)
  have hupper : (∫ t in s..u, 2/(airyAiReal t)^2) ≤ 1/(airyAiReal u)^2 :=
    hmono.trans (sub_le_self _ (by positivity))
  refine ⟨mul_nonneg (by positivity) hint0,?_⟩
  dsimp only [relativeGreen]
  calc
    (airyAiReal u)^4*(∫ t in s..u, 2/(airyAiReal t)^2) ≤
        (airyAiReal u)^4*(1/(airyAiReal u)^2) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (airyAiReal u)^2 := by field_simp

/-- A globally continuous auxiliary reciprocal agrees with the physical one on the tail. -/
noncomputable def tailReciprocal (t : ℝ /- [definition] -/)
    : ℝ := 2/(airyAiReal (max 1 t))^2
theorem tailReciprocal_continuous : Continuous tailReciprocal := by
  have hc : Continuous (fun t : ℝ => airyAiReal (max 1 t)) :=
    continuous_airyAiReal.comp (continuous_const.max continuous_id)
  exact continuous_const.div (hc.pow 2) (fun t => pow_ne_zero 2
    (airyAiReal_pos_of_nonneg (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _))).ne')
/-- The literal Green kernel is continuous on its integration tail. -/
theorem relativeGreen_continuousOn
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/)
    : ContinuousOn (relativeGreen s) (Ici s) := by
  have hc := tailReciprocal_continuous
  have hj : Continuous (fun u => ∫ t in s..u, tailReciprocal t) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable s u)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt
  have hK : Continuous (fun u => (airyAiReal u)^4*(∫ t in s..u, tailReciprocal t)) :=
    (continuous_airyAiReal.pow 4).mul hj
  apply hK.continuousOn.congr
  intro u hu
  dsimp only [relativeGreen]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu] at ht
  simp only [tailReciprocal,max_eq_right (hs.trans ht.1)]
/-- A certified absolute mass bound for the physical reduction-of-order kernel. -/
theorem relativeGreen_tail_mass
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/)
    : IntegrableOn (relativeGreen s) (Ioi s) ∧
      (∫ u in Ioi s, |relativeGreen s u|) ≤ (airyAiReal s)^2/2 := by
  have hm : ∀ᵐ u ∂volume.restrict (Ioi s), |relativeGreen s u| ≤ (airyAiReal u)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have h := relativeGreen_bounds s u hs hu.le
    simpa only [abs_of_nonneg h.1] using h.2
  have hAi : IntegrableOn (fun u => (airyAiReal u)^2) (Ioi s) := integrable_airyAiReal_sq_Ioi s
  have hi : IntegrableOn (relativeGreen s) (Ioi s) :=
    hAi.mono' (((relativeGreen_continuousOn s hs).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) (by simpa only [Real.norm_eq_abs] using hm)
  have htr := RMTFoundations.TWOneBounds.integral_Ioi_translate (fun t => (airyAiReal t)^2) 0 s
  have he := airyAiReal_sq_integral s
  change (∫ u in Ioi 0, (airyAiReal (s+u))^2)=airyEnergy s at he
  have h0 : (∫ u in Ioi s, (airyAiReal u)^2)=airyEnergy s := by
    simpa only [zero_add,add_zero,add_comm] using htr.symm.trans (by simpa only [add_comm] using he)
  exact ⟨hi,(integral_mono_ae hi.abs hAi hm).trans (h0.le.trans (airyEnergy_le_airyAi_sq_half s hs))⟩
/-- The physical kernel is nonzero at the strict tail interval [1,2]. -/
theorem relativeGreen_one_two_positive : 0 < relativeGreen 1 2 := by
  have hc : ContinuousOn (fun t => 2/(airyAiReal t)^2) (Icc (1:ℝ) 2) :=
    continuousOn_const.div (continuous_airyAiReal.pow 2).continuousOn (fun t ht =>
      pow_ne_zero 2 (airyAiReal_pos_of_nonneg (by linarith [ht.1] : 0 ≤ t)).ne')
  have hi : 0 < ∫ t in (1:ℝ)..2, 2/(airyAiReal t)^2 :=
    intervalIntegral.integral_pos (by norm_num) hc (fun t _ => by positivity)
      ⟨1,by norm_num,div_pos (by norm_num)
        (pow_pos (airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ)≤1)) 2)⟩
  exact mul_pos (pow_pos (airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ)≤2)) 4) hi
/-- A common physical tail is constructed with a strict radius-two contraction factor. -/
theorem relativeGreen_contraction_tail :
    ∃ a ≥ (1:ℝ), ∀ s ≥ a, IntegrableOn (relativeGreen s) (Ioi s) ∧
      3*(2:ℝ)^2*(∫ u in Ioi s, |relativeGreen s u|)<1 := by
  obtain ⟨a,ha,hsmall⟩ := RMTFoundations.TracyWidom.HMAirySmallness.eventually_airy_cubic_coefficient_small 2
  refine ⟨a,ha,fun s hs => ?_⟩
  have hm := relativeGreen_tail_mass s (ha.trans hs)
  exact ⟨hm.1,lt_of_le_of_lt (mul_le_mul_of_nonneg_left hm.2 (by norm_num))
    (by simpa only [mul_div_assoc] using (hsmall s hs).2)⟩
/-- Every mass and floor binder is realized on the genuine positive Airy tail. -/
theorem relativeGreen_joint_probe : 0 < airyAiReal 1 ∧ 0 < airyAiReal 2 ∧
    0 < relativeGreen 1 2 ∧ relativeGreen 1 2 ≤ (airyAiReal 2)^2 ∧
    ContinuousOn (relativeGreen 1) (Ici 1) ∧
    IntegrableOn (relativeGreen 1) (Ioi 1) ∧
    (∫ u in Ioi 1, |relativeGreen 1 u|) ≤ (airyAiReal 1)^2/2 :=
  ⟨airyAiReal_pos_of_nonneg (by norm_num),airyAiReal_pos_of_nonneg (by norm_num),
    relativeGreen_one_two_positive,
    (relativeGreen_bounds 1 2 le_rfl (by norm_num)).2,
    relativeGreen_continuousOn 1 le_rfl,relativeGreen_tail_mass 1 le_rfl⟩
end RMTFoundations.TracyWidom.HMAiryKernel
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.reciprocal_square_derivative
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.reciprocal_square_derivative_lower
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_bounds
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.tailReciprocal
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.tailReciprocal_continuous
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_continuousOn
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_tail_mass
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_joint_probe
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_one_two_positive
#print axioms RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen_contraction_tail
