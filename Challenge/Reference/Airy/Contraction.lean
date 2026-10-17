import Challenge.Reference.Airy.FourierBounds
import Challenge.Reference.Airy.Damping
import Mathlib
import Challenge.Reference.Airy.Core
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.AiryBounds

open MeasureTheory FourierTransform RMTFoundations.Airy
open Set Filter Complex
open scoped InnerProductSpace InnerProduct TemperedDistribution
open scoped SchwartzMap ENNReal Topology ContDiff

open FourierTransform LineDeriv
open scoped SchwartzMap TemperedDistribution
open Asymptotics
open scoped Asymptotics
open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open Filter

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open FourierTransform
open scoped SchwartzMap

open RMTFoundations.Airy
open Set

noncomputable def airyDampedShiftMultiplier
    (β s ξ : ℝ /- [definition] -/) : ℂ :=
  RMTFoundations.AiryBounds.fourierPositivePhase ξ s * (𝓕 (RMTFoundations.Airy.laplaceDamped RMTFoundations.Airy.airyAiComplexReal β)) ξ

theorem airyDampedShiftMultiplier_integrable
    (β s : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) : Integrable (airyDampedShiftMultiplier β s) := by
  apply (RMTFoundations.Airy.airyDamped_fourier_integrable β hβ).norm.mono' ?_ ?_
  · exact (by unfold RMTFoundations.AiryBounds.fourierPositivePhase; fun_prop : Continuous (fun ξ => RMTFoundations.AiryBounds.fourierPositivePhase ξ s)).aestronglyMeasurable.mul
      (RMTFoundations.Airy.airyDamped_fourier_integrable β hβ).aestronglyMeasurable
  · exact ae_of_all _ (fun ξ => by simp only [airyDampedShiftMultiplier, norm_mul,
      RMTFoundations.AiryBounds.fourierPositivePhase_norm, one_mul]; rfl)

theorem airyDampedShiftMultiplier_bound
    (β s ξ : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    ‖airyDampedShiftMultiplier β s ξ‖ ≤ Real.exp (β^3 / 3) := by
  simp only [airyDampedShiftMultiplier, norm_mul, RMTFoundations.AiryBounds.fourierPositivePhase_norm, one_mul]
  exact RMTFoundations.Airy.airyDamped_fourier_norm_le β ξ hβ

theorem airyDampedShiftMultiplier_inverse
    (β s x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    (𝓕⁻ (airyDampedShiftMultiplier β s)) x =
      (Real.exp (β * (x + s)) : ℂ) * (airyAiReal (x + s) : ℂ) := by
  unfold airyDampedShiftMultiplier
  rw [RMTFoundations.AiryBounds.inverse_fourier_phase_shift,
    RMTFoundations.Airy.airyDamped_inverse_fourier β (x + s) hβ]
  simp only [RMTFoundations.Airy.laplaceDamped, RMTFoundations.Airy.airyAiComplexReal, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

theorem airyDampedShift_response
    (β s x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    (∫ y : ℝ, RMTFoundations.AiryBounds.dampedHalfLineFunction β f y *
      (𝓕⁻ (airyDampedShiftMultiplier β s)) (x + y)) =
      (Real.exp (β * (x + s)) : ℂ) *
        ((∫ y : ℝ, airyAiReal (x + y + s) * f y ∂halfLineMeasure : ℝ) : ℂ) := by
  simp_rw [airyDampedShiftMultiplier_inverse β s _ hβ]
  have hi : (fun y => RMTFoundations.AiryBounds.dampedHalfLineFunction β f y *
      ((Real.exp (β * (x + y + s)) : ℂ) * (airyAiReal (x + y + s) : ℂ))) =
      (Ioi 0).indicator (fun y => (Real.exp (-β * y) : ℂ) * (f y : ℂ) *
        ((Real.exp (β * (x + y + s)) : ℂ) * (airyAiReal (x + y + s) : ℂ))) := by
    funext y
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · simp [RMTFoundations.AiryBounds.dampedHalfLineFunction, hy]
    · simp [RMTFoundations.AiryBounds.dampedHalfLineFunction, hy]
  rw [hi, integral_indicator measurableSet_Ioi]
  change (∫ y : ℝ in Ioi 0, (Real.exp (-β * y) : ℂ) * (f y : ℂ) *
    ((Real.exp (β * (x + y + s)) : ℂ) * (airyAiReal (x + y + s) : ℂ))) = _
  rw [← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    have he : Real.exp (-β * y) * Real.exp (β * (x + y + s)) =
        Real.exp (β * (x + s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [Complex.ofReal_mul]
    calc
      (Real.exp (-β * y) : ℂ) * (f y : ℂ) *
          ((Real.exp (β * (x + y + s)) : ℂ) * (airyAiReal (x + y + s) : ℂ)) =
        ((Real.exp (-β * y) : ℂ) * (Real.exp (β * (x + y + s)) : ℂ)) *
          ((airyAiReal (x + y + s) : ℂ) * (f y : ℂ)) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, he])

/-- A quantitative bound at every positive damping parameter, with every real shift. -/
theorem airyHankelShift_norm_apply_le_damping
    (s β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ‖airyHankelShift s f‖ ≤ Real.exp (β^3 / 3 - β * s) * ‖f‖ := by
  let F := RMTFoundations.AiryBounds.dampedHalfLineFunction β f
  let M := airyDampedShiftMultiplier β s
  let H : ℝ → ℂ := fun x => ∫ y : ℝ, F y * (𝓕⁻ M) (x + y)
  have hF2 := RMTFoundations.AiryBounds.dampedHalfLine_memLp β hβ.le f
  obtain ⟨hH, hHnorm⟩ := RMTFoundations.AiryBounds.inverse_fourier_kernel_L2_bound M F
    (airyDampedShiftMultiplier_integrable β s hβ) (RMTFoundations.AiryBounds.dampedHalfLine_integrable β hβ f)
    hF2 (Real.exp (β^3 / 3))
    (ae_of_all _ (fun ξ => airyDampedShiftMultiplier_bound β s ξ hβ))
  have hres := hH.restrict (Ioi 0)
  have hpoint : ‖airyHankelShift s f‖ ≤
      Real.exp (-β * s) * ‖hres.toLp H‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [airyHankelShift_apply_ae s f, hres.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioi] with x hx hy hpos
    rw [hx, hy]
    have he := airyDampedShift_response β s x hβ f
    change H x = _ at he
    change ‖(∫ t : ℝ, airyAiReal (x + t + s) * f t ∂halfLineMeasure : ℝ)‖ ≤
      Real.exp (-β * s) * ‖H x‖
    rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_real]
    rw [← mul_assoc, ← Real.exp_add]
    have harg : -β * s + β * (x + s) = β * x := by ring
    rw [harg]
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp_iff.mpr (mul_nonneg hβ.le hpos.le))
  have hrestrict : ‖hres.toLp H‖ ≤ ‖hH.toLp H‖ := RMTFoundations.AiryBounds.restrict_L2_norm_le H hH
  have hF : ‖hF2.toLp F‖ ≤ ‖f‖ := RMTFoundations.AiryBounds.dampedHalfLine_norm_le β hβ.le f
  calc
    ‖airyHankelShift s f‖ ≤ Real.exp (-β * s) * ‖hres.toLp H‖ := hpoint
    _ ≤ Real.exp (-β * s) * ‖hH.toLp H‖ :=
      mul_le_mul_of_nonneg_left hrestrict (Real.exp_pos _).le
    _ ≤ Real.exp (-β * s) * (Real.exp (β^3 / 3) * ‖hF2.toLp F‖) :=
      mul_le_mul_of_nonneg_left hHnorm (Real.exp_pos _).le
    _ ≤ Real.exp (-β * s) * (Real.exp (β^3 / 3) * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

theorem airyHankelShift_norm_apply_le
    (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ‖airyHankelShift s f‖ ≤ ‖f‖ := by
  have hb := RMTFoundations.Airy.laplaceDampingSequence_tendsto
  have hc := (Real.continuous_exp.continuousAt.tendsto.comp
    (((hb.pow 3).div_const 3).sub (hb.mul_const s))).mul_const ‖f‖
  norm_num at hc
  apply ge_of_tendsto hc
  exact Eventually.of_forall fun n => airyHankelShift_norm_apply_le_damping s
    (RMTFoundations.Airy.laplaceDampingSequence n) (RMTFoundations.Airy.laplaceDampingSequence_pos n) f

theorem norm_airyHankelShift_le_one
    (s : ℝ /- [definition] -/) : ‖airyHankelShift s‖ ≤ 1 := by
  apply (airyHankelShift s).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa only [one_mul] using airyHankelShift_norm_apply_le s f

theorem norm_airyKernelShift_le_one
    (s : ℝ /- [definition] -/) : ‖airyKernelShift s‖ ≤ 1 := by
  calc ‖airyKernelShift s‖ ≤ ‖airyHankelShift s‖ * ‖airyHankelShift s‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_airyHankelShift_le_one s)
      (norm_airyHankelShift_le_one s) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem airy_contraction_joint_probe
    (s : ℝ /- [definition] -/) :
    airyAiReal 0 > 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      ‖airyHankelShift s‖ ≤ 1 ∧ ‖airyKernelShift s‖ ≤ 1 :=
  ⟨airyAiReal_zero_pos, shiftedUnitVector_norm 0,
    norm_airyHankelShift_le_one s, norm_airyKernelShift_le_one s⟩

end RMTFoundations.AiryBounds

#print axioms RMTFoundations.AiryBounds.airyDampedShiftMultiplier
#print axioms RMTFoundations.AiryBounds.airyDampedShiftMultiplier_integrable
#print axioms RMTFoundations.AiryBounds.airyDampedShiftMultiplier_bound
#print axioms RMTFoundations.AiryBounds.airyDampedShiftMultiplier_inverse
#print axioms RMTFoundations.AiryBounds.airyDampedShift_response
#print axioms RMTFoundations.AiryBounds.airyHankelShift_norm_apply_le_damping
#print axioms RMTFoundations.AiryBounds.airyHankelShift_norm_apply_le
#print axioms RMTFoundations.AiryBounds.norm_airyHankelShift_le_one
#print axioms RMTFoundations.AiryBounds.norm_airyKernelShift_le_one
#print axioms RMTFoundations.AiryBounds.airy_contraction_joint_probe
