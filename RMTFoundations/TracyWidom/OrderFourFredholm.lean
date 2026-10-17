import RMTFoundations.TracyWidom.DetFactor
import RMTFoundations.TracyWidom.Probability


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds RMTFoundations.AiryBounds

/-- GSE determinant average at the raw Airy cutoff. TW96 uses s/sqrt(2) here. -/
noncomputable def TW4AiryR (s : ℝ /- [definition] -/) : ℝ :=
  (TW1R s + hankelDetPlus s)/2

/-- GSE with the Tracy-Widom 1996 equation (54) normalization. -/
noncomputable def TW4R (s : ℝ /- [definition] -/) : ℝ := TW4AiryR (Real.sqrt 2 * s)

theorem TW4AiryR_fredholm
    (s : ℝ /- [definition] -/) :
    TW4AiryR s = ((TW1 s + kernelFredholm RMTFoundations.Airy.halfLineMeasure
      (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) 1).re)/2 := by
  simp [TW4AiryR, TW1R, hankelDetPlus]

theorem TW4AiryR_positive
    (s : ℝ /- [definition] -/) : 0 < TW4AiryR s := by
  exact div_pos (add_pos (TW1R_positive_bounds s).1 (hankelDetPlus_positive s)) (by norm_num)

theorem TW4R_positive
    (s : ℝ /- [definition] -/) : 0 < TW4R s := TW4AiryR_positive _

theorem hankelDetPlus_eq_ratio
    (s : ℝ /- [definition] -/) : hankelDetPlus s = TW2R s / TW1R s := by
  apply (eq_div_iff (TW1R_positive_bounds s).1.ne').mpr
  simpa [mul_comm] using (TW2R_factorization s).symm

theorem TW4AiryR_eq_ratio
    (s : ℝ /- [definition] -/) : TW4AiryR s = (TW1R s + TW2R s / TW1R s)/2 := by
  rw [TW4AiryR, hankelDetPlus_eq_ratio]

theorem TW4AiryR_square_gap
    (s : ℝ /- [definition] -/) :
    (TW4AiryR s)^2 - TW2R s = (TW1R s - hankelDetPlus s)^2/4 := by
  rw [TW4AiryR, TW2R_factorization]
  ring

theorem TW2R_le_TW4AiryR_square
    (s : ℝ /- [definition] -/) : TW2R s ≤ (TW4AiryR s)^2 := by
  have := TW4AiryR_square_gap s
  nlinarith [sq_nonneg (TW1R s-hankelDetPlus s)]

theorem continuous_hankelDetPlus : Continuous hankelDetPlus := by
  have h : hankelDetPlus = fun s => TW2R s / TW1R s := funext hankelDetPlus_eq_ratio
  rw [h]
  exact TW2R_continuous.div TW1R_continuous (fun s => (TW1R_positive_bounds s).1.ne')

theorem continuous_TW4AiryR : Continuous TW4AiryR :=
  (TW1R_continuous.add continuous_hankelDetPlus).div_const 2

theorem continuous_TW4R : Continuous TW4R :=
  continuous_TW4AiryR.comp (continuous_const.mul continuous_id)

theorem tendsto_hankelDetPlus_atTop : Tendsto hankelDetPlus atTop (𝓝 1) := by
  have h := TW2R_tendsto_atTop_one.div TW1R_tendsto_atTop_one (by norm_num : (1:ℝ) ≠ 0)
  rw [show hankelDetPlus = (fun s => TW2R s / TW1R s) from funext hankelDetPlus_eq_ratio]
  convert h using 1 <;> first | rfl | norm_num | (funext s; rfl)

theorem tendsto_TW4AiryR_atTop : Tendsto TW4AiryR atTop (𝓝 1) := by
  change Tendsto (fun s => (TW1R s + hankelDetPlus s)/2) atTop (𝓝 1)
  convert (TW1R_tendsto_atTop_one.add tendsto_hankelDetPlus_atTop).div_const 2 using 1 <;> norm_num

theorem TW4R_raw_scaling
    (s : ℝ /- [definition] -/) : TW4R (s / Real.sqrt 2) = TW4AiryR s := by
  dsimp [TW4R]
  congr 1
  field_simp

/-- Actual nonzero Airy data satisfy all binders of the determinant identities. -/
theorem TW4_fredholm_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
    (∀ s : ℝ, 0 < TW1R s ∧ 0 < TW2R s ∧ 0 < hankelDetPlus s ∧
      0 < TW4AiryR s ∧ 0 < TW4R s ∧
      TW2R s = TW1R s * hankelDetPlus s ∧
      (TW4AiryR s)^2-TW2R s = (TW1R s-hankelDetPlus s)^2/4) ∧
    Continuous TW4AiryR ∧ Continuous TW4R ∧
    Tendsto TW4AiryR atTop (𝓝 1) :=
  ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne',
    fun s => ⟨(TW1R_positive_bounds s).1, TW2R_positive s,
      hankelDetPlus_positive s, TW4AiryR_positive s, TW4R_positive s,
      TW2R_factorization s, TW4AiryR_square_gap s⟩,
    continuous_TW4AiryR, continuous_TW4R, tendsto_TW4AiryR_atTop⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4AiryR
#print axioms RMTFoundations.TracyWidom.TW4R
#print axioms RMTFoundations.TracyWidom.TW4AiryR_fredholm
#print axioms RMTFoundations.TracyWidom.TW4AiryR_positive
#print axioms RMTFoundations.TracyWidom.TW4R_positive
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_eq_ratio
#print axioms RMTFoundations.TracyWidom.TW4AiryR_eq_ratio
#print axioms RMTFoundations.TracyWidom.TW4AiryR_square_gap
#print axioms RMTFoundations.TracyWidom.TW2R_le_TW4AiryR_square
#print axioms RMTFoundations.TracyWidom.continuous_hankelDetPlus
#print axioms RMTFoundations.TracyWidom.continuous_TW4AiryR
#print axioms RMTFoundations.TracyWidom.continuous_TW4R
#print axioms RMTFoundations.TracyWidom.tendsto_hankelDetPlus_atTop
#print axioms RMTFoundations.TracyWidom.tendsto_TW4AiryR_atTop
#print axioms RMTFoundations.TracyWidom.TW4R_raw_scaling
#print axioms RMTFoundations.TracyWidom.TW4_fredholm_all_binder_joint_probe
