import RMTFoundations.TracyWidom.OrderFourFredholm
import RMTFoundations.TracyWidom.C1
import RMTFoundations.TracyWidom.OrderTwoLogDerivative
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryBounds RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates

/-- The existing physical plus determinant and the foundations definition coincide. -/
theorem hankelDetPlus_eq_TWHankelPlusR
    (s : ℝ /- [definition] -/) :
    hankelDetPlus s = RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR s := by
  exact (RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR_eq_kernelFredholm_re s).symm

/-- Genuine plus derivative, obtained from the Airy determinant proof. -/
theorem hankelDetPlus_hasDerivAt
    (s : ℝ /- [definition] -/) :
    HasDerivAt hankelDetPlus
      (hankelDetPlus s * (resolventU s-resolventQ s)/2) s := by
  have he : hankelDetPlus = RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR :=
    funext hankelDetPlus_eq_TWHankelPlusR
  have h := RMTFoundations.TracyWidom.PlusDerivative.hasDerivAt_TWHankelPlusR_canonical_resolvent s
  rw [← he] at h
  have hm := airy_boundary_resolvent_parity_identity s
  have hp := RMTFoundations.TracyWidom.OrderTwoFactorization.airy_inverse_quadratic_parity_sum s (airyBoundaryVector s)
  have hid : -(airyAiReal s - inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) =
      resolventU s-resolventQ s := by
    dsimp [resolventU,resolventQ]
    linarith [hm,hp]
  have hc : hankelDetPlus s*(resolventU s-resolventQ s)/2 =
      -hankelDetPlus s*(airyAiReal s-inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s)))/2 := by
    rw [←hid]
    ring
  rw [←hc] at h
  exact h

/-- The raw GSE derivative coefficient; its sign is a separate physical obligation. -/
noncomputable def TW4AirySlope (s : ℝ /- [definition] -/) : ℝ :=
  ((TW1R s+hankelDetPlus s)*resolventU s+
    (TW1R s-hankelDetPlus s)*resolventQ s)/4

/-- The sqrt(2) chain-rule factor is retained in the TW96 convention. -/
noncomputable def TW4Slope (s : ℝ /- [definition] -/) : ℝ :=
  Real.sqrt 2 * TW4AirySlope (Real.sqrt 2*s)

theorem TW4AiryR_hasDerivAt
    (s : ℝ /- [definition] -/) : HasDerivAt TW4AiryR (TW4AirySlope s) s := by
  have h := ((RMTFoundations.TracyWidom.ResolventCoordinates.hasDerivAt_TW1R_coordinates s).add
    (hankelDetPlus_hasDerivAt s)).div_const 2
  convert h using 1 <;> first | rfl | (dsimp [TW4AirySlope]; ring)

theorem TW4R_hasDerivAt
    (s : ℝ /- [definition] -/) : HasDerivAt TW4R (TW4Slope s) s := by
  have h := (TW4AiryR_hasDerivAt (Real.sqrt 2*s)).comp s
    ((hasDerivAt_id s).const_mul (Real.sqrt 2))
  convert h using 1 <;> first | rfl | (dsimp [TW4Slope]; ring)

theorem TW4AiryR_differentiable : Differentiable ℝ TW4AiryR :=
  fun s => (TW4AiryR_hasDerivAt s).differentiableAt

theorem TW4R_differentiable : Differentiable ℝ TW4R :=
  fun s => (TW4R_hasDerivAt s).differentiableAt

theorem resolventQ_continuous_for_TW4 : Continuous resolventQ := by
  unfold resolventQ
  have hi : Continuous (fun s => Ring.inverse (1-airyKernelShift s)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (RMTFoundations.TracyWidom.AiryNormDerivative.hasDerivAt_airyKernelResolvent_norm s).continuousAt
  exact Ai_continuous.add (boundaryVector_continuous.inner
    (hankel_continuous.clm_apply (hi.clm_apply boundaryVector_continuous)))

theorem TW4AirySlope_continuous : Continuous TW4AirySlope := by
  unfold TW4AirySlope
  exact (((TW1R_continuous.add continuous_hankelDetPlus).mul
    RMTFoundations.TracyWidom.OrderTwoLogDerivative.resolventU_continuous).add
    ((TW1R_continuous.sub continuous_hankelDetPlus).mul
      resolventQ_continuous_for_TW4)).div_const 4

theorem TW4Slope_continuous : Continuous TW4Slope :=
  continuous_const.mul (TW4AirySlope_continuous.comp (continuous_const.mul continuous_id))

theorem TW4AiryR_contDiff_one : ContDiff ℝ 1 TW4AiryR := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨TW4AiryR_differentiable, ?_⟩
  rw [show deriv TW4AiryR = TW4AirySlope from funext fun s => (TW4AiryR_hasDerivAt s).deriv]
  exact TW4AirySlope_continuous

theorem TW4R_contDiff_one : ContDiff ℝ 1 TW4R := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨TW4R_differentiable, ?_⟩
  rw [show deriv TW4R = TW4Slope from funext fun s => (TW4R_hasDerivAt s).deriv]
  exact TW4Slope_continuous

/-- Exact remaining GSE sign inequality, with actual objects and no derivative premise. -/
theorem TW4AiryR_monotone_iff_resolvent_sign :
    Monotone TW4AiryR ↔ ∀ s : ℝ,
      (hankelDetPlus s-TW1R s)*resolventQ s ≤
      (TW1R s+hankelDetPlus s)*resolventU s := by
  constructor
  · intro hm s
    have hd : 0 ≤ deriv TW4AiryR s := hm.deriv_nonneg
    rw [(TW4AiryR_hasDerivAt s).deriv] at hd
    dsimp [TW4AirySlope] at hd
    linarith
  · intro hs
    apply monotone_of_hasDerivAt_nonneg TW4AiryR_hasDerivAt
    intro s
    dsimp [TW4AirySlope]
    have h := hs s
    linarith

theorem TW4AiryR_log_derivative
    (s : ℝ /- [definition] -/) :
    HasDerivAt (fun t => Real.log (TW4AiryR t))
      (TW4AirySlope s/TW4AiryR s) s :=
  (TW4AiryR_hasDerivAt s).log (TW4AiryR_positive s).ne'

/-- Every regularity binder is jointly realized on the actual nonzero Airy row. -/
theorem TW4_regularity_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < TW4AiryR 0 ∧ 0 < TW4R 0 ∧
    0 < resolventU 0 ∧ Continuous TW4AirySlope ∧ Continuous TW4Slope ∧
    ContDiff ℝ 1 TW4AiryR ∧ ContDiff ℝ 1 TW4R ∧
    (∀ s : ℝ, HasDerivAt TW4AiryR (TW4AirySlope s) s ∧
      HasDerivAt TW4R (TW4Slope s) s) :=
  ⟨airyBoundaryVector_ne_zero 0,TW4AiryR_positive 0,TW4R_positive 0,
    airy_inverse_square_boundary_positive 0,TW4AirySlope_continuous,TW4Slope_continuous,
    TW4AiryR_contDiff_one,TW4R_contDiff_one,
    fun s => ⟨TW4AiryR_hasDerivAt s,TW4R_hasDerivAt s⟩⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hankelDetPlus_eq_TWHankelPlusR
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AirySlope
#print axioms RMTFoundations.TracyWidom.TW4Slope
#print axioms RMTFoundations.TracyWidom.TW4AiryR_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4R_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AiryR_differentiable
#print axioms RMTFoundations.TracyWidom.TW4R_differentiable
#print axioms RMTFoundations.TracyWidom.resolventQ_continuous_for_TW4
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_continuous
#print axioms RMTFoundations.TracyWidom.TW4Slope_continuous
#print axioms RMTFoundations.TracyWidom.TW4AiryR_contDiff_one
#print axioms RMTFoundations.TracyWidom.TW4R_contDiff_one
#print axioms RMTFoundations.TracyWidom.TW4AiryR_monotone_iff_resolvent_sign
#print axioms RMTFoundations.TracyWidom.TW4AiryR_log_derivative
#print axioms RMTFoundations.TracyWidom.TW4_regularity_all_binder_joint_probe
