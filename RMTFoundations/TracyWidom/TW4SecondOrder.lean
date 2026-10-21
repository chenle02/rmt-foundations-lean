import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.PhysicalPainleveII
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open scoped ContDiff
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom.PhysicalPainleveII RMTFoundations.TracyWidom.OrderTwoLogDerivative

/-- The antisymmetric branch of the actual determinant pair; no sign is assumed. -/
noncomputable def TW4AirySkew
    (s : ℝ /- [definition] -/)
    : ℝ := (hankelDetPlus s-TW1R s)/2

/-- The two determinant branches obey a genuine coupled first-order system. -/
theorem TW4AirySlope_eq_pair
    (s : ℝ /- [definition] -/)
    : TW4AirySlope s =
      (resolventU s*TW4AiryR s-resolventQ s*TW4AirySkew s)/2 := by
  dsimp [TW4AirySlope,TW4AiryR,TW4AirySkew]
  ring

theorem TW4AirySkew_hasDerivAt
    (s : ℝ /- [definition] -/)
    : HasDerivAt TW4AirySkew
      ((resolventU s*TW4AirySkew s-resolventQ s*TW4AiryR s)/2) s := by
  have h := ((hankelDetPlus_hasDerivAt s).sub
    (hasDerivAt_TW1R_coordinates s)).div_const 2
  convert! h using 1
  dsimp [TW4AirySkew,TW4AiryR]
  ring

/-- The physical GSE slope derivative. The p term retains its exact sign. -/
theorem TW4AirySlope_hasDerivAt
    (s : ℝ /- [definition] -/)
    : HasDerivAt TW4AirySlope
      ((((resolventU s)^2-(resolventQ s)^2)*TW4AiryR s-
        2*resolventP s*TW4AirySkew s)/4) s := by
  have he : (fun t =>
      (resolventU t*TW4AiryR t-resolventQ t*TW4AirySkew t)/2) = TW4AirySlope :=
    funext fun t => (TW4AirySlope_eq_pair t).symm
  have h := (((hasDerivAt_resolventU_negative_q_sq s).mul (TW4AiryR_hasDerivAt s)).sub
    ((hasDerivAt_resolventQ s).mul (TW4AirySkew_hasDerivAt s))).div_const 2
  change HasDerivAt (fun t =>
    (resolventU t*TW4AiryR t-resolventQ t*TW4AirySkew t)/2) _ s at h
  rw [he,TW4AirySlope_eq_pair] at h
  convert! h using 1
  ring

/-- A second-order ODE for the genuine GSE Fredholm average, rather than a new model. -/
theorem TW4AiryR_second_order_equation
    (s : ℝ /- [definition] -/)
    : HasDerivAt (deriv TW4AiryR)
      ((((resolventU s)^2-(resolventQ s)^2)*TW4AiryR s-
        2*resolventP s*TW4AirySkew s)/4) s := by
  rw [show deriv TW4AiryR=TW4AirySlope from
    funext fun t => (TW4AiryR_hasDerivAt t).deriv]
  exact TW4AirySlope_hasDerivAt s

/-- Elimination of the skew branch gives a scalar ODE without dividing by q.
The formula remains valid at an endpoint-coordinate zero. -/
theorem TW4AiryR_scalar_second_order_identity
    (s : ℝ /- [definition] -/)
    : 4*resolventQ s*deriv TW4AirySlope s-4*resolventP s*TW4AirySlope s =
      -(resolventQ s*((resolventU s)^2+(resolventQ s)^2)+
        2*resolventU s*deriv resolventQ s)*TW4AiryR s := by
  rw [(TW4AirySlope_hasDerivAt s).deriv,(hasDerivAt_resolventQ s).deriv,
    TW4AirySlope_eq_pair]
  ring

theorem TW4AirySkew_continuous : Continuous TW4AirySkew :=
  (continuous_hankelDetPlus.sub TW1R_continuous).div_const 2

theorem TW4AirySlope_contDiff_one : ContDiff ℝ 1 TW4AirySlope := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (TW4AirySlope_hasDerivAt s).differentiableAt,?_⟩
  rw [show deriv TW4AirySlope=fun s =>
      (((resolventU s)^2-(resolventQ s)^2)*TW4AiryR s-
        2*resolventP s*TW4AirySkew s)/4 from
    funext fun s => (TW4AirySlope_hasDerivAt s).deriv]
  have hp : Continuous resolventP :=
    (show Differentiable ℝ resolventP from
      fun s => (hasDerivAt_resolventP s).differentiableAt).continuous
  exact (((resolventU_continuous.pow 2).sub
    (resolventQ_continuous_for_TW4.pow 2)).mul continuous_TW4AiryR).sub
    ((continuous_const.mul hp).mul TW4AirySkew_continuous) |>.div_const 4

theorem TW4AiryR_contDiff_two : ContDiff ℝ 2 TW4AiryR := by
  rw [show (2:ℕ∞ω)=1+1 from rfl,contDiff_succ_iff_deriv]
  refine ⟨TW4AiryR_differentiable,?_,?_⟩
  · simp
  · rw [show deriv TW4AiryR=TW4AirySlope from
      funext fun s => (TW4AiryR_hasDerivAt s).deriv]
    exact TW4AirySlope_contDiff_one

theorem TW4R_contDiff_two : ContDiff ℝ 2 TW4R :=
  TW4AiryR_contDiff_two.comp (contDiff_const.mul contDiff_id)

/-- The second-order equation and both regularity statements coexist at every
physical shift, with nonzero source witnesses in each shift-sign region. -/
theorem TW4_second_order_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryVector 2 ≠ 0 ∧
      (∀ s : ℝ, HasDerivAt TW4AirySkew
        ((resolventU s*TW4AirySkew s-resolventQ s*TW4AiryR s)/2) s) ∧
      (∀ s : ℝ, HasDerivAt (deriv TW4AiryR)
        ((((resolventU s)^2-(resolventQ s)^2)*TW4AiryR s-
          2*resolventP s*TW4AirySkew s)/4) s) ∧
      (∀ s : ℝ, 4*resolventQ s*deriv TW4AirySlope s-4*resolventP s*TW4AirySlope s =
        -(resolventQ s*((resolventU s)^2+(resolventQ s)^2)+
          2*resolventU s*deriv resolventQ s)*TW4AiryR s) ∧
      ContDiff ℝ 1 TW4AirySlope ∧ ContDiff ℝ 2 TW4AiryR ∧ ContDiff ℝ 2 TW4R :=
  ⟨airyBoundaryVector_ne_zero (-3),airyBoundaryVector_ne_zero 0,
    airyBoundaryVector_ne_zero 2,TW4AirySkew_hasDerivAt,TW4AiryR_second_order_equation,
    TW4AiryR_scalar_second_order_identity,TW4AirySlope_contDiff_one,
    TW4AiryR_contDiff_two,TW4R_contDiff_two⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4AirySkew
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_eq_pair
#print axioms RMTFoundations.TracyWidom.TW4AirySkew_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW4AiryR_second_order_equation
#print axioms RMTFoundations.TracyWidom.TW4AiryR_scalar_second_order_identity
#print axioms RMTFoundations.TracyWidom.TW4AirySkew_continuous
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_contDiff_one
#print axioms RMTFoundations.TracyWidom.TW4AiryR_contDiff_two
#print axioms RMTFoundations.TracyWidom.TW4R_contDiff_two
#print axioms RMTFoundations.TracyWidom.TW4_second_order_all_binder_joint_probe
