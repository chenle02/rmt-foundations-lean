import RMTFoundations.TracyWidom.OrderOneBounds
import RMTFoundations.Airy.HankelFactorization



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryWeightedKernel

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds

/-- One spatial polynomial factor is absorbed by a slower exponential. -/
theorem spatial_exp_absorption
    (x : ℝ) -- [definition]
    (hx : 0 ≤ x) -- [standing]
    : x * Real.exp (-x) ≤ 2 * Real.exp (-(1/2:ℝ)*x) := by
  have h := Real.add_one_le_exp (x/2)
  have hx' : x ≤ 2*Real.exp (x/2) := by linarith
  calc x*Real.exp (-x) ≤ (2*Real.exp (x/2))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hx' (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1; ring

/-- The genuine square Airy kernel has an exponential envelope at every real shift. -/
theorem shiftedKernel_exp_bound
    (s : ℝ) -- [definition]
    : ∃ D : ℝ, 0 < D ∧ ∀ x y : ℝ,
      |airyKernelIntegral (x+s) (y+s)| ≤ D*Real.exp (-x)*Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := airyKernelIntegral_bound
  refine ⟨C*Real.exp (-s)^2, by positivity, ?_⟩
  intro x y
  simpa only [neg_add, Real.exp_add, pow_two, mul_assoc, mul_comm, mul_left_comm] using hb (x+s) (y+s)

/-- Every actual square-kernel row is L², at every real spatial coordinate. -/
theorem memLp_AiryKernelRow
    (s x : ℝ) -- [definition]
    : MemLp (fun y => airyKernelIntegral (x+s) (y+s)) 2 halfLineMeasure := by
  have hae : airyHankelShift s (sliceLp halfLineMeasure (airyHankelShiftKernel s) x)
      =ᵐ[halfLineMeasure] fun y => airyKernelIntegral (x+s) (y+s) := by
    filter_upwards [airyHankelShift_slice_apply_ae s x] with y hy
    exact hy.trans (airyKernelIntegral_symm (y+s) (x+s))
  exact MemLp.ae_eq hae (Lp.memLp _)

/-- Actual square-kernel response integrals exist for every L² input and coordinate. -/
theorem integrable_AiryKernelResponse
    (s x : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Integrable (fun y => airyKernelIntegral (x+s) (y+s)*f y) halfLineMeasure :=
  (memLp_AiryKernelRow s x).integrable_mul (Lp.memLp f)

/-- Every actual kernel response has an exponential scalar majorant. -/
theorem airyKernelResponse_exp_bound
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
      |∫ y, airyKernelIntegral (x+s) (y+s)*f y ∂halfLineMeasure| ≤ D*Real.exp (-x) := by
  obtain ⟨C,hC,hb⟩ := shiftedKernel_exp_bound s
  let J : ℝ := ∫ y, Real.exp (-y)*|f y| ∂halfLineMeasure
  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
  refine ⟨C*J, mul_nonneg hC.le hJ, ?_⟩
  intro x
  have hi : Integrable (fun y => (C*Real.exp (-x))*(Real.exp (-y)*|f y|)) halfLineMeasure :=
    (integrable_expWeight_mul_abs f).const_mul _
  have hn := norm_integral_le_of_norm_le (f := fun y => airyKernelIntegral (x+s) (y+s)*f y) hi
    (ae_of_all _ (fun y => by
      simp only [Real.norm_eq_abs, abs_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb x y) (abs_nonneg (f y))))
  rw [integral_const_mul] at hn
  simpa only [Real.norm_eq_abs, J, mul_assoc, mul_comm, mul_left_comm] using hn

/-- Multiplication by the spatial coordinate preserves the L² class of every Airy-kernel response. -/
theorem memLp_weightedKernelResponse
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : MemLp (fun x : ℝ => x*(airyKernelShift s f) x) 2 halfLineMeasure := by
  obtain ⟨D,hD,hb⟩ := airyKernelResponse_exp_bound s f
  have hm : AEStronglyMeasurable (fun x : ℝ => x*(airyKernelShift s f) x) halfLineMeasure :=
    continuous_id.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  apply ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).const_mul (2*D)).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi, airyKernelShift_apply_ae s f] with x hx hk
  have hx0 : 0 ≤ x := (show 0 < x from hx).le
  change |x*(airyKernelShift s f) x| ≤ (2*D)*Real.exp (-(1/2:ℝ)*x)
  rw [abs_mul,abs_of_nonneg hx0,hk]
  calc x*|∫ y, airyKernelIntegral (x+s) (y+s)*f y ∂halfLineMeasure| ≤ x*(D*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (hb x) hx0
    _ = D*(x*Real.exp (-x)) := by ring
    _ ≤ D*(2*Real.exp (-(1/2:ℝ)*x)) :=
      mul_le_mul_of_nonneg_left (spatial_exp_absorption x hx0) hD
    _ = _ := by ring

/-- The actual weighted kernel image; no unbounded multiplication operator is introduced. -/
noncomputable def weightedKernelResponse
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Lp ℝ 2 halfLineMeasure := (memLp_weightedKernelResponse s f).toLp _

theorem weightedKernelResponse_apply_ae
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : weightedKernelResponse s f =ᵐ[halfLineMeasure] fun x => x*(airyKernelShift s f) x :=
  (memLp_weightedKernelResponse s f).coeFn_toLp

/-- A genuinely nonzero physical input simultaneously realizes all weighted-image fields. -/
theorem weighted_kernel_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧
      (∀ f : Lp ℝ 2 halfLineMeasure, MemLp (fun x : ℝ => x*(airyKernelShift 0 f) x) 2 halfLineMeasure) ∧
      (weightedKernelResponse 0 (airyBoundaryVector 0) =ᵐ[halfLineMeasure]
        fun x => x*(airyKernelShift 0 (airyBoundaryVector 0)) x) ∧
      (∃ D : ℝ, 0 < D ∧ ∀ x y : ℝ,
        |airyKernelIntegral x y| ≤ D*Real.exp (-x)*Real.exp (-y)) ∧
      (2:ℝ)*Real.exp (-2) ≤ 2*Real.exp (-1) := by
  refine ⟨airyBoundaryVector_ne_zero 0, memLp_weightedKernelResponse 0,
    weightedKernelResponse_apply_ae 0 (airyBoundaryVector 0), ?_, ?_⟩
  · simpa only [add_zero] using shiftedKernel_exp_bound 0
  · simpa using spatial_exp_absorption 2 (by norm_num)

end RMTFoundations.TracyWidom.AiryWeightedKernel

#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.spatial_exp_absorption
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.shiftedKernel_exp_bound
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.memLp_AiryKernelRow
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.integrable_AiryKernelResponse
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.airyKernelResponse_exp_bound
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.memLp_weightedKernelResponse
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.weightedKernelResponse
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.weightedKernelResponse_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedKernel.weighted_kernel_joint_probe
