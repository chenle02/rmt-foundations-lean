import RMTFoundations.TracyWidom.AiryEndpointRowDerivative
import RMTFoundations.TracyWidom.AiryBoundaryDerivative
import RMTFoundations.TracyWidom.AiryCommutator



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryWeightedEndpointRow

open MeasureTheory Filter Set InnerProductSpace
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.AiryEndpointRowDerivative RMTFoundations.TracyWidom.AiryBoundaryDerivative
open RMTFoundations.TracyWidom.AiryCommutator

/-- A genuine L² realization of the weighted endpoint row, with no multiplication-domain premise. -/
noncomputable def weightedEndpointRow
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure :=
      (deriv airyAiReal s) • airyBoundaryVector s - airyAiReal s • airyBoundaryDerivative s

/-- The Airy numerator identity identifies the weighted L² row at every shift. -/
theorem weightedEndpointRow_apply_ae
    (s : ℝ) -- [definition]
    : weightedEndpointRow s =ᵐ[halfLineMeasure]
      fun y => y * airyKernelIntegral (y+s) s := by
  filter_upwards [Lp.coeFn_sub ((deriv airyAiReal s) • airyBoundaryVector s)
      (airyAiReal s • airyBoundaryDerivative s),
    Lp.coeFn_smul (deriv airyAiReal s) (airyBoundaryVector s),
    Lp.coeFn_smul (airyAiReal s) (airyBoundaryDerivative s),
    airyBoundaryVector_apply_ae s, airyBoundaryDerivative_apply_ae s] with y hsub ha hb hx hy
  change (((deriv airyAiReal s) • airyBoundaryVector s -
    airyAiReal s • airyBoundaryDerivative s) y) = y * airyKernelIntegral (y+s) s
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [ha, hb]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx, hy]
  have hk : y * airyKernelIntegral (y+s) s =
      airyAiReal (y+s) * deriv airyAiReal s - deriv airyAiReal (y+s) * airyAiReal s := by
    simpa only [sub_zero, zero_add] using shifted_airy_kernel_multiplication_identity y 0 s
  calc
    deriv airyAiReal s * airyAiReal (s+y) - airyAiReal s * deriv airyAiReal (s+y) =
      airyAiReal (y+s) * deriv airyAiReal s - deriv airyAiReal (y+s) * airyAiReal s := by
        rw [add_comm s y]
        ring
    _ = y * airyKernelIntegral (y+s) s := hk.symm

/-- The same actual weighted row is multiplication of the actual endpoint-row representative. -/
theorem weightedEndpointRow_eq_mul_endpointRow_ae
    (s : ℝ) -- [definition]
    : weightedEndpointRow s =ᵐ[halfLineMeasure] fun y => y * (airyEndpointRow s y) := by
  filter_upwards [weightedEndpointRow_apply_ae s, airyEndpointRow_apply_ae s] with y hw hk
  rw [hw, hk]

/-- The polynomially weighted physical endpoint row is genuinely L². -/
theorem memLp_weightedEndpointKernelRow
    (s : ℝ) -- [definition]
    : MemLp (fun y => y * airyKernelIntegral (y+s) s) 2 halfLineMeasure :=
  (memLp_congr_ae (weightedEndpointRow_apply_ae s)).mp (Lp.memLp (weightedEndpointRow s))

/-- Every actual L² test vector gives an absolutely integrable weighted endpoint product. -/
theorem integrable_weightedEndpointKernelRow_mul
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Integrable (fun y => y * airyKernelIntegral (y+s) s * f y) halfLineMeasure :=
  (memLp_weightedEndpointKernelRow s).integrable_mul (Lp.memLp f)

theorem integrable_abs_weightedEndpointKernelRow_mul
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Integrable (fun y => |y * airyKernelIntegral (y+s) s * f y|) halfLineMeasure := by
  simpa only [Real.norm_eq_abs] using (integrable_weightedEndpointKernelRow_mul s f).norm

/-- Reduction of the actual weighted integral, without a weighted-test-vector domain assumption. -/
theorem weightedEndpointKernelRow_integral
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : (∫ y, y * airyKernelIntegral (y+s) s * f y ∂halfLineMeasure) =
      (deriv airyAiReal s) * inner ℝ (airyBoundaryVector s) f -
        airyAiReal s * inner ℝ (airyBoundaryDerivative s) f := by
  calc
    (∫ y, y * airyKernelIntegral (y+s) s * f y ∂halfLineMeasure) =
      inner ℝ (weightedEndpointRow s) f := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [weightedEndpointRow_apply_ae s] with y hy
        simp only [hy, RCLike.inner_apply, conj_trivial]
        ring
    _ = (deriv airyAiReal s) * inner ℝ (airyBoundaryVector s) f -
        airyAiReal s * inner ℝ (airyBoundaryDerivative s) f := by
      rw [weightedEndpointRow, inner_sub_left, real_inner_smul_left, real_inner_smul_left]

/-- Actual shift-zero nonzero test vector jointly realizes the L² source, weighted
representative, absolute integrability and exact integral reduction. -/
theorem weightedEndpointRow_all_binder_joint_probe :
    ∃ f : Lp ℝ 2 halfLineMeasure,
      f = airyBoundaryVector 0 ∧ f ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧
      0 < airyAiReal 0 ∧
      (weightedEndpointRow 0 =ᵐ[halfLineMeasure] fun y => y * (airyEndpointRow 0 y)) ∧
      MemLp (fun y => y * airyKernelIntegral y 0) 2 halfLineMeasure ∧
      Integrable (fun y => y * airyKernelIntegral y 0 * f y) halfLineMeasure ∧
      Integrable (fun y => |y * airyKernelIntegral y 0 * f y|) halfLineMeasure ∧
      (∫ y, y * airyKernelIntegral y 0 * f y ∂halfLineMeasure) =
        (deriv airyAiReal 0) * inner ℝ (airyBoundaryVector 0) f -
          airyAiReal 0 * inner ℝ (airyBoundaryDerivative 0) f := by
  refine ⟨airyBoundaryVector 0, rfl, airyBoundaryVector_ne_zero 0,
    airyBoundaryDerivative_zero_ne, airyAiReal_zero_pos,
    weightedEndpointRow_eq_mul_endpointRow_ae 0, ?_, ?_, ?_, ?_⟩
  · simpa only [add_zero] using memLp_weightedEndpointKernelRow 0
  · simpa only [add_zero] using integrable_weightedEndpointKernelRow_mul 0 (airyBoundaryVector 0)
  · simpa only [add_zero] using integrable_abs_weightedEndpointKernelRow_mul 0 (airyBoundaryVector 0)
  · simpa only [add_zero] using weightedEndpointKernelRow_integral 0 (airyBoundaryVector 0)

end RMTFoundations.TracyWidom.AiryWeightedEndpointRow

#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.weightedEndpointRow
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.weightedEndpointRow_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.weightedEndpointRow_eq_mul_endpointRow_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.memLp_weightedEndpointKernelRow
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.integrable_weightedEndpointKernelRow_mul
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.integrable_abs_weightedEndpointKernelRow_mul
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.weightedEndpointKernelRow_integral
#print axioms RMTFoundations.TracyWidom.AiryWeightedEndpointRow.weightedEndpointRow_all_binder_joint_probe
