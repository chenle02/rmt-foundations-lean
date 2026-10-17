import RMTFoundations.TracyWidom.AiryWeightedKernel
import RMTFoundations.TracyWidom.AiryWeightedBoundary
import RMTFoundations.TracyWidom.ResponseDerivative
import RMTFoundations.TracyWidom.AiryCommutator



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryWeightedResponse

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.AiryBoundaryDerivative
open RMTFoundations.TracyWidom.AiryWeightedBoundary RMTFoundations.TracyWidom.AiryWeightedKernel
open RMTFoundations.TracyWidom.ResponseDerivative RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.AiryNormDerivative RMTFoundations.TracyWidom.AiryCommutator

/-- The physical spatially weighted Airy source Ma. -/
noncomputable def weightedAirySource
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := airyBoundaryODEVector s - s • airyBoundaryVector s

theorem weightedAirySource_apply_ae
    (s : ℝ) -- [definition]
    : weightedAirySource s =ᵐ[halfLineMeasure] fun x => x*airyAiReal (s+x) := by
  filter_upwards [Lp.coeFn_sub (airyBoundaryODEVector s) (s • airyBoundaryVector s),
    Lp.coeFn_smul s (airyBoundaryVector s), airyBoundaryODEVector_apply_ae s,
    airyBoundaryVector_apply_ae s] with x hsub hsmul hc ha
  change (airyBoundaryODEVector s - s • airyBoundaryVector s) x = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hc,ha]
  ring

/-- The genuine spatially weighted Airy source is L², without a domain premise. -/
theorem memLp_weightedAirySource
    (s : ℝ) -- [definition]
    : MemLp (fun x : ℝ => x*airyAiReal (s+x)) 2 halfLineMeasure :=
  MemLp.ae_eq (weightedAirySource_apply_ae s) (Lp.memLp _)

/-- The actual inverse equation in its response form. -/
theorem responseVector_eq_source_add_kernel
    (s : ℝ) -- [definition]
    : responseVector s = airyBoundaryVector s + airyKernelShift s (responseVector s) := by
  have h := contraction_ringInverse_right (airyKernelShift s)
    (norm_airyKernelShift_lt_one s) (airyBoundaryVector s)
  change responseVector s - airyKernelShift s (responseVector s) = airyBoundaryVector s at h
  calc responseVector s = (responseVector s - airyKernelShift s (responseVector s)) +
      airyKernelShift s (responseVector s) := by abel
    _ = _ := by rw [h]

theorem responseVector_eq_source_add_kernel_ae
    (s : ℝ) -- [definition]
    : responseVector s =ᵐ[halfLineMeasure]
      fun x => (airyBoundaryVector s) x + (airyKernelShift s (responseVector s)) x := by
  have h := Lp.coeFn_add (airyBoundaryVector s) (airyKernelShift s (responseVector s))
  rw [← responseVector_eq_source_add_kernel s] at h
  exact h

/-- The physical MQ is constructed using the true inverse equation and weighted kernel image. -/
noncomputable def weightedResponseVector
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := weightedAirySource s + weightedKernelResponse s (responseVector s)

theorem weightedResponseVector_apply_ae
    (s : ℝ) -- [definition]
    : weightedResponseVector s =ᵐ[halfLineMeasure] fun x => x*(responseVector s) x := by
  filter_upwards [Lp.coeFn_add (weightedAirySource s) (weightedKernelResponse s (responseVector s)),
    weightedAirySource_apply_ae s, weightedKernelResponse_apply_ae s (responseVector s),
    responseVector_eq_source_add_kernel_ae s, airyBoundaryVector_apply_ae s] with x hadd hMa hMK hQ ha
  change (weightedAirySource s + weightedKernelResponse s (responseVector s)) x = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hMa,hMK,hQ,ha]
  ring

/-- The genuine physical Q belongs to the multiplication domain, without a domain premise. -/
theorem memLp_weightedResponseVector
    (s : ℝ) -- [definition]
    : MemLp (fun x : ℝ => x*(responseVector s) x) 2 halfLineMeasure :=
  MemLp.ae_eq (weightedResponseVector_apply_ae s) (Lp.memLp _)

/-- The derivative-source scalar pairing is the actual canonical v coordinate. -/
theorem derivative_source_response_pairing
    (s : ℝ) -- [definition]
    : inner ℝ (airyBoundaryDerivative s) (responseVector s) = resolventV s := by
  rw [responseVector, ← airyKernelResolvent_symmetric]
  rw [real_inner_comm]
  rfl

/-- Numerator integration is justified by the genuine weighted-response domain. -/
theorem weighted_response_commutator_scalar
    (s x : ℝ) -- [definition]
    : x*(∫ y, airyKernelIntegral (x+s) (y+s)*(responseVector s) y ∂halfLineMeasure) -
        (∫ y, airyKernelIntegral (x+s) (y+s)*(weightedResponseVector s) y ∂halfLineMeasure) =
      airyAiReal (s+x)*resolventV s - deriv airyAiReal (s+x)*resolventU s := by
  have hKQ := integrable_AiryKernelResponse s x (responseVector s)
  have hKM := integrable_AiryKernelResponse s x (weightedResponseVector s)
  have hA : Integrable (fun y => airyAiReal (s+y)*(responseVector s) y) halfLineMeasure := by
    have hh := (Lp.memLp (airyBoundaryVector s)).integrable_mul (Lp.memLp (responseVector s))
    apply hh.congr
    filter_upwards [airyBoundaryVector_apply_ae s] with y hy
    simp only [Pi.mul_apply]
    rw [hy]
  have hB : Integrable (fun y => deriv airyAiReal (s+y)*(responseVector s) y) halfLineMeasure :=
    (memLp_airyDerivative s).integrable_mul (Lp.memLp (responseVector s))
  have hpairA : (∫ y, airyAiReal (s+y)*(responseVector s) y ∂halfLineMeasure) = resolventU s := by
    rw [← airyBoundaryVector_pairing (responseVector s) s]
    change inner ℝ (responseVector s) (airyBoundaryVector s) =
      inner ℝ (airyBoundaryVector s) (responseVector s)
    exact real_inner_comm (airyBoundaryVector s) (responseVector s)
  have hpairB : (∫ y, deriv airyAiReal (s+y)*(responseVector s) y ∂halfLineMeasure) = resolventV s := by
    rw [← airyBoundaryDerivative_pairing (responseVector s) s]
    exact (real_inner_comm (airyBoundaryDerivative s) (responseVector s)).trans
      (derivative_source_response_pairing s)
  calc
    _ = ∫ y, x*(airyKernelIntegral (x+s) (y+s)*(responseVector s) y) -
        airyKernelIntegral (x+s) (y+s)*(weightedResponseVector s) y ∂halfLineMeasure := by
      rw [integral_sub (hKQ.const_mul x) hKM, integral_const_mul]
    _ = ∫ y, airyAiReal (s+x)*(deriv airyAiReal (s+y)*(responseVector s) y) -
        deriv airyAiReal (s+x)*(airyAiReal (s+y)*(responseVector s) y) ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [weightedResponseVector_apply_ae s] with y hy
      rw [hy]
      have hn : (x-y)*airyKernelIntegral (x+s) (y+s) =
          airyAiReal (s+x)*deriv airyAiReal (s+y) - deriv airyAiReal (s+x)*airyAiReal (s+y) := by
        simpa only [add_comm] using shifted_airy_kernel_multiplication_identity x y s
      calc _ = ((x-y)*airyKernelIntegral (x+s) (y+s))*(responseVector s) y := by ring
        _ = _ := by rw [hn]; ring
    _ = airyAiReal (s+x)*(∫ y, deriv airyAiReal (s+y)*(responseVector s) y ∂halfLineMeasure) -
        deriv airyAiReal (s+x)*(∫ y, airyAiReal (s+y)*(responseVector s) y ∂halfLineMeasure) := by
      rw [integral_sub (hB.const_mul _) (hA.const_mul _), integral_const_mul, integral_const_mul]
    _ = _ := by rw [hpairB,hpairA]

/-- Endpoint numerator integration supplies the precise weighted pairing needed for p′. -/
theorem weighted_response_endpoint_integral
    (s : ℝ) -- [definition]
    : (∫ y, airyKernelIntegral s (y+s)*(weightedResponseVector s) y ∂halfLineMeasure) =
      resolventU s*deriv airyAiReal s-resolventV s*airyAiReal s := by
  have h := weighted_response_commutator_scalar s 0
  simp only [zero_add,add_zero,zero_mul] at h
  linear_combination -h

/-- The multiplication commutator holds on the actual physical inverse response. -/
theorem weighted_response_commutator
    (s : ℝ) -- [definition]
    : weightedKernelResponse s (responseVector s) - airyKernelShift s (weightedResponseVector s) =
      resolventV s • airyBoundaryVector s - resolventU s • airyBoundaryDerivative s := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (weightedKernelResponse s (responseVector s))
      (airyKernelShift s (weightedResponseVector s)),
    Lp.coeFn_sub (resolventV s • airyBoundaryVector s) (resolventU s • airyBoundaryDerivative s),
    weightedKernelResponse_apply_ae s (responseVector s),
    airyKernelShift_apply_ae s (responseVector s), airyKernelShift_apply_ae s (weightedResponseVector s),
    Lp.coeFn_smul (resolventV s) (airyBoundaryVector s),
    Lp.coeFn_smul (resolventU s) (airyBoundaryDerivative s),
    airyBoundaryVector_apply_ae s, airyBoundaryDerivative_apply_ae s] with x hl hr hw hKQ hKM hva hub ha hb
  rw [hl,hr]
  simp only [Pi.sub_apply]
  rw [hw,hKQ,hKM,hva,hub]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ha,hb]
  simpa only [mul_comm] using weighted_response_commutator_scalar s x

/-- The actual weighted response solves the operator equation with the integrable-kernel defect. -/
theorem weighted_response_inverse_equation
    (s : ℝ) -- [definition]
    : weightedResponseVector s - airyKernelShift s (weightedResponseVector s) =
      weightedAirySource s + resolventV s • airyBoundaryVector s -
        resolventU s • airyBoundaryDerivative s := by
  calc
    _ = weightedAirySource s + (weightedKernelResponse s (responseVector s) -
        airyKernelShift s (weightedResponseVector s)) := by
      change (weightedAirySource s + weightedKernelResponse s (responseVector s)) -
        airyKernelShift s (weightedResponseVector s) = _
      abel
    _ = _ := by rw [weighted_response_commutator]; abel

/-- The faithful inverse multiplication formula for the physical Ma, MQ, Q, P families. -/
theorem inverse_weightedAirySource
    (s : ℝ) -- [definition]
    : Ring.inverse (1-airyKernelShift s) (weightedAirySource s) =
      weightedResponseVector s - resolventV s • responseVector s +
        resolventU s • derivativeResponseVector s := by
  have hleft := contraction_ringInverse_left (airyKernelShift s)
    (norm_airyKernelShift_lt_one s) (weightedResponseVector s)
  have he : weightedResponseVector s =
      Ring.inverse (1-airyKernelShift s) (weightedAirySource s) +
        resolventV s • responseVector s - resolventU s • derivativeResponseVector s := by
    calc
      _ = Ring.inverse (1-airyKernelShift s)
          (weightedResponseVector s-airyKernelShift s (weightedResponseVector s)) := hleft.symm
      _ = Ring.inverse (1-airyKernelShift s)
          (weightedAirySource s + resolventV s • airyBoundaryVector s -
            resolventU s • airyBoundaryDerivative s) := by rw [weighted_response_inverse_equation]
      _ = _ := by simp only [map_sub,map_add,map_smul]; rfl
  rw [he]
  abel

/-- The true Airy ODE source is the sum of its spatial and shift components. -/
theorem inverse_airyBoundaryODEVector
    (s : ℝ) -- [definition]
    : Ring.inverse (1-airyKernelShift s) (airyBoundaryODEVector s) =
      weightedResponseVector s + s • responseVector s - resolventV s • responseVector s +
        resolventU s • derivativeResponseVector s := by
  have hc : airyBoundaryODEVector s = weightedAirySource s + s • airyBoundaryVector s := by
    unfold weightedAirySource
    abel
  rw [hc,map_add,map_smul,inverse_weightedAirySource]
  change weightedResponseVector s-resolventV s • responseVector s+
      resolventU s • derivativeResponseVector s+s • responseVector s = _
  abel

/-- All weighted-domain and commutator fields hold jointly on the nonzero physical shift-zero instance. -/
theorem weighted_response_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      weightedAirySource 0 ≠ 0 ∧ weightedResponseVector 0 ≠ 0 ∧
      (∀ s : ℝ, MemLp (fun x : ℝ => x*(responseVector s) x) 2 halfLineMeasure) ∧
      (weightedAirySource 0 =ᵐ[halfLineMeasure] fun x => x*airyAiReal x) ∧
      (weightedResponseVector 0 =ᵐ[halfLineMeasure] fun x => x*(responseVector 0) x) ∧
      weightedResponseVector 0-airyKernelShift 0 (weightedResponseVector 0) =
        weightedAirySource 0+resolventV 0 • airyBoundaryVector 0-
          resolventU 0 • airyBoundaryDerivative 0 ∧
      Ring.inverse (1-airyKernelShift 0) (weightedAirySource 0) =
        weightedResponseVector 0-resolventV 0 • responseVector 0+
          resolventU 0 • derivativeResponseVector 0 := by
  have hpositive (f g : Lp ℝ 2 halfLineMeasure) (hf : f ≠ 0)
      (hg : g =ᵐ[halfLineMeasure] fun x => x*f x) : g ≠ 0 := by
    intro hz
    apply hf
    apply Lp.ext
    filter_upwards [hg,Lp.coeFn_zero ℝ 2 halfLineMeasure,
      ae_restrict_mem measurableSet_Ioi] with x hx hzero hpos
    rw [hz,hzero] at hx
    have hh : f x = 0 := (mul_eq_zero.mp hx.symm).resolve_left hpos.ne'
    exact hh.trans hzero.symm
  have hQ : responseVector 0 ≠ 0 := response_derivative_all_binder_joint_probe.2.2.1
  have hMa : weightedAirySource 0 =ᵐ[halfLineMeasure] fun x => x*(airyBoundaryVector 0) x := by
    filter_upwards [weightedAirySource_apply_ae 0,airyBoundaryVector_apply_ae 0] with x hx ha
    rw [hx,ha]
  refine ⟨airyBoundaryVector_ne_zero 0,hQ,
    hpositive _ _ (airyBoundaryVector_ne_zero 0) hMa,
    hpositive _ _ hQ (weightedResponseVector_apply_ae 0),memLp_weightedResponseVector,
    ?_,weightedResponseVector_apply_ae 0,weighted_response_inverse_equation 0,
    inverse_weightedAirySource 0⟩
  simpa only [zero_add] using weightedAirySource_apply_ae 0

end RMTFoundations.TracyWidom.AiryWeightedResponse
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weightedAirySource
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weightedAirySource_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.memLp_weightedAirySource
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.responseVector_eq_source_add_kernel
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.responseVector_eq_source_add_kernel_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weightedResponseVector
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weightedResponseVector_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.memLp_weightedResponseVector
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.derivative_source_response_pairing
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weighted_response_commutator_scalar
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weighted_response_endpoint_integral
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weighted_response_commutator
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weighted_response_inverse_equation
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.inverse_weightedAirySource
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.inverse_airyBoundaryODEVector
#print axioms RMTFoundations.TracyWidom.AiryWeightedResponse.weighted_response_joint_probe
