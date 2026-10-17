import RMTFoundations.TracyWidom.HMAiryEnvelope


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMNormalization
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open RMTFoundations.Fredholm RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.HMAiryEnvelope

/-- The actual canonical response has an eventual norm bound from its genuine resolvent equation. -/
theorem eventually_norm_response_le_twice_boundary :
    ∀ᶠ s : ℝ in atTop,
      ‖Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)‖ ≤ 2*‖airyBoundaryVector s‖ := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [he] with s hs
  have hK : ‖airyKernelShift s‖ ≤ 1/2 := by
    have h := ContinuousLinearMap.opNorm_comp_le (airyHankelShift s) (airyHankelShift s)
    change ‖airyKernelShift s‖ ≤ ‖airyHankelShift s‖*‖airyHankelShift s‖ at h
    nlinarith [h,norm_nonneg (airyHankelShift s)]
  let Q := Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)
  have hr : Q-airyKernelShift s Q=airyBoundaryVector s :=
    contraction_ringInverse_right (airyKernelShift s) (norm_airyKernelShift_lt_one s) _
  have heq : Q=airyBoundaryVector s+airyKernelShift s Q := sub_eq_iff_eq_add.mp hr
  have htri := norm_add_le (airyBoundaryVector s) (airyKernelShift s Q)
  rw [←heq] at htri
  have hop := (airyKernelShift s).le_opNorm Q
  have hb := mul_le_mul_of_nonneg_right hK (norm_nonneg Q)
  change ‖Q‖ ≤  2*‖airyBoundaryVector s‖
  nlinarith

/-- The actual endpoint correction is relatively small, with all inverse inputs discharged. -/
theorem eventually_resolventQ_relative_error_le :
    ∀ᶠ s : ℝ in atTop,
      |resolventQ s/airyAiReal s-1| ≤ ‖airyHankelShift s‖*airyAiReal s := by
  filter_upwards [eventually_norm_response_le_twice_boundary,eventually_ge_atTop (1:ℝ)] with s hn hs
  have hp : 0<airyAiReal s := airyAiReal_pos_of_nonneg (by linarith)
  let Q := Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)
  have he : resolventQ s-airyAiReal s=inner ℝ (airyBoundaryVector s) (airyHankelShift s Q) := by
    simp only [resolventQ,Q,add_sub_cancel_left]
  have hinner : |resolventQ s-airyAiReal s| ≤
      2*‖airyHankelShift s‖*airyEnergy s := by
    rw [he]
    calc
      |inner ℝ (airyBoundaryVector s) (airyHankelShift s Q)| ≤
          ‖airyBoundaryVector s‖*‖airyHankelShift s Q‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖airyBoundaryVector s‖*(‖airyHankelShift s‖*‖Q‖) :=
        mul_le_mul_of_nonneg_left ((airyHankelShift s).le_opNorm Q) (norm_nonneg _)
      _ ≤ ‖airyBoundaryVector s‖*(‖airyHankelShift s‖*(2*‖airyBoundaryVector s‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) (norm_nonneg _)
      _ = 2*‖airyHankelShift s‖*‖airyBoundaryVector s‖^2 := by ring
      _ = 2*‖airyHankelShift s‖*airyEnergy s := by rw [airyBoundaryVector_norm_sq]
  have hsq : |resolventQ s-airyAiReal s| ≤ ‖airyHankelShift s‖*(airyAiReal s)^2 := by
    have h := mul_le_mul_of_nonneg_left (airyEnergy_le_airyAi_sq_half s hs)
      (by positivity : 0 ≤ 2*‖airyHankelShift s‖)
    calc
      _ ≤ 2*‖airyHankelShift s‖*airyEnergy s := hinner
      _ ≤ 2*‖airyHankelShift s‖*((airyAiReal s)^2/2) := h
      _ = _ := by ring
  have hediv : resolventQ s/airyAiReal s-1=(resolventQ s-airyAiReal s)/airyAiReal s := by
    field_simp [hp.ne']
  rw [hediv,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  simpa only [pow_two,mul_assoc] using hsq

/-- The physical resolvent endpoint has the Airy normalization at plus infinity.
This does not assert global Hastings–McLeod ODE existence or uniqueness. -/
theorem resolventQ_relative_Airy_atTop :
    Tendsto (fun s : ℝ => resolventQ s/airyAiReal s) atTop (𝓝 1) := by
  have he : ∀ᶠ s : ℝ in atTop, ‖resolventQ s/airyAiReal s-1‖ ≤ airyAiReal s := by
    filter_upwards [eventually_resolventQ_relative_error_le,eventually_ge_atTop (1:ℝ)] with s hs hs1
    have hp := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ s)).le
    simp only [Real.norm_eq_abs]
    exact hs.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_airyHankelShift_lt_one s).le hp)
  have hh : Tendsto (fun s : ℝ => resolventQ s/airyAiReal s-1) atTop (𝓝 0) :=
    squeeze_zero_norm' he airyAi_atTop_zero
  simpa only [sub_add_cancel,zero_add] using hh.add_const 1

/-- All physical objects and tail conclusions occur jointly in the genuine shift-one instance. -/
theorem HM_normalization_all_binder_joint_probe :
    airyBoundaryVector 1 ≠ 0 ∧ 0<airyAiReal 1 ∧
      airyEnergy 1 ≤ (airyAiReal 1)^2/2 ∧
      (∀ x : ℝ, 0 ≤ x → airyAiReal (1+x)≤airyAiReal 1*Real.exp (-x)) ∧
      (∀ᶠ s : ℝ in atTop, ‖Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)‖≤ 2*‖airyBoundaryVector s‖) ∧
      Tendsto (fun s : ℝ => resolventQ s/airyAiReal s) atTop (𝓝 1) :=
  ⟨airyBoundaryVector_ne_zero 1,airyAiReal_pos_of_nonneg (by norm_num),
    airyEnergy_le_airyAi_sq_half 1 le_rfl,
    fun x hx => airyAi_relative_exp_envelope 1 x le_rfl hx,
    eventually_norm_response_le_twice_boundary,resolventQ_relative_Airy_atTop⟩

end RMTFoundations.TracyWidom.HMNormalization
#print axioms RMTFoundations.TracyWidom.HMNormalization.eventually_norm_response_le_twice_boundary
#print axioms RMTFoundations.TracyWidom.HMNormalization.eventually_resolventQ_relative_error_le
#print axioms RMTFoundations.TracyWidom.HMNormalization.resolventQ_relative_Airy_atTop
#print axioms RMTFoundations.TracyWidom.HMNormalization.HM_normalization_all_binder_joint_probe
