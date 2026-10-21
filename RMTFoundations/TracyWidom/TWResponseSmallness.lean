import RMTFoundations.TracyWidom.HMNormalization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open Filter MeasureTheory
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.HMAiryEnvelope
open RMTFoundations.TracyWidom.HMNormalization

/-- The canonical diagonal response is bounded by the genuine Airy square on a tail. -/
theorem eventually_resolventU_le_airyAi_sq :
    ∀ᶠ s : ℝ in atTop, resolventU s  ≤  (airyAiReal s)^2 := by
  filter_upwards [eventually_norm_response_le_twice_boundary,
    eventually_ge_atTop (1:ℝ)] with s hn hs
  calc
    resolventU s  ≤  |resolventU s| := le_abs_self _
    _  ≤  ‖airyBoundaryVector s‖ *
        ‖Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)‖ :=
      abs_real_inner_le_norm _ _
    _  ≤  ‖airyBoundaryVector s‖*(2*‖airyBoundaryVector s‖) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = 2*airyEnergy s := by rw [←airyBoundaryVector_norm_sq]; ring
    _  ≤  (airyAiReal s)^2 := by
      have h := airyEnergy_le_airyAi_sq_half s hs
      linarith

/-- The diagonal response is lower order than the Airy boundary value.
All inverse and energy inputs refer to the actual Fredholm operator. -/
theorem resolventU_relative_Airy_atTop_zero :
    Tendsto (fun s : ℝ => resolventU s/airyAiReal s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := airyAiReal) ?_ airyAi_atTop_zero
  filter_upwards [eventually_resolventU_le_airyAi_sq,
    eventually_ge_atTop (1:ℝ)] with s hu hs
  have ha : 0 < airyAiReal s := airyAiReal_pos_of_nonneg (by linarith)
  have hp : 0 < resolventU s := airy_inverse_square_boundary_positive s
  rw [Real.norm_eq_abs,abs_of_pos (div_pos hp ha)]
  apply (div_le_iff₀ ha).mpr
  simpa only [pow_two] using hu

/-- Actual endpoint positivity and strict q > u coexist on a nonempty right tail. -/
theorem eventually_resolventQ_gt_resolventU :
    ∀ᶠ s : ℝ in atTop, 0 < resolventQ s ∧ resolventU s < resolventQ s := by
  have hq := resolventQ_relative_Airy_atTop.eventually
    (eventually_gt_nhds (by norm_num : (1/2:ℝ) < 1))
  have hu := resolventU_relative_Airy_atTop_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
  filter_upwards [hq,hu,eventually_ge_atTop (1:ℝ)] with s hqs hus hs
  have ha : 0 < airyAiReal s := airyAiReal_pos_of_nonneg (by linarith)
  have hp : 0 < resolventU s := airy_inverse_square_boundary_positive s
  have hqq := (lt_div_iff₀ ha).mp hqs
  have huu := (div_lt_iff₀ ha).mp hus
  constructor  <;>  linarith

/-- The true q-normalization and the diagonal smallness imply u/q→0. -/
theorem resolventU_relative_resolventQ_atTop_zero :
    Tendsto (fun s : ℝ => resolventU s/resolventQ s) atTop (𝓝 0) := by
  have h := resolventU_relative_Airy_atTop_zero.div resolventQ_relative_Airy_atTop
    (by norm_num : (1:ℝ) ≠ 0)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_resolventQ_gt_resolventU] with s hs hq
  have ha : airyAiReal s ≠ 0 :=
    (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ s)).ne'
  have hqne : resolventQ s ≠ 0 := hq.1.ne'
  dsimp only [Pi.div_apply]
  field_simp [ha,hqne]

/-- All asymptotic premises are jointly realized by the actual nonzero Airy model;
the existential shift also has strict endpoint and diagonal inequalities. -/
theorem response_relative_smallness_all_binder_joint_probe :
    (∃ s : ℝ, 1 ≤ s ∧ airyBoundaryVector s ≠ 0 ∧ 0 < airyAiReal s ∧
      0 < resolventU s ∧ resolventU s < resolventQ s) ∧
    Tendsto (fun s : ℝ => resolventQ s/airyAiReal s) atTop (𝓝 1) ∧
    Tendsto (fun s : ℝ => resolventU s/airyAiReal s) atTop (𝓝 0) ∧
    Tendsto (fun s : ℝ => resolventU s/resolventQ s) atTop (𝓝 0) := by
  obtain ⟨s,hs,hq⟩ := ((eventually_ge_atTop (1:ℝ)).and
    eventually_resolventQ_gt_resolventU).exists
  exact ⟨⟨s,hs,airyBoundaryVector_ne_zero s,
    airyAiReal_pos_of_nonneg (by linarith),airy_inverse_square_boundary_positive s,hq.2⟩,
    resolventQ_relative_Airy_atTop,resolventU_relative_Airy_atTop_zero,
    resolventU_relative_resolventQ_atTop_zero⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.eventually_resolventU_le_airyAi_sq
#print axioms RMTFoundations.TracyWidom.resolventU_relative_Airy_atTop_zero
#print axioms RMTFoundations.TracyWidom.eventually_resolventQ_gt_resolventU
#print axioms RMTFoundations.TracyWidom.resolventU_relative_resolventQ_atTop_zero
#print axioms RMTFoundations.TracyWidom.response_relative_smallness_all_binder_joint_probe
