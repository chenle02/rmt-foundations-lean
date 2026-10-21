import RMTFoundations.TracyWidom.HMNormalization
import RMTFoundations.TracyWidom.IntegralRepresentations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.HMNormalization
open RMTFoundations.TracyWidom.HMAiryEnvelope

/-- Fourth powers of the genuine Airy value are negligible against its square tail.
The proof uses l'Hopital on actual differentiated functions, not an asymptotic ansatz. -/
theorem airy_fourth_relative_energy_atTop_zero :
    Tendsto (fun s : ℝ => (airyAiReal s)^4/airyEnergy s) atTop (𝓝 0) := by
  have hd : ∀ᶠ s : ℝ in atTop, HasDerivAt (fun t => (airyAiReal t)^4)
      (4*(airyAiReal s)^3*deriv airyAiReal s) s :=
    Eventually.of_forall (fun s => (hasDerivAt_airyAiReal' s).pow 4)
  have he : ∀ᶠ s : ℝ in atTop, HasDerivAt airyEnergy (-(airyAiReal s)^2) s :=
    Eventually.of_forall hasDerivAt_airyEnergy
  have hen : ∀ᶠ s : ℝ in atTop, -(airyAiReal s)^2 ≠ 0 := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact neg_ne_zero.mpr (pow_ne_zero 2 (airyAiReal_pos_of_nonneg hs).ne')
  have hz : Tendsto (fun s : ℝ => (airyAiReal s)^4) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 4≠0)] using airyAi_atTop_zero.pow 4
  have hr : Tendsto (fun s : ℝ =>
      (4*(airyAiReal s)^3*deriv airyAiReal s)/(-(airyAiReal s)^2)) atTop (𝓝 0) := by
    have h := (airyAi_atTop_zero.mul airyAi_derivative_atTop_zero).const_mul (-4:ℝ)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    have hn := (airyAiReal_pos_of_nonneg hs).ne'
    field_simp [hn] <;> ring
  exact HasDerivAt.lhopital_zero_atTop hd he hen hz airyEnergy_tendsto_zero hr

/-- The Airy-normalized physical endpoint has the same fourth-power smallness. -/
theorem endpoint_fourth_relative_energy_atTop_zero :
    Tendsto (fun s : ℝ => (resolventQ s)^4/airyEnergy s) atTop (𝓝 0) := by
  have hr := resolventQ_relative_Airy_atTop.pow 4
  have h := hr.mul airy_fourth_relative_energy_atTop_zero
  simp only [one_pow,one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  have hn := (airyAiReal_pos_of_nonneg hs).ne'
  have he := (airyEnergy_pos s).ne'
  simp only [div_pow]
  field_simp [hn,he]

/-- A genuine spectral lower bound supplies the diagonal energy floor everywhere. -/
theorem airyEnergy_half_le_resolventU
    (s : ℝ) -- [definition]
    : airyEnergy s/2 ≤ resolventU s := by
  have hH := (isSelfAdjoint_airyHankelShift s).isSymmetric
  have hK : ∀ x y, inner ℝ (airyKernelShift s x) y = inner ℝ x (airyKernelShift s y) := by
    intro x y
    exact (hH (airyHankelShift s x) y).trans (hH x (airyHankelShift s y))
  have hn := norm_airyKernelShift_lt_one s
  have hl := contraction_resolvent_half_norm_lower (airyKernelShift s)
    (Ring.inverse (1-airyKernelShift s)) hn hK
    (contraction_ringInverse_right (airyKernelShift s) hn)
    (contraction_ringInverse_left (airyKernelShift s) hn) (airyBoundaryVector s)
  rw [airyBoundaryVector_inner_self] at hl
  exact hl

/-- The actual Fredholm Hamiltonian gap is strictly positive on a nonempty right tail. -/
theorem eventually_endpoint_fourth_lt_resolventU :
    ∀ᶠ s : ℝ in atTop, (resolventQ s)^4 < resolventU s := by
  have h := endpoint_fourth_relative_energy_atTop_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [h] with s hs
  have hh := (div_lt_iff₀ (airyEnergy_pos s)).mp hs
  have hu := airyEnergy_half_le_resolventU s
  linarith

/-- Every limit and energy-floor premise is jointly supplied on the same nonzero physical model. -/
theorem right_gap_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧
      Tendsto (fun s : ℝ => (resolventQ s)^4/airyEnergy s) atTop (𝓝 0) ∧
      (∀ s : ℝ, airyEnergy s/2 ≤ resolventU s) ∧
      (∃ s : ℝ, 0 ≤ s ∧ 0 < airyAiReal s ∧ (resolventQ s)^4 < resolventU s) := by
  obtain ⟨s,hs,hgap⟩ := ((eventually_ge_atTop (0:ℝ)).and
    eventually_endpoint_fourth_lt_resolventU).exists
  exact ⟨airyBoundaryVector_ne_zero 0,endpoint_fourth_relative_energy_atTop_zero,
    airyEnergy_half_le_resolventU,s,hs,airyAiReal_pos_of_nonneg hs,hgap⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.airy_fourth_relative_energy_atTop_zero
#print axioms RMTFoundations.TracyWidom.endpoint_fourth_relative_energy_atTop_zero
#print axioms RMTFoundations.TracyWidom.airyEnergy_half_le_resolventU
#print axioms RMTFoundations.TracyWidom.eventually_endpoint_fourth_lt_resolventU
#print axioms RMTFoundations.TracyWidom.right_gap_all_binder_joint_probe
