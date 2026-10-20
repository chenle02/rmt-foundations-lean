import RMTFoundations.TracyWidom.HMGreenRepresentation
import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.HMNormalization
import RMTFoundations.TracyWidom.IntegralRepresentations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open Filter Set
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom.PhysicalPainleveII RMTFoundations.TracyWidom.HMNormalization
open RMTFoundations.TracyWidom.HMGreenRepresentation RMTFoundations.TracyWidom.IntegralRepresentations

/-- Weighted decay required to identify the physical Hamiltonian with u. -/
theorem TW_endpoint_weighted_square_atTop_zero :
    Tendsto (fun s => s*(resolventQ s)^2) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := airyAiReal_abs_le_exp'
  obtain ⟨a,_,ha⟩ := normalized_positive_tail resolventQ resolventQ_relative_Airy_atTop
  have hr := resolventQ_relative_Airy_atTop.eventually
    (eventually_lt_nhds (by norm_num : (1 : ℝ)<2))
  have hupper : ∀ᶠ s : ℝ in atTop,
      s*(resolventQ s)^2 ≤ (2*C)^2*(s*Real.exp (-s)) := by
    filter_upwards [hr,eventually_ge_atTop a,eventually_ge_atTop (0 : ℝ)] with s hs hsa hs0
    have hp := (ha s hsa).1
    have hAi : 0 < airyAiReal s := airyAiReal_pos_of_nonneg hs0
    have hq : resolventQ s ≤ 2*C*Real.exp (-s) := by
      have hqAi := (div_lt_iff₀ hAi).mp hs
      have hAiBound := hbound s
      rw [abs_of_pos hAi] at hAiBound
      nlinarith
    have hsq := pow_le_pow_left₀ hp.le hq 2
    have he : (Real.exp (-s))^2 ≤ Real.exp (-s) := by
      have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (-s)]
    have hsq' : (resolventQ s)^2 ≤ (2*C)^2*Real.exp (-s) := by
      calc
        _ ≤ (2*C*Real.exp (-s))^2 := hsq
        _ = (2*C)^2*(Real.exp (-s))^2 := by ring
        _ ≤ (2*C)^2*Real.exp (-s) :=
          mul_le_mul_of_nonneg_left he (sq_nonneg (2*C))
    simpa only [mul_assoc,mul_left_comm s] using mul_le_mul_of_nonneg_left hsq' hs0
  have hlim : Tendsto (fun s : ℝ => (2*C)^2*(s*Real.exp (-s))) atTop (𝓝 0) := by
    simpa only [pow_one,mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((2*C)^2)
  apply squeeze_zero' _ hupper hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact mul_nonneg hs (sq_nonneg _)

/-- A direct identity of the genuine endpoint and diagonal Fredholm coordinates. -/
theorem resolvent_hamiltonian_identity
    (s : ℝ) -- [definition]
    : (deriv resolventQ s)^2-s*(resolventQ s)^2-(resolventQ s)^4 = resolventU s := by
  let f : ℝ → ℝ := fun t =>
    (deriv resolventQ t)^2-t*(resolventQ t)^2-(resolventQ t)^4-resolventU t
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    have hq : HasDerivAt resolventQ (deriv resolventQ t) t :=
      (hasDerivAt_resolventQ t).differentiableAt.hasDerivAt
    have h := ((((hasDerivAt_deriv_resolventQ t).pow 2).sub
      ((hasDerivAt_id t).mul (hq.pow 2))).sub (hq.pow 4)).sub
      (hasDerivAt_resolventU_negative_q_sq t)
    convert! h using 1 <;> simp only [id_eq,Pi.pow_apply,Pi.mul_apply] <;> ring
  have hq : Differentiable ℝ resolventQ :=
    fun t => (hasDerivAt_resolventQ t).differentiableAt
  have hdz := normalized_derivative_boundary resolventQ hq
    hasDerivAt_deriv_resolventQ resolventQ_relative_Airy_atTop
  have hqz := normalized_atTop_zero resolventQ resolventQ_relative_Airy_atTop
  have huz := primitive_slope_tendsto_zero
    (fun t => Real.log (RMTFoundations.AiryKernel.TW2R t)) resolventU
    RMTFoundations.TracyWidom.OrderTwoLogDerivative.resolventU_continuous
    RMTFoundations.TracyWidom.OrderTwoLogDerivative.hasDerivAt_log_TW2R_coordinates
    (fun t => (airy_inverse_square_boundary_positive t).le) resolventU_antitone
    log_TW2R_tendsto_zero
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f,zero_pow (by norm_num : 2≠0),zero_pow (by norm_num : 4≠0),sub_zero]
      using (((hdz.pow 2).sub TW_endpoint_weighted_square_atTop_zero).sub (hqz.pow 4)).sub huz
  have he : f = fun _ => f s := by
    funext t
    exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
      (fun x => (hd x).deriv) t s
  rw [he] at hf
  have hz : f s = 0 := tendsto_nhds_unique tendsto_const_nhds hf
  dsimp [f] at hz
  linarith

/-- Logarithmic-slope curvature equals the Hamiltonian gap; no global q-sign is assumed. -/
theorem endpoint_logarithmic_slope_hasDerivAt
    (s : ℝ) -- [definition]
    (hq : resolventQ s ≠ 0) -- [standing]
    : HasDerivAt (fun t => deriv resolventQ t/resolventQ t)
      (((resolventQ s)^4-resolventU s)/(resolventQ s)^2) s := by
  have hd := (hasDerivAt_deriv_resolventQ s).div
    ((hasDerivAt_resolventQ s).differentiableAt.hasDerivAt) hq
  have he : (s*resolventQ s+2*(resolventQ s)^3)*resolventQ s -
      deriv resolventQ s*deriv resolventQ s = (resolventQ s)^4-resolventU s := by
    nlinarith [resolvent_hamiltonian_identity s]
  rw [he] at hd
  exact hd

/-- Every physical identity binder is jointly realized on the actual nonzero Airy model. -/
theorem TW_hamiltonian_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < resolventU 0 ∧
      (∀ s : ℝ, (deriv resolventQ s)^2-s*(resolventQ s)^2-(resolventQ s)^4=resolventU s) ∧
      (∃ s : ℝ, resolventQ s ≠ 0 ∧
        HasDerivAt (fun t => deriv resolventQ t/resolventQ t)
          (((resolventQ s)^4-resolventU s)/(resolventQ s)^2) s) := by
  obtain ⟨a,_,ha⟩ := normalized_positive_tail resolventQ resolventQ_relative_Airy_atTop
  have hq := (ha a le_rfl).1.ne'
  exact ⟨airyBoundaryVector_ne_zero 0,airy_inverse_square_boundary_positive 0,
    resolvent_hamiltonian_identity,a,hq,endpoint_logarithmic_slope_hasDerivAt a hq⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW_endpoint_weighted_square_atTop_zero
#print axioms RMTFoundations.TracyWidom.resolvent_hamiltonian_identity
#print axioms RMTFoundations.TracyWidom.endpoint_logarithmic_slope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW_hamiltonian_all_binder_joint_probe
