import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.OrderFourEndpoints
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Filter Set
open scoped Topology
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates

/-- The actual GOE strict density gives a strict q+u floor everywhere. -/
theorem endpoint_add_diagonal_positive
    (s : ℝ) -- [definition]
    : 0 < resolventQ s+resolventU s := by
  have h := airy_canonical_boundary_positive s
  rw [airy_boundary_resolvent_parity_identity] at h
  exact h

/-- The physical GSE density is automatically positive wherever q does not exceed u. -/
theorem TW4AirySlope_positive_of_q_le_u
    (s : ℝ) -- [definition]
    (hq : resolventQ s ≤ resolventU s) -- [standing]
    : 0 < TW4AirySlope s := by
  have hp := mul_pos (TW1R_positive_bounds s).1 (endpoint_add_diagonal_positive s)
  have hn := mul_nonneg (hankelDetPlus_positive s).le (sub_nonneg.mpr hq)
  dsimp [TW4AirySlope]
  nlinarith

/-- A genuine nonempty physical q<u region follows from the plus determinant's left
boundary and its positive value at zero. This does not assert an entire left ray. -/
theorem exists_physical_endpoint_lt_diagonal :
    ∃ s : ℝ, s < 0 ∧ resolventQ s < resolventU s := by
  have hp := hankelDetPlus_positive 0
  have hl := tendsto_hankelDetPlus_atBot.eventually (gt_mem_nhds hp)
  obtain ⟨a,ha,hab⟩ := (hl.and (eventually_lt_atBot (0:ℝ))).exists
  have hd : Differentiable ℝ hankelDetPlus :=
    fun t => (hankelDetPlus_hasDerivAt t).differentiableAt
  obtain ⟨s,hs,hderiv⟩ := exists_deriv_eq_slope hankelDetPlus hab
    continuous_hankelDetPlus.continuousOn hd.differentiableOn
  have hpos : 0 < deriv hankelDetPlus s := by
    rw [hderiv]
    exact div_pos (sub_pos.mpr ha) (sub_pos.mpr hab)
  rw [(hankelDetPlus_hasDerivAt s).deriv] at hpos
  have hmul : 0 < hankelDetPlus s*(resolventU s-resolventQ s) := by linarith
  have hdiff := (mul_pos_iff_of_pos_left (hankelDetPlus_positive s)).mp hmul
  exact ⟨s,hs.2,by linarith⟩

/-- Every sign hypothesis holds jointly on one actual nondegenerate negative
shift; the global strict GOE floor is supplied rather than assumed. -/
theorem easy_GSE_sign_all_binder_joint_probe :
    ∃ s : ℝ, s < 0 ∧ airyBoundaryVector s ≠ 0 ∧
      0 < TW1R s ∧ 0 < hankelDetPlus s ∧
      0 < resolventQ s+resolventU s ∧ resolventQ s ≤ resolventU s ∧
      0 < TW4AirySlope s := by
  obtain ⟨s,hs,hqu⟩ := exists_physical_endpoint_lt_diagonal
  exact ⟨s,hs,airyBoundaryVector_ne_zero s,(TW1R_positive_bounds s).1,
    hankelDetPlus_positive s,endpoint_add_diagonal_positive s,hqu.le,
    TW4AirySlope_positive_of_q_le_u s hqu.le⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.endpoint_add_diagonal_positive
#print axioms RMTFoundations.TracyWidom.TW4AirySlope_positive_of_q_le_u
#print axioms RMTFoundations.TracyWidom.exists_physical_endpoint_lt_diagonal
#print axioms RMTFoundations.TracyWidom.easy_GSE_sign_all_binder_joint_probe
