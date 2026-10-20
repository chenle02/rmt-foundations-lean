import RMTFoundations.TracyWidom.TWResponseSmallness
import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.PlusLeftTail
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Filter Set
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates

/-- The actual plus determinant has strictly negative derivative on a right tail.
It cannot be treated as a second increasing CDF in the GSE determinant average. -/
theorem eventually_hankelDetPlus_deriv_neg :
    ∀ᶠ s : ℝ in atTop, deriv hankelDetPlus s < 0 := by
  filter_upwards [eventually_resolventQ_gt_resolventU] with s hs
  rw [(hankelDetPlus_hasDerivAt s).deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (hankelDetPlus_positive s) (sub_neg.mpr hs.2)) (by norm_num)

/-- Strict right-tail antitonicity is an unconditional theorem of the physical model. -/
theorem hankelDetPlus_strictAntiOn_tail :
    ∃ a : ℝ, 1 ≤ a ∧ StrictAntiOn hankelDetPlus (Ici a) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp eventually_hankelDetPlus_deriv_neg
  let b := max a 1
  refine ⟨b,le_max_right _ _,?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Ici b) continuous_hankelDetPlus.continuousOn
  intro s hs
  have hb : b < s := by simpa only [interior_Ici,mem_Ioi] using hs
  exact ha s ((le_max_left a 1).trans hb.le)

/-- The right-tail plus determinant approaches one from strictly above. -/
theorem eventually_hankelDetPlus_gt_one :
    ∀ᶠ s : ℝ in atTop, 1 < hankelDetPlus s := by
  obtain ⟨a,_,ha⟩ := hankelDetPlus_strictAntiOn_tail
  filter_upwards [eventually_ge_atTop a] with s hs
  have hst : hankelDetPlus (s+1) < hankelDetPlus s :=
    ha hs (show a ≤ s+1 by linarith) (by linarith)
  have hl : 1 ≤ hankelDetPlus (s+1) := le_of_tendsto tendsto_hankelDetPlus_atTop (by
    filter_upwards [eventually_ge_atTop (s+1)] with t ht
    exact ha.antitoneOn (by linarith : a ≤ s+1) (by linarith : a ≤ t) ht)
  exact hl.trans_lt hst

/-- A compiled counterinstance to the proposed global plus-factor monotonicity. -/
theorem hankelDetPlus_not_monotone : ¬ Monotone hankelDetPlus := by
  intro hm
  obtain ⟨s,hs⟩ := eventually_hankelDetPlus_deriv_neg.exists
  exact (not_lt_of_ge (hm.deriv_nonneg (x:=s))) hs

/-- Global antitonicity fails too: positivity and the left limit zero rule it out. -/
theorem hankelDetPlus_not_antitone : ¬ Antitone hankelDetPlus := by
  intro ha
  have hz : hankelDetPlus 0 ≤ 0 := ge_of_tendsto tendsto_hankelDetPlus_atBot (by
    filter_upwards [eventually_le_atBot (0:ℝ)] with s hs
    exact ha hs)
  exact (not_le_of_gt (hankelDetPlus_positive 0)) hz

/-- Universal F2≤F1 is false: the actual order is reversed on a right tail. -/
theorem eventually_TW1R_lt_TW2R :
    ∀ᶠ s : ℝ in atTop, TW1R s < TW2R s := by
  filter_upwards [eventually_hankelDetPlus_gt_one] with s hs
  rw [TW2R_factorization]
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left hs (TW1R_positive_bounds s).1

/-- Two actual shifts simultaneously witness decreasing plus values above one,
nonzero Airy data and the reversed F1/F2 order. -/
theorem plus_nonmonotone_all_binder_joint_probe :
    (∃ s t : ℝ, 1 ≤ s ∧ s < t ∧ airyBoundaryVector s ≠ 0 ∧
      0 < resolventU s ∧ resolventU s < resolventQ s ∧
      1 < hankelDetPlus t ∧ hankelDetPlus t < hankelDetPlus s ∧
      deriv hankelDetPlus s < 0 ∧ TW1R s < TW2R s) ∧
    ¬ Monotone hankelDetPlus ∧ ¬ Antitone hankelDetPlus := by
  obtain ⟨a,ha,hm⟩ := hankelDetPlus_strictAntiOn_tail
  obtain ⟨b,hb⟩ := eventually_atTop.mp eventually_hankelDetPlus_gt_one
  obtain ⟨s,hs,hq,hd,horder⟩ := ((eventually_ge_atTop (max a b)).and
    (eventually_resolventQ_gt_resolventU.and
      (eventually_hankelDetPlus_deriv_neg.and eventually_TW1R_lt_TW2R))).exists
  have hsa : a ≤ s := (le_max_left _ _).trans hs
  have hsb : b ≤ s := (le_max_right _ _).trans hs
  refine ⟨⟨s,s+1,ha.trans hsa,by linarith,airyBoundaryVector_ne_zero s,
    airy_inverse_square_boundary_positive s,hq.2,hb (s+1) (by linarith),
    hm hsa (show a ≤ s+1 by linarith) (show s < s+1 by linarith),hd,horder⟩,
    hankelDetPlus_not_monotone,hankelDetPlus_not_antitone⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.eventually_hankelDetPlus_deriv_neg
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_strictAntiOn_tail
#print axioms RMTFoundations.TracyWidom.eventually_hankelDetPlus_gt_one
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_not_monotone
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_not_antitone
#print axioms RMTFoundations.TracyWidom.eventually_TW1R_lt_TW2R
#print axioms RMTFoundations.TracyWidom.plus_nonmonotone_all_binder_joint_probe
