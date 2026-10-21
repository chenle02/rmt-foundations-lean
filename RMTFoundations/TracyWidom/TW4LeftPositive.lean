import RMTFoundations.TracyWidom.HMGlobalSquaredUpper
import RMTFoundations.TracyWidom.TW4Hamiltonian
import RMTFoundations.TracyWidom.TW4EasySign
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set Filter
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.OrderTwoLogDerivative RMTFoundations.TracyWidom.IntegralRepresentations

/-- The sign-free squared upper profile and a genuine diagonal budget imply
endpoint domination on the reflected physical model. NON-ledger comparison. -/
theorem endpoint_abs_lt_diagonal_of_left_budget
    (t : ℝ) -- [definition]
    (ht : 0 < t) -- [standing]
    (hupper : (resolventQ (-t))^2 ≤ 3*t/4) -- [standing]
    (hbudget : 4 < t*resolventU (-t)) -- [standing]
    : |resolventQ (-t)| < resolventU (-t) := by
  have hu : 0 < resolventU (-t) := airy_inverse_square_boundary_positive _
  have hham := resolvent_hamiltonian_identity (-t)
  have hfourth : (resolventQ (-t))^4 ≤ 3*t*(resolventQ (-t))^2/4 := by
    have h := mul_le_mul_of_nonneg_right hupper (sq_nonneg (resolventQ (-t)))
    nlinarith
  have henergy : t*(resolventQ (-t))^2 ≤ 4*resolventU (-t) := by
    nlinarith [sq_nonneg (deriv resolventQ (-t))]
  have hsq : (resolventQ (-t))^2 < (resolventU (-t))^2 := by
    by_contra hn
    have hge := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hge ht.le
    have hstrict := mul_lt_mul_of_pos_right hbudget hu
    nlinarith
  have ha : |resolventQ (-t)|^2 = (resolventQ (-t))^2 := sq_abs _
  nlinarith [abs_nonneg (resolventQ (-t))]

/-- The actual endpoint is dominated by the positive diagonal on a whole left
tail, without a global endpoint-sign or square-root-profile premise. -/
theorem eventually_abs_endpoint_lt_diagonal_reflected :
    ∀ᶠ t : ℝ in atTop, |resolventQ (-t)| < resolventU (-t) := by
  have hu0 : 0 < resolventU 0 := airy_inverse_square_boundary_positive 0
  have hupper := RMTFoundations.TracyWidom.HMGlobalSquaredUpper.resolventQ_squared_ratio_eventually_le
    (3/4) (by norm_num)
  filter_upwards [hupper,eventually_gt_atTop (0:ℝ),eventually_gt_atTop (4/resolventU 0)]
    with t hup ht htb
  have hf : resolventU 0 ≤ resolventU (-t) := resolventU_antitone (by linarith)
  have hbudget : 4 < t*resolventU (-t) := by
    have hb := (div_lt_iff₀ hu0).mp htb
    have hm := mul_le_mul_of_nonneg_left hf ht.le
    nlinarith
  exact endpoint_abs_lt_diagonal_of_left_budget t ht
    (by have h := (div_le_iff₀ ht).mp hup; nlinarith [h]) hbudget

/-- The raw GSE candidate has a strictly positive derivative on a genuine
whole left tail. The sign-free PII upper producer is called inside the proof. -/
theorem eventually_TW4AirySlope_positive_atBot :
    ∀ᶠ s : ℝ in atBot, 0 < TW4AirySlope s := by
  obtain ⟨a,ha⟩ := eventually_atTop.1 eventually_abs_endpoint_lt_diagonal_reflected
  filter_upwards [eventually_le_atBot (-a)] with s hs
  have h := ha (-s) (by linarith)
  simp only [neg_neg] at h
  exact TW4AirySlope_positive_of_q_le_u s ((le_abs_self _).trans h.le)

/-- The actual raw GSE candidate is strictly increasing on a nonempty left ray. -/
theorem exists_TW4AiryR_strictMono_left_tail :
    ∃ a : ℝ, a ≤ 0 ∧ StrictMonoOn TW4AiryR (Iic a) ∧
      (∀ s, s ≤ a → 0 < TW4AirySlope s) := by
  obtain ⟨b,hb⟩ := eventually_atBot.1 eventually_TW4AirySlope_positive_atBot
  let a := min 0 b
  have hp (s : ℝ) (hs : s ≤ a) : 0 < TW4AirySlope s :=
    hb s (hs.trans (min_le_right _ _))
  refine ⟨a,min_le_left _ _,?_,hp⟩
  apply strictMonoOn_of_deriv_pos (convex_Iic a) continuous_TW4AiryR.continuousOn
  intro s hs
  rw [(TW4AiryR_hasDerivAt s).deriv]
  have hs' : s ∈ Iic a := interior_subset hs
  exact hp s hs'

/-- Every left-budget binder is jointly supplied by the actual nonzero Airy
model, on the same reflected point of a genuine whole left ray. -/
theorem left_GSE_density_all_binder_joint_probe :
    (∃ t : ℝ, 0 < t ∧ airyBoundaryVector (-t) ≠ 0 ∧
      (resolventQ (-t))^2 ≤ 3*t/4 ∧ 4 < t*resolventU (-t) ∧
      |resolventQ (-t)| < resolventU (-t) ∧ 0 < TW4AirySlope (-t)) ∧
      (∃ a : ℝ, a ≤ 0 ∧ StrictMonoOn TW4AiryR (Iic a) ∧
        (∀ s, s ≤ a → 0 < TW4AirySlope s)) := by
  have hu0 : 0 < resolventU 0 := airy_inverse_square_boundary_positive 0
  obtain ⟨t,hup,ht,hb⟩ := ((RMTFoundations.TracyWidom.HMGlobalSquaredUpper.resolventQ_squared_ratio_eventually_le
    (3/4) (by norm_num)).and ((eventually_gt_atTop (0:ℝ)).and
      (eventually_gt_atTop (4/resolventU 0)))).exists
  have hf : resolventU 0 ≤ resolventU (-t) := resolventU_antitone (by linarith)
  have hbudget : 4 < t*resolventU (-t) := by
    have h := (div_lt_iff₀ hu0).mp hb
    nlinarith [mul_le_mul_of_nonneg_left hf ht.le]
  have hupper : (resolventQ (-t))^2 ≤ 3*t/4 := by
    have h := (div_le_iff₀ ht).mp hup
    nlinarith [h]
  have hdom := endpoint_abs_lt_diagonal_of_left_budget t ht hupper hbudget
  exact ⟨⟨t,ht,airyBoundaryVector_ne_zero _,hupper,hbudget,hdom,
    TW4AirySlope_positive_of_q_le_u (-t) ((le_abs_self _).trans hdom.le)⟩,
    exists_TW4AiryR_strictMono_left_tail⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.endpoint_abs_lt_diagonal_of_left_budget
#print axioms RMTFoundations.TracyWidom.eventually_abs_endpoint_lt_diagonal_reflected
#print axioms RMTFoundations.TracyWidom.eventually_TW4AirySlope_positive_atBot
#print axioms RMTFoundations.TracyWidom.exists_TW4AiryR_strictMono_left_tail
#print axioms RMTFoundations.TracyWidom.left_GSE_density_all_binder_joint_probe
