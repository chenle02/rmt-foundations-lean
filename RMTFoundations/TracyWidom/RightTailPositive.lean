import RMTFoundations.TracyWidom.LeftTail
import RMTFoundations.Airy.Spectral
import RMTFoundations.Airy.Contraction
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology BigOperators
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWLeftTail RMTFoundations.Fredholm

/-- Two finite Bonferroni bounds for a product of positive contractions. -/
theorem rightTail_finite_product_bounds
    {ι : Type*} -- [definition]
    (S : Finset ι /- [definition] -/)
    (a : ι → ℝ /- [definition] -/)
    (h0 : ∀ i, 0 ≤ a i /- [standing] -/)
    (h1 : ∀ i, a i ≤ 1 /- [standing] -/) :
    (∑ i ∈ S, a i) - (∑ i ∈ S, a i)^2 / 2 ≤ 1 - ∏ i ∈ S, (1-a i) ∧
      1 - ∏ i ∈ S, (1-a i) ≤ ∑ i ∈ S, a i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have ht : 0 ≤ ∑ j ∈ S, a j := Finset.sum_nonneg (fun j _ => h0 j)
    have hn : 0 ≤ 1-a i := sub_nonneg.mpr (h1 i)
    have hlo := mul_le_mul_of_nonneg_left ih.1 hn
    have hup := mul_le_mul_of_nonneg_left ih.2 hn
    constructor <;> nlinarith [sq_nonneg (a i), mul_nonneg (h0 i) (sq_nonneg (∑ j ∈ S, a j)),
      mul_nonneg (h0 i) ht]

/-- Infinite products have a trace-linear tail with quadratic absolute error. -/
theorem rightTail_positive_product_bounds
    (a : ℕ → ℝ /- [definition] -/)
    (d t : ℝ /- [definition] -/)
    (h0 : ∀ i, 0 ≤ a i /- [standing] -/)
    (h1 : ∀ i, a i ≤ 1 /- [standing] -/)
    (hp : HasProd (fun i => 1-a i) d /- [standing] -/)
    (ht : HasSum a t /- [standing] -/) :
    t-t^2/2 ≤ 1-d ∧ 1-d ≤ t := by
  have hleft := Filter.Tendsto.sub ht ((ht.pow 2).div_const 2)
  have hright := (tendsto_const_nhds (x := (1:ℝ))).sub hp
  constructor
  · exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall (fun S => (rightTail_finite_product_bounds S a h0 h1).1))
  · exact le_of_tendsto_of_tendsto hright ht
      (Eventually.of_forall (fun S => (rightTail_finite_product_bounds S a h0 h1).2))

/-- Unconditional bounds at the literal Airy-kernel determinant and trace. -/
theorem TW2_rightTail_trace_bounds (s : ℝ /- [definition] -/) :
    airyTraceIntegral s - (airyTraceIntegral s)^2/2 ≤ 1-TW2R s ∧
      1-TW2R s ≤ airyTraceIntegral s := by
  obtain ⟨a,h0,h1,hp,ht⟩ := TW2R_spectral_bridge_of_contraction s
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  exact rightTail_positive_product_bounds a (TW2R s) (airyTraceIntegral s) h0 h1 hp ht

/-- The physical error between the TW2 upper tail and its leading trace term. -/
theorem TW2_rightTail_trace_error (s : ℝ /- [definition] -/) :
    |(1-TW2R s)-airyTraceIntegral s| ≤ (airyTraceIntegral s)^2/2 := by
  obtain ⟨hl,hu⟩ := TW2_rightTail_trace_bounds s
  rw [abs_of_nonpos (by linarith : (1-TW2R s)-airyTraceIntegral s ≤ 0)]
  linarith

/-- All spectral binders hold together at an actual nonzero Airy cutoff. -/
theorem TW2_rightTail_physical_joint_probe :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) ∧
      HasProd (fun i => 1-a i) (TW2R 0) ∧ HasSum a (airyTraceIntegral 0) ∧
      airyAiReal 0 ≠ 0 ∧
      (airyTraceIntegral 0-(airyTraceIntegral 0)^2/2 ≤ 1-TW2R 0 ∧
        1-TW2R 0 ≤ airyTraceIntegral 0) := by
  obtain ⟨a,h0,h1,hp,ht⟩ := TW2R_spectral_bridge_of_contraction 0
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one 0)
  exact ⟨a,h0,h1,hp,ht,airyAiReal_zero_pos.ne',TW2_rightTail_trace_bounds 0⟩

/-- A two-mode positive contraction inhabits every finite-product binder. -/
theorem rightTail_finite_all_binder_joint_probe :
    ∃ (S : Finset (Fin 2)) (a : Fin 2 → ℝ),
      S.card = 2 ∧ (∀ i, 0 < a i) ∧ (∀ i, a i ≤ 1) ∧
      ((∑ i ∈ S, a i) - (∑ i ∈ S, a i)^2/2 ≤ 1-∏ i ∈ S, (1-a i) ∧
        1-∏ i ∈ S, (1-a i) ≤ ∑ i ∈ S, a i) := by
  classical
  let a : Fin 2 → ℝ := fun _ => 1/4
  have h0 : ∀ i, 0 < a i := by intro i; norm_num [a]
  have h1 : ∀ i, a i ≤ 1 := by intro i; norm_num [a]
  exact ⟨Finset.univ,a,by simp,h0,h1,
    rightTail_finite_product_bounds Finset.univ a (fun i => (h0 i).le) h1⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.rightTail_finite_product_bounds
#print axioms RMTFoundations.TracyWidom.rightTail_positive_product_bounds
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_trace_bounds
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_trace_error
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_physical_joint_probe
#print axioms RMTFoundations.TracyWidom.rightTail_finite_all_binder_joint_probe
