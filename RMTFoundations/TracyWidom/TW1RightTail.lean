import RMTFoundations.Airy.Spectral
import RMTFoundations.TracyWidom.OrderOneBounds
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds

theorem signed_log_quadratic_remainder
    (x : ℝ /- [definition] -/)
    (hx : |x| ≤ (1 / 2 : ℝ) /- [standing] -/) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hlt : |x| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.sum_range_one, zero_add, Nat.cast_zero, Nat.cast_one, pow_one, div_one] at h
  have hd : 0 < 1 - |x| := by linarith
  have hb : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    rw [sq_abs]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * |x| by linarith)]
  simpa only [add_comm] using h.trans hb

theorem signed_product_log_quadratic_remainder
    {ι : Type* /- [definition] -/}
    (a : ι → ℝ /- [definition] -/)
    (ha : Summable a /- [standing] -/)
    (ha2 : Summable (fun i => (a i) ^ 2) /- [standing] -/)
    (hb : ∀ i, |a i| ≤ (1 / 2 : ℝ) /- [standing] -/) :
    |Real.log (∏' i, (1 - a i)) + (∑' i, a i)| ≤ 2 * (∑' i, (a i) ^ 2) := by
  have hp : ∀ i, 0 < 1 - a i := fun i => by
    have h := le_abs_self (a i)
    linarith [hb i]
  have hl : Summable (fun i => Real.log (1 - a i)) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable ha.neg
  rw [← Real.rexp_tsum_eq_tprod hp hl, Real.log_exp, ← hl.tsum_add ha]
  have hr := hl.add ha
  have hrn : Summable (fun i => |Real.log (1 - a i) + a i|) := by
    simpa only [Real.norm_eq_abs] using hr.norm
  have hn : |(∑' i, (Real.log (1 - a i) + a i))| ≤
      (∑' i, |Real.log (1 - a i) + a i|) := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hr.norm
  exact hn.trans (by
    rw [← tsum_mul_left]
    exact hrn.tsum_le_tsum (fun i => signed_log_quadratic_remainder (a i) (hb i))
      (ha2.mul_left 2))

theorem TW1R_log_remainder_of_norm_le_half
    (s : ℝ /- [definition] -/)
    (hs : ‖airyHankelShift s‖ ≤ (1 / 2 : ℝ) /- [standing] -/) :
    |Real.log (TW1R s) + trace (airyHankelShift s)| ≤
      2 * trace (airyKernelShift s) := by
  obtain ⟨ι, hc, b, a, he, hk, ha, ha2, ht, ht2, hp, hq⟩ :=
    airy_simultaneous_eigenbasis s
  letI := hc
  have hprod : HasProd (fun i => 1 - a i) (TW1R s) := by
    simpa [TW1R, TW1, sub_eq_add_neg] using hp (-1)
  rw [← hprod.tprod_eq, ← ht.tsum_eq, ← ht2.tsum_eq]
  apply signed_product_log_quadratic_remainder a ha.of_norm ha2.of_norm
  intro i
  have h := real_eigenvalue_norm_le (airyHankelShift s) (b i)
    (b.orthonormal.norm_eq_one i) (a i) (he i)
  simpa only [Real.norm_eq_abs] using h.trans hs

theorem TW1R_log_remainder_eventually :
    ∀ᶠ s : ℝ in atTop,
      |Real.log (TW1R s) + trace (airyHankelShift s)| ≤
        2 * trace (airyKernelShift s) := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with s hs
  exact TW1R_log_remainder_of_norm_le_half s hs.le

theorem TW1R_exponential_sandwich_of_norm_le_half
    (s : ℝ /- [definition] -/)
    (hs : ‖airyHankelShift s‖ ≤ (1 / 2 : ℝ) /- [standing] -/) :
    Real.exp (-trace (airyHankelShift s) - 2 * trace (airyKernelShift s)) ≤ TW1R s ∧
      TW1R s ≤ Real.exp (-trace (airyHankelShift s)) := by
  have hr := TW1R_log_remainder_of_norm_le_half s hs
  have hp := (TW1R_positive_bounds s).1
  constructor
  · rw [← Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp hr).1
    linarith
  · rw [trace_airyHankelShift_eq_half_tail]
    convert (TW1R_bounds s).2.1 using 1
    simp only [airyTailIntegral]
    congr 2
    ring

theorem TW1R_tail_trace_upper_of_norm_le_half
    (s : ℝ /- [definition] -/)
    (hs : ‖airyHankelShift s‖ ≤ (1 / 2 : ℝ) /- [standing] -/) :
    1 - TW1R s ≤ trace (airyHankelShift s) + 2 * trace (airyKernelShift s) := by
  have h := (TW1R_exponential_sandwich_of_norm_le_half s hs).1
  have he := Real.add_one_le_exp (-trace (airyHankelShift s) - 2 * trace (airyKernelShift s))
  linarith

/-- Rational lower bound with unit leading coefficient at the origin. -/
theorem exp_neg_tail_rational_lower
    (t : ℝ /- [definition] -/)
    (ht : 0 ≤ t /- [standing] -/) :
    t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  apply (div_le_iff₀ (show 0 < 1 + t by linarith)).mpr
  nlinarith

theorem TW1R_tail_trace_lower
    (s : ℝ /- [definition] -/) :
    trace (airyHankelShift s) / (1 + trace (airyHankelShift s)) ≤ 1 - TW1R s := by
  have ht : 0 < trace (airyHankelShift s) := by
    rw [trace_airyHankelShift_eq_half_tail]
    exact mul_pos (by norm_num) (airy_tail_positive s)
  have h := exp_neg_tail_rational_lower (trace (airyHankelShift s)) ht.le
  have hupper : TW1R s ≤ Real.exp (-trace (airyHankelShift s)) := by
    rw [trace_airyHankelShift_eq_half_tail]
    convert (TW1R_bounds s).2.1 using 1
    simp only [airyTailIntegral]
    congr 2
    ring
  linarith

theorem TW1R_tail_trace_sandwich_eventually :
    ∀ᶠ s : ℝ in atTop,
      trace (airyHankelShift s) / (1 + trace (airyHankelShift s)) ≤ 1 - TW1R s ∧
      1 - TW1R s ≤ trace (airyHankelShift s) + 2 * trace (airyKernelShift s) := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with s hs
  exact ⟨TW1R_tail_trace_lower s, TW1R_tail_trace_upper_of_norm_le_half s hs.le⟩

theorem signed_spectrum_all_binder_joint_probe :
    ∃ a : Fin 2 → ℝ,
      Summable a ∧ Summable (fun i => (a i) ^ 2) ∧
      (∀ i, |a i| ≤ (1 / 2 : ℝ)) ∧ a 0 < 0 ∧ 0 < a 1 ∧
      |Real.log (∏' i, (1 - a i)) + (∑' i, a i)| ≤ 2 * (∑' i, (a i) ^ 2) := by
  let a : Fin 2 → ℝ := fun i => if i = 0 then -(1 / 4 : ℝ) else 1 / 2
  have hb : ∀ i, |a i| ≤ (1 / 2 : ℝ) := by
    intro i
    fin_cases i <;> norm_num [a]
  exact ⟨a, summable_of_hasFiniteSupport (Set.toFinite _),
    summable_of_hasFiniteSupport (Set.toFinite _), hb, by norm_num [a],
    by norm_num [a], signed_product_log_quadratic_remainder a
      (summable_of_hasFiniteSupport (Set.toFinite _))
      (summable_of_hasFiniteSupport (Set.toFinite _)) hb⟩

theorem TW1R_right_tail_all_binder_joint_probe :
    ∃ s : ℝ, ‖airyHankelShift s‖ ≤ (1 / 2 : ℝ) ∧ airyAiReal 0 > 0 ∧
      ‖shiftedUnitVector 0‖ = 1 ∧
      |Real.log (TW1R s) + trace (airyHankelShift s)| ≤ 2 * trace (airyKernelShift s) ∧
      Real.exp (-trace (airyHankelShift s) - 2 * trace (airyKernelShift s)) ≤ TW1R s ∧
      TW1R s ≤ Real.exp (-trace (airyHankelShift s)) ∧
      trace (airyHankelShift s) / (1 + trace (airyHankelShift s)) ≤ 1 - TW1R s ∧
      1 - TW1R s ≤ trace (airyHankelShift s) + 2 * trace (airyKernelShift s) := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨s, hs⟩ := he.exists
  exact ⟨s, hs.le, airyAiReal_zero_pos, shiftedUnitVector_norm 0,
    TW1R_log_remainder_of_norm_le_half s hs.le,
    (TW1R_exponential_sandwich_of_norm_le_half s hs.le).1,
    (TW1R_exponential_sandwich_of_norm_le_half s hs.le).2,
    TW1R_tail_trace_lower s, TW1R_tail_trace_upper_of_norm_le_half s hs.le⟩

theorem signed_trace_tail_ratio
    (f t q : ℝ → ℝ /- [definition] -/)
    (hp : ∀ᶠ s : ℝ in atTop, 0 < t s /- [standing] -/)
    (hb : ∀ᶠ s : ℝ in atTop,
      t s / (1 + t s) ≤ f s ∧ f s ≤ t s + 2 * q s /- [standing] -/)
    (ht : Tendsto t atTop (𝓝 0) /- [standing] -/)
    (hq : Tendsto (fun s => q s / t s) atTop (𝓝 0) /- [standing] -/) :
    Tendsto (fun s => f s / t s) atTop (𝓝 1) := by
  have hl : Tendsto (fun s => 1 / (1 + t s)) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    convert! hc.div (hc.add ht) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1 <;> simp
  have hu : Tendsto (fun s => 1 + 2 * (q s / t s)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hq.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hp, hb] with s hs hh
    have hd := div_le_div_of_nonneg_right hh.1 hs.le
    have he : t s / (1 + t s) / t s = 1 / (1 + t s) := by
      field_simp [hs.ne', show 1 + t s ≠ 0 by linarith]
    simpa only [he] using hd
  · filter_upwards [hp, hb] with s hs hh
    have hd := div_le_div_of_nonneg_right hh.2 hs.le
    simpa only [add_div, mul_div_assoc, div_self hs.ne'] using hd

theorem TW1R_tail_ratio_of_square_trace_ratio
    (hsmall : Tendsto (fun s => trace (airyKernelShift s) / trace (airyHankelShift s))
      atTop (𝓝 0) /- [standing] -/) :
    Tendsto (fun s => (1 - TW1R s) / trace (airyHankelShift s)) atTop (𝓝 1) := by
  apply signed_trace_tail_ratio (fun s => 1 - TW1R s)
    (fun s => trace (airyHankelShift s)) (fun s => trace (airyKernelShift s))
  · apply Filter.Eventually.of_forall
    intro s
    rw [trace_airyHankelShift_eq_half_tail]
    exact mul_pos (by norm_num) (airy_tail_positive s)
  · exact TW1R_tail_trace_sandwich_eventually
  · have h : Tendsto (fun s : ℝ => ∫ x in Set.Ioi s, airyAiReal x) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    have he := h.const_mul (1 / 2 : ℝ)
    simpa only [trace_airyHankelShift_eq_half_tail, mul_zero] using he
  · exact hsmall

theorem signed_trace_tail_ratio_all_binder_joint_probe :
    ∃ f t q : ℝ → ℝ,
      (∀ᶠ s : ℝ in atTop, 0 < t s) ∧
      (∀ᶠ s : ℝ in atTop, t s / (1 + t s) ≤ f s ∧ f s ≤ t s + 2 * q s) ∧
      Tendsto t atTop (𝓝 0) ∧ Tendsto (fun s => q s / t s) atTop (𝓝 0) ∧
      f 0 = 1 ∧ Tendsto (fun s => f s / t s) atTop (𝓝 1) := by
  let t : ℝ → ℝ := fun s => Real.exp (-s)
  have hp : ∀ᶠ s : ℝ in atTop, 0 < t s :=
    Filter.Eventually.of_forall (fun s => Real.exp_pos _)
  have hb : ∀ᶠ s : ℝ in atTop,
      t s / (1 + t s) ≤ t s ∧ t s ≤ t s + 2 * 0 := by
    apply Filter.Eventually.of_forall
    intro s
    constructor
    · apply (div_le_iff₀ (show 0 < 1 + t s by positivity)).mpr
      nlinarith [sq_nonneg (t s)]
    · simp
  have ht : Tendsto t atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hq : Tendsto (fun s => (0 : ℝ) / t s) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  exact ⟨t, t, fun _ => 0, hp, hb, ht, hq, by norm_num [t],
    signed_trace_tail_ratio t t (fun _ => 0) hp hb ht hq⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.signed_log_quadratic_remainder
#print axioms RMTFoundations.TracyWidom.signed_product_log_quadratic_remainder
#print axioms RMTFoundations.TracyWidom.TW1R_log_remainder_of_norm_le_half
#print axioms RMTFoundations.TracyWidom.TW1R_log_remainder_eventually
#print axioms RMTFoundations.TracyWidom.TW1R_exponential_sandwich_of_norm_le_half
#print axioms RMTFoundations.TracyWidom.TW1R_tail_trace_upper_of_norm_le_half
#print axioms RMTFoundations.TracyWidom.exp_neg_tail_rational_lower
#print axioms RMTFoundations.TracyWidom.TW1R_tail_trace_lower
#print axioms RMTFoundations.TracyWidom.TW1R_tail_trace_sandwich_eventually
#print axioms RMTFoundations.TracyWidom.signed_spectrum_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.TW1R_right_tail_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.signed_trace_tail_ratio
#print axioms RMTFoundations.TracyWidom.TW1R_tail_ratio_of_square_trace_ratio
#print axioms RMTFoundations.TracyWidom.signed_trace_tail_ratio_all_binder_joint_probe
