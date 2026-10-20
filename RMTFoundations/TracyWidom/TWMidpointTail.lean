import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set

/-- Translation of an upper-tail Lebesgue integral, without integrability assumptions. -/
theorem midpoint_tail_translate_integral
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    : (∫ x in Ioi (0 : ℝ), q (x+s)) = ∫ t in Ioi s, q t := by
  rw [←integral_indicator measurableSet_Ioi,←integral_indicator measurableSet_Ioi]
  have h := integral_add_right_eq_self (μ := volume) ((Ioi s).indicator q) s
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  have he : x+s ∈ Ioi s ↔ x ∈ Ioi (0:ℝ) := by
    simp only [mem_Ioi]
    constructor <;> intro hx <;> linarith
  simp only [indicator_apply,he]

/-- The doubled argument supplies the exact one-half normalization. -/
theorem midpoint_tail_double_integral
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    : (∫ x in Ioi (0:ℝ), q (x+x+s)) = (∫ t in Ioi s, q t)/2 := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => q (t+s)) 0
    (b := 2) (by norm_num)
  simp only [mul_zero,smul_eq_mul] at h
  rw [midpoint_tail_translate_integral q s] at h
  convert h using 1 <;> congr 1
  · funext x
    congr 1
    ring
  · ring

/-- A midpoint product bound gives the square-tail comparison required by the GSE sign.
All integrals are genuine Lebesgue integrals; no tail identity is assumed. -/
theorem midpoint_square_tail_comparison
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : ∀ t, s ≤ t → 0 ≤ q t /- [standing] -/)
    (hi : IntegrableOn (fun x => (q (x+s))^2) (Ioi 0) /- [standing] -/)
    (hm : ∀ x, 0 ≤ x → q s*q (x+x+s) ≤ (q (x+s))^2 /- [standing] -/)
    : q s*(∫ t in Ioi s, q t)/2 ≤ ∫ x in Ioi 0, (q (x+s))^2 := by
  have he := midpoint_tail_double_integral q s
  have hn : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ q s*q (x+x+s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (hq s le_rfl) (hq (x+x+s) (by have : 0 < x := hx; linarith))
  have hb : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))),
      q s*q (x+x+s) ≤ (q (x+s))^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hm x (show 0 ≤ x from le_of_lt hx)
  have h := integral_mono_of_nonneg hn hi hb
  rw [integral_const_mul,he] at h
  simpa only [mul_div_assoc] using h

/-- The square-tail output has the original upper-half-line coordinates. -/
theorem midpoint_square_tail_comparison_unshifted
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : ∀ t, s ≤ t → 0 ≤ q t /- [standing] -/)
    (hi : IntegrableOn (fun x => (q (x+s))^2) (Ioi 0) /- [standing] -/)
    (hm : ∀ x, 0 ≤ x → q s*q (x+x+s) ≤ (q (x+s))^2 /- [standing] -/)
    : q s*(∫ t in Ioi s, q t)/2 ≤ ∫ t in Ioi s, (q t)^2 := by
  have h := midpoint_square_tail_comparison q s hq hi hm
  have he := midpoint_tail_translate_integral (fun t => (q t)^2) s
  rw [he] at h
  exact h

/-- The exponential endpoint realizes the whole midpoint hypothesis with nonzero value. -/
theorem midpoint_tail_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, ∃ s : ℝ,
      q s = 1 ∧
      (∀ t, s ≤ t → 0 ≤ q t) ∧
      IntegrableOn (fun x => (q (x+s))^2) (Ioi 0) ∧
      (∀ x, 0 ≤ x → q s*q (x+x+s) ≤ (q (x+s))^2) ∧
      q s*(∫ t in Ioi s, q t)/2 ≤ ∫ t in Ioi s, (q t)^2 := by
  let q : ℝ → ℝ := fun t => Real.exp (-t)
  have hp (t : ℝ) : 0 < q t := Real.exp_pos _
  have he (x : ℝ) : (q (x+0))^2 = Real.exp (-(2*x)) := by
    dsimp [q]
    rw [add_zero,pow_two,←Real.exp_add]
    congr 1
    ring
  have hi : IntegrableOn (fun x => (q (x+0))^2) (Ioi 0) := by
    simp_rw [he]
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) 0
  have hm (x : ℝ) (hx : 0 ≤ x) : q 0*q (x+x+0) ≤ (q (x+0))^2 := by
    rw [he]
    dsimp [q]
    simp only [neg_zero,Real.exp_zero,one_mul,add_zero]
    apply le_of_eq
    congr 1
    ring
  exact ⟨q,0,by simp [q],fun t ht => (hp t).le,hi,hm,
    midpoint_square_tail_comparison_unshifted q 0 (fun t ht => (hp t).le) hi hm⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.midpoint_tail_translate_integral
#print axioms RMTFoundations.TracyWidom.midpoint_tail_double_integral
#print axioms RMTFoundations.TracyWidom.midpoint_square_tail_comparison
#print axioms RMTFoundations.TracyWidom.midpoint_square_tail_comparison_unshifted
#print axioms RMTFoundations.TracyWidom.midpoint_tail_all_binder_joint_probe
