import RMTFoundations.TracyWidom.HMAiryEnvelope
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMAiryPowerTail
open Set MeasureTheory Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMAiryEnvelope
/-- The actual Airy fourth-power tail has a relative, certified mass bound. -/
theorem airy_fourth_tail_bound
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/)
    : IntegrableOn (fun t => (airyAiReal t)^4) (Ioi s) ∧
      (∫ t in Ioi s, (airyAiReal t)^4) ≤ (airyAiReal s)^4/4 := by
  let g : ℝ → ℝ := fun t => ((airyAiReal s)^4*Real.exp (4*s))*Real.exp (-4*t)
  have hg : IntegrableOn g (Ioi s) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-4:ℝ)<0) s).const_mul _
  have hb : ∀ᵐ t ∂volume.restrict (Ioi s), (airyAiReal t)^4 ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : s < t := ht
    have hp := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).le
    have he := airyAi_relative_exp_envelope s (t-s) hs (by linarith : 0 ≤ t-s)
    rw [show s+(t-s)=t by ring] at he
    have hpow := pow_le_pow_left₀ hp he 4
    have h_exp : (Real.exp (-(t-s)))^4 = Real.exp (4*s)*Real.exp (-4*t) := by
      rw [show (Real.exp (-(t-s)))^4 = Real.exp (-(t-s))*Real.exp (-(t-s))*
        Real.exp (-(t-s))*Real.exp (-(t-s)) by ring,
        ← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow,h_exp,g,mul_assoc] using hpow
  have hi : IntegrableOn (fun t => (airyAiReal t)^4) (Ioi s) :=
    hg.mono' (continuous_airyAiReal.pow 4).aestronglyMeasurable.restrict
      (by
        filter_upwards [hb] with t ht
        simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (airyAiReal t)^4)] using ht)
  have hint : (∫ t in Ioi s, g t) = (airyAiReal s)^4/4 := by
    dsimp only [g]
    rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-4:ℝ)<0) s]
    have he : Real.exp (4*s)*Real.exp (-4*s)=1 := by rw [← Real.exp_add];simp
    calc
      ((airyAiReal s)^4*Real.exp (4*s)) * (-Real.exp (-4*s)/(-4)) =
        (airyAiReal s)^4/4*(Real.exp (4*s)*Real.exp (-4*s)) := by ring
      _ = _ := by rw [he,mul_one]
  exact ⟨hi,(integral_mono_ae hi hg hb).trans_eq hint⟩
/-- Shift one supplies the floor and uses the genuinely positive Airy model. -/
theorem fourth_tail_joint_probe : 0 < airyAiReal 1 ∧
    IntegrableOn (fun t => (airyAiReal t)^4) (Ioi 1) ∧
    (∫ t in Ioi 1, (airyAiReal t)^4) ≤ (airyAiReal 1)^4/4 :=
  ⟨airyAiReal_pos_of_nonneg (by norm_num),airy_fourth_tail_bound 1 le_rfl⟩
end RMTFoundations.TracyWidom.HMAiryPowerTail
#print axioms RMTFoundations.TracyWidom.HMAiryPowerTail.airy_fourth_tail_bound
#print axioms RMTFoundations.TracyWidom.HMAiryPowerTail.fourth_tail_joint_probe
