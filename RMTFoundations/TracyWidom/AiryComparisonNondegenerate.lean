import Mathlib
import RMTFoundations.TracyWidom.AiryPerturbationComparison
import RMTFoundations.TracyWidom.NonnegativeTriangleFoundation
import RMTFoundations.TracyWidom.HMGreenRepresentation
import RMTFoundations.TracyWidom.HMAirySmallness
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryComparisonNondegenerate
open MeasureTheory Set Filter Real
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMGreenRepresentation
open RMTFoundations.TracyWidom.HMAiryEnvelope RMTFoundations.TracyWidom.AiryPerturbationComparison

/-- Literal square-tail mass bound for the actual Airy reference. -/
theorem airy_square_tail_bound
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/) :
    (∫ t in Ioi s, (airyAiReal t)^2) ≤ (airyAiReal s)^2 / 2 := by
  have htr := RMTFoundations.TWOneBounds.integral_Ioi_translate
    (fun t => (airyAiReal t)^2) 0 s
  have he := airyAiReal_sq_integral s
  change (∫ u in Ioi 0, (airyAiReal (s+u))^2) = airyEnergy s at he
  have h0 : (∫ u in Ioi s, (airyAiReal u)^2) = airyEnergy s := by
    simpa only [zero_add, add_zero, add_comm] using htr.symm.trans
      (by simpa only [add_comm] using he)
  rw [h0]
  exact airyEnergy_le_airyAi_sq_half s hs

/-- The canonical normalized nonlinear solution supplies an active positive
coefficient perturbation epsilon=2q² on every point of an infinite tail.
Every standing binder of the physical Airy ODE comparison is exhibited jointly,
including the actual two-variable absolute integrability. No equality with Ai,
zero perturbation, zero measure or zero budget is used. -/
theorem positive_perturbation_all_binder_joint_probe :
    ∃ (q : ℝ → ℝ) (s : ℝ),
      let ε : ℝ → ℝ := fun t => 2*(q t)^2
      let b : ℝ → ℝ := fun t => (airyAiReal t)^2
      0 < s ∧ (0 < (8 : ℝ)) ∧
      (∀ t, s ≤ t → 0 < ε t) ∧ q ≠ airyAiReal ∧
      (∀ t, HasDerivAt q (deriv q t) t) ∧
      (∀ t, HasDerivAt (deriv q) ((t+ε t)*q t) t) ∧
      IntegrableOn b (Ioi s) ∧ (∀ t, s ≤ t → 0 ≤ b t) ∧
      (∀ t, s ≤ t → |ε t| ≤ 8*b t) ∧
      BddAbove ((fun t => |q t/airyAiReal t|) '' Ici s) ∧
      (∀ x, s ≤ x → IntegrableOn (fun t => ε t*airyAiReal t*q t) (Ioi x)) ∧
      Tendsto (fun t => airyAiReal t*deriv q t-deriv airyAiReal t*q t) atTop (𝓝 0) ∧
      Tendsto (fun t => q t/airyAiReal t) atTop (𝓝 1) ∧
      (∀ x, s ≤ x → IntegrableOn
        (fun t => (airyAiReal t*deriv q t-deriv airyAiReal t*q t)/(airyAiReal t)^2) (Ioi x)) ∧
      (∀ x, s ≤ x → Integrable
        (fun z : ℝ × ℝ => if z.1 < z.2 then ((airyAiReal z.1)^2)⁻¹ *
          (ε z.2*airyAiReal z.2*q z.2) else 0)
        ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x)))) ∧
      0 < tailBudget s 8 b ∧ tailBudget s 8 b < 1 ∧
      (∀ x, s ≤ x →
        |q x/airyAiReal x-1| ≤ tailBudget s 8 b/(1-tailBudget s 8 b) ∧
        |q x-airyAiReal x| ≤ (tailBudget s 8 b/(1-tailBudget s 8 b))*airyAiReal x) := by
  obtain ⟨q, _, hq, hqq, hn, _, _⟩ :=
    RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  obtain ⟨a, ha, hQ⟩ := normalized_nested_green_representation q hq hqq hn
  obtain ⟨c, hc, hC⟩ := RMTFoundations.TracyWidom.HMAirySmallness.eventually_airy_cubic_coefficient_small 2
  let s := max a c
  have has : a ≤ s := le_max_left _ _
  have hcs : c ≤ s := le_max_right _ _
  have hs1 : 1 ≤ s := ha.trans has
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  let ε : ℝ → ℝ := fun t => 2*(q t)^2
  let b : ℝ → ℝ := fun t => (airyAiReal t)^2
  have hpos : ∀ t, s ≤ t → 0 < ε t := by
    intro t ht
    dsimp only [ε]
    exact mul_pos (by norm_num) (pow_pos (hQ t (has.trans ht)).1 2)
  have hneq : q ≠ airyAiReal := by
    intro heq
    have H := hqq s
    rw [heq] at H
    have He := H.unique (hasDerivAt_deriv_airyAiReal' s)
    have hp := airyAiReal_pos_of_nonneg hs.le
    nlinarith [pow_pos hp 3]
  have hy : ∀ t, HasDerivAt q (deriv q t) t := fun t => (hq t).hasDerivAt
  have hyp : ∀ t, HasDerivAt (deriv q) ((t+ε t)*q t) t := by
    intro t
    convert! hqq t using 1 <;> dsimp only [ε] <;> ring
  have hb : IntegrableOn b (Ioi s) := integrable_airyAiReal_sq_Ioi s
  have hbn : ∀ t, s ≤ t → 0 ≤ b t := fun t _ => sq_nonneg _
  have hε : ∀ t, s ≤ t → |ε t| ≤ 8*b t := by
    intro t ht
    have hA := airyAiReal_pos_of_nonneg (hs.le.trans ht)
    have H := (hQ t (has.trans ht)).2.1
    rw [abs_div, abs_of_pos hA] at H
    have H' := (div_le_iff₀ hA).mp H
    have H'' := pow_le_pow_left₀ (abs_nonneg (q t)) H' 2
    dsimp only [ε, b]
    rw [abs_of_pos (hpos t ht)]
    nlinarith [sq_abs (q t)]
  have hbdd : BddAbove ((fun t => |q t/airyAiReal t|) '' Ici s) := by
    refine ⟨2, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact (hQ t (has.trans ht)).2.1
  have hsource : ∀ x, s ≤ x → IntegrableOn
      (fun t => ε t*airyAiReal t*q t) (Ioi x) := by
    intro x hx
    convert! (hQ x (has.trans hx)).2.2.1 using 1
    ext t
    dsimp only [ε]
    ring
  have hflux := normalized_wronskian_boundary q hq hqq hn
  have houter : ∀ x, s ≤ x → IntegrableOn
      (fun t => (airyAiReal t*deriv q t-deriv airyAiReal t*q t)/(airyAiReal t)^2) (Ioi x) := by
    intro x hx
    have H := ((hQ x (has.trans hx)).2.2.2.2.1).neg
    apply H.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change -((∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) = _
    rw [(hQ t (has.trans (hx.trans ht.le))).2.2.2.1]
    ring
  have hjoint : ∀ x, s ≤ x → Integrable
      (fun z : ℝ × ℝ => if z.1 < z.2 then ((airyAiReal z.1)^2)⁻¹ *
        (ε z.2*airyAiReal z.2*q z.2) else 0)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) := by
    intro x hx
    apply RMTFoundations.TracyWidom.NonnegativeTriangleFoundation.integrable_triangle
      (fun t => ((airyAiReal t)^2)⁻¹) (fun t => ε t*airyAiReal t*q t) x
    · exact (measurable_airyAiReal.pow_const 2).inv
    · exact ((hq.continuous.measurable.pow_const 2).const_mul 2).mul
        measurable_airyAiReal |>.mul hq.continuous.measurable
    · intros; positivity
    · intro t ht
      have hp := (hQ t (has.trans (hx.trans ht))).1.le
      have hA := (airyAiReal_pos_of_nonneg (hs.le.trans (hx.trans ht))).le
      dsimp only [ε]
      positivity
    · intro t ht; exact hsource t (hx.trans ht)
    · convert! (hQ x (has.trans hx)).2.2.2.2.1 using 1
      ext t
      have hf : (fun r => ε r*airyAiReal r*q r) =
          (fun r => 2*airyAiReal r*(q r)^3) := by
        ext r
        dsimp only [ε]
        ring
      rw [hf, div_eq_mul_inv]
      ring
  have hmass := airy_square_tail_bound s hs1
  have hI : 0 < ∫ t in Ioi s, b t := by
    apply (integral_pos_iff_support_of_nonneg_ae (by
      filter_upwards [] with t; exact sq_nonneg _) hb).mpr
    have he : Function.support b ∩ Ioi s = Ioi s := by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      exact ⟨fun h => h.2, fun ht => ⟨pow_ne_zero 2
        (airyAiReal_pos_of_nonneg (hs.le.trans ht.le)).ne', ht⟩⟩
    have hbmeas : MeasurableSet (Function.support b) :=
      (measurableSet_eq_fun (measurable_airyAiReal.pow_const 2)
        (show Measurable (fun _ : ℝ => (0 : ℝ)) from measurable_const)).compl
    rw [Measure.restrict_apply hbmeas, he]
    simp
  have hpbudget : 0 < tailBudget s 8 b := by
    dsimp only [tailBudget]
    positivity
  have hsmall : tailBudget s 8 b < 1 := by
    have hr : 1 ≤ sqrt s := by simpa using sqrt_le_sqrt hs1
    have hcc := (hC s hcs).2
    have hbound : tailBudget s 8 b ≤ 2*(airyAiReal s)^2 := by
      dsimp only [tailBudget]
      have hi0 := hI.le
      have hscale0 : 8 / (2*sqrt s) ≤ (4 : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < 2*sqrt s)).mpr
        nlinarith
      have hscale : (1 / (2*sqrt s))*8 ≤ (4 : ℝ) := by
        convert! hscale0 using 1 <;> ring
      calc
        (1 / (2*sqrt s))*8*(∫ t in Ioi s, b t) ≤ 4*(∫ t in Ioi s, b t) :=
          mul_le_mul_of_nonneg_right hscale hi0
        _ ≤ 4*((airyAiReal s)^2/2) := mul_le_mul_of_nonneg_left hmass (by norm_num)
        _ = 2*(airyAiReal s)^2 := by ring
    dsimp only [b] at hbound ⊢
    nlinarith [sq_nonneg (airyAiReal s)]
  have H := ai_ode_comparison s 8 b ε q (deriv q) hs (by norm_num)
    hy hyp hb hbn hε hbdd hsource hflux hn houter hjoint hsmall
  exact ⟨q, s, hs, by norm_num, hpos, hneq, hy, hyp, hb, hbn, hε,
    hbdd, hsource, hflux, hn, houter, hjoint, hpbudget, hsmall, H⟩

end RMTFoundations.TracyWidom.AiryComparisonNondegenerate

#print axioms RMTFoundations.TracyWidom.AiryComparisonNondegenerate.airy_square_tail_bound
#print axioms RMTFoundations.TracyWidom.AiryComparisonNondegenerate.positive_perturbation_all_binder_joint_probe
