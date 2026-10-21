import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.NonnegativeTriangleFoundation
open MeasureTheory Set

/-- Tonelli supplies genuine joint absolute integrability on a half-line
triangle from nonnegative factors, integrable inner tails and their integrable
weighted mass. This is independent of Airy functions and random matrices. -/
theorem integrable_triangle
    (p q : ℝ → ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hp : Measurable p /- [standing] -/)
    (hq : Measurable q /- [standing] -/)
    (hpn : ∀ t, x ≤ t → 0 ≤ p t /- [standing] -/)
    (hqn : ∀ t, x ≤ t → 0 ≤ q t /- [standing] -/)
    (hi : ∀ t, x ≤ t → IntegrableOn q (Ioi t) /- [standing] -/)
    (ho : IntegrableOn (fun t => p t * ∫ r in Ioi t, q r) (Ioi x) /- [standing] -/) :
    Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then p z.1 * q z.2 else 0)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) := by
  let μ : Measure ℝ := volume.restrict (Ioi x)
  let f : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 then p z.1 * q z.2 else 0
  have hm : Measurable f :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((hp.comp measurable_fst).mul (hq.comp measurable_snd)) measurable_const
  have htail (t : ℝ) (ht : x ≤ t) : Ioi t ∩ Ioi x = Ioi t := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, ht.trans_lt h⟩⟩
  have hi' (t : ℝ) (ht : x ≤ t) : Integrable (fun r => f (t, r)) μ := by
    have h : IntegrableOn (fun r => p t * q r) (Ioi t) μ := by
      dsimp only [IntegrableOn, μ]
      rw [Measure.restrict_restrict measurableSet_Ioi, htail t ht]
      exact (hi t ht).const_mul (p t)
    convert! h.integrable_indicator measurableSet_Ioi using 1
  have he (t : ℝ) (ht : x ≤ t) :
      (∫ r, ‖f (t, r)‖ ∂μ) = p t * ∫ r in Ioi t, q r := by
    have hn : (fun r => ‖f (t, r)‖) =ᵐ[μ] (fun r => f (t, r)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg]
      dsimp only [f]
      have hP := hpn t ht
      have hQ := hqn r hr.le
      split_ifs <;> positivity
    rw [integral_congr_ae hn]
    change (∫ r, (Ioi t).indicator (fun r => p t * q r) r ∂μ) = _
    rw [integral_indicator measurableSet_Ioi]
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioi, htail t ht, integral_const_mul]
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hi' t ht.le
  · exact ho.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (he t ht.le).symm)

/-- Exact positive exponential tail mass, from its antiderivative and decay. -/
theorem exponential_tail_mass
    (t : ℝ /- [definition] -/) :
    (∫ r in Ioi t, Real.exp (-r)) = Real.exp (-t) := by
  have hd (r : ℝ) : HasDerivAt (fun x => -Real.exp (-x)) (Real.exp (-r)) r := by
    convert! ((hasDerivAt_id r).neg.exp).neg using 1 <;>
      simp only [Pi.neg_apply, id_eq] <;> ring
  have hl : Filter.Tendsto (fun r : ℝ => -Real.exp (-r)) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hd t).continuousAt.continuousWithinAt) (fun r _ => hd r)
    (integrableOn_exp_neg_Ioi t) hl
  simpa only [zero_sub, neg_neg] using H

/-- Positive exponential factors inhabit all Tonelli binders on an infinite,
nonempty triangle; both inner and outer masses are derived explicitly. -/
theorem exponential_all_binder_joint_probe :
    Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then
      Real.exp (-z.2) else 0)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have ho : IntegrableOn (fun t => (1 : ℝ) * ∫ r in Ioi t, Real.exp (-r)) (Ioi 0) := by
    convert! (integrableOn_exp_neg_Ioi 0) using 1
    ext t
    simp only [one_mul, exponential_tail_mass]
  have H := integrable_triangle (fun _ => 1) (fun t => Real.exp (-t)) 0
    measurable_const
    (Real.continuous_exp.comp continuous_id.neg).measurable
    (by intros; norm_num) (fun _ _ => (Real.exp_pos _).le)
    (fun t _ => integrableOn_exp_neg_Ioi t) ho
  simpa only [one_mul] using H

end RMTFoundations.TracyWidom.NonnegativeTriangleFoundation

#print axioms RMTFoundations.TracyWidom.NonnegativeTriangleFoundation.integrable_triangle
#print axioms RMTFoundations.TracyWidom.NonnegativeTriangleFoundation.exponential_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.NonnegativeTriangleFoundation.exponential_tail_mass
