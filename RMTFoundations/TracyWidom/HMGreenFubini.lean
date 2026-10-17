import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMGreenFubini
open Set MeasureTheory Filter
open scoped Topology
/-- Absolutely integrable positive nested tail kernels may be exchanged into
one reduction-of-order Green integral. Both integrability claims are proved. -/
theorem nested_tail_fubini
    (f g : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (hg : Continuous g /- [standing] -/)
    (hfp : ∀ t ≥ s, 0 ≤ f t /- [standing] -/)
    (hgp : ∀ t ≥ s, 0 ≤ g t /- [standing] -/)
    (hgi : ∀ t ≥ s, IntegrableOn g (Ioi t) /- [standing] -/)
    (hoi : IntegrableOn (fun t => f t*(∫ u in Ioi t,g u)) (Ioi s) /- [standing] -/)
    : IntegrableOn (fun u => g u*(∫ t in s..u,f t)) (Ioi s) ∧
      (∫ t in Ioi s,f t*(∫ u in Ioi t,g u)) =
        ∫ u in Ioi s,g u*(∫ t in s..u,f t) := by
  let μ := volume.restrict (Ioi s)
  let H : ℝ × ℝ → ℝ :=
    {z : ℝ × ℝ | z.1<z.2}.indicator (fun z => f z.1*g z.2)
  have hH : AEStronglyMeasurable H (μ.prod μ) :=
    (((hf.comp continuous_fst).mul (hg.comp continuous_snd)).stronglyMeasurable.indicator
      (isOpen_lt continuous_fst continuous_snd).measurableSet).aestronglyMeasurable
  have hsection (t : ℝ) : (fun u => H (t,u)) = (Ioi t).indicator (fun u => f t*g u) := rfl
  have hinter (t : ℝ) (ht : s ≤ t) : Ioi t ∩ Ioi s=Ioi t :=
    inter_eq_left.mpr (fun u hu => lt_of_le_of_lt ht hu)
  have hslice (t : ℝ) (ht : s ≤ t) : Integrable (fun u => H (t,u)) μ := by
    rw [hsection]
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
    change Integrable (fun u => f t*g u) ((volume.restrict (Ioi s)).restrict (Ioi t))
    rw [Measure.restrict_restrict measurableSet_Ioi,hinter t ht]
    exact (hgi t ht).const_mul _
  have hleft (t : ℝ) (ht : s ≤ t) : (∫ u,H (t,u) ∂μ)=f t*(∫ u in Ioi t,g u) := by
    rw [hsection,integral_indicator measurableSet_Ioi]
    change (∫ u, f t*g u ∂(volume.restrict (Ioi s)).restrict (Ioi t))=_
    rw [Measure.restrict_restrict measurableSet_Ioi,hinter t ht,integral_const_mul]
  have hnonneg (t u : ℝ) (ht : s ≤ t) (hu : s ≤ u) : 0 ≤ H (t,u) := by
    dsimp [H,Set.indicator]
    split_ifs
    · exact mul_nonneg (hfp t ht) (hgp u hu)
    · exact le_rfl
  have hnorm : (fun t => ∫ u, ‖H (t,u)‖ ∂μ) =ᵐ[μ]
      (fun t => f t*(∫ u in Ioi t,g u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : s<t := ht
    have he : (∫ u, ‖H (t,u)‖ ∂μ)=(∫ u,H (t,u) ∂μ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg t u ht'.le hu.le)]
    exact he.trans (hleft t ht'.le)
  have hprod : Integrable H (μ.prod μ) := by
    apply (integrable_prod_iff hH).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hslice t ht.le
    · exact hoi.congr hnorm.symm
  have hright (u : ℝ) (hu : s ≤ u) : (∫ t,H (t,u) ∂μ)=g u*(∫ t in s..u,f t) := by
    have he : (fun t => H (t,u))=(Iio u).indicator (fun t => f t*g u) := rfl
    rw [he,integral_indicator measurableSet_Iio]
    change (∫ t,f t*g u ∂(volume.restrict (Ioi s)).restrict (Iio u))=_
    rw [Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio u ∩ Ioi s=Ioo s u := by ext t;simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo];tauto
    rw [hset,integral_mul_const,intervalIntegral.integral_of_le hu,integral_Ioc_eq_integral_Ioo]
    ring
  have hrightae : (fun u => ∫ t,H (t,u) ∂μ) =ᵐ[μ] (fun u => g u*(∫ t in s..u,f t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hright u hu.le
  have hleftae : (fun t => ∫ u,H (t,u) ∂μ) =ᵐ[μ] (fun t => f t*(∫ u in Ioi t,g u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hleft t ht.le
  refine ⟨hprod.integral_prod_right.congr hrightae,?_⟩
  calc
    (∫ t in Ioi s,f t*(∫ u in Ioi t,g u)) = ∫ t,∫ u,H (t,u) ∂μ ∂μ :=
      integral_congr_ae hleftae.symm
    _ = ∫ u,∫ t,H (t,u) ∂μ ∂μ := integral_integral_swap hprod
    _ = _ := integral_congr_ae hrightae
/-- All Fubini input binders hold simultaneously on the nonzero exponential
forcing and the nonzero constant kernel, throughout an infinite integration tail. -/
theorem nested_fubini_all_binder_joint_probe :
    ∃ f g : ℝ → ℝ, f 0=1 ∧ g 0=1 ∧ Continuous f ∧ Continuous g ∧
      (∀ t ≥ (0:ℝ), 0 ≤ f t) ∧ (∀ t ≥ (0:ℝ), 0 ≤ g t) ∧
      (∀ t ≥ (0:ℝ), IntegrableOn g (Ioi t)) ∧
      IntegrableOn (fun t => f t*(∫ u in Ioi t,g u)) (Ioi 0) ∧
      IntegrableOn (fun u => g u*(∫ t in (0:ℝ)..u,f t)) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ),f t*(∫ u in Ioi t,g u)) =
        ∫ u in Ioi (0:ℝ),g u*(∫ t in (0:ℝ)..u,f t) := by
  let f : ℝ → ℝ := fun _ => 1
  let g : ℝ → ℝ := fun t => Real.exp (-t)
  have hf : Continuous f := continuous_const
  have hg : Continuous g := Real.continuous_exp.comp continuous_id.neg
  have hfp : ∀ t ≥ (0:ℝ), 0 ≤ f t := fun _ _ => by norm_num [f]
  have hgp : ∀ t ≥ (0:ℝ), 0 ≤ g t := fun t _ => (Real.exp_pos (-t)).le
  have hgi : ∀ t ≥ (0:ℝ), IntegrableOn g (Ioi t) := fun t _ => integrableOn_exp_neg_Ioi t
  have he (t : ℝ) : (∫ u in Ioi t,g u)=Real.exp (-t) := by
    simpa only [g,neg_one_mul,div_neg,div_one,neg_neg] using
      integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) t
  have hoi : IntegrableOn (fun t => f t*(∫ u in Ioi t,g u)) (Ioi 0) := by
    convert integrableOn_exp_neg_Ioi 0 using 1
    funext t
    rw [he t]
    simp only [f,one_mul]
  exact ⟨f,g,rfl,by simp [g],hf,hg,hfp,hgp,hgi,hoi,
    nested_tail_fubini f g 0 hf hg hfp hgp hgi hoi⟩
end RMTFoundations.TracyWidom.HMGreenFubini
#print axioms RMTFoundations.TracyWidom.HMGreenFubini.nested_tail_fubini
#print axioms RMTFoundations.TracyWidom.HMGreenFubini.nested_fubini_all_binder_joint_probe
