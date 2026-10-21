import RMTFoundations.TracyWidom.Airy2Operator
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
/-- The physical extended kernel is continuous in both spatial coordinates at fixed times.
No assertion of continuity across equal time labels is made. -/
theorem extendedAiryKernel_continuous_spatial
    (t r : ℝ /- [definition] -/) :
    Continuous (fun p : ℝ × ℝ => extendedAiryKernel t r p.1 p.2) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate 2 (fun i => if i=0 then t else r)
  have hg : t < r → 4*a ≤ r-t := by simpa using hgap (0 : Fin 2) 1
  obtain ⟨C,hC,hAi⟩ := Ai_slow_exponential_envelope
  have hAi' := hAi a ha.le ha1
  have hAiCont : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  have heq : (fun p : ℝ × ℝ => extendedAiryKernel t r p.1 p.2) =
      (fun p => ∫ u, extendedAiryIntegrand t r p.1 p.2 u ∂halfLineMeasure) := by
    funext p
    exact extendedAiryKernel_eq_integral _ _ _ _
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro p0
  have hn1 : ∀ᶠ p : ℝ × ℝ in 𝓝 p0, p0.1-1 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by dsimp; linarith)
  have hn2 : ∀ᶠ p : ℝ × ℝ in 𝓝 p0, p0.2-1 < p.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by dsimp; linarith)
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun u : ℝ => C^2*Real.exp (-a*((p0.1-1)+(p0.2-1)))*Real.exp (-(2*a)*u))
  · exact Eventually.of_forall fun p => (extendedAiryIntegrand_integrable t r p.1 p.2).aestronglyMeasurable
  · filter_upwards [hn1,hn2] with p hp1 hp2
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    calc ‖extendedAiryIntegrand t r p.1 p.2 u‖
        ≤ C^2*Real.exp (-a*(p.1+p.2))*Real.exp (-(2*a)*u) := by
          simpa only [Real.norm_eq_abs] using
            extended_integrand_spatial_envelope C a t r p.1 p.2 u hC.le ha hAi' hu.le hg
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg C))
        (Real.exp_nonneg _)
  · exact (integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0).const_mul _
  · apply Eventually.of_forall
    intro u
    by_cases h : r ≤ t
    · simp only [extendedAiryIntegrand,if_pos h]
      fun_prop
    · simp only [extendedAiryIntegrand,if_neg h]
      fun_prop

/-- A fixed floor for all cutoffs gives one uniform physical envelope. -/
theorem shiftedExtendedKernel_lower_cut_envelope
    (m : ℕ /- [definition] -/)
    (times floor : Fin m → ℝ /- [definition] -/) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ cuts : Fin m → ℝ,
      (∀ i, floor i ≤ cuts i) → ∀ p q,
      |shiftedExtendedKernel m times cuts p q| ≤
        C*Real.exp (-a*(p.2+floor p.1))*Real.exp (-a*(q.2+floor q.1)) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate m times
  obtain ⟨D,hD,hAi⟩ := Ai_slow_exponential_envelope
  let E : ℝ := D^2 * ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
  refine ⟨a,E+1,ha,by linarith,?_⟩
  intro cuts hfloor p q
  have hp := hfloor p.1
  have hq := hfloor q.1
  have h1 : Real.exp (-a*(p.2+cuts p.1)) ≤ Real.exp (-a*(p.2+floor p.1)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-a*(q.2+cuts q.1)) ≤ Real.exp (-a*(q.2+floor q.1)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc |shiftedExtendedKernel m times cuts p q|
      ≤ E*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) :=
        extendedAiryKernel_spatial_envelope D a _ _ _ _ hD.le ha
          (hAi a ha.le ha1) (hgap p.1 q.1)
    _ ≤ E*Real.exp (-a*(p.2+floor p.1))*Real.exp (-a*(q.2+floor q.1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hE) h2 (Real.exp_nonneg _)
        (mul_nonneg hE (Real.exp_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : E ≤ E+1) (Real.exp_nonneg _))
      (Real.exp_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Joint threshold continuity of the physical multi-time Fredholm series.
This supplies the analytic continuity requirement, without a probability assumption. -/
theorem airy2FredholmCandidate_continuous_cuts
    (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) :
    Continuous (airy2FredholmCandidate m times) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  apply continuous_iff_continuousAt.mpr
  intro cuts0
  let floor : Fin m → ℝ := fun i => cuts0 i-1
  obtain ⟨a,C,ha,hC,hb⟩ := shiftedExtendedKernel_lower_cut_envelope m times floor
  have hn : ∀ᶠ cuts : Fin m → ℝ in 𝓝 cuts0, ∀ i, floor i < cuts i := by
    apply eventually_all.mpr
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).mem_nhds (by dsimp [floor]; linarith)
  change ContinuousAt (fun cuts : Fin m → ℝ => kernelFredholm (timeSpaceMeasure m)
    (shiftedExtendedKernel m times cuts) (-1)) cuts0
  apply kernelFredholm_continuousAt_of_minor_bound (timeSpaceMeasure m)
    (fun cuts => shiftedExtendedKernel m times cuts) cuts0
    (fun p => Real.exp (-a*(p.2+floor p.1))) C hC.le
    (timeSpace_exponential_square_integrable m floor a ha)
  · exact Eventually.of_forall (fun cuts => shiftedExtendedKernel_measurable m times cuts)
  · filter_upwards [hn] with cuts hc
    intro n x
    exact weighted_kernel_minor_bound_pow n (shiftedExtendedKernel m times cuts) C
      (fun p => Real.exp (-a*(p.2+floor p.1))) x hC.le (fun _ => Real.exp_nonneg _)
      (hb cuts (fun i => (hc i).le))
  · intro p q
    change ContinuousAt (fun cuts : Fin m → ℝ => extendedAiryKernel (times p.1) (times q.1)
      (p.2+cuts p.1) (q.2+cuts q.1)) cuts0
    have hf : Continuous (fun cuts : Fin m → ℝ =>
        (p.2 + cuts p.1, q.2 + cuts q.1)) := by fun_prop
    exact ((extendedAiryKernel_continuous_spatial (times p.1) (times q.1)).comp hf).continuousAt

/-- Threshold continuity and all non-event inputs are instantiated on a nonzero two-time Airy model. -/
theorem continuity_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Continuous (airy2FredholmCandidate 2 times) ∧
      Continuous (fun p : ℝ × ℝ => extendedAiryKernel (times 0) (times 1) p.1 p.2) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,airy2FredholmCandidate_continuous_cuts _ _,
    extendedAiryKernel_continuous_spatial _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_continuous_spatial
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel_lower_cut_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_continuous_cuts
#print axioms RMTFoundations.TracyWidom.Airy2.continuity_all_binder_joint_probe
