import RMTFoundations.TracyWidom.Airy2Decay
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open MeasureTheory Set Filter
open RMTFoundations.Airy RMTFoundations.AiryKernel
/-- The physical block integrand is measurable jointly in space and spectral coordinate. -/
theorem shiftedExtendedIntegrand_measurable
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    Measurable (fun z : (TimeSpace m × TimeSpace m) × ℝ =>
      extendedAiryIntegrand (times z.1.1.1) (times z.1.2.1)
        (z.1.1.2+cuts z.1.1.1) (z.1.2.2+cuts z.1.2.1) z.2) := by
  unfold extendedAiryIntegrand
  have hAi : Measurable airyAiReal := measurable_airyAiReal
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

/-- Integrating the measurable physical branches gives the actual measurable block kernel. -/
theorem shiftedExtendedKernel_measurable
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    Measurable (Function.uncurry (shiftedExtendedKernel m times cuts)) := by
  have h := (shiftedExtendedIntegrand_measurable m times cuts).stronglyMeasurable.integral_prod_right'
    (ν := halfLineMeasure)
  have he : Function.uncurry (shiftedExtendedKernel m times cuts) =
      (fun p : TimeSpace m × TimeSpace m => ∫ u,
        extendedAiryIntegrand (times p.1.1) (times p.2.1)
          (p.1.2+cuts p.1.1) (p.2.2+cuts p.2.1) u ∂halfLineMeasure) := by
    funext p
    exact extendedAiryKernel_eq_integral _ _ _ _
  rw [he]
  exact h.measurable

/-- Measurability is instantiated at distinct times and mixed cuts on nonzero Airy data. -/
theorem measurable_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Measurable (Function.uncurry (shiftedExtendedKernel 2 times cuts)) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,shiftedExtendedKernel_measurable _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij
/-- A common threshold shift has an explicit vanishing envelope for every physical block. -/
theorem shiftedExtendedKernel_shift_envelope
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ s p q,
      |shiftedExtendedKernel m times (fun i => cuts i+s) p q| ≤
        (C*Real.exp (-a*s)^2)*Real.exp (-a*(p.2+cuts p.1))*
          Real.exp (-a*(q.2+cuts q.1)) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate m times
  obtain ⟨D,hD,hAi⟩ := Ai_slow_exponential_envelope
  let E : ℝ := D^2 * ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
  refine ⟨a,E+1,ha,by linarith,?_⟩
  intro s p q
  have hb := extendedAiryKernel_spatial_envelope D a (times p.1) (times q.1)
    (p.2+(cuts p.1+s)) (q.2+(cuts q.1+s)) hD.le ha (hAi a ha.le ha1) (hgap p.1 q.1)
  calc |shiftedExtendedKernel m times (fun i => cuts i+s) p q|
      ≤ E*Real.exp (-a*(p.2+(cuts p.1+s)))*Real.exp (-a*(q.2+(cuts q.1+s))) := hb
    _ = (E*Real.exp (-a*s)^2)*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) := by
      rw [show -a*(p.2+(cuts p.1+s)) = -a*(p.2+cuts p.1)+(-a*s) by ring,
        show -a*(q.2+(cuts q.1+s)) = -a*(q.2+cuts q.1)+(-a*s) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := by gcongr; linarith

/-- Raising every cutoff sends the physical multi-time series to the empty-event normalization.
This is a proved analytic limit; it does not assert positivity of rectangle increments. -/
theorem airy2FredholmCandidate_tendsto_common_shift_one
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    Tendsto (fun s : ℝ => airy2FredholmCandidate m times (fun i => cuts i+s))
      atTop (𝓝 1) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨a,C,ha,hC,hb⟩ := shiftedExtendedKernel_shift_envelope m times cuts
  have he : Tendsto (fun s : ℝ => Real.exp (-a*s)) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def,id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop ha tendsto_id)
  unfold airy2FredholmCandidate
  suffices hn : Tendsto
      (fun s : ℝ => kernelFredholm (timeSpaceMeasure m)
        (shiftedExtendedKernel m times (fun i => cuts i+s)) (-1)) atTop
      (𝓝 (kernelFredholm (timeSpaceMeasure m) (fun _ _ => 0) (-1))) by
    simpa only [kernelFredholm_zero_kernel] using hn
  apply kernelFredholm_tendsto_of_minor_bound (timeSpaceMeasure m) atTop
    (fun s => shiftedExtendedKernel m times (fun i => cuts i+s))
    (fun _ _ => 0) (fun p => Real.exp (-a*(p.2+cuts p.1))) C hC.le
    (timeSpace_exponential_square_integrable m cuts a ha)
  · exact Eventually.of_forall (fun s => shiftedExtendedKernel_measurable m times _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    intro n x
    have hkernel : ∀ p q : TimeSpace m,
        |shiftedExtendedKernel m times (fun i => cuts i+s) p q| ≤
          C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) := by
      intro p q
      have he1 : Real.exp (-a*s)^2 ≤ 1 := by
        have h := Real.exp_le_one_iff.mpr (show -a*s ≤ 0 by nlinarith)
        nlinarith [Real.exp_nonneg (-a*s)]
      have hc : C * Real.exp (-a*s)^2 ≤ C := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hC.le
      exact (hb s p q).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) (Real.exp_nonneg _))
    exact weighted_kernel_minor_bound_pow n
      (shiftedExtendedKernel m times (fun i => cuts i+s)) C
      (fun p => Real.exp (-a*(p.2+cuts p.1))) x hC.le (fun _ => Real.exp_nonneg _) hkernel
  · intro p q
    apply squeeze_zero_norm'
    · exact Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hb s p q)
    · simpa using (((he.pow 2).const_mul C).mul_const
        (Real.exp (-a*(p.2+cuts p.1)))).mul_const (Real.exp (-a*(q.2+cuts q.1)))

/-- The entire physical block kernel is square integrable on its actual Hilbert-space domain. -/
theorem shiftedExtendedKernel_memLp_two
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    MemLp (Function.uncurry (shiftedExtendedKernel m times cuts)) 2
      ((timeSpaceMeasure m).prod (timeSpaceMeasure m)) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨a,C,ha,hC,hb⟩ := shiftedExtendedKernel_envelope m times cuts
  have hm := shiftedExtendedKernel_measurable m times cuts
  have hw := timeSpace_exponential_square_integrable m cuts a ha
  have hi := (hw.mul_prod hw).const_mul (C^2)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hi.mono' (hm.pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  have h := pow_le_pow_left₀ (abs_nonneg _) (hb p.1 p.2) 2
  simpa only [Real.norm_of_nonneg (sq_nonneg _),sq_abs,mul_pow,mul_assoc,Function.uncurry] using h

/-- The actual extended Airy integral operator; no trace-class assertion is built into its type. -/
noncomputable def extendedAiryOperator
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    TimeSpaceL2 m →L[ℝ] TimeSpaceL2 m := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  exact kernelOperator (shiftedExtendedKernel_memLp_two m times cuts)

/-- The physical operator is Hilbert–Schmidt. This does not upgrade it to trace class. -/
theorem extendedAiryOperator_isHilbertSchmidt
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    IsHilbertSchmidt (extendedAiryOperator m times cuts) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  exact isHilbertSchmidt_kernelOperator (shiftedExtendedKernel_memLp_two m times cuts)

/-- The realized physical extended operator is compact. -/
theorem extendedAiryOperator_isCompact
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    IsCompactOperator (extendedAiryOperator m times cuts) :=
  (extendedAiryOperator_isHilbertSchmidt m times cuts).isCompactOperator

/-- All physical normalization and operator binders hold jointly at two strictly ordered times. -/
theorem operator_normalization_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Tendsto (fun s : ℝ => airy2FredholmCandidate 2 times (fun i => cuts i+s)) atTop (𝓝 1) ∧
      MemLp (Function.uncurry (shiftedExtendedKernel 2 times cuts)) 2
        ((timeSpaceMeasure 2).prod (timeSpaceMeasure 2)) ∧
      IsHilbertSchmidt (extendedAiryOperator 2 times cuts) ∧
      IsCompactOperator (extendedAiryOperator 2 times cuts) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,airy2FredholmCandidate_tendsto_common_shift_one _ _ _,
    shiftedExtendedKernel_memLp_two _ _ _,extendedAiryOperator_isHilbertSchmidt _ _ _,
    extendedAiryOperator_isCompact _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedIntegrand_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.measurable_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel_shift_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_tendsto_common_shift_one
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel_memLp_two
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryOperator
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryOperator_isHilbertSchmidt
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryOperator_isCompact
#print axioms RMTFoundations.TracyWidom.Airy2.operator_normalization_all_binder_joint_probe
