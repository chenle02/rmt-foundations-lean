import RMTFoundations.TracyWidom.Airy2
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel

/-- A common constant works for every slower exponential rate between zero and one. -/
theorem Ai_slow_exponential_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x : ℝ,
      |airyAiReal x| ≤ C * Real.exp (-a*x) := by
  obtain ⟨C0,h0p,h0⟩ := Ai_global_bounded
  obtain ⟨C1,h1p,h1⟩ := airyAiReal_abs_le_exp'
  refine ⟨max C0 C1, lt_of_lt_of_le h0p (le_max_left _ _), ?_⟩
  intro a ha ha1 x
  by_cases hx : 0 ≤ x
  · calc |airyAiReal x| ≤ C1 * Real.exp (-x) := h1 x
      _ ≤ max C0 C1 * Real.exp (-a*x) :=
        mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by nlinarith))
          (Real.exp_nonneg _) (le_trans h1p.le (le_max_right _ _))
  · have he : 1 ≤ Real.exp (-a*x) := Real.one_le_exp_iff.mpr (by nlinarith)
    calc |airyAiReal x| ≤ C0 := h0 x
      _ ≤ max C0 C1 := le_max_left _ _
      _ ≤ max C0 C1 * Real.exp (-a*x) :=
        le_mul_of_one_le_right (le_trans h0p.le (le_max_left _ _)) he

/-- The spectral integrand is controlled by a single integrable exponential.
The affine slope is +1 in the forward branch and -1 in the backward branch. -/
theorem weighted_integrand_spatial_envelope
    (C a d b x y u : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C * Real.exp (-a*z) /- [standing] -/)
    (hu : 0 ≤ u /- [standing] -/)
    (hdec : 2*a ≤ d+2*a*b /- [standing] -/) :
    |Real.exp (-d*u) * airyAiReal (x+b*u) * airyAiReal (y+b*u)| ≤
      C^2 * Real.exp (-a*(x+y)) * Real.exp (-(2*a)*u) := by
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-d*u) * |airyAiReal (x+b*u)| * |airyAiReal (y+b*u)|
      ≤ Real.exp (-d*u) * (C*Real.exp (-a*(x+b*u))) *
          (C*Real.exp (-a*(y+b*u))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hAi _) (Real.exp_nonneg _)) (hAi _)
          (abs_nonneg _) (mul_nonneg (Real.exp_nonneg _) (by positivity))
    _ = C^2 * Real.exp (-a*(x+y)) * Real.exp (-(d+2*a*b)*u) := by
      rw [show -(d+2*a*b)*u = -d*u + (-a*b*u + -a*b*u) by ring,
        show -a*(x+b*u) = -a*x + -a*b*u by ring,
        show -a*(y+b*u) = -a*y + -a*b*u by ring,
        show -a*(x+y) = -a*x + -a*y by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ C^2 * Real.exp (-a*(x+y)) * Real.exp (-(2*a)*u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

/-- A positive rate below a quarter of every backward gap controls both physical branches. -/
theorem extended_integrand_spatial_envelope
    (C a t r x y u : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (_ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C * Real.exp (-a*z) /- [standing] -/)
    (hu : 0 ≤ u /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    |extendedAiryIntegrand t r x y u| ≤
      C^2 * Real.exp (-a*(x+y)) * Real.exp (-(2*a)*u) := by
  by_cases h : r ≤ t
  · simpa [extendedAiryIntegrand,h] using
      weighted_integrand_spatial_envelope C a (t-r) 1 x y u hC hAi hu (by linarith [_ha])
  · have hg := hgap (lt_of_not_ge h)
    simpa [extendedAiryIntegrand,h,sub_eq_add_neg] using
      weighted_integrand_spatial_envelope C a (r-t) (-1) x y u hC hAi hu (by linarith [_ha])

/-- Nonzero physical Airy data simultaneously satisfy every estimate at a real backward gap. -/
theorem spatial_envelope_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ C : ℝ, 0 < C ∧
    (∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-(1/4 : ℝ)*z)) ∧
    (∀ x y u : ℝ, 0 ≤ u →
      |extendedAiryIntegrand 0 1 x y u| ≤
        C^2*Real.exp (-(1/4 : ℝ)*(x+y))*Real.exp (-(1/2 : ℝ)*u)) := by
  obtain ⟨C,hC,hAi⟩ := Ai_slow_exponential_envelope
  have h := hAi (1/4) (by norm_num) (by norm_num)
  refine ⟨airyAiReal_zero_pos.ne',C,hC,h,?_⟩
  intro x y u hu
  convert extended_integrand_spatial_envelope C (1/4) 0 1 x y u hC.le
    (by norm_num) h hu (by norm_num) using 1
  norm_num

/-- A single positive rate can be chosen for every strict gap in any finite time family.
Repeated times do not obstruct analytic convergence; their probability interpretation is separate. -/
theorem finiteTime_positive_rate
    (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ i j, times i < times j → 4*a ≤ times j-times i := by
  classical
  let f : Fin m × Fin m → ℝ := fun p =>
    if times p.1 < times p.2 then 4/(times p.2-times p.1) else 0
  let S : ℝ := ∑ p, f p
  have hf : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs with h
    · positivity
    · rfl
  have hS : 0 ≤ S := Finset.sum_nonneg (fun p _ => hf p)
  let a : ℝ := (S+1)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : (S+1)*a = 1 := mul_inv_cancel₀ (by linarith)
  refine ⟨a,ha,?_,?_⟩
  · have := mul_le_mul_of_nonneg_right (show 1 ≤ S+1 by linarith) ha.le
    simpa [hae] using this
  · intro i j hij
    have hg : 0 < times j-times i := sub_pos.mpr hij
    have hterm : 4/(times j-times i) ≤ S := by
      have := Finset.single_le_sum (fun p _ => hf p) (Finset.mem_univ (i,j))
      simpa [f,hij] using this
    calc
      4*a = (4/(times j-times i))*((times j-times i)*a) := by
        rw [← mul_assoc,div_mul_cancel₀ _ hg.ne']
      _ ≤ (S+1)*((times j-times i)*a) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hg.le ha.le)
      _ = times j-times i := by nlinarith [hae]

/-- Physical branch decay integrated without a conditional operator or probability hypothesis. -/
theorem extendedAiryKernel_spatial_envelope
    (C a t r x y : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    |extendedAiryKernel t r x y| ≤
      (C^2 * ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure) *
        Real.exp (-a*x) * Real.exp (-a*y) := by
  have he : Integrable (fun u : ℝ => Real.exp (-(2*a)*u)) halfLineMeasure :=
    integrableOn_exp_mul_Ioi (by linarith : -(2*a) < 0) 0
  have hb := he.const_mul (C^2*Real.exp (-a*(x+y)))
  rw [extendedAiryKernel_eq_integral]
  calc |∫ u, extendedAiryIntegrand t r x y u ∂halfLineMeasure|
      ≤ ∫ u, |extendedAiryIntegrand t r x y u| ∂halfLineMeasure :=
        by simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (extendedAiryIntegrand t r x y) (μ := halfLineMeasure))
    _ ≤ ∫ u, C^2*Real.exp (-a*(x+y))*Real.exp (-(2*a)*u) ∂halfLineMeasure := by
      apply integral_mono_ae (extendedAiryIntegrand_integrable t r x y).norm hb
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      exact extended_integrand_spatial_envelope C a t r x y u hC ha hAi hu.le hgap
    _ = _ := by
      rw [integral_const_mul, show -a*(x+y) = -a*x + -a*y by ring,Real.exp_add]
      ring

/-- A common physical envelope on the exact finite time/cut domain. -/
theorem shiftedExtendedKernel_envelope
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ p q,
      |shiftedExtendedKernel m times cuts p q| ≤
        C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate m times
  obtain ⟨D,hD,hAi⟩ := Ai_slow_exponential_envelope
  let E : ℝ := D^2 * ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
  refine ⟨a,E+1,ha,by linarith,?_⟩
  intro p q
  exact (extendedAiryKernel_spatial_envelope D a _ _ _ _ hD.le ha
    (hAi a ha.le ha1) (hgap p.1 q.1)).trans
      (by dsimp [E]; gcongr; linarith)

/-- The physical exponential weight is square integrable on the actual finite union of half-lines. -/
theorem timeSpace_exponential_square_integrable
    (m : ℕ /- [definition] -/)
    (cuts : Fin m → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/) :
    Integrable (fun p : TimeSpace m => Real.exp (-a*(p.2+cuts p.1))^2)
      (timeSpaceMeasure m) := by
  have hf : Integrable (fun i : Fin m => Real.exp (-a*cuts i)^2) Measure.count :=
    integrable_count_iff.mpr (summable_of_hasFiniteSupport (Set.toFinite _))
  have hg : Integrable (fun x : ℝ => Real.exp (-a*x)^2) halfLineMeasure := by
    have heq : (fun x : ℝ => Real.exp (-a*x)^2) =
        (fun x : ℝ => Real.exp (-(2*a)*x)) := by
      funext x
      rw [sq,← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0
  change Integrable (fun p : TimeSpace m => Real.exp (-a*(p.2+cuts p.1))^2)
    (Measure.count.prod halfLineMeasure)
  convert hf.mul_prod hg using 1
  funext p
  rw [show -a*(p.2+cuts p.1) = -a*cuts p.1 + -a*p.2 by ring,Real.exp_add,mul_pow]

/-- The actual multi-time Fredholm series converges absolutely at every complex parameter. -/
theorem airy2Fredholm_absolute
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    Summable (fun n => ‖(kernelCoefficient (timeSpaceMeasure m)
      (shiftedExtendedKernel m times cuts) n : ℂ)*z^n‖) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨a,C,ha,hC,hb⟩ := shiftedExtendedKernel_envelope m times cuts
  apply kernelFredholm_absolute_of_minor_bound (timeSpaceMeasure m)
    (shiftedExtendedKernel m times cuts) (fun p => Real.exp (-a*(p.2+cuts p.1))) C hC.le
    (timeSpace_exponential_square_integrable m cuts a ha) _ z
  intro n x
  exact weighted_kernel_minor_bound_pow n _ C _ x hC.le (fun _ => Real.exp_nonneg _) hb

/-- Entire dependence on the determinant parameter for the physical multi-time kernel. -/
theorem airy2Fredholm_entire
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    AnalyticOnNhd ℂ (kernelFredholm (timeSpaceMeasure m)
      (shiftedExtendedKernel m times cuts)) Set.univ := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨a,C,ha,hC,hb⟩ := shiftedExtendedKernel_envelope m times cuts
  apply kernelFredholm_entire_of_minor_bound (timeSpaceMeasure m)
    (shiftedExtendedKernel m times cuts) (fun p => Real.exp (-a*(p.2+cuts p.1))) C hC.le
    (timeSpace_exponential_square_integrable m cuts a ha)
  intro n x
  exact weighted_kernel_minor_bound_pow n _ C _ x hC.le (fun _ => Real.exp_nonneg _) hb

/-- Joint convergence and an actual nonzero complex parameter on two distinct physical time slices. -/
theorem series_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Summable (fun n => ‖(kernelCoefficient (timeSpaceMeasure 2)
        (shiftedExtendedKernel 2 times cuts) n : ℂ)*(-1 : ℂ)^n‖) ∧
      AnalyticOnNhd ℂ (kernelFredholm (timeSpaceMeasure 2)
        (shiftedExtendedKernel 2 times cuts)) Set.univ := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,airy2Fredholm_absolute _ _ _ _,airy2Fredholm_entire _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij

end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.Ai_slow_exponential_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.weighted_integrand_spatial_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.extended_integrand_spatial_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.spatial_envelope_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.finiteTime_positive_rate
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_spatial_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_exponential_square_integrable
#print axioms RMTFoundations.TracyWidom.Airy2.airy2Fredholm_absolute
#print axioms RMTFoundations.TracyWidom.Airy2.airy2Fredholm_entire
#print axioms RMTFoundations.TracyWidom.Airy2.series_all_binder_joint_probe
