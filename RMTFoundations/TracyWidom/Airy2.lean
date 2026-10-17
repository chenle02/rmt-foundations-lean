import RMTFoundations.TracyWidom.Distribution

/-! Extended Airy kernel and checked one-time seams. The multi-time Fredholm
expression below is a candidate, not a certified probability distribution.
No process-existence or multi-time probability input is assumed. -/


set_option autoImplicit false

namespace RMTFoundations.TracyWidom.Airy2

open MeasureTheory Set Filter
open scoped Topology Matrix
open RMTFoundations.Airy
open RMTFoundations.AiryKernel

/-- The two time branches, with the negative-energy integral parametrized by u > 0.
The exponential signs agree with the standard extended Airy kernel convention. -/
noncomputable def extendedAiryKernel
    (t r x y : ℝ /- [definition] -/) : ℝ :=
  if r ≤ t then
    ∫ u in Ioi (0 : ℝ), Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (y+u)
  else
    -(∫ u in Ioi (0 : ℝ), Real.exp (-(r-t)*u) * airyAiReal (x-u) * airyAiReal (y-u))

/-- The forward branch is stated without changing its exponential weight. -/
theorem extendedAiryKernel_forward
    (t r x y : ℝ /- [definition] -/)
    (h : r ≤ t /- [standing] -/) :
    extendedAiryKernel t r x y =
      ∫ u in Ioi (0 : ℝ), Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (y+u) := by
  simp only [extendedAiryKernel, if_pos h]

/-- The backward branch retains the essential minus sign. -/
theorem extendedAiryKernel_backward
    (t r x y : ℝ /- [definition] -/)
    (h : t < r /- [standing] -/) :
    extendedAiryKernel t r x y =
      -(∫ u in Ioi (0 : ℝ), Real.exp (-(r-t)*u) * airyAiReal (x-u) * airyAiReal (y-u)) := by
  simp only [extendedAiryKernel, if_neg (not_le.mpr h)]

/-- At equal times the physical scalar Airy kernel is recovered. -/
theorem extendedAiryKernel_equal_time
    (t x y : ℝ /- [definition] -/) :
    extendedAiryKernel t t x y = airyKernelIntegral x y := by
  simp [extendedAiryKernel, airyKernelIntegral]

/-- Common time translation leaves both branches unchanged. -/
theorem extendedAiryKernel_time_translate
    (t r c x y : ℝ /- [definition] -/) :
    extendedAiryKernel (t+c) (r+c) x y = extendedAiryKernel t r x y := by
  simp only [extendedAiryKernel, add_le_add_iff_right, add_sub_add_right_eq_sub]

/-- Positive-half-line coordinates for the finite disjoint union of time slices. -/
abbrev TimeSpace (m : ℕ /- [definition] -/) := Fin m × ℝ

/-- Counting measure on time labels, Lebesgue measure on the shifted tail coordinates. -/
noncomputable def timeSpaceMeasure
    (m : ℕ /- [definition] -/) : Measure (TimeSpace m) :=
  Measure.count.prod halfLineMeasure

/-- The Hilbert space on which the proposed block kernel is to be realized. -/
noncomputable abbrev TimeSpaceL2 (m : ℕ /- [definition] -/) := Lp ℝ 2 (timeSpaceMeasure m)

/-- Thresholds are translated independently on each time slice. -/
noncomputable def shiftedExtendedKernel
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (p q : TimeSpace m /- [definition] -/) : ℝ :=
  extendedAiryKernel (times p.1) (times q.1) (p.2+cuts p.1) (q.2+cuts q.1)

/-- A formal Fredholm-series value. Absolute convergence, operator realization,
and the probability/consistency properties are separate open obligations. -/
noncomputable def airy2FredholmCandidate
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) : ℂ :=
  kernelFredholm (timeSpaceMeasure m) (shiftedExtendedKernel m times cuts) (-1)

/-- Time translation of the whole formal finite-dimensional expression. -/
theorem airy2FredholmCandidate_time_translate
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (c : ℝ /- [definition] -/) :
    airy2FredholmCandidate m (fun i => times i+c) cuts =
      airy2FredholmCandidate m times cuts := by
  have hk : shiftedExtendedKernel m (fun i => times i+c) cuts =
      shiftedExtendedKernel m times cuts := by
    funext p q
    exact extendedAiryKernel_time_translate _ _ _ _ _
  unfold airy2FredholmCandidate
  rw [hk]

/-- The physical one-time scalar kernel formula, before relabeling into TimeSpace 1. -/
noncomputable def oneTimeFredholm
    (t s : ℝ /- [definition] -/) : ℂ :=
  kernelFredholm halfLineMeasure (fun x y => extendedAiryKernel t t (x+s) (y+s)) (-1)

/-- This one-time expression equals the TW2 Fredholm function. -/
theorem oneTimeFredholm_eq_TW2
    (t s : ℝ /- [definition] -/) :
    oneTimeFredholm t s = RMTFoundations.TracyWidom.TW2 s := by
  simp only [oneTimeFredholm, extendedAiryKernel_equal_time]
  rfl

/-- All one-time probability properties jointly hold on the actual nonzero Airy data.
This does not assert that the multi-time candidate is a probability distribution. -/
theorem oneTime_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    (∀ t s : ℝ, oneTimeFredholm t s = RMTFoundations.TracyWidom.TW2 s) ∧
    Monotone RMTFoundations.TracyWidom.TW2R ∧
    Continuous RMTFoundations.TracyWidom.TW2R ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atBot (𝓝 0) ∧
    Tendsto RMTFoundations.TracyWidom.TW2R atTop (𝓝 1) := by
  exact ⟨airyAiReal_zero_pos.ne', oneTimeFredholm_eq_TW2,
    RMTFoundations.TracyWidom.monotone_TW2R,
    RMTFoundations.TracyWidom.continuous_TW2R,
    RMTFoundations.TracyWidom.tendsto_TW2R_atBot,
    RMTFoundations.TracyWidom.tendsto_TW2R_atTop⟩

/-- Exact finite-block determinant accounting; diagonal bounds omit the mixed product. -/
theorem two_site_determinant
    (a b u v : ℝ /- [definition] -/) :
    (1 - (!![a, u; v, b] : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (1-a)*(1-b)-u*v := by
  simp [Matrix.det_fin_two]

/-- A symmetric block with individually positive strictly contractive diagonal slices.
Its full determinant is negative. This is not a physical Airy-kernel instance. -/
theorem diagonal_contractions_joint_counterinstance :
    ∃ K : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i, 0 < K i i ∧ K i i < 1) ∧
      K 0 1 = K 1 0 ∧ K 0 1 ≠ 0 ∧ (1-K).det < 0 := by
  refine ⟨!![(1/2 : ℝ), 1; 1, (1/2 : ℝ)], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num
  · norm_num
  · rw [two_site_determinant]
    norm_num

/-- Both branch-order hypotheses and a nonzero time translation are jointly satisfiable. -/
theorem kernel_branch_all_binder_joint_probe :
    (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1 ∧ (3 : ℝ) ≠ 0 ∧
    extendedAiryKernel 1 0 0 0 =
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * airyAiReal u * airyAiReal u ∧
    extendedAiryKernel 0 1 0 0 =
      -(∫ u in Ioi (0 : ℝ), Real.exp (-u) * airyAiReal (-u) * airyAiReal (-u)) ∧
    extendedAiryKernel 4 3 0 0 = extendedAiryKernel 1 0 0 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simpa using extendedAiryKernel_forward 1 0 0 0 (by norm_num)
  · simpa using extendedAiryKernel_backward 0 1 0 0 (by norm_num)
  · convert extendedAiryKernel_time_translate 1 0 3 0 0 using 1; norm_num


/-- Exact relabeling of the singleton time slice; no probability assertion is encoded. -/
def singletonEquiv : ℝ ≃ᵐ TimeSpace 1 where
  toFun x := (0,x)
  invFun p := p.2
  left_inv x := rfl
  right_inv p := by
    rcases p with ⟨i,x⟩
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [hi]
  measurable_toFun := measurable_prodMk_left
  measurable_invFun := measurable_snd

/-- Counting measure on a singleton is exactly its Dirac mass. -/
theorem singleton_measurePreserving :
    MeasurePreserving singletonEquiv halfLineMeasure (timeSpaceMeasure 1) := by
  refine ⟨singletonEquiv.measurable, ?_⟩
  change Measure.map (fun x : ℝ => ((0 : Fin 1),x)) halfLineMeasure =
    (Measure.count : Measure (Fin 1)).prod halfLineMeasure
  rw [Subsingleton.count_eq_dirac (0 : Fin 1), Measure.dirac_prod]

/-- The relabeling acts at every integration variable of the Fredholm coefficient. -/
theorem kernelCoefficient_singleton
    (k : TimeSpace 1 → TimeSpace 1 → ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    kernelCoefficient halfLineMeasure (fun x y => k (0,x) (0,y)) n =
      kernelCoefficient (timeSpaceMeasure 1) k n := by
  letI : SigmaFinite (timeSpaceMeasure 1) := by
    unfold timeSpaceMeasure
    infer_instance
  unfold kernelCoefficient
  congr 1
  exact (measurePreserving_pi _ _ (fun _ : Fin n => singleton_measurePreserving)).integral_comp
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => singletonEquiv)).measurableEmbedding
    (kernelMinor k n)

/-- The same exact relabeling holds for the formal Fredholm series. -/
theorem kernelFredholm_singleton
    (k : TimeSpace 1 → TimeSpace 1 → ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    kernelFredholm halfLineMeasure (fun x y => k (0,x) (0,y)) z =
      kernelFredholm (timeSpaceMeasure 1) k z := by
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  dsimp only
  rw [kernelCoefficient_singleton]

/-- The singleton slice of the actual multi-time candidate equals TW2. -/
theorem airy2FredholmCandidate_one_time
    (times cuts : Fin 1 → ℝ /- [definition] -/) :
    airy2FredholmCandidate 1 times cuts =
      RMTFoundations.TracyWidom.TW2 (cuts 0) := by
  unfold airy2FredholmCandidate
  rw [← kernelFredholm_singleton]
  change oneTimeFredholm (times 0) (cuts 0) = _
  exact oneTimeFredholm_eq_TW2 _ _

/-- All singleton transport binders are instantiated on physical nonzero data. -/
theorem singleton_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    airy2FredholmCandidate 1 (fun _ => 3) (fun _ => -1) =
      RMTFoundations.TracyWidom.TW2 (-1) ∧
    MeasurePreserving singletonEquiv halfLineMeasure (timeSpaceMeasure 1) := by
  exact ⟨airyAiReal_zero_pos.ne', airy2FredholmCandidate_one_time _ _,
    singleton_measurePreserving⟩

open MeasureTheory Set Filter
open RMTFoundations.Airy

/-- The negative-half bound and positive-half decay give a single physical global bound. -/
theorem Ai_global_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |airyAiReal x| ≤ C := by
  obtain ⟨C0,h0⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨C1,h1pos,h1⟩ := airyAiReal_abs_le_exp'
  have h0nn : 0 ≤ C0 := (abs_nonneg _).trans (h0 0 le_rfl)
  refine ⟨C0+C1+1, by linarith, ?_⟩
  intro x
  by_cases hx : x ≤ 0
  · exact (h0 x hx).trans (by linarith)
  · have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hi := (h1 x).trans (mul_le_mul_of_nonneg_left he h1pos.le)
    simp only [mul_one] at hi
    linarith

/-- Both positive and negative spectral branches are absolutely integrable at a
strict time gap; the oscillatory negative branch uses global boundedness. -/
theorem Ai_weighted_product_integrable
    (d x y a : ℝ /- [definition] -/)
    (hd : 0 < d /- [standing] -/) :
    Integrable (fun u : ℝ => Real.exp (-d*u) * airyAiReal (x+a*u) * airyAiReal (y+a*u))
      halfLineMeasure := by
  obtain ⟨C,hCpos,hC⟩ := Ai_global_bounded
  have hi : Integrable (fun u : ℝ => C^2 * Real.exp (-d*u)) halfLineMeasure :=
    (integrableOn_exp_mul_Ioi (by linarith : -d < 0) 0).const_mul (C^2)
  have hm : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-d*u) * airyAiReal (x+a*u) * airyAiReal (y+a*u))
      halfLineMeasure := by
    apply Continuous.aestronglyMeasurable
    have hc : Continuous airyAiReal :=
      continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airyAiReal z).continuousAt
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hc.comp (continuous_const.add (continuous_const.mul continuous_id)))).mul
      (hc.comp (continuous_const.add (continuous_const.mul continuous_id)))
  apply hi.mono' hm
  apply Eventually.of_forall
  intro u
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-d*u) * |airyAiReal (x+a*u)| * |airyAiReal (y+a*u)|
      ≤ Real.exp (-d*u) * C * C :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hC _) (Real.exp_nonneg _)) (hC _)
          (abs_nonneg _) (mul_nonneg (Real.exp_nonneg _) hCpos.le)
    _ = C^2 * Real.exp (-d*u) := by ring

/-- The global bound and both strict-gap integrability bounds hold together on
nonzero physical Airy data with nonzero space and time separation. -/
theorem integrability_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |airyAiReal x| ≤ C) ∧
    Integrable (fun u : ℝ => Real.exp (-u) * airyAiReal u * airyAiReal (1+u)) halfLineMeasure ∧
    Integrable (fun u : ℝ => Real.exp (-u) * airyAiReal (-u) * airyAiReal (1-u)) halfLineMeasure := by
  refine ⟨airyAiReal_zero_pos.ne', Ai_global_bounded, ?_, ?_⟩
  · simpa using Ai_weighted_product_integrable 1 0 1 1 (by norm_num)
  · simpa [sub_eq_add_neg] using Ai_weighted_product_integrable 1 0 1 (-1) (by norm_num)


/-- The signed integrand of the physical extended kernel. -/
noncomputable def extendedAiryIntegrand
    (t r x y u : ℝ /- [definition] -/) : ℝ :=
  if r ≤ t then Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (y+u)
  else -(Real.exp (-(r-t)*u) * airyAiReal (x-u) * airyAiReal (y-u))

/-- Every branch of the physical kernel is an ordinary absolutely convergent integral,
including equal times; this removes the scalar Bochner-integral fallback issue. -/
theorem extendedAiryIntegrand_integrable
    (t r x y : ℝ /- [definition] -/) :
    Integrable (extendedAiryIntegrand t r x y) halfLineMeasure := by
  change Integrable (fun u : ℝ => if r ≤ t then
    Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (y+u)
    else -(Real.exp (-(r-t)*u) * airyAiReal (x-u) * airyAiReal (y-u))) halfLineMeasure
  by_cases h : r ≤ t
  · by_cases he : r = t
    · subst r
      simpa [IntegrableOn, halfLineMeasure] using integrable_airyAiReal_mul_Ioi x y
    · have hd : 0 < t-r := sub_pos.mpr (lt_of_le_of_ne h he)
      simpa [h] using Ai_weighted_product_integrable (t-r) x y 1 hd
  · have hd : 0 < r-t := sub_pos.mpr (lt_of_not_ge h)
    simpa [h, sub_eq_add_neg] using
      (Ai_weighted_product_integrable (r-t) x y (-1) hd).neg

/-- The signed-integrand realization is literally the defined extended Airy kernel. -/
theorem extendedAiryKernel_eq_integral
    (t r x y : ℝ /- [definition] -/) :
    extendedAiryKernel t r x y = ∫ u, extendedAiryIntegrand t r x y u ∂halfLineMeasure := by
  by_cases h : r ≤ t
  · simp [extendedAiryKernel, extendedAiryIntegrand, h, halfLineMeasure]
  · simp [extendedAiryKernel, extendedAiryIntegrand, h, halfLineMeasure, integral_neg]

/-- Joint physical realizations at all time orders, on a nonzero Airy instance. -/
theorem extended_integral_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    (∀ t r x y : ℝ, Integrable (extendedAiryIntegrand t r x y) halfLineMeasure ∧
      extendedAiryKernel t r x y = ∫ u, extendedAiryIntegrand t r x y u ∂halfLineMeasure) := by
  exact ⟨airyAiReal_zero_pos.ne', fun t r x y =>
    ⟨extendedAiryIntegrand_integrable t r x y, extendedAiryKernel_eq_integral t r x y⟩⟩


/-- Merely duplicating the same finite time slice changes its gap determinant.
A repeated-time process law instead reduces to the single slice with minimum cutoff. -/
theorem duplicated_slice_joint_counterinstance :
    ∃ K : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j, K i j = (1/2 : ℝ)) ∧
      (∀ i, 0 < K i i ∧ K i i < 1) ∧
      (1-K).det = 0 ∧ 1-K 0 0 = (1/2 : ℝ) := by
  refine ⟨!![(1/2 : ℝ), (1/2 : ℝ); (1/2 : ℝ), (1/2 : ℝ)], ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · rw [two_site_determinant]
    norm_num
  · norm_num

/-- Distinct ordered times, mixed nonzero thresholds and a nonzero common time shift
jointly inhabit the formal expression's intended future probability domain. -/
theorem multiTime_domain_all_binder_joint_probe :
    ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      airy2FredholmCandidate 2 (fun i => times i+3) cuts =
        airy2FredholmCandidate 2 times cuts := by
  refine ⟨fun i => (i.val : ℝ), fun i => if i=0 then -1 else 1, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · norm_num
  · norm_num
  · exact airy2FredholmCandidate_time_translate _ _ _ _

end RMTFoundations.TracyWidom.Airy2

#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_forward
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_backward
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_equal_time
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_time_translate
#print axioms RMTFoundations.TracyWidom.Airy2.TimeSpace
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceMeasure
#print axioms RMTFoundations.TracyWidom.Airy2.TimeSpaceL2
#print axioms RMTFoundations.TracyWidom.Airy2.shiftedExtendedKernel
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_time_translate
#print axioms RMTFoundations.TracyWidom.Airy2.oneTimeFredholm
#print axioms RMTFoundations.TracyWidom.Airy2.oneTimeFredholm_eq_TW2
#print axioms RMTFoundations.TracyWidom.Airy2.oneTime_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.two_site_determinant
#print axioms RMTFoundations.TracyWidom.Airy2.diagonal_contractions_joint_counterinstance
#print axioms RMTFoundations.TracyWidom.Airy2.kernel_branch_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.singletonEquiv
#print axioms RMTFoundations.TracyWidom.Airy2.singleton_measurePreserving
#print axioms RMTFoundations.TracyWidom.Airy2.kernelCoefficient_singleton
#print axioms RMTFoundations.TracyWidom.Airy2.kernelFredholm_singleton
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_one_time
#print axioms RMTFoundations.TracyWidom.Airy2.singleton_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.Ai_global_bounded
#print axioms RMTFoundations.TracyWidom.Airy2.Ai_weighted_product_integrable
#print axioms RMTFoundations.TracyWidom.Airy2.integrability_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryIntegrand
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryIntegrand_integrable
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_eq_integral
#print axioms RMTFoundations.TracyWidom.Airy2.extended_integral_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.duplicated_slice_joint_counterinstance
#print axioms RMTFoundations.TracyWidom.Airy2.multiTime_domain_all_binder_joint_probe
