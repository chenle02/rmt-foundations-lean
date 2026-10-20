import Mathlib
import RMTFoundations.TracyWidom.Measures
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.Airy2
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2Probability
open MeasureTheory Set Filter
open scoped Topology ENNReal
def lowerBox (m : ℕ /- [definition] -/) (s : Fin m → ℝ /- [definition] -/) :
    Set (Fin m → ℝ) := {x | ∀ i, x i ≤ s i}
noncomputable def jointCDF (m : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/) (s : Fin m → ℝ /- [definition] -/) :
    ℝ := μ.real (lowerBox m s)
theorem lowerBox_measurable (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) : MeasurableSet (lowerBox m s) := by
  have he : lowerBox m s = ⋂ i, (fun x : Fin m → ℝ => x i) ⁻¹' Iic (s i) := by
    ext x; simp [lowerBox]
  rw [he]
  exact MeasurableSet.iInter fun i => measurableSet_Iic.preimage (measurable_pi_apply i)
theorem jointCDF_monotone (m : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/) : Monotone (jointCDF m μ) := by
  letI := hμ
  intro s t hst
  exact measureReal_mono (μ := μ)
    (fun x hx i => (hx i).trans (hst i)) (by finiteness)
theorem jointCDF_bounds (m : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (s : Fin m → ℝ /- [definition] -/) :
    0 ≤ jointCDF m μ s ∧ jointCDF m μ s ≤ 1 := by
  letI := hμ
  exact ⟨measureReal_nonneg, measureReal_le_one⟩


theorem lowerBox_eq_pi (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) :
    lowerBox m s = Set.pi univ (fun i => Iic (s i)) := by
  ext x
  simp only [lowerBox, mem_setOf_eq, mem_univ_pi, mem_Iic]

/-- A finite-dimensional real law is determined by its whole joint CDF.
This proves uniqueness; it does not construct a law for a kernel candidate. -/
theorem measure_eq_of_jointCDF (m : ℕ /- [definition] -/)
    (μ ν : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (hν : IsProbabilityMeasure ν /- [standing] -/)
    (h : ∀ s, jointCDF m μ s = jointCDF m ν s /- [standing] -/) :
    μ = ν := by
  letI := hμ
  letI := hν
  let C : Fin m → Set (Set ℝ) := fun _ => range (Iic : ℝ → Set ℝ)
  have hC : ∀ i, MeasurableSpace.generateFrom (C i) = (inferInstance : MeasurableSpace ℝ) := by
    intro i
    exact (borel_eq_generateFrom_Iic ℝ).symm
  have hspan : ∀ i, IsCountablySpanning (C i) := by
    intro i
    refine ⟨fun n => Iic (n : ℝ), fun n => ⟨(n : ℝ), rfl⟩, ?_⟩
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x
  apply ext_of_generate_finite (Set.pi univ '' Set.pi univ C)
    (generateFrom_eq_pi hC hspan).symm
    (IsPiSystem.pi fun _ => isPiSystem_Iic)
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : ∀ i, ∃ a : ℝ, Iic a = s i := fun i => hs i (mem_univ i)
    choose a ha using hs'
    have he : Set.pi univ s = lowerBox m a := by
      rw [lowerBox_eq_pi]
      congr 1
      funext i
      exact (ha i).symm
    rw [he]
    exact (measureReal_eq_measureReal_iff).mp (h a)
  · simp

/-- Pushforward along any finite coordinate selector, including repeated selectors. -/
theorem jointCDF_map_coordinates (m n : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (f : Fin n → Fin m /- [definition] -/)
    (s : Fin n → ℝ /- [definition] -/) :
    jointCDF n (μ.map (fun x i => x (f i))) s =
      μ.real {x | ∀ i, x (f i) ≤ s i} := by
  unfold jointCDF
  rw [map_measureReal_apply (by fun_prop) (lowerBox_measurable n s)]
  rfl

/-- Once joint-CDF equality is available, marginal consistency is equality of measures.
No physical producer is hidden in this deduction. -/
theorem marginal_eq_of_jointCDF (m n : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (ν : Measure (Fin n → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (hν : IsProbabilityMeasure ν /- [standing] -/)
    (f : Fin n → Fin m /- [definition] -/)
    (h : ∀ s, μ.real {x | ∀ i, x (f i) ≤ s i} = jointCDF n ν s
      /- [standing] -/) :
    μ.map (fun x i => x (f i)) = ν := by
  letI := hμ
  apply measure_eq_of_jointCDF n _ ν ((Measure.isProbabilityMeasure_map_iff
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i))).aemeasurable).2 inferInstance) hν
  intro s
  rw [jointCDF_map_coordinates]
  exact h s



theorem lowerBox_mono (m : ℕ /- [definition] -/)
    (s t : Fin m → ℝ /- [definition] -/)
    (h : s ≤ t /- [standing] -/) : lowerBox m s ⊆ lowerBox m t := by
  intro x hx i
  exact (hx i).trans (h i)

/-- Simultaneously removing all finite cuts normalizes every real probability law. -/
theorem jointCDF_common_atTop (m : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/) :
    Tendsto (fun a : ℝ => jointCDF m μ (fun _ => a)) atTop (𝓝 1) := by
  letI := hμ
  have hm : Monotone (fun a : ℝ => lowerBox m (fun _ => a)) :=
    fun _ _ h => lowerBox_mono m _ _ (fun _ => h)
  have he : (⋃ a : ℝ, lowerBox m (fun _ => a)) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := (Set.finite_range x).bddAbove
    exact mem_iUnion.mpr ⟨a, fun i => ha (mem_range_self i)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
  rw [he, measure_univ] at ht
  have htr := ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) |>.comp ht
  simpa [jointCDF, Measure.real, Function.comp_def] using htr

/-- In positive dimension, the common lower-cut limit is zero. -/
theorem jointCDF_common_atBot (m : ℕ /- [definition] -/)
    (hm : 0 < m /- [standing] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/) :
    Tendsto (fun a : ℝ => jointCDF m μ (fun _ => a)) atBot (𝓝 0) := by
  letI := hμ
  have hmon : Monotone (fun a : ℝ => lowerBox m (fun _ => a)) :=
    fun _ _ h => lowerBox_mono m _ _ (fun _ => h)
  have he : (⋂ a : ℝ, lowerBox m (fun _ => a)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let i : Fin m := ⟨0, hm⟩
    have h := (mem_iInter.mp hx (x i - 1)) i
    linarith
  have ht := tendsto_measure_iInter_atBot (μ := μ)
    (fun a => (lowerBox_measurable m _).nullMeasurableSet) hmon
    ⟨0, by finiteness⟩
  rw [he, measure_empty] at ht
  have htr := ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞) |>.comp ht
  simpa [jointCDF, Measure.real, Function.comp_def] using htr

/-- Remove every unretained cut simultaneously. The retained joint event remains. -/
theorem jointCDF_remove_cuts (m : ℕ /- [definition] -/)
    (μ : Measure (Fin m → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (J : Finset (Fin m) /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) :
    Tendsto (fun a : ℝ => jointCDF m μ (fun i => if i ∈ J then s i else a))
      atTop (𝓝 (μ.real {x | ∀ i ∈ J, x i ≤ s i})) := by
  classical
  letI := hμ
  have hm : Monotone (fun a : ℝ => lowerBox m (fun i => if i ∈ J then s i else a)) := by
    intro a b hab
    apply lowerBox_mono
    intro i
    dsimp only
    split_ifs <;> simp_all
  have he : (⋃ a : ℝ, lowerBox m (fun i => if i ∈ J then s i else a)) =
      {x | ∀ i ∈ J, x i ≤ s i} := by
    ext x
    constructor
    · rintro hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      intro i hi
      simpa [hi] using ha i
    · intro hx
      obtain ⟨a, ha⟩ := (Set.finite_range x).bddAbove
      apply mem_iUnion.mpr
      refine ⟨a, ?_⟩
      intro i
      dsimp only [lowerBox, mem_setOf_eq]
      split_ifs with hi
      · exact hx i hi
      · exact ha (mem_range_self i)
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
  rw [he] at ht
  have htr := ENNReal.tendsto_toReal (by finiteness :
    μ {x | ∀ i ∈ J, x i ≤ s i} ≠ ∞) |>.comp ht
  simpa [jointCDF, Measure.real, Function.comp_def] using htr



/-- This genuine full-dimensional example law has independent TW2 coordinates.
It is a probability witness for the measure lemmas, not the Airy2 time law. -/
noncomputable def TW2ProductLaw (m : ℕ /- [definition] -/) :
    Measure (Fin m → ℝ) :=
  Measure.pi (fun _ => RMTFoundations.TracyWidom.TW2Measure)

theorem TW2ProductLaw_probability (m : ℕ /- [definition] -/) :
    IsProbabilityMeasure (TW2ProductLaw m) := by
  unfold TW2ProductLaw
  infer_instance

theorem TW2ProductLaw_jointCDF (m : ℕ /- [definition] -/)
    (s : Fin m → ℝ /- [definition] -/) :
    jointCDF m (TW2ProductLaw m) s = ∏ i, RMTFoundations.TracyWidom.TW2R (s i) := by
  classical
  unfold jointCDF TW2ProductLaw
  rw [lowerBox_eq_pi, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [RMTFoundations.TracyWidom.TW2Measure_Iic, ENNReal.toReal_ofReal]
  exact (RMTFoundations.TracyWidom.TW2R_bounds (s i)).1

/-- Every measure premise and both asymptotic limits hold on a noncollapsed TW2 product.
The root applies the proved deductions, with all non-event binders supplied by terms. -/
theorem probability_core_all_binder_joint_probe :
    IsProbabilityMeasure (TW2ProductLaw 2) ∧
    0 < jointCDF 2 (TW2ProductLaw 2) (fun _ => 0) ∧
    jointCDF 2 (TW2ProductLaw 2) (fun _ => 0) < 1 ∧
    Monotone (jointCDF 2 (TW2ProductLaw 2)) ∧
    (∀ s, 0 ≤ jointCDF 2 (TW2ProductLaw 2) s ∧ jointCDF 2 (TW2ProductLaw 2) s ≤ 1) ∧
    Tendsto (fun a : ℝ => jointCDF 2 (TW2ProductLaw 2) (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => jointCDF 2 (TW2ProductLaw 2) (fun _ => a)) atBot (𝓝 0) ∧
    Tendsto (fun a : ℝ => jointCDF 2 (TW2ProductLaw 2)
      (fun i => if i ∈ ({0} : Finset (Fin 2)) then -1 else a)) atTop
      (𝓝 ((TW2ProductLaw 2).real {x | ∀ i ∈ ({0} : Finset (Fin 2)), x i ≤ -1})) := by
  have hp := TW2ProductLaw_probability 2
  have h0 := RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0
  have h1 : RMTFoundations.TracyWidom.TW2R 0 < 1 :=
    (RMTFoundations.TracyWidom.TW2R_strictMono (by norm_num : (0 : ℝ) < 1)).trans_le
      (RMTFoundations.TracyWidom.TW2R_bounds 1).2
  have he : jointCDF 2 (TW2ProductLaw 2) (fun _ => 0) =
      RMTFoundations.TracyWidom.TW2R 0 * RMTFoundations.TracyWidom.TW2R 0 := by
    rw [TW2ProductLaw_jointCDF]
    simp [pow_two]
  refine ⟨hp, ?_, ?_, jointCDF_monotone 2 _ hp,
    jointCDF_bounds 2 _ hp, jointCDF_common_atTop 2 _ hp,
    jointCDF_common_atBot 2 (by norm_num) _ hp,
    jointCDF_remove_cuts 2 _ hp {0} (fun _ => -1)⟩
  · rw [he]
    exact mul_pos h0 h0
  · rw [he]
    nlinarith


/-- Joint probabilities obey the rectangle inequality, which separate monotonicity
does not supply. -/
theorem jointCDF_rectangle_nonneg
    (μ : Measure (Fin 2 → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (a b c d : ℝ /- [definition] -/)
    (hab : a ≤ b /- [standing] -/)
    (hcd : c ≤ d /- [standing] -/) :
    0 ≤ jointCDF 2 μ ![b,d] - jointCDF 2 μ ![a,d] -
      jointCDF 2 μ ![b,c] + jointCDF 2 μ ![a,c] := by
  letI := hμ
  have he : lowerBox 2 ![a,d] ∩ lowerBox 2 ![b,c] = lowerBox 2 ![a,c] := by
    ext x
    simp only [lowerBox, mem_inter_iff, mem_setOf_eq, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · intro h
      exact ⟨h.1.1, h.2.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hcd⟩, ⟨h.1.trans hab, h.2⟩⟩
  have hu : lowerBox 2 ![a,d] ∪ lowerBox 2 ![b,c] ⊆ lowerBox 2 ![b,d] := by
    intro x hx
    rcases hx with hx | hx
    · exact lowerBox_mono 2 _ _ (by intro i; fin_cases i <;> simp [hab]) hx
    · exact lowerBox_mono 2 _ _ (by intro i; fin_cases i <;> simp [hcd]) hx
  have h := measureReal_union_add_inter (μ := μ) (s := lowerBox 2 ![a,d])
    (lowerBox_measurable 2 ![b,c])
  rw [he] at h
  have h' := measureReal_mono (μ := μ) hu (by finiteness)
  unfold jointCDF
  linarith

/-- The alternating increment is the probability of the actual open-closed rectangle. -/
theorem jointCDF_rectangle_mass
    (μ : Measure (Fin 2 → ℝ) /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/)
    (a b c d : ℝ /- [definition] -/)
    (hab : a ≤ b /- [standing] -/)
    (hcd : c ≤ d /- [standing] -/) :
    jointCDF 2 μ ![b,d] - jointCDF 2 μ ![a,d] -
      jointCDF 2 μ ![b,c] + jointCDF 2 μ ![a,c] =
      μ.real {x | a < x 0 ∧ x 0 ≤ b ∧ c < x 1 ∧ x 1 ≤ d} := by
  letI := hμ
  let U := lowerBox 2 ![a,d] ∪ lowerBox 2 ![b,c]
  have hi : lowerBox 2 ![a,d] ∩ lowerBox 2 ![b,c] = lowerBox 2 ![a,c] := by
    ext x
    simp only [lowerBox, mem_inter_iff, mem_setOf_eq, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · intro h
      exact ⟨h.1.1, h.2.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hcd⟩, ⟨h.1.trans hab, h.2⟩⟩
  have hu : U ⊆ lowerBox 2 ![b,d] := by
    intro x hx
    rcases hx with hx | hx
    · exact lowerBox_mono 2 _ _ (by intro i; fin_cases i <;> simp [hab]) hx
    · exact lowerBox_mono 2 _ _ (by intro i; fin_cases i <;> simp [hcd]) hx
  have hd : lowerBox 2 ![b,d] \ U =
      {x | a < x 0 ∧ x 0 ≤ b ∧ c < x 1 ∧ x 1 ≤ d} := by
    ext x
    simp only [U, lowerBox, Set.mem_sdiff, mem_union, mem_setOf_eq, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> grind
  have hsum := measureReal_union_add_inter (μ := μ) (s := lowerBox 2 ![a,d])
    (lowerBox_measurable 2 ![b,c])
  rw [hi] at hsum
  have hdiff := measureReal_sdiff (μ := μ) hu
    ((lowerBox_measurable 2 ![a,d]).union (lowerBox_measurable 2 ![b,c]))
  rw [hd] at hdiff
  unfold jointCDF
  change μ.real (lowerBox 2 ![b,d]) - μ.real (lowerBox 2 ![a,d]) -
    μ.real (lowerBox 2 ![b,c]) + μ.real (lowerBox 2 ![a,c]) = _
  change μ.real _ = μ.real _ - μ.real
    (lowerBox 2 ![a,d] ∪ lowerBox 2 ![b,c]) at hdiff
  linarith



/-- The existing actual one-time Fredholm candidate has a constructed probability law. -/
theorem one_time_physical_law
    (times cuts : Fin 1 → ℝ /- [definition] -/) :
    jointCDF 1 (TW2ProductLaw 1) cuts =
      (RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate 1 times cuts).re := by
  rw [RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_one_time,
    TW2ProductLaw_jointCDF]
  simp [RMTFoundations.AiryKernel.TW2R]

/-- Nonzero physical Airy data, the complete singleton law, and its asymptotic CDF fields. -/
theorem one_time_physical_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
    IsProbabilityMeasure (TW2ProductLaw 1) ∧
    (∀ times cuts : Fin 1 → ℝ, jointCDF 1 (TW2ProductLaw 1) cuts =
      (RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate 1 times cuts).re) ∧
    Tendsto (fun a : ℝ => jointCDF 1 (TW2ProductLaw 1) (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => jointCDF 1 (TW2ProductLaw 1) (fun _ => a)) atBot (𝓝 0) := by
  have hp := TW2ProductLaw_probability 1
  exact ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne', hp, one_time_physical_law,
    jointCDF_common_atTop 1 _ hp, jointCDF_common_atBot 1 (by norm_num) _ hp⟩

/-- All uniqueness, selector, marginal and rectangle hypotheses are realized jointly
on a genuine full-dimensional two-coordinate TW2 law with a retained second coordinate. -/
theorem measure_transport_rectangle_all_binder_joint_probe :
    let μ := TW2ProductLaw 2
    let f : Fin 1 → Fin 2 := fun _ => 1
    let ν := μ.map (fun x i => x (f i))
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (μ = μ) ∧
    (∀ s, jointCDF 1 ν s = μ.real {x | ∀ i, x (f i) ≤ s i}) ∧
    (μ.map (fun x i => x (f i)) = ν) ∧
    0 ≤ jointCDF 2 μ ![0,2] - jointCDF 2 μ ![-1,2] -
      jointCDF 2 μ ![0,1] + jointCDF 2 μ ![-1,1] ∧
    jointCDF 2 μ ![0,2] - jointCDF 2 μ ![-1,2] -
      jointCDF 2 μ ![0,1] + jointCDF 2 μ ![-1,1] =
      μ.real {x | -1 < x 0 ∧ x 0 ≤ 0 ∧ 1 < x 1 ∧ x 1 ≤ 2} := by
  dsimp only
  have hp := TW2ProductLaw_probability 2
  letI := hp
  have hm : Measurable (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 1) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply 1
  have hn : IsProbabilityMeasure ((TW2ProductLaw 2).map
      (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 1)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine ⟨hp, hn, measure_eq_of_jointCDF 2 _ _ hp hp (fun _ => rfl),
    jointCDF_map_coordinates 2 1 _ (fun _ => 1), ?_,
    jointCDF_rectangle_nonneg _ hp (-1) 0 1 2 (by norm_num) (by norm_num),
    jointCDF_rectangle_mass _ hp (-1) 0 1 2 (by norm_num) (by norm_num)⟩
  exact marginal_eq_of_jointCDF 2 1 _ _ hp hn (fun _ => 1)
    (fun s => (jointCDF_map_coordinates 2 1 _ (fun _ => 1) s).symm)

noncomputable def cutBucket (x : ℝ /- [definition] -/) : Fin 4 :=
  if x < 0 then 0 else if x < 1 then 1 else if x < 2 then 2 else 3
noncomputable def signedGrid (i j : Fin 4 /- [definition] -/) : ℝ :=
  if i = 0 ∨ j = 0 then 0 else if i = 3 then (j.val : ℝ) / 3
  else if j = 3 then (i.val : ℝ) / 3 else if i = 1 ∧ j = 1 then 0 else 1/3
noncomputable def quasiCDF (s : Fin 2 → ℝ /- [definition] -/) : ℝ :=
  signedGrid (cutBucket (s 0)) (cutBucket (s 1))
theorem cutBucket_monotone : Monotone cutBucket := by
  intro x y hxy
  unfold cutBucket
  split_ifs <;> norm_num [Fin.le_def] at * <;> linarith
theorem signedGrid_row_monotone (j : Fin 4 /- [definition] -/) :
    Monotone (fun i => signedGrid i j) := by
  intro a b hab
  fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num [signedGrid, Fin.le_def, Fin.ext_iff] at *
theorem signedGrid_col_monotone (i : Fin 4 /- [definition] -/) :
    Monotone (signedGrid i) := by
  intro a b hab
  fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [signedGrid, Fin.le_def, Fin.ext_iff] at *
theorem quasiCDF_monotone : Monotone quasiCDF := by
  intro s t hst
  exact (signedGrid_row_monotone _ (cutBucket_monotone (hst 0))).trans
    (signedGrid_col_monotone _ (cutBucket_monotone (hst 1)))
theorem quasiCDF_bounds (s : Fin 2 → ℝ /- [definition] -/) :
    0 ≤ quasiCDF s ∧ quasiCDF s ≤ 1 := by
  unfold quasiCDF
  generalize cutBucket (s 0) = a
  generalize cutBucket (s 1) = b
  fin_cases a <;> fin_cases b <;> norm_num [signedGrid, Fin.ext_iff]
theorem monotone_bounded_negative_rectangle_joint_counterinstance :
    Monotone quasiCDF ∧ (∀ s, 0 ≤ quasiCDF s ∧ quasiCDF s ≤ 1) ∧
    quasiCDF ![1,1] - quasiCDF ![0,1] - quasiCDF ![1,0] + quasiCDF ![0,0] =
      -(1/3 : ℝ) := by
  refine ⟨quasiCDF_monotone, quasiCDF_bounds, ?_⟩
  change signedGrid (cutBucket 1) (cutBucket 1) -
    signedGrid (cutBucket 0) (cutBucket 1) -
    signedGrid (cutBucket 1) (cutBucket 0) +
    signedGrid (cutBucket 0) (cutBucket 0) = -(1/3 : ℝ)
  norm_num [signedGrid, cutBucket, Fin.ext_iff]


/-- Separate monotonicity and probability bounds do not construct a joint law.
This refutes a generic shortcut, not the physical Airy2 candidate. -/
theorem quasiCDF_has_no_probability_law :
    ¬ ∃ μ : Measure (Fin 2 → ℝ),
      IsProbabilityMeasure μ ∧ ∀ s, jointCDF 2 μ s = quasiCDF s := by
  rintro ⟨μ,hμ,hcdf⟩
  have h := jointCDF_rectangle_nonneg μ hμ 0 1 0 1 (by norm_num) (by norm_num)
  simp only [hcdf] at h
  rw [monotone_bounded_negative_rectangle_joint_counterinstance.2.2] at h
  norm_num at h



theorem quasiCDF_common_atTop :
    Tendsto (fun a : ℝ => quasiCDF (fun _ => a)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have h0 : ¬ a < 0 := not_lt.mpr (by linarith)
  have h1 : ¬ a < 1 := not_lt.mpr (by linarith)
  have h2 : ¬ a < 2 := not_lt.mpr ha
  norm_num [quasiCDF, cutBucket, signedGrid, h0, h1, h2, Fin.ext_iff]

theorem quasiCDF_common_atBot :
    Tendsto (fun a : ℝ => quasiCDF (fun _ => a)) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with a ha
  norm_num [quasiCDF, cutBucket, signedGrid, ha, Fin.ext_iff]

/-- Bounded monotonicity plus correct common-cut limits still misses rectangle positivity. -/
theorem probability_shortcut_complete_joint_counterprobe :
    Monotone quasiCDF ∧ (∀ s, 0 ≤ quasiCDF s ∧ quasiCDF s ≤ 1) ∧
    Tendsto (fun a : ℝ => quasiCDF (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => quasiCDF (fun _ => a)) atBot (𝓝 0) ∧
    (¬ ∃ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ ∧
      ∀ s, jointCDF 2 μ s = quasiCDF s) := by
  exact ⟨quasiCDF_monotone, quasiCDF_bounds, quasiCDF_common_atTop,
    quasiCDF_common_atBot, quasiCDF_has_no_probability_law⟩

end RMTFoundations.TracyWidom.Airy2Probability

#print axioms RMTFoundations.TracyWidom.Airy2Probability.lowerBox
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF
#print axioms RMTFoundations.TracyWidom.Airy2Probability.lowerBox_measurable
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_monotone
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_bounds
#print axioms RMTFoundations.TracyWidom.Airy2Probability.lowerBox_eq_pi
#print axioms RMTFoundations.TracyWidom.Airy2Probability.measure_eq_of_jointCDF
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_map_coordinates
#print axioms RMTFoundations.TracyWidom.Airy2Probability.marginal_eq_of_jointCDF
#print axioms RMTFoundations.TracyWidom.Airy2Probability.lowerBox_mono
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_common_atTop
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_common_atBot
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_remove_cuts
#print axioms RMTFoundations.TracyWidom.Airy2Probability.TW2ProductLaw
#print axioms RMTFoundations.TracyWidom.Airy2Probability.TW2ProductLaw_probability
#print axioms RMTFoundations.TracyWidom.Airy2Probability.TW2ProductLaw_jointCDF
#print axioms RMTFoundations.TracyWidom.Airy2Probability.probability_core_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_rectangle_nonneg
#print axioms RMTFoundations.TracyWidom.Airy2Probability.jointCDF_rectangle_mass
#print axioms RMTFoundations.TracyWidom.Airy2Probability.one_time_physical_law
#print axioms RMTFoundations.TracyWidom.Airy2Probability.one_time_physical_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2Probability.measure_transport_rectangle_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2Probability.cutBucket
#print axioms RMTFoundations.TracyWidom.Airy2Probability.signedGrid
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF
#print axioms RMTFoundations.TracyWidom.Airy2Probability.cutBucket_monotone
#print axioms RMTFoundations.TracyWidom.Airy2Probability.signedGrid_row_monotone
#print axioms RMTFoundations.TracyWidom.Airy2Probability.signedGrid_col_monotone
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF_monotone
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF_bounds
#print axioms RMTFoundations.TracyWidom.Airy2Probability.monotone_bounded_negative_rectangle_joint_counterinstance
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF_has_no_probability_law
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF_common_atTop
#print axioms RMTFoundations.TracyWidom.Airy2Probability.quasiCDF_common_atBot
#print axioms RMTFoundations.TracyWidom.Airy2Probability.probability_shortcut_complete_joint_counterprobe
