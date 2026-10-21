import RMTFoundations.TracyWidom.FiniteDysonGaussianLaw
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.FiniteDysonMarginals
open MeasureTheory ProbabilityTheory
open scoped NNReal
open RMTFoundations.TracyWidom.FiniteDysonGaussianLaw
open RMTFoundations.TracyWidom.GUEIdentification

lemma ouCoefficient_square_successor (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (j l : Fin (m+1) /- [definition] -/)
    (hnext : l.val = j.val+1 /- [standing] -/) :
    (∑ k : Fin (m+1), (ouCoefficient m t l k)^2) =
      (Real.exp (-(t l.val-t j.val)))^2 *
        (∑ k : Fin (m+1), (ouCoefficient m t j k)^2) +
          (Real.sqrt (1-Real.exp (-2*(t l.val-t j.val))))^2 := by
  have he (k : Fin (m+1)) : (ouCoefficient m t l k)^2 =
      (Real.exp (-(t l.val-t j.val)))^2 * (ouCoefficient m t j k)^2 +
        if k = l then (Real.sqrt (1-Real.exp (-2*(t l.val-t j.val))))^2 else 0 := by
    rw [ouCoefficient_successor m t j l k hnext]
    by_cases hk : k = l
    · subst k
      have hnj : ¬ l ≤ j := by simp only [Fin.le_iff_val_le_val]; omega
      simp [ouCoefficient, hnj]
    · simp [hk, mul_pow]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

lemma ouCoefficient_square_sum (m : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/)
    (j : Fin (m+1) /- [definition] -/) :
    ∑ k : Fin (m+1), (ouCoefficient m t j k)^2 = 1 := by
  induction j using Fin.induction with
  | zero => simp [ouCoefficient_initial]
  | succ j ih =>
    rw [ouCoefficient_square_successor m t j.castSucc j.succ (by simp)]
    rw [ih]
    have hgap : 0 ≤ t j.succ.val - t j.castSucc.val :=
      sub_nonneg.mpr (ht (by simp))
    have hn : 0 ≤ 1-Real.exp (-2*(t j.succ.val-t j.castSucc.val)) := by
      have he := Real.exp_le_one_iff.mpr (show -2*(t j.succ.val-t j.castSucc.val) ≤ 0 by linarith)
      linarith
    have he : (Real.exp (-(t j.succ.val-t j.castSucc.val)))^2 =
        Real.exp (-2*(t j.succ.val-t j.castSucc.val)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Real.sq_sqrt hn, he]
    ring

lemma independent_gaussian_finite_sum {ι Ω : Type* /- [definition] -/} [MeasurableSpace Ω /- [definition] -/]
    (μ : Measure Ω /- [definition] -/)
    (X : ι → Ω → ℝ /- [definition] -/)
    (v : ι → ℝ≥0 /- [definition] -/)
    (hind : iIndepFun X μ /- [standing] -/)
    (hm : ∀ i, Measurable (X i) /- [standing] -/)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 (v i) /- [standing] -/)
    (s : Finset ι /- [definition] -/)
    (hμ : IsProbabilityMeasure μ /- [standing] -/) :
    μ.map (∑ i ∈ s, X i) = gaussianReal 0 (∑ i ∈ s, v i) := by
  classical
  letI := hμ
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, gaussianReal_zero_var]
    change μ.map (fun _ => (0 : ℝ)) = Measure.dirac 0
    rw [Measure.map_const]
    simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : Measurable (∑ j ∈ s, X j) := by
      simpa only [Finset.sum_fn] using Finset.measurable_sum s (fun j _ => hm j)
    have hiLaw : HasLaw (X i) (gaussianReal 0 (v i)) μ := ⟨(hm i).aemeasurable, hlaw i⟩
    have hsLaw : HasLaw (∑ j ∈ s, X j) (gaussianReal 0 (∑ j ∈ s, v j)) μ :=
      ⟨hs.aemeasurable, ih⟩
    have h := gaussianReal_add_gaussianReal_of_indepFun
      ((hind.indepFun_finsetSum_of_notMem hm hi).symm) hiLaw hsLaw
    simpa using h

lemma ou_single_coordinate_law (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/)
    (j : Fin (m+1) /- [definition] -/)
    (q : Fin (n+1) × Fin (n+1) × Fin 2 /- [definition] -/) :
    (innovationMeasure m n).map (fun x => ouCoordinates m n t j x q) =
      gaussianReal 0 1 := by
  let X : Fin (m+1) → ((Fin (m+1) × (Fin (n+1) × Fin (n+1) × Fin 2)) → ℝ) → ℝ :=
    fun k x => ouCoefficient m t j k * x (k,q)
  let v : Fin (m+1) → ℝ≥0 := fun k => NNReal.mk ((ouCoefficient m t j k)^2) (sq_nonneg _)
  have hidx : Function.Injective (fun k : Fin (m+1) => (k,q)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hi : iIndepFun X (innovationMeasure m n) :=
    ((innovations_independent m n).precomp hidx).comp
      (fun k => fun z : ℝ => ouCoefficient m t j k*z) (by intro k; fun_prop)
  have hm (k : Fin (m+1)) : Measurable (X k) := by unfold X; fun_prop
  have hl (k : Fin (m+1)) : (innovationMeasure m n).map (X k) = gaussianReal 0 (v k) := by
    have hh := gaussianReal_const_mul
      (show HasLaw (fun x => x (k,q)) (gaussianReal 0 1) (innovationMeasure m n) from
        ⟨(measurable_pi_apply (k,q)).aemeasurable, innovation_coordinate_law m n (k,q)⟩)
      (ouCoefficient m t j k)
    simpa [X, v] using hh.map_eq
  have hv : (∑ k : Fin (m+1), v k) = 1 := by
    apply NNReal.eq
    simpa [v] using ouCoefficient_square_sum m t ht j
  have h := independent_gaussian_finite_sum (innovationMeasure m n) X v hi hm hl Finset.univ (by infer_instance)
  rw [hv] at h
  simpa [X, ouCoordinates, Finset.sum_fn] using h

lemma gaussian_pi_weighted_sum (m : ℕ /- [definition] -/)
    (a : Fin (m+1) → ℝ /- [definition] -/)
    (ha : ∑ k, (a k)^2 = 1 /- [standing] -/) :
    (Measure.pi fun _ : Fin (m+1) => gaussianReal 0 1).map
      (fun x => ∑ k, a k*x k) = gaussianReal 0 1 := by
  let μ := Measure.pi fun _ : Fin (m+1) => gaussianReal 0 1
  let X : Fin (m+1) → (Fin (m+1) → ℝ) → ℝ := fun k x => a k*x k
  let v : Fin (m+1) → ℝ≥0 := fun k => NNReal.mk ((a k)^2) (sq_nonneg _)
  have hi : iIndepFun X μ :=
    (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).comp
      (fun k => fun z : ℝ => a k*z) (by intro k; fun_prop)
  have hm (k : Fin (m+1)) : Measurable (X k) := by unfold X; fun_prop
  have hl (k : Fin (m+1)) : μ.map (X k) = gaussianReal 0 (v k) := by
    have hh := gaussianReal_const_mul
      (show HasLaw (Function.eval k) (gaussianReal 0 1) μ from
        ⟨(measurable_pi_apply k).aemeasurable,
          (measurePreserving_eval (μ := fun _ => gaussianReal 0 1) k).map_eq⟩) (a k)
    simpa [X, v] using hh.map_eq
  have hv : (∑ k, v k) = 1 := by
    apply NNReal.eq
    simpa [v] using ha
  have h := independent_gaussian_finite_sum μ X v hi hm hl Finset.univ (by infer_instance)
  rw [hv] at h
  simpa [X, μ, Finset.sum_fn] using h

lemma innovation_blocks_law (m n : ℕ /- [definition] -/) :
    (innovationMeasure m n).map
      (fun x (q : Fin (n+1) × Fin (n+1) × Fin 2) (k : Fin (m+1)) => x (k,q)) =
      Measure.pi (fun _ : Fin (n+1) × Fin (n+1) × Fin 2 =>
        Measure.pi fun _ : Fin (m+1) => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : (Fin (n+1) × Fin (n+1) × Fin 2) × Fin (m+1) => ℝ)
    (Equiv.prodComm (Fin (m+1)) (Fin (n+1) × Fin (n+1) × Fin 2))
  have hs : (innovationMeasure m n).map e =
      Measure.pi (fun _ : (Fin (n+1) × Fin (n+1) × Fin 2) × Fin (m+1) =>
        gaussianReal 0 1) := by
    exact (measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1)
      (Equiv.prodComm (Fin (m+1)) (Fin (n+1) × Fin (n+1) × Fin 2))).map_eq
  have hc := Measure.infinitePi_map_curry
    (fun (_ : Fin (n+1) × Fin (n+1) × Fin 2) (_ : Fin (m+1)) => gaussianReal 0 1)
  simp_rw [Measure.infinitePi_eq_pi] at hc
  have he : (fun x (q : Fin (n+1) × Fin (n+1) × Fin 2) (k : Fin (m+1)) => x (k,q)) =
      (MeasurableEquiv.curry (Fin (n+1) × Fin (n+1) × Fin 2) (Fin (m+1)) ℝ) ∘ e := by
    rfl
  rw [he, ← Measure.map_map (by fun_prop) e.measurable, hs]
  exact hc

/-- Every sampled coordinate array has the exact  independent GUE
source law at increasing (or merely nondecreasing) times. -/
lemma stationary_GUE_coordinate_law (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/)
    (j : Fin (m+1) /- [definition] -/) :
    (innovationMeasure m n).map (ouCoordinates m n t j) = gueMeasure n := by
  let f : (Fin (n+1) × Fin (n+1) × Fin 2 → Fin (m+1) → ℝ) →
      (Fin (n+1) × Fin (n+1) × Fin 2 → ℝ) :=
    fun x q => ∑ k, ouCoefficient m t j k * x q k
  have hf : Measurable f := by
    unfold f
    fun_prop
  have he : ouCoordinates m n t j = f ∘
      (fun x (q : Fin (n+1) × Fin (n+1) × Fin 2) (k : Fin (m+1)) => x (k,q)) := rfl
  rw [he, ← Measure.map_map hf (by fun_prop), innovation_blocks_law]
  rw [Measure.pi_map_pi (fun q => (show Measurable
    (fun x : Fin (m+1) → ℝ => ∑ k, ouCoefficient m t j k*x k) by fun_prop).aemeasurable)]
  simp_rw [gaussian_pi_weighted_sum m (ouCoefficient m t j)
    (ouCoefficient_square_sum m t ht j)]
  rfl

/-- The canonical coordinate product sigma-algebra on finite complex matrices. -/
noncomputable local instance matrix_measurableSpace (n : ℕ /- [definition] -/) :
    MeasurableSpace (Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :=
  inferInstanceAs (MeasurableSpace (Fin (n+1) → Fin (n+1) → ℂ))

noncomputable local instance matrix_borelSpace (n : ℕ /- [definition] -/) :
    BorelSpace (Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :=
  inferInstanceAs (BorelSpace (Fin (n+1) → Fin (n+1) → ℂ))

lemma gueMatrix_continuous (n : ℕ /- [definition] -/) : Continuous (gueMatrix n) := by
  unfold gueMatrix
  fun_prop

lemma stationary_GUE_matrix_law (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/)
    (j : Fin (m+1) /- [definition] -/) :
    (innovationMeasure m n).map (ouMatrix m n t j) =
      (gueMeasure n).map (gueMatrix n) := by
  change (innovationMeasure m n).map ((gueMatrix n) ∘ (ouCoordinates m n t j)) = _
  rw [← Measure.map_map (gueMatrix_continuous n).measurable
    (ouCoordinates_continuous m n t j).measurable, stationary_GUE_coordinate_law m n t ht j]

/-- Consequently every coordinate marginal of the genuine top-eigenvalue
joint probability law is the same  GUE top-eigenvalue pushforward. -/
lemma stationary_GUE_top_marginal (m n : ℕ /- [definition] -/)
    (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/)
    (j : Fin (m+1) /- [definition] -/) :
    (topJointLaw m n t).map (Function.eval j) = (gueMeasure n).map
      (fun x => RMTFoundations.TracyWidom.LargestEigenvalue.lamMax (gueMatrix n x)) := by
  unfold topJointLaw
  rw [Measure.map_map (measurable_pi_apply j) (topPath_continuous m n t).measurable]
  change (innovationMeasure m n).map
    (RMTFoundations.TracyWidom.LargestEigenvalue.lamMax ∘ ouMatrix m n t j) = _
  rw [← Measure.map_map (RMTFoundations.TracyWidom.LargestEigenvalue.continuous_lamMax (k := n+1)).measurable
    (ouMatrix_continuous m n t j).measurable, stationary_GUE_matrix_law m n t ht j]
  rw [Measure.map_map (RMTFoundations.TracyWidom.LargestEigenvalue.continuous_lamMax (k := n+1)).measurable
    (gueMatrix_continuous n).measurable]
  rfl

/-- A simultaneous nondegenerate instance discharges all standing hypotheses
and obtains the stationary laws at every time, including a genuine later-time
innovation and a 3-by-3 Hermitian matrix. -/
theorem stationary_all_binder_joint_probe :
    ∃ t : ℕ → ℝ, StrictMono t ∧ Monotone t ∧
      0 < ouCoefficient 1 t 1 1 ∧
      (∀ m n, IsProbabilityMeasure (innovationMeasure m n)) ∧
      (∀ m j, ∑ k : Fin (m+1), (ouCoefficient m t j k)^2 = 1) ∧
      (∀ m n j, (innovationMeasure m n).map (ouCoordinates m n t j) = gueMeasure n) ∧
      (∀ j : Fin 2, (innovationMeasure 1 2).map (ouCoordinates 1 2 t j) = gueMeasure 2) := by
  let t : ℕ → ℝ := fun k => k
  have ht : StrictMono t := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  exact ⟨t, ht, ht.monotone,
    successor_innovation_positive 1 t 0 1 (by norm_num) (by norm_num [t]),
    fun m n => inferInstance, fun m j => ouCoefficient_square_sum m t ht.monotone j,
    fun m n j => stationary_GUE_coordinate_law m n t ht.monotone j,
    fun j => stationary_GUE_coordinate_law 1 2 t ht.monotone j⟩

/-- The finite Gaussian sum lemma's independentness, measurability, coordinate
laws and source probability hypotheses coexist on two nondegenerate Gaussian
coordinates; their sum has positive variance two. -/
theorem independent_sum_all_binder_joint_probe :
    ∃ μ : Measure (Fin 2 → ℝ), ∃ X : Fin 2 → (Fin 2 → ℝ) → ℝ,
      ∃ v : Fin 2 → ℝ≥0, IsProbabilityMeasure μ ∧ iIndepFun X μ ∧
      (∀ i, Measurable (X i)) ∧ (∀ i, μ.map (X i) = gaussianReal 0 (v i)) ∧
      (∀ i, 0 < v i) ∧
      μ.map (∑ i : Fin 2, X i) = gaussianReal 0 2 := by
  let μ : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let X : Fin 2 → (Fin 2 → ℝ) → ℝ := fun i x => x i
  have hi : iIndepFun X μ := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hl : ∀ i, μ.map (X i) = gaussianReal 0 1 := fun i =>
    (measurePreserving_eval (μ := fun _ => gaussianReal 0 1) i).map_eq
  have hp : IsProbabilityMeasure μ := by unfold μ; infer_instance
  refine ⟨μ, X, fun _ => 1, hp, hi, hm, hl, (by intro i; norm_num), ?_⟩
  simpa using independent_gaussian_finite_sum μ X (fun _ => 1) hi hm hl Finset.univ hp

end RMTFoundations.TracyWidom.FiniteDysonMarginals

#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.ouCoefficient_square_successor
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.ouCoefficient_square_sum
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.independent_gaussian_finite_sum
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.ou_single_coordinate_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.gaussian_pi_weighted_sum
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.innovation_blocks_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_GUE_coordinate_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.gueMatrix_continuous
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_GUE_matrix_law
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_GUE_top_marginal
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.independent_sum_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.matrix_measurableSpace
#print axioms RMTFoundations.TracyWidom.FiniteDysonMarginals.matrix_borelSpace
