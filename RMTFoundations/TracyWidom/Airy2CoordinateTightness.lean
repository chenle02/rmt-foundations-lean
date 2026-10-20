import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2CoordinateTightness
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability

/-- Tight coordinate marginals force joint tightness, without independence. -/
theorem joint_tight_of_coordinate_tight (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hcoord : ∀ i, IsTightMeasureSet (range (fun n =>
      (μ n : Measure (Fin m → ℝ)).map (fun x => x i))) /- [standing] -/) :
    IsTightMeasureSet (range (fun n => (μ n : Measure (Fin m → ℝ)))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let δ : ℝ≥0∞ := ε / (m+1)
  have hd : 0 < δ := ENNReal.div_pos_iff.mpr ⟨hε.ne', by simp⟩
  have hi (i : Fin m) : ∃ K : Set ℝ, IsCompact K ∧ ∀ n,
      (μ n : Measure (Fin m → ℝ)).map (fun x => x i) Kᶜ ≤ δ := by
    obtain ⟨K,hK,ht⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (hcoord i) δ hd
    exact ⟨K,hK,fun n => ht _ (mem_range_self n)⟩
  choose K hK ht using hi
  let B : Set (Fin m → ℝ) := Set.pi univ K
  refine ⟨B, isCompact_univ_pi hK, ?_⟩
  rintro ν ⟨n,rfl⟩
  have he : Bᶜ = ⋃ i, (fun x : Fin m → ℝ => x i) ⁻¹' (K i)ᶜ := by
    ext x
    simp [B]
  rw [he]
  calc
    _ ≤ ∑ i, (μ n : Measure (Fin m → ℝ)) ((fun x => x i) ⁻¹' (K i)ᶜ) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ i, ((μ n : Measure (Fin m → ℝ)).map (fun x => x i)) (K i)ᶜ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Measure.map_apply (measurable_pi_apply i) (hK i).measurableSet.compl]
    _ ≤ ∑ _i : Fin m, δ := Finset.sum_le_sum fun i _ => ht i n
    _ = m * δ := by simp [nsmul_eq_mul]
    _ ≤ ε := by
      dsimp only [δ]
      calc
        (m : ℝ≥0∞) * (ε / (m+1)) ≤ (m+1) * (ε / (m+1)) := by gcongr; exact le_add_right le_rfl
        _ = ε := by rw [mul_comm, ENNReal.div_mul_cancel (by simp) (by simp)]

/-- All marginal tightness premises hold jointly for a noncollapsed TW2 product. -/
theorem coordinate_tight_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    (∀ i, IsTightMeasureSet (range (fun n =>
      (μ n : Measure (Fin 2 → ℝ)).map (fun x => x i)))) ∧
    IsTightMeasureSet (range (fun n => (μ n : Measure (Fin 2 → ℝ)))) ∧
    0 < jointCDF 2 (TW2ProductLaw 2) (fun _ => 0) ∧
    jointCDF 2 (TW2ProductLaw 2) (fun _ => 0) < 1 := by
  dsimp only
  letI := TW2ProductLaw_probability 2
  let μ : ℕ → ProbabilityMeasure (Fin 2 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  have hc : ∀ i, IsTightMeasureSet (range (fun n =>
      (μ n : Measure (Fin 2 → ℝ)).map (fun x => x i))) := by
    intro i
    simp only [μ, ProbabilityMeasure.coe_mk, range_const]
    exact isTightMeasureSet_singleton
  have hp := probability_core_all_binder_joint_probe
  exact ⟨hc,joint_tight_of_coordinate_tight 2 μ hc,hp.2.1,hp.2.2.1⟩
end RMTFoundations.TracyWidom.Airy2CoordinateTightness

#print axioms RMTFoundations.TracyWidom.Airy2CoordinateTightness.joint_tight_of_coordinate_tight
#print axioms RMTFoundations.TracyWidom.Airy2CoordinateTightness.coordinate_tight_all_binder_joint_probe
