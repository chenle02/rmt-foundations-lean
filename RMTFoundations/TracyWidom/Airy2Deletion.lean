import RMTFoundations.TracyWidom.Airy2
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
/-- Zero rows outside a measurable subset remove precisely those integration sites. -/
theorem kernelCoefficient_restrict_zero_rows
    {α : Type*} /- [definition] -/
    [MeasurableSpace α] /- [standing] -/
    (μ : Measure α) /- [definition] -/
    [SigmaFinite μ] /- [standing] -/
    (S : Set α) /- [definition] -/
    (hS : MeasurableSet S) /- [standing] -/
    (k : α → α → ℝ) /- [definition] -/
    (hz : ∀ x, x ∉ S → ∀ y, k x y = 0) /- [standing] -/
    (n : ℕ) /- [definition] -/ :
    kernelCoefficient μ k n = kernelCoefficient (μ.restrict S) k n := by
  classical
  let T : Set (Fin n → α) := Set.univ.pi (fun _ => S)
  have hT : MeasurableSet T := MeasurableSet.pi countable_univ (fun _ _ => hS)
  have hr : Measure.pi (fun _ : Fin n => μ.restrict S) =
      (Measure.pi (fun _ : Fin n => μ)).restrict T :=
    (Measure.restrict_pi_pi (fun _ : Fin n => μ) (fun _ => S)).symm
  unfold kernelCoefficient
  rw [hr,← integral_indicator hT]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ T
  · simp [hx]
  · have hi : ∃ i : Fin n, x i ∉ S := by simpa [T,Set.mem_pi] using hx
    obtain ⟨i,hi⟩ := hi
    have hm : kernelMinor k n x = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero i (fun j => hz (x i) hi (x j))
    simp [hx,hm]

/-- Row-support restriction holds for the entire formal series, with no convergence assumption. -/
theorem kernelFredholm_restrict_zero_rows
    {α : Type*} /- [definition] -/
    [MeasurableSpace α] /- [standing] -/
    (μ : Measure α) /- [definition] -/
    [SigmaFinite μ] /- [standing] -/
    (S : Set α) /- [definition] -/
    (hS : MeasurableSet S) /- [standing] -/
    (k : α → α → ℝ) /- [definition] -/
    (hz : ∀ x, x ∉ S → ∀ y, k x y = 0) /- [standing] -/
    (z : ℂ) /- [definition] -/ :
    kernelFredholm μ k z = kernelFredholm (μ.restrict S) k z := by
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  exact congrArg (fun v : ℝ => (v : ℂ)*z^n) (kernelCoefficient_restrict_zero_rows μ S hS k hz n)

/-- A single retained label has exactly the half-line measure of its physical coordinate. -/
theorem retainedLabel_measurePreserving
    (m : ℕ /- [definition] -/)
    (i : Fin m /- [definition] -/) :
    MeasurePreserving (fun x : ℝ => (i,x)) halfLineMeasure
      ((timeSpaceMeasure m).restrict {p : TimeSpace m | p.1=i}) := by
  refine ⟨measurable_prodMk_left,?_⟩
  have hset : {p : TimeSpace m | p.1=i} = {i} ×ˢ (Set.univ : Set ℝ) := by ext p; simp
  rw [hset]
  unfold timeSpaceMeasure
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_univ,Measure.restrict_singleton,Measure.count_singleton,one_smul]
  exact (Measure.dirac_prod i).symm

/-- Relabeling one retained slice acts on every variable of each Fredholm coefficient. -/
theorem kernelCoefficient_retainedLabel
    (m n : ℕ /- [definition] -/)
    (i : Fin m /- [definition] -/)
    (k : TimeSpace m → TimeSpace m → ℝ /- [definition] -/) :
    kernelCoefficient halfLineMeasure (fun x y => k (i,x) (i,y)) n =
      kernelCoefficient ((timeSpaceMeasure m).restrict {p : TimeSpace m | p.1=i}) k n := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  unfold kernelCoefficient
  congr 1
  have hemb : MeasurableEmbedding (fun x : Fin n → ℝ => fun a => (i,x a)) := by
    apply MeasurableEmbedding.of_measurable_inverse (by fun_prop)
      (g := fun y : Fin n → TimeSpace m => fun a => (y a).2)
    · have hr : Set.range (fun x : Fin n → ℝ => fun a => (i,x a)) =
          {y : Fin n → TimeSpace m | ∀ a, (y a).1 = i} := by
        ext y
        constructor
        · rintro ⟨x,rfl⟩; simp
        · intro hy
          refine ⟨fun a => (y a).2,?_⟩
          funext a
          exact Prod.ext (hy a).symm rfl
      rw [hr]
      have hi : ∀ a : Fin n, MeasurableSet {y : Fin n → TimeSpace m | (y a).1 = i} := by
        intro a
        exact measurableSet_eq_fun (by fun_prop) measurable_const
      simpa only [Set.setOf_forall] using MeasurableSet.iInter hi
    · fun_prop
    · intro x; rfl
  exact (measurePreserving_pi _ _ (fun _ : Fin n => retainedLabel_measurePreserving m i)).integral_comp
    hemb
    (kernelMinor k n)

/-- A physical block kernel with all but one label removed has the exact TW2 value. -/
theorem removedLabels_Fredholm_eq_TW2
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (i : Fin m /- [definition] -/) :
    kernelFredholm (timeSpaceMeasure m)
      (fun p q => if p.1=i ∧ q.1=i then shiftedExtendedKernel m times cuts p q else 0) (-1) =
      RMTFoundations.TracyWidom.TW2 (cuts i) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  let k : TimeSpace m → TimeSpace m → ℝ :=
    fun p q => if p.1=i ∧ q.1=i then shiftedExtendedKernel m times cuts p q else 0
  have hS : MeasurableSet {p : TimeSpace m | p.1=i} := by measurability
  have hz : ∀ p : TimeSpace m, p ∉ {p : TimeSpace m | p.1=i} → ∀ q, k p q = 0 := by
    intro p hp q
    simp only [Set.mem_setOf_eq] at hp
    simp [k,hp]
  change kernelFredholm (timeSpaceMeasure m) k (-1) = _
  rw [kernelFredholm_restrict_zero_rows _ _ hS k hz]
  have he : kernelFredholm ((timeSpaceMeasure m).restrict {p : TimeSpace m | p.1=i}) k (-1) =
      kernelFredholm halfLineMeasure (fun x y => k (i,x) (i,y)) (-1) := by
    unfold kernelFredholm kernelSeries
    apply tsum_congr
    intro n
    exact congrArg (fun v : ℝ => (v : ℂ)*(-1)^n) (kernelCoefficient_retainedLabel m n i k).symm
  rw [he]
  simpa only [k,and_self,if_true,shiftedExtendedKernel,oneTimeFredholm] using
    oneTimeFredholm_eq_TW2 (times i) (cuts i)

/-- Zero-row restriction is exercised on a genuine nonzero Airy kernel and a retained time label. -/
theorem deletion_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      kernelFredholm (timeSpaceMeasure 2)
        (fun p q => if p.1=(0 : Fin 2) ∧ q.1=0 then shiftedExtendedKernel 2 times cuts p q else 0) (-1) =
        RMTFoundations.TracyWidom.TW2 (-1) ∧
      MeasurePreserving (fun x : ℝ => ((0 : Fin 2),x)) halfLineMeasure
        ((timeSpaceMeasure 2).restrict {p : TimeSpace 2 | p.1=0}) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,?_,retainedLabel_measurePreserving _ _⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · simpa using removedLabels_Fredholm_eq_TW2 2 (fun i => (i.val : ℝ))
      (fun i => if i=0 then -1 else 1) 0

open scoped Classical
/-- Masking discarded rows and columns equals restriction to the surviving measured domain. -/
theorem kernelFredholm_mask_restrict
    {α : Type*} /- [definition] -/
    [MeasurableSpace α] /- [standing] -/
    (μ : Measure α) /- [definition] -/
    [SigmaFinite μ] /- [standing] -/
    (S : Set α) /- [definition] -/
    (hS : MeasurableSet S) /- [standing] -/
    (k : α → α → ℝ) /- [definition] -/
    (z : ℂ) /- [definition] -/ :
    kernelFredholm μ (fun x y => if x∈S ∧ y∈S then k x y else 0) z =
      kernelFredholm (μ.restrict S) k z := by
  let mask : α → α → ℝ := fun x y => if x∈S ∧ y∈S then k x y else 0
  change kernelFredholm μ mask z = _
  rw [kernelFredholm_restrict_zero_rows μ S hS mask (by intro x hx y; simp [mask,hx])]
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  have hc : kernelCoefficient (μ.restrict S) mask n = kernelCoefficient (μ.restrict S) k n := by
    unfold kernelCoefficient
    congr 1
    exact integral_congr_ae (kernelMinor_congr_on_full_measure (μ.restrict S) mask k S
      (ae_restrict_mem hS) (by intro x hx y hy; simp [mask,hx,hy]) n)
  exact congrArg (fun v : ℝ => (v : ℂ)*z^n) hc

/-- Support restriction is jointly instantiated for the nonzero physical Airy kernel. -/
theorem mask_restrict_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      kernelFredholm (timeSpaceMeasure 2)
        (fun p q => if p.1≠(1 : Fin 2) ∧ q.1≠1 then shiftedExtendedKernel 2 times cuts p q else 0) (-1) =
        kernelFredholm ((timeSpaceMeasure 2).restrict {p : TimeSpace 2 | p.1≠1})
          (shiftedExtendedKernel 2 times cuts) (-1) := by
  letI : SigmaFinite (timeSpaceMeasure 2) := by unfold timeSpaceMeasure; infer_instance
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · let k := shiftedExtendedKernel 2 (fun i => (i.val : ℝ)) (fun i => if i=0 then -1 else 1)
    refine Eq.trans ?_ (kernelFredholm_mask_restrict (timeSpaceMeasure 2)
      {p : TimeSpace 2 | p.1≠(1 : Fin 2)} (by measurability) k (-1))
    apply congrArg (fun f : TimeSpace 2 → TimeSpace 2 → ℝ =>
      kernelFredholm (timeSpaceMeasure 2) f (-1))
    funext p q
    by_cases h : p.1≠(1 : Fin 2) ∧ q.1≠1 <;> simp [h] <;> dsimp [k] <;>
      first
      | rfl
      | apply congrArg (fun cuts : Fin 2 → ℝ =>
          shiftedExtendedKernel 2 (fun i => (i.val : ℝ)) cuts p q)
        funext i
        split_ifs <;> rfl


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.kernelCoefficient_restrict_zero_rows
#print axioms RMTFoundations.TracyWidom.Airy2.kernelFredholm_restrict_zero_rows
#print axioms RMTFoundations.TracyWidom.Airy2.retainedLabel_measurePreserving
#print axioms RMTFoundations.TracyWidom.Airy2.kernelCoefficient_retainedLabel
#print axioms RMTFoundations.TracyWidom.Airy2.removedLabels_Fredholm_eq_TW2
#print axioms RMTFoundations.TracyWidom.Airy2.deletion_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.kernelFredholm_mask_restrict
#print axioms RMTFoundations.TracyWidom.Airy2.mask_restrict_all_binder_joint_probe
