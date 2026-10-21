import Mathlib
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2RectangleLimits
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.Airy2Probability

/-- Successive upper-minus-lower coordinate differences; in m dimensions this
retains every one of the 2^m corners, including the mixed corners. -/
noncomputable def rectangleDifference (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (F : (Fin m → ℝ) → ℝ /- [definition] -/)
    (a b : Fin m → ℝ /- [definition] -/) : ℝ :=
  match l with
  | [] => F b
  | i :: l => rectangleDifference m l F a b -
      rectangleDifference m l F a (Function.update b i (a i))

def restrictedRectangle (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (a b : Fin m → ℝ /- [definition] -/) : Set (Fin m → ℝ) :=
  {x | (∀ i, x i ≤ b i) ∧ ∀ i ∈ l, a i < x i}

theorem restrictedRectangle_measurable (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (a b : Fin m → ℝ /- [definition] -/) : MeasurableSet (restrictedRectangle m l a b) := by
  have he : restrictedRectangle m l a b = lowerBox m b ∩
      ⋂ i ∈ l.toFinset, (fun x : Fin m → ℝ => x i) ⁻¹' Ioi (a i) := by
    ext x; simp [restrictedRectangle,lowerBox]
  rw [he]
  exact (lowerBox_measurable m b).inter (MeasurableSet.biInter l.toFinset.countable_toSet (fun i _ =>
    measurableSet_Ioi.preimage (measurable_pi_apply i)))

theorem rectangleDifference_jointCDF_eq (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (hnodup : l.Nodup /- [standing] -/)
    (μ : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (a b : Fin m → ℝ /- [definition] -/)
    (hab : ∀ i ∈ l, a i ≤ b i /- [standing] -/) :
    rectangleDifference m l (jointCDF m μ) a b =
      (μ : Measure (Fin m → ℝ)).real (restrictedRectangle m l a b) := by
  classical
  induction l generalizing b with
  | nil => simp [rectangleDifference,jointCDF,restrictedRectangle,lowerBox]
  | cons i l ih =>
    have hn : i ∉ l ∧ l.Nodup := List.nodup_cons.mp hnodup
    let b' : Fin m → ℝ := Function.update b i (a i)
    have hb : ∀ j ∈ l, a j ≤ b j := fun j hj => hab j (List.mem_cons_of_mem i hj)
    have hb' : ∀ j ∈ l, a j ≤ b' j := by
      intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hn.1 hj
      simpa [b',Function.update_of_ne hji] using hb j hj
    have hsub : restrictedRectangle m l a b' ⊆ restrictedRectangle m l a b := by
      intro x hx
      refine ⟨fun j => (hx.1 j).trans ?_,hx.2⟩
      by_cases hji : j=i
      · subst j
        simpa [b'] using hab i (List.mem_cons_self)
      · simp [b',Function.update_of_ne hji]
    have he : restrictedRectangle m (i::l) a b =
        restrictedRectangle m l a b \ restrictedRectangle m l a b' := by
      ext x
      simp only [restrictedRectangle,mem_setOf_eq,Set.mem_sdiff,List.mem_cons,forall_eq_or_imp]
      constructor
      · rintro ⟨hxb,hxi,hxl⟩
        refine ⟨⟨hxb,hxl⟩,?_⟩
        rintro ⟨hx',_⟩
        have h := hx' i
        have hh : x i ≤ a i := by simpa [b'] using h
        exact (not_le.mpr hxi) hh
      · rintro ⟨⟨hxb,hxl⟩,hnot⟩
        refine ⟨hxb,?_,hxl⟩
        by_contra hx
        apply hnot
        refine ⟨?_,hxl⟩
        intro j
        by_cases hji : j=i
        · subst j
          simpa [b'] using le_of_not_gt hx
        · simpa [b',Function.update_of_ne hji] using hxb j
    change rectangleDifference m l (jointCDF m μ) a b -
      rectangleDifference m l (jointCDF m μ) a b' = _
    rw [ih hn.2 b hb,ih hn.2 b' hb',he,measureReal_sdiff hsub
      (restrictedRectangle_measurable m l a b')]

/-- The rectangle increment of any dimension is a literal probability mass. -/
theorem rectangleDifference_jointCDF_nonneg (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (hnodup : l.Nodup /- [standing] -/)
    (μ : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (a b : Fin m → ℝ /- [definition] -/)
    (hab : ∀ i ∈ l, a i ≤ b i /- [standing] -/) :
    0 ≤ rectangleDifference m l (jointCDF m μ) a b := by
  rw [rectangleDifference_jointCDF_eq m l hnodup μ a b hab]
  exact measureReal_nonneg

/-- Pointwise limits preserve all finite rectangle increments. -/
theorem rectangleDifference_tendsto (m : ℕ /- [definition] -/)
    (l : List (Fin m) /- [definition] -/)
    (F : ℕ → (Fin m → ℝ) → ℝ /- [definition] -/)
    (G : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => F n s) atTop (𝓝 (G s)) /- [standing] -/)
    (a b : Fin m → ℝ /- [definition] -/) :
    Tendsto (fun n => rectangleDifference m l (F n) a b) atTop
      (𝓝 (rectangleDifference m l G a b)) := by
  classical
  induction l generalizing b with
  | nil => exact hlim b
  | cons i l ih => exact (ih b).sub (ih (Function.update b i (a i)))

theorem pointwise_limit_all_rectangles_nonneg (m : ℕ /- [definition] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (G : (Fin m → ℝ) → ℝ /- [definition] -/)
    (hlim : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop (𝓝 (G s))
      /- [standing] -/)
    (l : List (Fin m) /- [definition] -/)
    (hnodup : l.Nodup /- [standing] -/)
    (a b : Fin m → ℝ /- [definition] -/)
    (hab : ∀ i ∈ l, a i ≤ b i /- [standing] -/) :
    0 ≤ rectangleDifference m l G a b := by
  apply ge_of_tendsto (rectangleDifference_tendsto m l (fun n => jointCDF m (μ n)) G hlim a b)
  exact Eventually.of_forall fun n => rectangleDifference_jointCDF_nonneg m l hnodup (μ n) a b hab

/-- The entire inclusion-exclusion and pointwise-limit chain is applied on a
nondegenerate two-dimensional TW2 law; its rectangle has strictly positive mass. -/
theorem rectangle_limits_all_binder_joint_probe :
    let μ : ProbabilityMeasure (Fin 2 → ℝ) :=
      ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
    let F := jointCDF 2 (TW2ProductLaw 2)
    ([0,1] : List (Fin 2)).Nodup ∧
    (∀ i ∈ ([0,1] : List (Fin 2)), (-1 : ℝ) ≤ 0) ∧
    (∀ s, Tendsto (fun _ : ℕ => jointCDF 2 μ s) atTop (𝓝 (F s))) ∧
    rectangleDifference 2 [0,1] F (fun _ => -1) (fun _ => 0) =
      (TW2ProductLaw 2).real (restrictedRectangle 2 [0,1] (fun _ => -1) (fun _ => 0)) ∧
    0 < rectangleDifference 2 [0,1] F (fun _ => -1) (fun _ => 0) ∧
    0 ≤ rectangleDifference 2 [0,1] F (fun _ => -1) (fun _ => 0) := by
  dsimp only
  let μ : ProbabilityMeasure (Fin 2 → ℝ) :=
    ⟨TW2ProductLaw 2,TW2ProductLaw_probability 2⟩
  let F := jointCDF 2 (TW2ProductLaw 2)
  have hn : ([0,1] : List (Fin 2)).Nodup := by decide
  have hab : ∀ i ∈ ([0,1] : List (Fin 2)), (-1 : ℝ) ≤ 0 := by intros; norm_num
  have hl : ∀ s, Tendsto (fun _ : ℕ => jointCDF 2 μ s) atTop (𝓝 (F s)) :=
    fun _ => tendsto_const_nhds
  have he : rectangleDifference 2 [0,1] F (fun _ => -1) (fun _ => 0) =
      (RMTFoundations.TracyWidom.TW2R 0 - RMTFoundations.TracyWidom.TW2R (-1))^2 := by
    simp [F,rectangleDifference,TW2ProductLaw_jointCDF,Fin.prod_univ_two,Function.update]
    ring
  have hp : 0 < RMTFoundations.TracyWidom.TW2R 0 - RMTFoundations.TracyWidom.TW2R (-1) :=
    sub_pos.mpr (RMTFoundations.TracyWidom.TW2R_strictMono (by norm_num : (-1 : ℝ) < 0))
  exact ⟨hn,hab,hl,rectangleDifference_jointCDF_eq 2 [0,1] hn μ
      (fun _ => -1) (fun _ => 0) hab,
    he.symm ▸ sq_pos_of_pos hp,
    pointwise_limit_all_rectangles_nonneg 2 (fun _ => μ) F hl [0,1] hn
      (fun _ => -1) (fun _ => 0) hab⟩
end RMTFoundations.TracyWidom.Airy2RectangleLimits

#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.rectangleDifference
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.restrictedRectangle
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.restrictedRectangle_measurable
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.rectangleDifference_jointCDF_eq
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.rectangleDifference_jointCDF_nonneg
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.rectangleDifference_tendsto
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.pointwise_limit_all_rectangles_nonneg
#print axioms RMTFoundations.TracyWidom.Airy2RectangleLimits.rectangle_limits_all_binder_joint_probe
