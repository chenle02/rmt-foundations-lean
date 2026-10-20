import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation
open Set Filter MeasureTheory Real
open scoped Topology
/-- Explicit threshold for a positive quadratic tail. -/
lemma quadratic_lower (a b M x : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/)
    (hx1 : 1 ≤ x /- [standing] -/)
    (hx : (|M|+|b|+1)/a ≤ x /- [standing] -/) :
    M < a*x^2-b := by
  have hlin : |M|+|b|+1 ≤ x*a := (div_le_iff₀ ha).mp hx
  have hsq : x ≤ x^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq ha.le
  nlinarith [le_abs_self M, le_abs_self b]
lemma quadratic_unbounded (a b s M : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/) :
    ∃ x : ℝ, s ≤ x ∧ M < a*x^2-b := by
  let x := max (max s 1) ((|M|+|b|+1)/a)
  refine ⟨x, (le_max_left s 1).trans (le_max_left _ _), ?_⟩
  exact quadratic_lower a b M x ha
    ((le_max_right s 1).trans (le_max_left _ _)) (le_max_right _ _)

lemma quadratic_tendsto (a b : ℝ /- [definition] -/) (ha : 0 < a /- [standing] -/) :
    Tendsto (fun x : ℝ => a*x^2-b) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (max 1 ((|M|+|b|+1)/a))] with x hx
  exact (quadratic_lower a b M x ha ((le_max_left _ _).trans hx)
    ((le_max_right _ _).trans hx)).le

lemma quadratic_abs_tendsto (a b : ℝ /- [definition] -/) (ha : 0 < a /- [standing] -/) :
    Tendsto (fun x : ℝ => |a*x^2-b|) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (max 1 ((|M|+|b|+1)/a))] with x hx
  exact (quadratic_lower a b M x ha ((le_max_left _ _).trans hx)
    ((le_max_right _ _).trans hx)).le.trans (le_abs_self _)

lemma no_bdd (a b s : ℝ /- [definition] -/) (ha : 0 < a /- [standing] -/) :
    ¬ BddAbove ((fun x => |a*x^2-b|) '' Ici s) := by
  rintro ⟨M,hM⟩
  obtain ⟨x,hx,he⟩ := quadratic_unbounded a b s M ha
  have hb := hM (show |a*x^2-b| ∈ (fun x => |a*x^2-b|) '' Ici s from ⟨x,hx,rfl⟩)
  linarith [le_abs_self (a*x^2-b)]

lemma no_sup (a b s : ℝ /- [definition] -/) (ha : 0 < a /- [standing] -/) :
    ¬ ∃ η : ℝ, ∀ x, s ≤ x → |a*x^2-b| ≤ η := by
  rintro ⟨η,hη⟩
  obtain ⟨x,hx,he⟩ := quadratic_unbounded a b s η ha
  linarith [hη x hx, le_abs_self (a*x^2-b)]

lemma positive_tail (a b : ℝ /- [definition] -/) (ha : 0 < a /- [standing] -/) :
    ∃ R : ℝ, ∀ x, R ≤ x → 1 ≤ a*x^2-b := by
  refine ⟨max 1 ((|(1:ℝ)|+|b|+1)/a),?_⟩
  intro x hx
  exact (quadratic_lower a b 1 x ha ((le_max_left _ _).trans hx)
    ((le_max_right _ _).trans hx)).le

/-- All real parameters vary; positive coefficient and both threshold conditions
hold jointly with a genuinely nonzero quadratic at every positive dimension. -/
theorem quadratic_joint_probe (n : ℕ /- [definition] -/) :
    ∃ a b s M x : ℝ, 0 < a ∧ 0 < b ∧ 0 < s ∧ 0 < M ∧
      1 ≤ x ∧ (|M|+|b|+1)/a ≤ x ∧ s ≤ x ∧ M < a*x^2-b := by
  let a : ℝ := 1 / ((n+1:ℕ):ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  let x : ℝ := max 1 ((|(1:ℝ)|+|(1:ℝ)|+1)/a)
  refine ⟨a,1,1,1,x,ha,by norm_num,by norm_num,by norm_num,
    le_max_left _ _,le_max_right _ _,le_max_left _ _,?_⟩
  exact quadratic_lower a 1 1 x ha (le_max_left _ _) (le_max_right _ _)

end RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation

#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_lower
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_unbounded
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_tendsto
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_abs_tendsto
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.no_bdd
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.no_sup
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.positive_tail
#print axioms RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_joint_probe
