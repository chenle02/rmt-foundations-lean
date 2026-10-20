import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.PositiveSquareFloor
open Filter
/-- A positive function whose square has a positive linear floor tends
to infinity. No differential equation is a premise. -/
theorem positive_square_floor_tendsto
    (f : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (g : ℝ /- [definition] -/)
    (hp : ∀ t ≥ a, 0 < f t /- [standing] -/)
    (hg : 0 < g /- [standing] -/)
    (hfloor : ∀ t ≥ a, g*t ≤ (f t)^2 /- [standing] -/)
    : Tendsto f atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop (max a (M^2/g))] with t ht
  have hta : a ≤ t := le_trans (le_max_left _ _) ht
  have htg : M^2/g ≤ t := le_trans (le_max_right _ _) ht
  have hMs : M^2 ≤ (f t)^2 :=
    le_trans (by nlinarith [(div_le_iff₀ hg).mp htg]) (hfloor t hta)
  by_contra hn
  have hlt : f t < M := lt_of_not_ge hn
  have hM : 0 ≤ M := le_of_lt (lt_trans (hp t hta) hlt)
  have hh := (sq_lt_sq₀ (hp t hta).le hM).mpr hlt
  exact not_lt_of_ge hMs hh
/-- exp supplies every positive-square-floor binder jointly. -/
theorem square_floor_all_binder_joint_probe :
    ∃ (f : ℝ → ℝ) (a g : ℝ), (∀ t ≥ a, 0 < f t) ∧
      0 < g ∧ (∀ t ≥ a, g*t ≤ (f t)^2) ∧
      f 0=1 ∧ f 1>1 ∧ Tendsto f atTop atTop := by
  have hp : ∀ t ≥ (0:ℝ), 0 < Real.exp t := fun t _ => Real.exp_pos t
  have hfloor : ∀ t ≥ (0:ℝ), (1:ℝ)*t ≤ (Real.exp t)^2 := by
    intro t ht
    have hh := Real.add_one_le_exp t
    nlinarith [sq_nonneg (Real.exp t-1)]
  have he : 1 < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
  exact ⟨Real.exp,0,1,hp,by norm_num,hfloor,by simp,he,
    positive_square_floor_tendsto Real.exp 0 1 hp (by norm_num) hfloor⟩
end RMTFoundations.TracyWidom.PositiveSquareFloor
#print axioms RMTFoundations.TracyWidom.PositiveSquareFloor.positive_square_floor_tendsto
#print axioms RMTFoundations.TracyWidom.PositiveSquareFloor.square_floor_all_binder_joint_probe
