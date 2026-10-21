import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom

/-- A positive log-concave endpoint satisfies the exact midpoint product comparison. -/
theorem log_concave_midpoint_product
    (q : ℝ → ℝ /- [definition] -/)
    (s x : ℝ /- [definition] -/)
    (hq : ∀ t, s ≤ t → 0 < q t /- [standing] -/)
    (hc : ConcaveOn ℝ (Set.Ici s) (fun t => Real.log (q t)) /- [standing] -/)
    (hx : 0 ≤ x /- [standing] -/)
    : q s*q (x+x+s) ≤ (q (x+s))^2 := by
  have hmid := hc.2 (show s ∈ Set.Ici s from by simp)
    (show x+x+s ∈ Set.Ici s from by change s ≤ x+x+s; linarith)
    (show (0:ℝ) ≤ 1/2 from by norm_num)
    (show (0:ℝ) ≤ 1/2 from by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1/2:ℝ)*s+(1/2)*(x+x+s) = x+s by ring] at hmid
  have hl : Real.log (q s)+Real.log (q (x+x+s)) ≤
      Real.log (q (x+s))+Real.log (q (x+s)) := by linarith
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add,Real.exp_add,Real.exp_log (hq s le_rfl),
    Real.exp_log (hq (x+x+s) (by linarith)),
    Real.exp_log (hq (x+s) (by linarith)),←pow_two] at he
  exact he

/-- Log-concavity is jointly inhabited by a nonconstant, everywhere positive endpoint. -/
theorem log_concave_midpoint_all_binder_joint_probe :
    ∃ q : ℝ → ℝ, ∃ s : ℝ,
      q s = 1 ∧ q (s+1) ≠ q s ∧
      (∀ t, s ≤ t → 0 < q t) ∧
      ConcaveOn ℝ (Set.Ici s) (fun t => Real.log (q t)) ∧
      (∀ x, 0 ≤ x → q s*q (x+x+s) ≤ (q (x+s))^2) := by
  let q : ℝ → ℝ := fun t => Real.exp (-t)
  have hq (t : ℝ) (ht : 0 ≤ t) : 0 < q t := Real.exp_pos _
  have hc : ConcaveOn ℝ (Set.Ici 0) (fun t => Real.log (q t)) := by
    refine ⟨convex_Ici 0,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [q,Real.log_exp,smul_eq_mul]
    exact le_of_eq (by ring)
  refine ⟨q,0,by simp [q],?_,hq,hc,fun x hx => log_concave_midpoint_product q 0 x hq hc hx⟩
  have he : q (0+1) < q 0 := by
    dsimp [q]
    apply Real.exp_lt_exp.mpr
    norm_num
  exact he.ne
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.log_concave_midpoint_product
#print axioms RMTFoundations.TracyWidom.log_concave_midpoint_all_binder_joint_probe
