import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom

/-- A global hyperbolic bound, proved by derivative comparison. -/
theorem sinh_le_mul_cosh_of_nonneg
    (x : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/)
    : Real.sinh x ≤ x*Real.cosh x := by
  have hd (t : ℝ) : HasDerivAt (fun t => t*Real.cosh t-Real.sinh t)
      (t*Real.sinh t) t := by
    convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t) using 1 <;> simp only [id_eq] <;> ring
  have hm : MonotoneOn (fun t => t*Real.cosh t-Real.sinh t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro t ht
      exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (fun t => t*Real.cosh t-Real.sinh t) t
      rw [(hd t).deriv]
      have ht0 : 0 ≤ t := by
        have : 0 < t := by simpa only [interior_Ici,Set.mem_Ioi] using ht
        exact this.le
      exact mul_nonneg ht0 (Real.sinh_nonneg_iff.mpr ht0)
  have h := hm (by simp) hx hx
  simp only [zero_mul,Real.sinh_zero,sub_zero] at h
  linarith

/-- The integral-comparison margin suffices for the GSE cosh sign. -/
theorem cosh_response_nonneg_of_half_tail_bound
    (q u m : ℝ /- [definition] -/)
    (hq : 0 ≤ q /- [standing] -/)
    (hm : 0 ≤ m /- [standing] -/)
    (hu : q*m/2 ≤ u /- [standing] -/)
    : 0 ≤ u*Real.cosh (m/2)-q*Real.sinh (m/2) := by
  have hs := sinh_le_mul_cosh_of_nonneg (m/2) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hs hq
  have h2 := mul_le_mul_of_nonneg_right hu (Real.cosh_pos (m/2)).le
  nlinarith

/-- Strict hyperbolic comparison for a nonzero tail. -/
theorem sinh_lt_mul_cosh_of_pos
    (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/)
    : Real.sinh x < x*Real.cosh x := by
  have hd (t : ℝ) : HasDerivAt (fun t => t*Real.cosh t-Real.sinh t)
      (t*Real.sinh t) t := by
    convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t) using 1 <;> simp only [id_eq] <;> ring
  have hm : StrictMonoOn (fun t => t*Real.cosh t-Real.sinh t) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro t ht
      change 0 < deriv (fun t => t*Real.cosh t-Real.sinh t) t
      rw [(hd t).deriv]
      have ht0 : 0 < t := by simpa only [interior_Ici,Set.mem_Ioi] using ht
      exact mul_pos ht0 (Real.sinh_pos_iff.mpr ht0)
  have h := hm (by simp) hx.le hx
  simp only [zero_mul,Real.sinh_zero,sub_zero] at h
  linarith

/-- Strict sign needs no strict improvement in the square-tail bound. -/
theorem cosh_response_pos_of_half_tail_bound
    (q u m : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hm : 0 < m /- [standing] -/)
    (hu : q*m/2 ≤ u /- [standing] -/)
    : 0 < u*Real.cosh (m/2)-q*Real.sinh (m/2) := by
  have hs := sinh_lt_mul_cosh_of_pos (m/2) (by linarith)
  have h1 := mul_lt_mul_of_pos_left hs hq
  have h2 := mul_le_mul_of_nonneg_right hu (Real.cosh_pos (m/2)).le
  nlinarith

/-- Chain-rule density formula for arbitrary classical cosh profiles. -/
theorem hasDerivAt_cosh_profile
    (g m : ℝ → ℝ /- [definition] -/)
    (s q u : ℝ /- [definition] -/)
    (hg : HasDerivAt g u s /- [standing] -/)
    (hm : HasDerivAt m (-q) s /- [standing] -/)
    : HasDerivAt (fun t => Real.exp (g t/2)*Real.cosh (m t/2))
      (Real.exp (g s/2)*(u*Real.cosh (m s/2)-q*Real.sinh (m s/2))/2) s := by
  convert! ((hg.div_const 2).exp).mul ((hm.div_const 2).cosh) using 1 <;> ring

/-- Monotonicity from a proved square-tail comparison; no distribution premise. -/
theorem cosh_profile_monotone_of_half_tail_bound
    (g m q u : ℝ → ℝ /- [definition] -/)
    (hg : ∀ s, HasDerivAt g (u s) s /- [standing] -/)
    (hm : ∀ s, HasDerivAt m (-q s) s /- [standing] -/)
    (hq : ∀ s, 0 ≤ q s /- [standing] -/)
    (hp : ∀ s, 0 ≤ m s /- [standing] -/)
    (hu : ∀ s, q s*m s/2 ≤ u s /- [standing] -/)
    : Monotone (fun s => Real.exp (g s/2)*Real.cosh (m s/2)) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun s => hasDerivAt_cosh_profile g m s (q s) (u s) (hg s) (hm s))
  intro s
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le
    (cosh_response_nonneg_of_half_tail_bound (q s) (u s) (m s) (hq s) (hp s) (hu s)))
    (by norm_num)

/-- Strictly increasing cosh profiles from positive endpoints and the same tail bound. -/
theorem cosh_profile_strictMono_of_half_tail_bound
    (g m q u : ℝ → ℝ /- [definition] -/)
    (hg : ∀ s, HasDerivAt g (u s) s /- [standing] -/)
    (hm : ∀ s, HasDerivAt m (-q s) s /- [standing] -/)
    (hq : ∀ s, 0 < q s /- [standing] -/)
    (hp : ∀ s, 0 < m s /- [standing] -/)
    (hu : ∀ s, q s*m s/2 ≤ u s /- [standing] -/)
    : StrictMono (fun s => Real.exp (g s/2)*Real.cosh (m s/2)) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(hasDerivAt_cosh_profile g m s (q s) (u s) (hg s) (hm s)).deriv]
  exact div_pos (mul_pos (Real.exp_pos _)
    (cosh_response_pos_of_half_tail_bound (q s) (u s) (m s) (hq s) (hp s) (hu s)))
    (by norm_num)

/-- All global profile premises hold jointly for a nonconstant exponential endpoint. -/
theorem cosh_sign_all_binder_joint_probe :
    ∃ g m q u : ℝ → ℝ,
      q 0 = 1 ∧ m 0 = 1 ∧ u 0 = 1/2 ∧
      (∀ s, HasDerivAt g (u s) s) ∧
      (∀ s, HasDerivAt m (-q s) s) ∧
      (∀ s, 0 < q s) ∧ (∀ s, 0 < m s) ∧
      (∀ s, q s*m s/2 ≤ u s) ∧
      Monotone (fun s => Real.exp (g s/2)*Real.cosh (m s/2)) ∧
      StrictMono (fun s => Real.exp (g s/2)*Real.cosh (m s/2)) := by
  let q : ℝ → ℝ := fun s => Real.exp (-s)
  let g : ℝ → ℝ := fun s => -(q s)^2/4
  let u : ℝ → ℝ := fun s => (q s)^2/2
  have hq (s : ℝ) : HasDerivAt q (-q s) s := by
    simpa only [q,Pi.neg_apply,id_eq,mul_neg_one] using ((hasDerivAt_id s).neg).exp
  have hg (s : ℝ) : HasDerivAt g (u s) s := by
    convert! (((hq s).pow 2).neg).div_const 4 using 1 <;> dsimp [g,u] <;> ring
  have hp (s : ℝ) : 0 < q s := Real.exp_pos _
  have hu (s : ℝ) : q s*q s/2 ≤ u s := by dsimp [u]; rw [pow_two]
  refine ⟨g,q,q,u,?_,?_,?_,hg,hq,hp,hp,hu,?_⟩
  · simp [q]
  · simp [q]
  · norm_num [u,q]
  · exact ⟨cosh_profile_monotone_of_half_tail_bound g q q u hg hq
      (fun s => (hp s).le) (fun s => (hp s).le) hu,
      cosh_profile_strictMono_of_half_tail_bound g q q u hg hq hp hp hu⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.sinh_le_mul_cosh_of_nonneg
#print axioms RMTFoundations.TracyWidom.cosh_response_nonneg_of_half_tail_bound
#print axioms RMTFoundations.TracyWidom.sinh_lt_mul_cosh_of_pos
#print axioms RMTFoundations.TracyWidom.cosh_response_pos_of_half_tail_bound
#print axioms RMTFoundations.TracyWidom.hasDerivAt_cosh_profile
#print axioms RMTFoundations.TracyWidom.cosh_profile_monotone_of_half_tail_bound
#print axioms RMTFoundations.TracyWidom.cosh_profile_strictMono_of_half_tail_bound
#print axioms RMTFoundations.TracyWidom.cosh_sign_all_binder_joint_probe
