import RMTFoundations.TracyWidom.TW4LeftPositive
import RMTFoundations.TracyWidom.TW4ScaledRight
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set
open RMTFoundations.TWOneBounds

/-- Both asymptotic regimes have strict actual GSE density signs. The
intervening compact interval remains an explicit open obligation. -/
theorem exists_TW4AiryR_strictMono_two_tails :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧
      StrictMonoOn TW4AiryR (Iic a) ∧ StrictMonoOn TW4AiryR (Ici b) ∧
      (∀ s, s ≤ a ∨ b ≤ s → 0 < TW4AirySlope s) := by
  obtain ⟨a,ha,hma,hpa⟩ := exists_TW4AiryR_strictMono_left_tail
  obtain ⟨b,hb,hmb,hpb,hu⟩ := exists_TW4AiryR_strictMono_right_tail
  refine ⟨a,b,ha,hb,hma,hmb,?_⟩
  intro s hs
  exact hs.elim (hpa s) (hpb s)

/-- The conventionally scaled actual GSE candidate is strictly increasing
with positive derivative on both genuine nonempty tails. -/
theorem exists_TW4R_strictMono_two_tails :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧
      StrictMonoOn TW4R (Iic a) ∧ StrictMonoOn TW4R (Ici b) ∧
      (∀ s, s ≤ a ∨ b ≤ s → 0 < TW4Slope s) := by
  obtain ⟨c,hc,hm,hp⟩ := exists_TW4AiryR_strictMono_left_tail
  obtain ⟨b,hb,hmb,hpb,hu⟩ := exists_TW4R_strictMono_right_tail
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let a := c/Real.sqrt 2
  have hscale (s : ℝ) (hs : s ≤ a) : Real.sqrt 2*s ≤ c := by
    have h := (le_div_iff₀ hroot).mp hs
    nlinarith
  have hma : StrictMonoOn TW4R (Iic a) := by
    intro x hx y hy hxy
    exact hm (hscale x hx) (hscale y hy) (mul_lt_mul_of_pos_left hxy hroot)
  refine ⟨a,b,div_nonpos_of_nonpos_of_nonneg hc hroot.le,hb,hma,hmb,?_⟩
  intro s hs
  rcases hs with hs | hs
  · exact mul_pos hroot (hp _ (hscale s hs))
  · exact hpb s hs

/-- Every tail-domain, derivative and monotonicity input coexists on one actual
nonzero Airy model at two separated finite points. -/
theorem two_tails_GSE_all_binder_joint_probe :
    ∃ a b x y : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ x ≤ a ∧ b ≤ y ∧ x < y ∧
      airyBoundaryVector (Real.sqrt 2*x) ≠ 0 ∧ airyBoundaryVector (Real.sqrt 2*y) ≠ 0 ∧
      StrictMonoOn TW4R (Iic a) ∧ StrictMonoOn TW4R (Ici b) ∧
      0 < TW4Slope x ∧ 0 < TW4Slope y ∧
      HasDerivAt TW4R (TW4Slope x) x ∧ HasDerivAt TW4R (TW4Slope y) y := by
  obtain ⟨a,b,ha,hb,hma,hmb,hp⟩ := exists_TW4R_strictMono_two_tails
  exact ⟨a,b,a-1,b+1,ha,hb,by linarith,by linarith,by linarith,
    airyBoundaryVector_ne_zero _,airyBoundaryVector_ne_zero _,hma,hmb,
    hp _ (Or.inl (by linarith)),hp _ (Or.inr (by linarith)),
    TW4R_hasDerivAt _,TW4R_hasDerivAt _⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.exists_TW4AiryR_strictMono_two_tails
#print axioms RMTFoundations.TracyWidom.exists_TW4R_strictMono_two_tails
#print axioms RMTFoundations.TracyWidom.two_tails_GSE_all_binder_joint_probe
