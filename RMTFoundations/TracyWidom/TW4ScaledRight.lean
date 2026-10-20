import RMTFoundations.TracyWidom.TW4RightPositive
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set Filter
open RMTFoundations.Airy RMTFoundations.TWOneBounds

/-- The conventionally scaled GSE candidate has a genuine positive
right-ray density and is strictly increasing there. No global CDF is assumed. -/
theorem exists_TW4R_strictMono_right_tail :
    ∃ a : ℝ, 0 ≤ a ∧ StrictMonoOn TW4R (Ici a) ∧
      (∀ s, a ≤ s → 0 < TW4Slope s) ∧
      (∀ s, a ≤ s → TW4R s < 1) := by
  obtain ⟨b,hb,hm,hp,hu⟩ := exists_TW4AiryR_strictMono_right_tail
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let a := b/Real.sqrt 2
  have hscale (s : ℝ) (hs : a ≤ s) : b ≤ Real.sqrt 2*s := by
    have h := (div_le_iff₀ hroot).mp hs
    linarith
  have hmono : StrictMonoOn TW4R (Ici a) := by
    intro x hx y hy hxy
    exact hm (hscale x hx) (hscale y hy) (mul_lt_mul_of_pos_left hxy hroot)
  refine ⟨a,div_nonneg hb hroot.le,hmono,?_,?_⟩
  · intro s hs
    exact mul_pos hroot (hp _ (hscale s hs))
  · intro s hs
    exact hu _ (hscale s hs)

/-- The scaled and raw right-ray properties are realized on the same actual
nonzero Airy model, including the pointwise derivative identification. -/
theorem scaled_right_GSE_all_binder_joint_probe :
    ∃ a s : ℝ, 0 ≤ a ∧ a ≤ s ∧ airyBoundaryVector (Real.sqrt 2*s) ≠ 0 ∧
      StrictMonoOn TW4R (Ici a) ∧ 0 < TW4Slope s ∧ TW4R s < 1 ∧
      HasDerivAt TW4R (TW4Slope s) s := by
  obtain ⟨a,ha,hm,hp,hu⟩ := exists_TW4R_strictMono_right_tail
  exact ⟨a,a,ha,le_rfl,airyBoundaryVector_ne_zero _,hm,hp a le_rfl,
    hu a le_rfl,TW4R_hasDerivAt a⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.exists_TW4R_strictMono_right_tail
#print axioms RMTFoundations.TracyWidom.scaled_right_GSE_all_binder_joint_probe
