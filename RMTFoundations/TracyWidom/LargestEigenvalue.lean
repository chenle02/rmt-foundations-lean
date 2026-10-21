import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.LargestEigenvalue
open scoped Matrix Matrix.Norms.L2Operator BigOperators ComplexInnerProductSpace Topology
open Matrix
section LamMax

variable {k : Type* /- [definition] -/} [Fintype k /- [definition] -/] [DecidableEq k /- [definition] -/]

/-- The largest eigenvalue, by its variational characterization. -/
noncomputable def lamMax (H : Matrix k k ℂ /- [definition] -/) : ℝ :=
  ⨆ x : {x : EuclideanSpace ℂ k // x ≠ 0}, (toEuclideanCLM (𝕜 := ℂ) H).rayleighQuotient x

theorem rayleigh_bdd (H : Matrix k k ℂ /- [definition] -/) :
    BddAbove (Set.range fun x : {x : EuclideanSpace ℂ k // x ≠ 0} =>
      (toEuclideanCLM (𝕜 := ℂ) H).rayleighQuotient x) :=
  ⟨‖H‖, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans ((toEuclideanCLM (𝕜 := ℂ) H).rayleighQuotient_le_norm x)⟩

theorem lamMax_le_add_norm [Nonempty k /- [definition] -/] (H1 H2 : Matrix k k ℂ /- [definition] -/) :
    lamMax H1 ≤ lamMax H2 + ‖H1 - H2‖ := by
  haveI : Nonempty {x : EuclideanSpace ℂ k // x ≠ 0} := by
    obtain ⟨i⟩ := ‹Nonempty k›
    exact ⟨⟨EuclideanSpace.single i 1, by simp⟩⟩
  refine ciSup_le fun x => ?_
  set T1 := toEuclideanCLM (𝕜 := ℂ) H1
  set T2 := toEuclideanCLM (𝕜 := ℂ) H2
  have hT : T1 = T2 + toEuclideanCLM (𝕜 := ℂ) (H1 - H2) := by
    simp [T1, T2, map_sub]
  have h1 : T1.rayleighQuotient x = T2.rayleighQuotient x
      + (toEuclideanCLM (𝕜 := ℂ) (H1 - H2)).rayleighQuotient x := by
    rw [hT, ContinuousLinearMap.rayleighQuotient_add]
  have h2 : T2.rayleighQuotient x ≤ lamMax H2 := le_ciSup (rayleigh_bdd H2) x
  have h3 : (toEuclideanCLM (𝕜 := ℂ) (H1 - H2)).rayleighQuotient x ≤ ‖H1 - H2‖ :=
    (le_abs_self _).trans ((toEuclideanCLM (𝕜 := ℂ) (H1 - H2)).rayleighQuotient_le_norm x)
  linarith

/-- **Weyl's inequality** for the largest eigenvalue. -/
theorem abs_lamMax_sub_le [Nonempty k /- [definition] -/] (H1 H2 : Matrix k k ℂ /- [definition] -/) :
    |lamMax H1 - lamMax H2| ≤ ‖H1 - H2‖ := by
  have a := lamMax_le_add_norm H1 H2
  have b := lamMax_le_add_norm H2 H1
  rw [← norm_neg, neg_sub] at b
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- `lamMax` is an eigenvalue ... -/
theorem lamMax_hasEigenvalue [Nonempty k /- [definition] -/] (H : Matrix k k ℂ /- [definition] -/) (hH : H.IsHermitian /- [standing] -/) :
    Module.End.HasEigenvalue (toEuclideanLin H) (lamMax H : ℂ) := by
  haveI : Nontrivial (EuclideanSpace ℂ k) := by
    obtain ⟨i⟩ := ‹Nonempty k›
    exact ⟨⟨EuclideanSpace.single i 1, 0, by simp⟩⟩
  have hS : (toEuclideanLin H).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have h := hS.hasEigenvalue_iSup_of_finiteDimensional
  have e : lamMax H = ⨆ x : {x : EuclideanSpace ℂ k // x ≠ 0},
      RCLike.re (inner ℂ (toEuclideanLin H (x : EuclideanSpace ℂ k)) (x : EuclideanSpace ℂ k))
        / ‖(x : EuclideanSpace ℂ k)‖ ^ 2 := rfl
  rw [e]
  exact h

/-- ... and it dominates every eigenvalue: it is the largest one. -/
theorem eigenvalues_le_lamMax (H : Matrix k k ℂ /- [definition] -/) (hH : H.IsHermitian /- [standing] -/) (i : k /- [definition] -/) :
    hH.eigenvalues i ≤ lamMax H := by
  set v := hH.eigenvectorBasis i
  have hv1 : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have hv0 : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv1; exact zero_ne_one hv1
  have hTv : toEuclideanCLM (𝕜 := ℂ) H v = (hH.eigenvalues i : ℂ) • v := by
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul]
    rw [hH.mulVec_eigenvectorBasis i, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hr : (toEuclideanCLM (𝕜 := ℂ) H).rayleighQuotient v = hH.eigenvalues i := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hTv,
      inner_smul_left, inner_self_eq_norm_sq_to_K, hv1]
    simp
  rw [← hr]
  exact le_ciSup (rayleigh_bdd H) ⟨v, hv0⟩

end LamMax
variable {k : Type* /- [definition] -/} [Fintype k /- [definition] -/] [DecidableEq k /- [definition] -/]

/-- The variational `λ_max` is one of the eigenvalues. -/
theorem exists_eig_eq_lamMax [Nonempty k /- [definition] -/] (H : Matrix k k ℂ /- [definition] -/) (hH : H.IsHermitian /- [standing] -/) :
    ∃ i, hH.eigenvalues i = lamMax H := by
  have h := lamMax_hasEigenvalue H hH
  have hs : ((lamMax H : ℝ) : ℂ) ∈ spectrum ℂ (toEuclideanLin H) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp h
  have e : spectrum ℂ (toEuclideanLin H) = spectrum ℂ H := Matrix.spectrum_toLpLin 2
  rw [e, hH.spectrum_eq_image_range] at hs
  obtain ⟨x, ⟨i, rfl⟩, he⟩ := hs
  exact ⟨i, RCLike.ofReal_injective he⟩

/-- "Every eigenvalue `≤ E`" is `λ_max ≤ E`. -/
theorem lamMax_le_iff [Nonempty k /- [definition] -/] (H : Matrix k k ℂ /- [definition] -/) (hH : H.IsHermitian /- [standing] -/) (E : ℝ /- [definition] -/) :
    lamMax H ≤ E ↔ ∀ i, hH.eigenvalues i ≤ E := by
  refine ⟨fun h i => (eigenvalues_le_lamMax H hH i).trans h, fun h => ?_⟩
  obtain ⟨i, hi⟩ := exists_eig_eq_lamMax H hH
  rw [← hi]; exact h i


/-- `λ_max` is `1`-Lipschitz for the operator norm (Weyl), hence continuous. -/
theorem continuous_lamMax {k : ℕ /- [definition] -/} [Nonempty (Fin k) /- [definition] -/] :
    Continuous (lamMax : Matrix (Fin k) (Fin k) ℂ → ℝ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun H1 H2 => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_lamMax_sub_le H1 H2


/-- A nonzero three-dimensional Hermitian instance jointly supports continuity and the spectral cutoff equivalence. -/
theorem all_binder_joint_probe :
    ∃ H : Matrix (Fin 3) (Fin 3) ℂ, ∃ hH : H.IsHermitian,
      H ≠ 0 ∧ Continuous (lamMax : Matrix (Fin 3) (Fin 3) ℂ → ℝ) ∧
      (∀ E : ℝ, lamMax H ≤ E ↔ ∀ i, hH.eigenvalues i ≤ E) := by
  refine ⟨1, Matrix.isHermitian_one, ?_, continuous_lamMax, fun E => lamMax_le_iff _ _ E⟩
  intro h
  have h00 := congrArg (fun H : Matrix (Fin 3) (Fin 3) ℂ => H 0 0) h
  norm_num at h00

end RMTFoundations.TracyWidom.LargestEigenvalue

#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.lamMax
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.rayleigh_bdd
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.lamMax_le_add_norm
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.abs_lamMax_sub_le
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.lamMax_hasEigenvalue
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.eigenvalues_le_lamMax
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.exists_eig_eq_lamMax
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.lamMax_le_iff
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.continuous_lamMax
#print axioms RMTFoundations.TracyWidom.LargestEigenvalue.all_binder_joint_probe
