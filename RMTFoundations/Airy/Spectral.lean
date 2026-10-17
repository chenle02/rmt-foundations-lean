/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in compact-spectral-LICENSE.
Authors: Adam Benenson; adaptations for this project by Le Chen's lab.
The eigenbasis construction below is adapted from compact-spectral at
72cd62dbdd4c397d26fc0c5777d60fea2211e938; it uses the spectral theorem
already proved in the project's pinned mathlib, with no upstream approximation dependency.
-/
import RMTFoundations.Airy.HankelFactorization
import Mathlib.Analysis.InnerProductSpace.Spectrum
import RMTFoundations.Airy.Distribution

namespace RMTFoundations.Fredholm

open MeasureTheory Filter Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel

universe u

set_option maxHeartbeats 800000

theorem exists_real_hilbert_eigenbasis
    {E : Type u /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : IsSelfAdjoint T /- [standing] -/ )
    (hTc : IsCompactOperator T /- [standing] -/ )
    : ∃ (ι : Type u) (μ : ι → ℝ) (b : HilbertBasis ι ℝ E),
      ∀ i, T (b i) = μ i • b i := by
  classical
  let t : Module.End ℝ E := (T : E →ₗ[ℝ] E)
  have hSymm : t.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  -- Each eigenspace is closed (as a kernel), hence complete.
  have complete_eigenspace : ∀ μ : ℝ, CompleteSpace (t.eigenspace μ) := by
    intro μ
    have hClosed : IsClosed ((t.eigenspace μ : Submodule ℝ E) : Set E) := by
      have :
          ((t.eigenspace μ : Submodule ℝ E) : Set E) =
            (LinearMap.ker ((T - μ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) :
              E →ₗ[ℝ] E) : Set E) := by
        ext x
        simp [t, LinearMap.mem_ker, sub_eq_zero]
      simpa [this] using
        (ContinuousLinearMap.isClosed_ker (f := (T - μ • ContinuousLinearMap.id ℝ E)))
    haveI : CompleteSpace ((t.eigenspace μ : Submodule ℝ E) : Set E) := hClosed.completeSpace_coe
    simpa using (inferInstance : CompleteSpace (t.eigenspace μ))
  -- Choose a Hilbert basis for each eigenspace, indexed by a set of vectors.
  classical
  choose w b hb using (fun μ : ℝ =>
    @exists_hilbertBasis ℝ _ (t.eigenspace μ) _ _ (complete_eigenspace μ))
  let ι : Type u := Σ μ : ℝ, w μ
  let μ' : ι → ℝ := fun i => i.1
  let v : ι → E := fun i => ((b i.1 i.2 : t.eigenspace i.1) : E)
  have hv_orthonormal : Orthonormal ℝ v := by
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨μi, vi⟩
      -- `b μi` is orthonormal in the eigenspace.
      have h' : ‖(b μi vi : t.eigenspace μi)‖ = 1 := by
        have : Orthonormal ℝ (b μi) := (b μi).orthonormal
        exact this.norm_eq_one vi
      -- Coercion to `E` does not change the norm.
      simpa [v] using h'
    · intro i j hij
      rcases i with ⟨μi, vi⟩
      rcases j with ⟨μj, vj⟩
      by_cases hμ : μi = μj
      · subst hμ
        have hv' : Orthonormal ℝ (b μi) := (b μi).orthonormal
        have hij' : vi ≠ vj := by
          intro h
          exact hij (by simp [h])
        -- Orthonormality within one eigenspace.
        have : inner ℝ (b μi vi : t.eigenspace μi) (b μi vj : t.eigenspace μi) = 0 :=
          hv'.2 hij'
        simpa [v] using this
      · -- Distinct eigenspaces are orthogonal for symmetric operators.
        have hOrtho : t.eigenspace μi ⟂ t.eigenspace μj :=
          (hSymm.orthogonalFamily_eigenspaces).isOrtho hμ
        have : inner ℝ (b μi vi : E) (b μj vj : E) = 0 := by
          have hmem : (b μi vi : E) ∈ (t.eigenspace μj)ᗮ :=
            hOrtho (b μi vi).property
          have : inner ℝ (b μj vj : E) (b μi vi : E) = 0 :=
            (Submodule.mem_orthogonal (K := t.eigenspace μj) (v := (b μi vi : E))).1 hmem
              (b μj vj : E) (b μj vj).property
          simpa using (inner_eq_zero_symm.mp this)
        simpa [v] using this
  have hv_span_orth : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    -- If `x` is orthogonal to the span of all basis vectors in all eigenspaces,
    -- then `x` is orthogonal to every eigenspace, hence zero by compactness.
    ext x
    constructor
    · intro hx
      have hxv : ∀ i : ι, inner ℝ (v i) x = 0 := by
        have hx' : ∀ y, y ∈ Submodule.span ℝ (Set.range v) → inner ℝ y x = 0 :=
          (Submodule.mem_orthogonal (K := Submodule.span ℝ (Set.range v)) (v := x)).1 hx
        intro i
        exact hx' (v i) (Submodule.subset_span ⟨i, rfl⟩)
      have hx_eigs : x ∈ (⨆ μ : ℝ, t.eigenspace μ)ᗮ := by
        -- Use `iInf_orthogonal` to show orthogonality to each eigenspace.
        have hx_each : ∀ μ : ℝ, x ∈ (t.eigenspace μ)ᗮ := by
          intro μ
          -- Let `f : t.eigenspace μ →L[ℝ] ℝ` be `y ↦ ⟪x, y⟫`.
          let f : (t.eigenspace μ) →L[ℝ] ℝ := (innerSL ℝ x).comp (t.eigenspace μ).subtypeL
          have hspan_le : Submodule.span ℝ (Set.range (b μ)) ≤ LinearMap.ker f.toLinearMap := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨i, rfl⟩
            change f (b μ i) = 0
            -- `x` is orthogonal to `b μ i`, since it appears among the `v`'s.
            have : inner ℝ x (b μ i : E) = 0 := by
              have : inner ℝ (b μ i : E) x = 0 := by
                -- This is `hxv` at index `⟨μ, i⟩`.
                simpa [v] using hxv ⟨μ, i⟩
              simpa using (inner_eq_zero_symm.mp this)
            simpa [f, ContinuousLinearMap.comp_apply] using this
          have hker_closed : IsClosed ((LinearMap.ker f.toLinearMap : Set (t.eigenspace μ))) := by
            simpa using (ContinuousLinearMap.isClosed_ker (f := f))
          have htop :
              (Submodule.span ℝ (Set.range (b μ))).topologicalClosure = ⊤ :=
            HilbertBasis.dense_span (b μ)
          have htop_le :
              (⊤ : Submodule ℝ (t.eigenspace μ)) ≤ LinearMap.ker f.toLinearMap := by
            -- The kernel is closed and contains a dense submodule, hence is `⊤`.
            have :
                (Submodule.span ℝ (Set.range (b μ))).topologicalClosure ≤
                  LinearMap.ker f.toLinearMap :=
              Submodule.topologicalClosure_minimal
                (Submodule.span ℝ (Set.range (b μ))) hspan_le hker_closed
            simpa [htop] using this
          have hf0 : ∀ y, f y = 0 := by
            intro y
            have : y ∈ LinearMap.ker f.toLinearMap := htop_le (by simp)
            simpa [LinearMap.mem_ker] using this
          -- Conclude `x` is orthogonal to the whole eigenspace.
          refine (Submodule.mem_orthogonal (K := t.eigenspace μ) (v := x)).2 ?_
          intro y hy
          have : inner ℝ x y = 0 := by
            -- `y` is a vector in the eigenspace, viewed as a subtype element.
            have : f ⟨y, hy⟩ = 0 := hf0 ⟨y, hy⟩
            simpa [f, ContinuousLinearMap.comp_apply] using this
          simpa using (inner_eq_zero_symm.mp this)
        -- Now package the pointwise orthogonality.
        have hx_inf : x ∈ ⨅ μ : ℝ, (t.eigenspace μ)ᗮ := by
          refine (Submodule.mem_iInf (p := fun μ : ℝ => (t.eigenspace μ)ᗮ) (x := x)).2 ?_
          intro μ
          exact hx_each μ
        simpa [Submodule.iInf_orthogonal] using hx_inf
      have hx0 : x = 0 := by
        have hxbot : x ∈ (⊥ : Submodule ℝ E) := by
          have :
              (⨆ μ : ℝ, t.eigenspace μ)ᗮ = (⊥ : Submodule ℝ E) :=
            ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hSymm
          simpa [this] using hx_eigs
        simpa using hxbot
      simp [hx0]
    · intro hx0
      subst hx0
      simp
  refine ⟨ι, μ', HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth, ?_⟩
  intro i
  rcases i with ⟨μi, vi⟩
  -- Show each basis vector is a nonzero vector in the `μi`-eigenspace.
  have hmem : (v ⟨μi, vi⟩) ∈ t.eigenspace μi := by
    -- `b μi vi` is an element of the eigenspace subtype.
    simp [v]
  have hne0 : v ⟨μi, vi⟩ ≠ 0 := by
    have hv' : Orthonormal ℝ v := hv_orthonormal
    have hv_norm : ‖v ⟨μi, vi⟩‖ = 1 := hv'.1 ⟨μi, vi⟩
    have hv_norm_ne : ‖v ⟨μi, vi⟩‖ ≠ 0 := by
      simp [hv_norm]
    exact (norm_ne_zero_iff.1 hv_norm_ne)
  -- Identify `b`'s coerced family with `v`.
  have hb' :
      (HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth) ⟨μi, vi⟩ = v ⟨μi, vi⟩ := by
    exact congrArg (fun f : ι → E => f ⟨μi, vi⟩)
      (HilbertBasis.coe_mkOfOrthogonalEqBot hv_orthonormal hv_span_orth)
  rw [hb']
  exact Module.End.mem_eigenspace_iff.mp hmem


/-- Real diagonal-product formula, valid at every coupling and allowing zero factors. -/
theorem realOperatorDet_diagonal
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (a : ι → ℝ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b T z = ∏' i, (1 + z * a i) := by
  classical
  have hsum : Summable (fun i => ‖z * a i‖) := by
    simpa only [norm_mul] using ha.mul_left ‖z‖
  rw [tprod_one_add (summable_finsetProd_of_summable_norm hsum),
    realOperatorDet, realNuclearDet]
  apply tsum_congr
  intro s
  have hm : realNuclearMinor b (fun i => T (b i)) s = ∏ i ∈ s, a i := by
    unfold realNuclearMinor
    have hmatrix : (fun i j : s => inner ℝ (b i) (T (b j))) =
        Matrix.diagonal (fun i : s => a i) := by
      funext i j
      rw [hdiag, inner_smul_right]
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal_apply, b.orthonormal.norm_eq_one]
      · have hval : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
        simp [Matrix.diagonal_apply, hij, b.orthonormal.2 hval]
    rw [hmatrix, Matrix.det_diagonal]
    exact Finset.prod_coe_sort s a
  rw [hm, Finset.prod_mul_distrib, Finset.prod_const]
  exact mul_comm _ _

/-- Trace class forces absolute summability of the actual eigenvalues. -/
theorem real_eigenvalues_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : IsTraceClass T /- [standing] -/ )
    (a : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    : Summable (fun i => ‖a i‖) := by
  simpa only [hdiag, inner_smul_right, real_inner_self_eq_norm_sq,
    b.orthonormal.norm_eq_one, one_pow, mul_one] using
    summable_norm_inner_diagonal hT b

/-- The genuine trace is the sum of eigenvalues, independently of the eigenbasis. -/
theorem real_eigenvalues_hasSum_trace
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : IsTraceClass T /- [standing] -/ )
    (a : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    : HasSum a (trace T) := by
  rw [trace_eq_tsum_inner hT b]
  simpa only [hdiag, inner_smul_right, real_inner_self_eq_norm_sq,
    b.orthonormal.norm_eq_one, one_pow, mul_one] using
    (summable_inner_diagonal hT b).hasSum

/-- Product convergence accompanies the determinant identity. -/
theorem realOperatorDet_diagonal_hasProd
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : IsTraceClass T /- [standing] -/ )
    (a : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : HasProd (fun i => 1 + z * a i) (realOperatorDet b T z) := by
  have ha := real_eigenvalues_absolute b T hT a hdiag
  rw [realOperatorDet_diagonal b T a ha hdiag]
  apply (multipliable_one_add_of_summable ?_).hasProd
  simpa only [norm_mul] using ha.mul_left ‖z‖

/-- Eigenvalues of a bounded real operator obey the operator-norm bound. -/
theorem real_eigenvalue_norm_le
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (v : E /- [definition] -/ )
    (hv : ‖v‖ = 1 /- [standing] -/ )
    (a : ℝ /- [definition] -/ )
    (he : T v = a • v /- [standing] -/ )
    : ‖a‖ ≤ ‖T‖ := by
  have h := T.le_opNorm v
  rw [he, norm_smul, hv, mul_one, mul_one] at h
  exact h

/-- Positivity of the quadratic form forces nonnegative eigenvalues. -/
theorem real_eigenvalue_nonneg
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (hpos : ∀ v, 0 ≤ inner ℝ v (T v)  /- [standing] -/ )
    (v : E /- [definition] -/ )
    (hv : ‖v‖ = 1 /- [standing] -/ )
    (a : ℝ /- [definition] -/ )
    (he : T v = a • v /- [standing] -/ )
    : 0 ≤ a := by
  simpa only [he, inner_smul_right, real_inner_self_eq_norm_sq, hv,
    one_pow, mul_one] using hpos v

/-- The two genuine Airy operators are simultaneously diagonal in a Hilbert basis.
The Airy-kernel eigenvalues are the squares of the Hankel eigenvalues. -/
theorem airy_simultaneous_eigenbasis
    (s : ℝ /- [definition] -/ )
    : ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure))
      (a : ι → ℝ),
      (∀ i, airyHankelShift s (b i) = a i • b i) ∧
      (∀ i, airyKernelShift s (b i) = (a i)^2 • b i) ∧
      Summable (fun i => ‖a i‖) ∧
      Summable (fun i => ‖(a i)^2‖) ∧
      HasSum a (trace (airyHankelShift s)) ∧
      HasSum (fun i => (a i)^2) (trace (airyKernelShift s)) ∧
      (∀ z, HasProd (fun i => 1 + z * a i) ((kernelFredholm halfLineMeasure (fun x y => airyAiReal (x + y + s)) (z : ℂ)).re)) ∧
      (∀ z, HasProd (fun i => 1 + z * (a i)^2) ((kernelFredholm halfLineMeasure (fun x y => airyKernelIntegral (x+s) (y+s)) (z : ℂ)).re)) := by
  obtain ⟨ι, a, b, he⟩ := exists_real_hilbert_eigenbasis (airyHankelShift s)
    (isSelfAdjoint_airyHankelShift s) (isHilbertSchmidt_airyHankelShift s).isCompactOperator
  letI : Countable ι := airyL2_basis_countable b
  have hk (i : ι) : airyKernelShift s (b i) = (a i)^2 • b i := by
    simp only [airyKernelShift, ContinuousLinearMap.comp_apply, he,
      map_smul, smul_smul, pow_two]
  have hB := isTraceClass_airyHankelShift s
  have hK := isTraceClass_airyKernelShift s
  refine ⟨ι, inferInstance, b, a, he, hk,
    real_eigenvalues_absolute b _ hB a he,
    real_eigenvalues_absolute b _ hK _ hk,
    real_eigenvalues_hasSum_trace b _ hB a he,
    real_eigenvalues_hasSum_trace b _ hK _ hk, ?_, ?_⟩
  · intro z
    rw [airyHankelFredholm_eq_realOperatorDet b s z, Complex.ofReal_re]
    exact realOperatorDet_diagonal_hasProd b _ hB a he z
  · intro z
    rw [airyKernelFredholm_eq_realOperatorDet b s z, Complex.ofReal_re]
    exact realOperatorDet_diagonal_hasProd b _ hK _ hk z

/-- Dominated finite-basis projections identify the trace with the Gram diagonal.
The only representation premise is a matrix-entry integral of the actual operator. -/
theorem real_trace_eq_integral_rows_of_entries
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : IsTraceClass T /- [standing] -/ )
    (hentry : ∀ i j, inner ℝ (b i) (T (b j)) =
      ∫ x, inner ℝ (b i) (c x) * inner ℝ (r x) (b j) ∂μ /- [standing] -/ )
    : trace T = ∫ x, inner ℝ (r x) (c x) ∂μ := by
  classical
  let F : Finset ι → X → ℝ := fun s x =>
    inner ℝ (realBasisProjection b s (r x)) (realBasisProjection b s (c x))
  have hleft : Tendsto (fun s => ∫ x, F s x ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (r x) (c x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖r x‖ * ‖c x‖)
    · exact Eventually.of_forall fun s =>
        ((realBasisProjection b s).continuous.comp_aestronglyMeasurable hr.aestronglyMeasurable).inner
        ((realBasisProjection b s).continuous.comp_aestronglyMeasurable hc.aestronglyMeasurable)
    · exact Eventually.of_forall fun s => Eventually.of_forall fun x =>
        (norm_inner_le_norm _ _).trans (mul_le_mul
          (realBasisProjection_norm_le b s (r x))
          (realBasisProjection_norm_le b s (c x)) (norm_nonneg _) (norm_nonneg _))
    · exact hr.norm.integrable_mul hc.norm
    · exact Eventually.of_forall fun x =>
        (realBasisProjection_tendsto b (r x)).inner (realBasisProjection_tendsto b (c x))
  have heq (s : Finset ι) : (∫ x, F s x ∂μ) =
      ∑ i ∈ s, inner ℝ (b i) (T (b i)) := by
    simp only [F, realBasisProjection_inner]
    rw [integral_finsetSum s (fun i _ =>
      (hr.inner_const (b i)).integrable_mul (hc.const_inner (b i)))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hentry]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  simp_rw [heq] at hleft
  have hright : Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℝ (b i) (T (b i)))
      atTop (𝓝 (trace T)) := by
    rw [trace_eq_tsum_inner hT b]
    exact (summable_inner_diagonal hT b).hasSum
  exact tendsto_nhds_unique hright hleft

/-- The kernel-application identities suffice to prove the trace formula for AB. -/
theorem real_trace_comp_eq_integral_rows
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (hevalA : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    (hevalBadj : ∀ f, ∀ᵐ x ∂μ, (B.adjoint f) x = inner ℝ (c x) f /- [standing] -/ )
    : trace (A ∘L B) = ∫ x, inner ℝ (r x) (c x) ∂μ := by
  have hr := l2_operator_rows_memLp μ b A
    (summable_norm_sq_apply_basis hA b) r hevalA
  have hc := l2_operator_rows_memLp μ b B.adjoint
    (summable_norm_sq_apply_basis hB.adjoint b) c hevalBadj
  rw [trace_comp_comm hA hB]
  apply real_trace_eq_integral_rows_of_entries μ b r c hr hc (B ∘L A)
    ⟨B, A, hB, hA, rfl⟩
  intro i j
  rw [ContinuousLinearMap.comp_apply, ← B.adjoint_inner_left (A (b j)) (b i), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hevalBadj (b i), hevalA (b j)] with x hi hj
  simp only [hi, hj, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    real_inner_comm (b i), mul_comm]

/-- The Airy kernel trace equals its canonical diagonal integral at every real level. -/
theorem trace_airyKernelShift_eq_diagonal
    (s : ℝ /- [definition] -/ )
    : trace (airyKernelShift s) =
      ∫ x, airyKernelIntegral (x + s) (x + s) ∂halfLineMeasure := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  have hself : (airyHankelShift s).adjoint = airyHankelShift s :=
    isSelfAdjoint_airyHankelShift s
  have h := real_trace_comp_eq_integral_rows halfLineMeasure b
    (airyHankelShift s) (airyHankelShift s)
    (isHilbertSchmidt_airyHankelShift s) (isHilbertSchmidt_airyHankelShift s)
    (sliceLp halfLineMeasure (airyHankelShiftKernel s))
    (sliceLp halfLineMeasure (airyHankelShiftKernel s))
    (kernelOperator_eval_inner_ae (memLp_airyHankelShiftKernel s))
    (by
      intro f
      rw [hself]
      exact kernelOperator_eval_inner_ae (memLp_airyHankelShiftKernel s) f)
  change trace (airyKernelShift s) = _ at h
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [sliceLp_apply_ae (memLp_airyHankelShiftSlice s x)] with t ht
    simp only [Real.inner_apply, ht, star_trivial, airyHankelShiftKernel,
      airyKernelIntegral, halfLineMeasure, add_assoc, add_left_comm, add_comm]

/-- The trace of the Hankel operator equals the actual Airy Hankel diagonal integral. -/
theorem trace_airyHankelShift_eq_diagonal
    (s : ℝ /- [definition] -/ )
    : trace (airyHankelShift s) =
      ∫ x, airyAiReal (x + x + s) ∂halfLineMeasure := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  rw [airyHankelShift_eq_derivative_volterra]
  have h := real_trace_comp_eq_integral_rows halfLineMeasure b
    (airyDerivativeFactor s) airyVolterraFactor.adjoint
    (isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel s))
    (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint
    (sliceLp halfLineMeasure (airyDerivativeFactorKernel s))
    (sliceLp halfLineMeasure airyVolterraFactorKernel)
    (kernelOperator_eval_inner_ae (memLp_airyDerivativeFactorKernel s))
    (by simpa only [ContinuousLinearMap.adjoint_adjoint, airyVolterraFactor] using
      kernelOperator_eval_inner_ae memLp_airyVolterraFactorKernel)
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [L2.inner_def]
  have hi : (∫ t, inner ℝ
      ((sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x) t)
      ((sliceLp halfLineMeasure airyVolterraFactorKernel x) t) ∂halfLineMeasure) =
      ∫ t, airyDerivativeFactorKernel s (x,t) * airyVolterraFactorKernel (x,t)
        ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [sliceLp_apply_ae (memLp_airyDerivativeFactorRow s x),
      sliceLp_apply_ae (memLp_airyVolterraFactorRow x)] with t hd hv
    simp only [Real.inner_apply, hd, hv, star_trivial, mul_comm]
  rw [hi, airyDerivative_volterra_convolution s x x hx.le hx.le]

/-- Physical-coordinate trace formula on (s,infinity). -/
theorem trace_airyKernelShift_eq_tail
    (s : ℝ /- [definition] -/ )
    : trace (airyKernelShift s) = ∫ x in Set.Ioi s, airyKernelIntegral x x := by
  rw [trace_airyKernelShift_eq_diagonal]
  exact (fredholm_measurePreserving_shift s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding
    (fun x => airyKernelIntegral x x)

/-- The Hankel trace is the standard one-half Airy tail integral. -/
theorem trace_airyHankelShift_eq_half_tail
    (s : ℝ /- [definition] -/ )
    : trace (airyHankelShift s) = (1 / 2 : ℝ) * ∫ x in Set.Ioi s, airyAiReal x := by
  rw [trace_airyHankelShift_eq_diagonal]
  have hmul := integral_comp_mul_left_Ioi (fun x => airyAiReal (x + s)) 0
    (by norm_num : (0 : ℝ) < 2)
  have hshift := (fredholm_measurePreserving_shift s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding airyAiReal
  simpa only [halfLineMeasure, two_mul, mul_zero, smul_eq_mul, inv_eq_one_div,
    hshift] using hmul


/-- Nonnegativity of the Airy-kernel quadratic form is unconditional. -/
theorem airyKernelShift_quadratic_nonneg
    (s : ℝ /- [definition] -/ )
    (v : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : 0 ≤ inner ℝ v (airyKernelShift s v) := by
  have h := (isSelfAdjoint_airyHankelShift s).isSymmetric v (airyHankelShift s v)
  change inner ℝ (airyHankelShift s v) (airyHankelShift s v) =
    inner ℝ v (airyKernelShift s v) at h
  rw [← h, real_inner_self_eq_norm_sq]
  positivity

/-- Contraction bounds imply the stated intervals for Airy eigenvalues and their squares. -/
theorem airy_simultaneous_eigenvalue_intervals
    {ι : Type* /- [definition] -/ }
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (a : ι → ℝ /- [definition] -/ )
    (he : ∀ i, airyHankelShift s (b i) = a i • b i /- [standing] -/ )
    (hnorm : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : ∀ i, -1 ≤ a i ∧ a i ≤ 1 ∧ 0 ≤ (a i)^2 ∧ (a i)^2 ≤ 1 := by
  intro i
  have hk : airyKernelShift s (b i) = (a i)^2 • b i := by
    simp only [airyKernelShift, ContinuousLinearMap.comp_apply, he,
      map_smul, smul_smul, pow_two]
  have hn := (real_eigenvalue_norm_le (airyKernelShift s) (b i)
    (b.orthonormal.norm_eq_one i) ((a i)^2) hk).trans hnorm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hn
  exact ⟨by nlinarith, by nlinarith, sq_nonneg _, hn⟩

/-- All physical trace and product data, with a constructed countable eigenbasis. -/
theorem airy_spectral_data
    (s : ℝ /- [definition] -/ )
    : ∃ (ι : Type) (_ : Countable ι)
      (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) (a : ι → ℝ),
      (∀ i, airyHankelShift s (b i) = a i • b i) ∧
      (∀ i, airyKernelShift s (b i) = (a i)^2 • b i) ∧
      Summable (fun i => ‖a i‖) ∧ Summable (fun i => ‖(a i)^2‖) ∧
      HasSum a ((1 / 2 : ℝ) * ∫ x in Set.Ioi s, airyAiReal x) ∧
      HasSum (fun i => (a i)^2) (∫ x in Set.Ioi s, airyKernelIntegral x x) ∧
      (∀ z : ℝ, HasProd (fun i => 1 + z * a i)
        ((kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) (z : ℂ)).re)) ∧
      (∀ z : ℝ, HasProd (fun i => 1 + z * (a i)^2)
        ((kernelFredholm halfLineMeasure
          (fun x y => airyKernelIntegral (x+s) (y+s)) (z : ℂ)).re)) := by
  obtain ⟨ι, hι, b, a, he, hk, ha, hak, htB, htK, hpB, hpK⟩ :=
    airy_simultaneous_eigenbasis s
  rw [trace_airyHankelShift_eq_half_tail s] at htB
  rw [trace_airyKernelShift_eq_tail s] at htK
  exact ⟨ι, hι, b, a, he, hk, ha, hak, htB, htK, hpB, hpK⟩

/-- A countable scalar spectral family can be indexed by natural numbers by padding with zeros. -/
theorem real_spectral_padding
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (a : ι → ℝ /- [definition] -/ )
    (tB tK : ℝ /- [definition] -/ )
    (dB dK : ℝ → ℝ /- [definition] -/ )
    (htB : HasSum a tB /- [standing] -/ )
    (htK : HasSum (fun i => (a i)^2) tK /- [standing] -/ )
    (hpB : ∀ z, HasProd (fun i => 1 + z * a i) (dB z)  /- [standing] -/ )
    (hpK : ∀ z, HasProd (fun i => 1 + z * (a i)^2) (dK z)  /- [standing] -/ )
    : ∃ e : ℕ → ℝ,
      (∀ n, e n = 0 ∨ ∃ i, e n = a i) ∧
      HasSum e tB ∧ HasSum (fun n => (e n)^2) tK ∧
      (∀ z, HasProd (fun n => 1 + z * e n) (dB z)) ∧
      (∀ z, HasProd (fun n => 1 + z * (e n)^2) (dK z)) := by
  classical
  letI := Encodable.ofCountable ι
  let f : ι → ℕ := Encodable.encode
  have hf : Function.Injective f := Encodable.encode_injective
  let e : ℕ → ℝ := Function.extend f a 0
  have hsquare : (fun n => (e n)^2) = Function.extend f (fun i => (a i)^2) 0 := by
    funext n
    by_cases hn : ∃ i, f i = n
    · obtain ⟨i,rfl⟩ := hn
      simp only [e,hf.extend_apply]
    · simp only [e,Function.extend_apply' _ _ _ hn, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]
  have hprod (z : ℝ) : (fun n => 1 + z * e n) =
      Function.extend f (fun i => 1 + z * a i) 1 := by
    funext n
    by_cases hn : ∃ i, f i = n
    · obtain ⟨i,rfl⟩ := hn
      simp only [e,hf.extend_apply]
    · simp only [e,Function.extend_apply' _ _ _ hn, Pi.zero_apply, Pi.one_apply, mul_zero, add_zero]
  have hprodK (z : ℝ) : (fun n => 1 + z * (e n)^2) =
      Function.extend f (fun i => 1 + z * (a i)^2) 1 := by
    funext n
    by_cases hn : ∃ i, f i = n
    · obtain ⟨i,rfl⟩ := hn
      simp only [e,hf.extend_apply]
    · simp only [e,Function.extend_apply' _ _ _ hn, Pi.zero_apply, Pi.one_apply,
        zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  refine ⟨e, ?_, (hasSum_extend_zero hf).2 htB, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : ∃ i, f i = n
    · obtain ⟨i,rfl⟩ := hn
      exact Or.inr ⟨i,hf.extend_apply a 0 i⟩
    · exact Or.inl (Function.extend_apply' (f := f) a (0 : ℕ → ℝ) n hn)
  · rw [hsquare]
    exact (hasSum_extend_zero hf).2 htK
  · intro z
    rw [hprod]
    exact (hasProd_extend_one hf).2 (hpB z)
  · intro z
    rw [hprodK]
    exact (hasProd_extend_one hf).2 (hpK z)

/-- Literal natural-index trace/product bridge requested by TWE; unconditional. -/
theorem airy_nat_spectral_data
    (s : ℝ /- [definition] -/ )
    : ∃ e : ℕ → ℝ,
      HasSum e ((1 / 2 : ℝ) * ∫ x in Set.Ioi s, airyAiReal x) ∧
      HasSum (fun n => (e n)^2) (∫ x in Set.Ioi s, airyKernelIntegral x x) ∧
      (∀ z : ℝ, HasProd (fun n => 1 + z * e n)
        ((kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) (z : ℂ)).re)) ∧
      (∀ z : ℝ, HasProd (fun n => 1 + z * (e n)^2)
        ((kernelFredholm halfLineMeasure
          (fun x y => airyKernelIntegral (x+s) (y+s)) (z : ℂ)).re)) ∧
      (∀ n, 0 ≤ (e n)^2) ∧
      (‖airyKernelShift s‖ ≤ 1 → ∀ n, -1 ≤ e n ∧ e n ≤ 1 ∧ (e n)^2 ≤ 1) := by
  obtain ⟨ι,hι,b,a,he,hk,ha,hak,htB,htK,hpB,hpK⟩ := airy_spectral_data s
  letI : Countable ι := hι
  obtain ⟨e,hval,htB,htK,hpB,hpK⟩ := real_spectral_padding a _ _ _ _ htB htK hpB hpK
  refine ⟨e,htB,htK,hpB,hpK,fun n => sq_nonneg _, ?_⟩
  intro hnorm n
  rcases hval n with hz | ⟨i,hi⟩
  · rw [hz]
    norm_num
  · rw [hi]
    have h := airy_simultaneous_eigenvalue_intervals s b a he hnorm i
    exact ⟨h.1,h.2.1,h.2.2.2⟩

/-- The physical TW2 product and trace bridge, retaining only the supplied norm bound. -/
theorem TW2R_spectral_bridge_of_contraction
    (s : ℝ /- [definition] -/ )
    (hnorm : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ (∀ n, e n ≤ 1) ∧
      HasProd (fun n => 1 - e n) (TW2R s) ∧
      HasSum e (∫ x in Set.Ioi s, airyKernelIntegral x x) := by
  obtain ⟨a,htB,htK,hpB,hpK,hpos,hbounds⟩ := airy_nat_spectral_data s
  refine ⟨fun n => (a n)^2, hpos, fun n => (hbounds hnorm n).2.2, ?_, htK⟩
  simpa only [TW2R,TW2,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,
    sub_eq_add_neg] using hpK (-1)

/-- The physical TW1 product and trace bridge uses the same constructed spectral family. -/
theorem TW1R_spectral_bridge_of_contraction
    (s : ℝ /- [definition] -/ )
    (hnorm : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : ∃ e : ℕ → ℝ, (∀ n, -1 ≤ e n) ∧ (∀ n, e n ≤ 1) ∧
      HasProd (fun n => 1 - e n) (TW1R s) ∧
      HasSum e ((1 / 2 : ℝ) * ∫ x in Set.Ioi s, airyAiReal x) ∧
      HasSum (fun n => (e n)^2) (∫ x in Set.Ioi s, airyKernelIntegral x x) := by
  obtain ⟨a,htB,htK,hpB,hpK,hpos,hbounds⟩ := airy_nat_spectral_data s
  refine ⟨a,fun n => (hbounds hnorm n).1, fun n => (hbounds hnorm n).2.1, ?_, htB,htK⟩
  simpa only [TW1R,TW1,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,
    sub_eq_add_neg] using hpB (-1)

/-- Closed contraction permits zero determinants, and still gives the full probability range. -/
theorem TW2R_mem_Icc_of_contraction
    (s : ℝ /- [definition] -/ )
    (hnorm : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : TW2R s ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨a,hpos,hle,hprod,htrace⟩ := TW2R_spectral_bridge_of_contraction s hnorm
  constructor
  · exact ge_of_tendsto hprod (Eventually.of_forall fun S =>
      Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hle i)))
  · exact le_of_tendsto hprod (Eventually.of_forall fun S =>
      Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (hle i))
        (fun i _ => by linarith [hpos i]))

/-- A nondegenerate actual Airy instance satisfies all unconditional spectral premises jointly. -/
theorem airy_spectral_joint_probe
    : 0 < airyAiReal 0 ∧ ‖RMTFoundations.Airy.shiftedUnitVector 0‖ = 1 ∧
      (∃ (ι : Type) (_ : Countable ι)
        (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) (a : ι → ℝ),
        (∀ i, airyHankelShift 0 (b i) = a i • b i) ∧
        (∀ i, airyKernelShift 0 (b i) = (a i)^2 • b i) ∧
        Summable (fun i => ‖a i‖) ∧ Summable (fun i => ‖(a i)^2‖) ∧
        HasSum a ((1 / 2 : ℝ) * ∫ x in Set.Ioi 0, airyAiReal x) ∧
        HasSum (fun i => (a i)^2) (∫ x in Set.Ioi 0, airyKernelIntegral x x) ∧
        (∀ z : ℝ, HasProd (fun i => 1 + z * a i)
          ((kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y)) (z : ℂ)).re)) ∧
        (∀ z : ℝ, HasProd (fun i => 1 + z * (a i)^2)
          ((kernelFredholm halfLineMeasure
            (fun x y => airyKernelIntegral x y) (z : ℂ)).re))) := by
  refine ⟨airyAiReal_pos_of_nonneg (by norm_num),
    RMTFoundations.Airy.shiftedUnitVector_norm 0, ?_⟩
  simpa only [add_zero] using airy_spectral_data 0

/-- The spectral contraction bounds hold together on a nondegenerate Airy instance. -/
theorem airy_contraction_spectral_joint_probe
    : ∃ s : ℝ, 0 ≤ s ∧ ‖airyKernelShift s‖ ≤ 1 ∧
      0 < airyAiReal s ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      TW2R s ∈ Set.Icc (0 : ℝ) 1 ∧
      (∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ (∀ n, e n ≤ 1) ∧
        HasProd (fun n => 1 - e n) (TW2R s) ∧
        HasSum e (∫ x in Set.Ioi s, airyKernelIntegral x x)) ∧
      (∃ e : ℕ → ℝ, (∀ n, -1 ≤ e n) ∧ (∀ n, e n ≤ 1) ∧
        HasProd (fun n => 1 - e n) (TW1R s) ∧
        HasSum e ((1 / 2 : ℝ) * ∫ x in Set.Ioi s, airyAiReal x) ∧
        HasSum (fun n => (e n)^2) (∫ x in Set.Ioi s, airyKernelIntegral x x)) := by
  obtain ⟨s, hnorm, hs⟩ :=
    (RMTFoundations.AiryDistribution.eventually_norm_airyKernelShift_lt_one.and
      (eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨s,hs,hnorm.le,airyAiReal_pos_of_nonneg hs,shiftedUnitVector_norm 0,
    TW2R_mem_Icc_of_contraction s hnorm.le,
    TW2R_spectral_bridge_of_contraction s hnorm.le,
    TW1R_spectral_bridge_of_contraction s hnorm.le⟩

/-- The real diagonal product is valid outside the small-norm disk, including a zero factor.
All diagonal, absolute-sum and trace-class premises are jointly realized on infinite-dimensional l2. -/
theorem real_diagonal_spectral_joint_probe
    : ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∃ a : ℕ → ℝ,
      IsTraceClass T ∧ Summable (fun i => ‖a i‖) ∧
      (∀ i, T (b i) = a i • b i) ∧ ‖T (b 0)‖ = 2 ∧
      realOperatorDet b T 1 = 3 ∧ realOperatorDet b T (-1 / 2) = 0 ∧
      HasSum a (trace T) ∧
      (∀ z, HasProd (fun i => 1 + z * a i) (realOperatorDet b T z)) := by
  let b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  let B := RMTFoundations.Airy.rankOne ℝ (b 0) (b 0)
  let A := (2 : ℝ) • B
  let T := A ∘L B
  let a : ℕ → ℝ := fun i => if i = 0 then 2 else 0
  have ha : Summable (fun i => ‖a i‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [a, hi]
  have he : ∀ i, T (b i) = a i • b i := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [T,A,B,a,RMTFoundations.Airy.rankOne_apply,b.orthonormal.norm_eq_one 0]
    · simp [T,A,B,a,RMTFoundations.Airy.rankOne_apply,orthonormal_iff_ite.mp b.orthonormal,hi,Ne.symm hi]
  have hB : IsHilbertSchmidt B := isHilbertSchmidt_rankOne (𝕜 := ℝ) (b 0) (b 0)
  have hA : IsHilbertSchmidt A := by
    have h := isHilbertSchmidt_rankOne (𝕜 := ℝ) (b 0) ((2 : ℝ) • b 0)
    have hEq : RMTFoundations.Airy.rankOne ℝ (b 0) ((2 : ℝ) • b 0) = A := by
      ext v
      simp [A,B,RMTFoundations.Airy.rankOne_apply,smul_smul,mul_comm]
    rw [hEq] at h
    exact h
  have hT : IsTraceClass T := ⟨A,B,hA,hB,rfl⟩
  have hd (z : ℝ) : realOperatorDet b T z = 1 + z * 2 := by
    rw [realOperatorDet_diagonal b T a ha he, tprod_eq_prod (s := {0})]
    · simp [a]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [a,hi]
  refine ⟨b,T,a,hT,ha,he,?_,?_,?_,
    real_eigenvalues_hasSum_trace b T hT a he,
    realOperatorDet_diagonal_hasProd b T hT a he⟩
  · rw [he]
    simp [a,norm_smul,b.orthonormal.norm_eq_one 0]
  · rw [hd]
    norm_num
  · rw [hd]
    norm_num

end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.exists_real_hilbert_eigenbasis
#print axioms RMTFoundations.Fredholm.realOperatorDet_diagonal
#print axioms RMTFoundations.Fredholm.real_eigenvalues_absolute
#print axioms RMTFoundations.Fredholm.real_eigenvalues_hasSum_trace
#print axioms RMTFoundations.Fredholm.realOperatorDet_diagonal_hasProd
#print axioms RMTFoundations.Fredholm.real_eigenvalue_norm_le
#print axioms RMTFoundations.Fredholm.real_eigenvalue_nonneg
#print axioms RMTFoundations.Fredholm.airy_simultaneous_eigenbasis
#print axioms RMTFoundations.Fredholm.real_trace_eq_integral_rows_of_entries
#print axioms RMTFoundations.Fredholm.real_trace_comp_eq_integral_rows
#print axioms RMTFoundations.Fredholm.trace_airyKernelShift_eq_diagonal
#print axioms RMTFoundations.Fredholm.trace_airyHankelShift_eq_diagonal
#print axioms RMTFoundations.Fredholm.trace_airyKernelShift_eq_tail
#print axioms RMTFoundations.Fredholm.trace_airyHankelShift_eq_half_tail
#print axioms RMTFoundations.Fredholm.airyKernelShift_quadratic_nonneg
#print axioms RMTFoundations.Fredholm.airy_simultaneous_eigenvalue_intervals
#print axioms RMTFoundations.Fredholm.airy_spectral_data
#print axioms RMTFoundations.Fredholm.real_spectral_padding
#print axioms RMTFoundations.Fredholm.airy_nat_spectral_data
#print axioms RMTFoundations.Fredholm.TW2R_spectral_bridge_of_contraction
#print axioms RMTFoundations.Fredholm.TW1R_spectral_bridge_of_contraction
#print axioms RMTFoundations.Fredholm.TW2R_mem_Icc_of_contraction
#print axioms RMTFoundations.Fredholm.airy_spectral_joint_probe
#print axioms RMTFoundations.Fredholm.airy_contraction_spectral_joint_probe
#print axioms RMTFoundations.Fredholm.real_diagonal_spectral_joint_probe
