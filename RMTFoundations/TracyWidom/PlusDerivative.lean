import RMTFoundations.TracyWidom.OrderOneMonotone


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.PlusDerivative
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal InnerProductSpace BigOperators
open RMTFoundations.Fredholm RMTFoundations.Airy RMTFoundations.AiryBounds
open RMTFoundations.AiryKernel RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone

/-- The genuine physical plus Airy Hankel Fredholm determinant. -/
noncomputable def TWHankelPlusR
    (s : ℝ) -- [definition]
    : ℝ := ∑' n, kernelCoefficient halfLineMeasure (B_fredholmKernel s) n * (1:ℝ)^n

theorem TWHankelPlusR_eq_kernelFredholm_re
    (s : ℝ) -- [definition]
    : TWHankelPlusR s =
      (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) ((1:ℝ):ℂ)).re := by
  rw [← B_fredholm_physical s ((1:ℝ):ℂ)]
  simpa only [TWHankelPlusR,Complex.ofReal_one,Complex.ofReal_re] using
    (congrArg Complex.re (kernelFredholm_real_coupling halfLineMeasure (B_fredholmKernel s) 1)).symm

theorem TWHankelPlusR_eq_realOperatorDet
    {ι : Type*} -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (s : ℝ) -- [definition]
    : TWHankelPlusR s = realOperatorDet b (airyHankelShift s) 1 := by
  letI := airyL2_basis_countable b
  rw [TWHankelPlusR_eq_kernelFredholm_re,airyHankelFredholm_eq_realOperatorDet b s 1,
    Complex.ofReal_re]

theorem airy_eigenvalue_one_add_pos
    {ι : Type*} -- [definition]
    (s : ℝ) -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (lam : ι → ℝ) -- [definition]
    (hd : ∀ i, airyHankelShift s (b i) = lam i • b i) -- [standing]
    (i : ι) -- [definition]
    : 0 < 1 + lam i := by
  have h := (airyHankelShift s).le_opNorm (b i)
  rw [hd i,norm_smul,b.orthonormal.norm_eq_one i,Real.norm_eq_abs,mul_one,mul_one] at h
  have ha := abs_lt.mp (h.trans_lt (norm_airyHankelShift_lt_one s))
  linarith [ha.1]

theorem airy_plus_ringInverse_right
    (s : ℝ) -- [definition]
    (g : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1+airyHankelShift s) g +
      airyHankelShift s (Ring.inverse (1+airyHankelShift s) g) = g := by
  have hn : ‖-airyHankelShift s‖ < 1 := by
    rw [norm_neg]; exact norm_airyHankelShift_lt_one s
  simpa only [sub_neg_eq_add,ContinuousLinearMap.neg_apply] using
    contraction_ringInverse_right (-airyHankelShift s) hn g

theorem airy_plus_eigenbasis_inverse_coefficient
    {ι : Type*} -- [definition]
    (s : ℝ) -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (lam : ι → ℝ) -- [definition]
    (hd : ∀ i, airyHankelShift s (b i) = lam i • b i) -- [standing]
    (g : Lp ℝ 2 halfLineMeasure) -- [definition]
    (i : ι) -- [definition]
    : inner ℝ (b i) (Ring.inverse (1+airyHankelShift s) g) = inner ℝ (b i) g/(1+lam i) := by
  have h := congrArg (inner ℝ (b i))
    (airy_plus_ringInverse_right s g)
  rw [inner_add_right] at h
  have hs := (isSelfAdjoint_airyHankelShift s).isSymmetric
  have hsym : inner ℝ (b i) (airyHankelShift s (Ring.inverse (1+airyHankelShift s) g)) =
      lam i*inner ℝ (b i) (Ring.inverse (1+airyHankelShift s) g) := by
    calc
      _ = inner ℝ (airyHankelShift s (b i)) (Ring.inverse (1+airyHankelShift s) g) := by
        exact (hs (b i) (Ring.inverse (1+airyHankelShift s) g)).symm
      _ = _ := by rw [hd i,real_inner_smul_left]
  rw [hsym] at h
  have hn : 1+lam i ≠ 0 := (airy_eigenvalue_one_add_pos s b lam hd i).ne'
  apply (eq_div_iff hn).mpr
  nlinarith [h]

theorem airy_plus_eigenbasis_inverse_quadratic_hasSum
    {ι : Type*} -- [definition]
    (s : ℝ) -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (lam : ι → ℝ) -- [definition]
    (hd : ∀ i, airyHankelShift s (b i) = lam i • b i) -- [standing]
    (g : Lp ℝ 2 halfLineMeasure) -- [definition]
    : HasSum (fun i => (inner ℝ (b i) g)^2/(1+lam i))
        (inner ℝ g (Ring.inverse (1+airyHankelShift s) g)) := by
  have h := (b.hasSum_repr (Ring.inverse (1+airyHankelShift s) g)).mapL (innerSL ℝ g)
  simpa only [b.repr_apply_apply,innerSL_apply_apply,inner_smul_right,real_inner_comm g,
    airy_plus_eigenbasis_inverse_coefficient s b lam hd,pow_two,div_mul_eq_mul_div] using h

theorem airy_plus_eigenbasis_rankOne_compression_det
    {ι : Type*} -- [definition]
    (s : ℝ) -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (lam : ι → ℝ) -- [definition]
    (hd : ∀ i, airyHankelShift s (b i) = lam i • b i) -- [standing]
    (g : Lp ℝ 2 halfLineMeasure) -- [definition]
    (t : ℝ) -- [definition]
    (v : Finset ι) -- [definition]
    : Matrix.det ((1 : Matrix v v ℝ) + Matrix.of (fun i j : v =>
        inner ℝ (b i) ((airyHankelShift s + t • rankOne ℝ g g) (b j)))) =
      (∏ i ∈ v, (1+lam i))*(1+t*(∑ i ∈ v, (inner ℝ (b i) g)^2/(1+lam i))) := by
  classical
  let d : v → ℝ := fun i => 1+lam i
  let u : v → ℝ := fun i => inner ℝ (b i) g
  have he : (1 : Matrix v v ℝ) + Matrix.of (fun i j : v =>
      inner ℝ (b i) ((airyHankelShift s + t • rankOne ℝ g g) (b j))) =
      Matrix.diagonal d + Matrix.of (fun i j => t*u i*u j) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.of_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,rankOne_apply,inner_add_right,inner_smul_right,hd,
      Matrix.add_apply,Matrix.diagonal_apply,d,u,Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp [b.orthonormal.norm_eq_one,real_inner_comm]
      ring
    · have hne : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
      simp [hij,orthonormal_iff_ite.mp b.orthonormal,hne,real_inner_comm]
      ring
  rw [he,finite_diagonal_rankOne_determinant d u (fun i =>
    (airy_eigenvalue_one_add_pos s b lam hd i).ne')]
  simp only [d,u]
  rw [Finset.prod_coe_sort v (fun i => 1+lam i),
    Finset.sum_coe_sort v (fun i => (inner ℝ (b i) g)^2/(1+lam i))]

theorem airy_plus_rankOne_operatorDet_eigenbasis
    {ι : Type*} -- [definition]
    (s : ℝ) -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (lam : ι → ℝ) -- [definition]
    (hd : ∀ i, airyHankelShift s (b i) = lam i • b i) -- [standing]
    (t : ℝ) -- [definition]
    : realOperatorDet b (airyHankelShift s + t • rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) (1) =
      TWHankelPlusR s * (1+t*inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) := by
  letI := airyL2_basis_countable b
  have hfac : ∃ A B : (Lp ℝ 2 halfLineMeasure) →L[ℝ] (Lp ℝ 2 halfLineMeasure),
      airyHankelShift s + t • rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s) = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖^2) ∧ Summable (fun i => ‖B (b i)‖^2) :=
    ⟨airyMarkedFactor s t,airyVolterraFactor.adjoint,(airyMarkedFactor_comp s t).symm,
      summable_norm_sq_apply_basis (airyMarkedFactor_isHilbertSchmidt s t) b,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint b⟩
  have hleft : Tendsto (fun v : Finset ι => Matrix.det ((1 : Matrix v v ℝ) +
      Matrix.of (fun i j : v => inner ℝ (b i)
        ((airyHankelShift s + t • rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) (b j)))))
      atTop (𝓝 (realOperatorDet b (airyHankelShift s + t • rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) (1))) := by
    simpa only [one_smul] using realOperatorDet_matrix_det_tendsto b _ hfac (1)
  have hp : HasProd (fun i => 1+lam i) (TWHankelPlusR s) := by
    have hm := multipliable_one_add_of_summable (airy_eigenbasis_absolute_on s b lam hd)
    have hv : TWHankelPlusR s = ∏' i, (1+lam i) := by
      rw [TWHankelPlusR_eq_kernelFredholm_re]
      simpa only [one_mul] using airy_eigenbasis_product_on s b lam hd 1
    rw [hv]
    exact hm.hasProd
  have hq := airy_plus_eigenbasis_inverse_quadratic_hasSum s b lam hd (airyBoundaryVector s)
  have hpt : Tendsto (fun v : Finset ι => ∏ i ∈ v, (1+lam i)) atTop (𝓝 (TWHankelPlusR s)) := hp
  have hqt : Tendsto (fun v : Finset ι => ∑ i ∈ v, (inner ℝ (b i) (airyBoundaryVector s))^2/(1+lam i))
      atTop (𝓝 (inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s)))) := hq
  have hright := hpt.mul ((tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := t)).mul hqt))
  simp_rw [airy_plus_eigenbasis_rankOne_compression_det s b lam hd (airyBoundaryVector s) t] at hleft
  exact tendsto_nhds_unique hleft hright

theorem airy_plus_rankOne_operatorDet_canonical
    (s t : ℝ) -- [definition]
    : realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
        (airyHankelShift s + t • rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) (1) =
      TWHankelPlusR s * (1+t*inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) := by
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator (isSelfAdjoint_airyHankelShift s).isSymmetric
  have h := airy_plus_rankOne_operatorDet_eigenbasis s b lam hd t
  rw [← airyRankOneKernel_eq_realOperatorDet b s t (1)] at h
  rw [← airyRankOneKernel_eq_realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)) s t (1)]
  exact h
theorem airyPlusRankOneKernel_series_exact
    (s t : ℝ) -- [definition]
    : (∑' n, kernelCoefficient halfLineMeasure (airyRankOneKernel s t) n*(1:ℝ)^n) =
      TWHankelPlusR s*(1+t*inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) := by
  rw [airyRankOneKernel_eq_realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)),
    airy_plus_rankOne_operatorDet_canonical]

theorem hasDerivAt_airyPlusRankOneKernel_series_resolvent
    (s : ℝ) -- [definition]
    : HasDerivAt
      (fun t => ∑' n, kernelCoefficient halfLineMeasure (airyRankOneKernel s t) n*(1:ℝ)^n)
      (TWHankelPlusR s*inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) 0 := by
  have he := funext (airyPlusRankOneKernel_series_exact s)
  rw [he]
  simpa using
    ((hasDerivAt_const (0:ℝ) (1:ℝ)).fun_add
      ((hasDerivAt_id (0:ℝ)).mul_const
        (inner ℝ (airyBoundaryVector s) (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))))).const_mul (TWHankelPlusR s)


theorem airyPlusBoundaryFredholmSeries_eq_canonical_resolvent
    (s : ℝ) -- [definition]
    : (∑' n, airyBoundaryFredholmCoefficient s n*(1:ℝ)^n) =
      TWHankelPlusR s*(airyAiReal s - inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s))) := by
  rw [airyBoundaryFredholmSeries_rankOne,
    ← (hasDerivAt_airyRankOneKernel_series s 1).deriv,
    (hasDerivAt_airyPlusRankOneKernel_series_resolvent s).deriv]
  change airyAiReal s * TWHankelPlusR s - _ = _
  ring

theorem hasDerivAt_TWHankelPlusR_canonical_resolvent
    (s : ℝ) -- [definition]
    : HasDerivAt TWHankelPlusR
      (-TWHankelPlusR s*(airyAiReal s - inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s)))/2) s := by
  letI := airyL2_basis_countable (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
  have h := hasDerivAt_airy_realOperatorDet_marked_series
    (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)) s 1
  have he : (fun t => realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
      (airyHankelShift t) 1) = TWHankelPlusR :=
    funext (fun t => (TWHankelPlusR_eq_realOperatorDet _ t).symm)
  rw [he,airyPlusBoundaryFredholmSeries_eq_canonical_resolvent] at h
  convert h using 1 <;> ring

theorem hasDerivAt_airyPlus_realOperatorDet_canonical_resolvent
    {ι : Type*} -- [definition]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => realOperatorDet b (airyHankelShift t) 1)
      (-realOperatorDet b (airyHankelShift s) 1*(airyAiReal s - inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1+airyHankelShift s) (airyBoundaryVector s)))/2) s := by
  have he : TWHankelPlusR = fun t => realOperatorDet b (airyHankelShift t) 1 :=
    funext (TWHankelPlusR_eq_realOperatorDet b)
  simpa only [he] using hasDerivAt_TWHankelPlusR_canonical_resolvent s

theorem airy_plus_eigenbasis_all_binder_joint_probe :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) (lam : ι → ℝ),
      (∀ i, airyHankelShift 0 (b i) = lam i • b i) ∧ airyBoundaryVector 0 ≠ 0 ∧
      (∀ i, 0 < 1+lam i) ∧
      (∀ t : ℝ, ∀ v : Finset ι,
        Matrix.det ((1 : Matrix v v ℝ) + Matrix.of (fun i j : v =>
          inner ℝ (b i) ((airyHankelShift 0 + t • rankOne ℝ (airyBoundaryVector 0) (airyBoundaryVector 0)) (b j)))) =
        (∏ i ∈ v, (1+lam i))*(1+t*(∑ i ∈ v, (inner ℝ (b i) (airyBoundaryVector 0))^2/(1+lam i)))) ∧
      HasSum (fun i => (inner ℝ (b i) (airyBoundaryVector 0))^2/(1+lam i))
        (inner ℝ (airyBoundaryVector 0) (Ring.inverse (1+airyHankelShift 0) (airyBoundaryVector 0))) ∧
      (∀ t : ℝ, realOperatorDet b (airyHankelShift 0 + t • rankOne ℝ (airyBoundaryVector 0) (airyBoundaryVector 0)) 1 =
        TWHankelPlusR 0*(1+t*inner ℝ (airyBoundaryVector 0)
          (Ring.inverse (1+airyHankelShift 0) (airyBoundaryVector 0)))) := by
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift 0)
    (isTraceClass_airyHankelShift 0).isCompactOperator (isSelfAdjoint_airyHankelShift 0).isSymmetric
  exact ⟨ι,b,lam,hd,airyBoundaryVector_ne_zero 0,airy_eigenvalue_one_add_pos 0 b lam hd,
    airy_plus_eigenbasis_rankOne_compression_det 0 b lam hd (airyBoundaryVector 0),
    airy_plus_eigenbasis_inverse_quadratic_hasSum 0 b lam hd (airyBoundaryVector 0),
    airy_plus_rankOne_operatorDet_eigenbasis 0 b lam hd⟩

theorem airy_plus_derivative_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧
      HasDerivAt TWHankelPlusR
        (-TWHankelPlusR 0*(airyAiReal 0 - inner ℝ (airyBoundaryVector 0)
          (Ring.inverse (1+airyHankelShift 0) (airyBoundaryVector 0)))/2) 0 := by
  exact ⟨airyBoundaryVector_ne_zero 0,hasDerivAt_TWHankelPlusR_canonical_resolvent 0⟩

end RMTFoundations.TracyWidom.PlusDerivative
#print axioms RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR
#print axioms RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR_eq_kernelFredholm_re
#print axioms RMTFoundations.TracyWidom.PlusDerivative.TWHankelPlusR_eq_realOperatorDet
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_eigenvalue_one_add_pos
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_ringInverse_right
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_eigenbasis_inverse_coefficient
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_eigenbasis_inverse_quadratic_hasSum
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_eigenbasis_rankOne_compression_det
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_rankOne_operatorDet_eigenbasis
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_rankOne_operatorDet_canonical
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airyPlusRankOneKernel_series_exact
#print axioms RMTFoundations.TracyWidom.PlusDerivative.hasDerivAt_airyPlusRankOneKernel_series_resolvent
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airyPlusBoundaryFredholmSeries_eq_canonical_resolvent
#print axioms RMTFoundations.TracyWidom.PlusDerivative.hasDerivAt_TWHankelPlusR_canonical_resolvent
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_eigenbasis_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.PlusDerivative.airy_plus_derivative_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.PlusDerivative.hasDerivAt_airyPlus_realOperatorDet_canonical_resolvent
