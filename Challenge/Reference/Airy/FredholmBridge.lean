import Challenge.Reference.Operator.IntegralRows

namespace RMTFoundations.Fredholm

open MeasureTheory Filter Topology
open scoped Classical ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel

/-- Every Hilbert basis of the actual half-line L2 space has a countable index.
This follows from separability, rather than a new standing assumption. -/
theorem airyL2_basis_countable
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    : Countable ι := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1 / 2 : ℝ))
      (Metric.ball (b j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hi : dist (b i) v < 1 / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hvi
    have hj : dist v (b j) < 1 / 2 := hvj
    have hdist : dist (b i) (b j) < 1 := by
      have ht := dist_triangle (b i) v (b j)
      linarith
    have hsq : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, b.orthonormal.1 i,
        b.orthonormal.1 j, b.orthonormal.2 hij]
      norm_num
    nlinarith [(dist_nonneg : 0 ≤ dist (b i) (b j))]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

/-- The genuine shifted Airy Hankel operator satisfies the bridge's HS hypotheses. -/
theorem airyHankelShift_hs_summable
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : Summable (fun i => ‖airyHankelShift s (b i)‖ ^ 2) :=
  summable_norm_sq_apply_basis (isHilbertSchmidt_airyHankelShift s) b

/-- The Airy Hankel slice representatives jointly give genuine L2 rows and applications. -/
theorem airyHankelShift_rows
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : MemLp (sliceLp halfLineMeasure (airyHankelShiftKernel s)) 2 halfLineMeasure ∧
      (∀ x, ∀ᵐ t ∂halfLineMeasure,
        (sliceLp halfLineMeasure (airyHankelShiftKernel s) x) t = airyAiReal (x + t + s)) ∧
      (∀ f, ∀ᵐ x ∂halfLineMeasure,
        (airyHankelShift s f) x =
          inner ℝ (sliceLp halfLineMeasure (airyHankelShiftKernel s) x) f) := by
  have hev := kernelOperator_eval_inner_ae (memLp_airyHankelShiftKernel s)
  refine ⟨l2_operator_rows_memLp halfLineMeasure b (airyHankelShift s)
    (airyHankelShift_hs_summable b s) _ hev, ?_, hev⟩
  intro x
  simpa only [star_trivial, airyHankelShiftKernel] using
    sliceLp_apply_ae (memLp_airyHankelShiftSlice s x)

/-- For every real level and coupling, the physical Airy kernel series is the
operator determinant of the genuine HS square on L2 of the positive half-line. -/
theorem airyKernelFredholm_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s z : ℝ /- [definition] -/ )
    : kernelFredholm halfLineMeasure
        (fun x y => airyKernelIntegral (x + s) (y + s)) (z : ℂ) =
      (realOperatorDet b (airyKernelShift s) z : ℂ) := by
  have hself : (airyHankelShift s).adjoint = airyHankelShift s :=
    isSelfAdjoint_airyHankelShift s
  have hrows := airyHankelShift_rows b s
  have h := kernelFredholm_convolution_eq_of_integral_factors halfLineMeasure b
    (airyHankelShift s) (airyHankelShift s)
    (airyHankelShift_hs_summable b s) (airyHankelShift_hs_summable b s)
    (fun x t => airyAiReal (x + t + s)) (fun t y => airyAiReal (t + y + s))
    (sliceLp halfLineMeasure (airyHankelShiftKernel s))
    (sliceLp halfLineMeasure (airyHankelShiftKernel s))
    Set.univ (Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun x _ => hrows.2.1 x)
    (fun y _ => by simpa only [add_comm y] using hrows.2.1 y)
    (airyHankelShift_apply_ae s)
    (by
      intro f
      filter_upwards [airyHankelShift_apply_ae s f] with y hy
      simpa only [hself, add_comm] using hy) z
  have hk : (fun x y => ∫ t, airyAiReal (x + t + s) * airyAiReal (t + y + s)
      ∂halfLineMeasure) = (fun x y => airyKernelIntegral (x + s) (y + s)) := by
    funext x y
    simp only [airyKernelIntegral, halfLineMeasure, add_left_comm, add_comm]
  rw [hk] at h
  exact h

/-- TW2 is the entire operator Fredholm determinant at coupling -1, for every
real level. No norm-disk, probability, or coefficient-identification premise. -/
theorem TW2_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : TW2 s = (realOperatorDet b (airyKernelShift s) (-1) : ℂ) := by
  simpa only [TW2, Complex.ofReal_neg, Complex.ofReal_one] using
    airyKernelFredholm_eq_realOperatorDet b s (-1)

/-- The real-valued TW2 definition is exactly the real operator determinant. -/
theorem TW2R_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : TW2R s = realOperatorDet b (airyKernelShift s) (-1) := by
  rw [TW2R, TW2_eq_realOperatorDet b s, Complex.ofReal_re]

/-- Basis independence of the actual Airy operator determinant, with no norm restriction. -/
theorem airyKernel_realOperatorDet_basis_independent
    {ι κ : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    [Countable κ /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (c : HilbertBasis κ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s z : ℝ /- [definition] -/ )
    : realOperatorDet b (airyKernelShift s) z = realOperatorDet c (airyKernelShift s) z := by
  apply Complex.ofReal_injective
  exact (airyKernelFredholm_eq_realOperatorDet b s z).symm.trans
    (airyKernelFredholm_eq_realOperatorDet c s z)

/-- Continuity of the operator formula at the physical coupling, inherited from
canonical kernel continuity after the unconditional operator identification. -/
theorem airyKernel_realOperatorDet_continuous
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    : Continuous (fun s => realOperatorDet b (airyKernelShift s) (-1)) := by
  have he : (fun s => realOperatorDet b (airyKernelShift s) (-1)) = TW2R := by
    funext s
    exact (TW2R_eq_realOperatorDet b s).symm
  rw [he]
  exact Complex.continuous_re.comp TW2_continuous

/-- Analyticity of the actual Airy operator determinant at every real coupling. -/
theorem airyKernel_realOperatorDet_entire
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : AnalyticOnNhd ℝ (realOperatorDet b (airyKernelShift s)) Set.univ := by
  exact realOperatorDet_entire b _ ⟨airyHankelShift s, airyHankelShift s,
    rfl, airyHankelShift_hs_summable b s, airyHankelShift_hs_summable b s⟩

/-- Finite compressions of the actual Airy operator converge to TW2R. This is
an ordinary matrix determinant, useful for positivity and order theorems. -/
theorem TW2R_finite_compressions_tendsto
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : Tendsto (fun t : Finset ι => Matrix.det ((1 : Matrix t t ℝ) -
        Matrix.of (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))))
      atTop (𝓝 (TW2R s)) := by
  letI := airyL2_basis_countable b
  rw [TW2R_eq_realOperatorDet b s]
  simpa only [neg_one_smul, sub_eq_add_neg] using
    realOperatorDet_matrix_det_tendsto b (airyKernelShift s)
      ⟨airyHankelShift s, airyHankelShift s, rfl,
        airyHankelShift_hs_summable b s, airyHankelShift_hs_summable b s⟩ (-1)

/-- Continuity at every real coupling, using the canonical kernel formula. -/
theorem airyKernel_realOperatorDet_continuous_coupling
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : Continuous (fun s => realOperatorDet b (airyKernelShift s) z) := by
  letI := airyL2_basis_countable b
  have he : (fun s => kernelFredholm halfLineMeasure (K_fredholmKernel s) (z : ℂ)) =
      (fun s => (realOperatorDet b (airyKernelShift s) z : ℂ)) := by
    funext s
    exact (K_fredholm_physical s (z : ℂ)).trans
      (airyKernelFredholm_eq_realOperatorDet b s z)
  have hc := K_fredholm_continuous (z : ℂ)
  rw [he] at hc
  simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc

/-- The canonical basis provides a determinant definition without user-supplied basis data. -/
noncomputable def airyOperatorTW2
    (s : ℝ /- [definition] -/ )
    : ℝ := realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
      (airyKernelShift s) (-1)

/-- Unconditional canonical-basis identification of the TW2 definition. -/
theorem TW2_eq_airyOperatorTW2
    (s : ℝ /- [definition] -/ )
    : TW2 s = (airyOperatorTW2 s : ℂ) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  exact TW2_eq_realOperatorDet b s

/-- Unconditional real-valued canonical-basis identification. -/
theorem TW2R_eq_airyOperatorTW2
    (s : ℝ /- [definition] -/ )
    : TW2R s = airyOperatorTW2 s := by
  rw [TW2R, TW2_eq_airyOperatorTW2 s, Complex.ofReal_re]

/-- The actual Airy space, rows, HS square, and canonical determinant are jointly
inhabited. The Airy function and an L2 unit vector certify nondegeneracy. -/
theorem airy_operator_joint_probe
    : ∃ b : HilbertBasis (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ℝ
        (Lp ℝ 2 halfLineMeasure),
      Countable (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ∧
      airyAiReal 0 ≠ 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      Summable (fun i => ‖airyHankelShift 0 (b i)‖ ^ 2) ∧
      (airyHankelShift 0).adjoint = airyHankelShift 0 ∧
      MemLp (sliceLp halfLineMeasure (airyHankelShiftKernel 0)) 2 halfLineMeasure ∧
      (∀ x, ∀ᵐ t ∂halfLineMeasure,
        (sliceLp halfLineMeasure (airyHankelShiftKernel 0) x) t = airyAiReal (x + t)) ∧
      (∀ f, ∀ᵐ x ∂halfLineMeasure, (airyHankelShift 0 f) x =
        inner ℝ (sliceLp halfLineMeasure (airyHankelShiftKernel 0) x) f) ∧
      TW2 0 = (realOperatorDet b (airyKernelShift 0) (-1) : ℂ) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  have hb := airyL2_basis_countable b
  letI := hb
  have hr := airyHankelShift_rows b 0
  refine ⟨b, hb, ?_, shiftedUnitVector_norm 0, airyHankelShift_hs_summable b 0,
    isSelfAdjoint_airyHankelShift 0, hr.1, ?_, hr.2.2, TW2_eq_realOperatorDet b 0⟩
  · exact (airyAiReal_zero_pos).ne'
  · simpa only [add_zero] using hr.2.1


end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.airyL2_basis_countable
#print axioms RMTFoundations.Fredholm.airyHankelShift_hs_summable
#print axioms RMTFoundations.Fredholm.airyHankelShift_rows
#print axioms RMTFoundations.Fredholm.airyKernelFredholm_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.TW2_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.TW2R_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.airyKernel_realOperatorDet_basis_independent
#print axioms RMTFoundations.Fredholm.airyKernel_realOperatorDet_continuous
#print axioms RMTFoundations.Fredholm.airyKernel_realOperatorDet_entire
#print axioms RMTFoundations.Fredholm.TW2R_finite_compressions_tendsto
#print axioms RMTFoundations.Fredholm.airyKernel_realOperatorDet_continuous_coupling
#print axioms RMTFoundations.Fredholm.airyOperatorTW2
#print axioms RMTFoundations.Fredholm.TW2_eq_airyOperatorTW2
#print axioms RMTFoundations.Fredholm.TW2R_eq_airyOperatorTW2
#print axioms RMTFoundations.Fredholm.airy_operator_joint_probe
