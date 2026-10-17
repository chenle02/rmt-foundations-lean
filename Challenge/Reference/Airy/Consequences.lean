import Challenge.Reference.TracyWidom.OrderTwo
import Challenge.Reference.Airy.Contraction
import Mathlib
import Challenge.Reference.Airy.HankelFactorization
import Challenge.Reference.Airy.Continuity
import Challenge.Reference.Airy.Distribution

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.AiryConsequences

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
open RMTFoundations.Airy RMTFoundations.AiryContinuity
open RMTFoundations.AiryDistribution RMTFoundations.AiryKernel RMTFoundations.Fredholm


section finite_matrix_helpers

open Matrix
open scoped MatrixOrder

/-- The determinant of a positive matrix below the identity is at most one. -/
theorem det_le_one {n : Type* /- [definition] -/} [Fintype n /- [standing] -/] [DecidableEq n /- [standing] -/]
    (A : Matrix n n ℝ /- [definition] -/)
    (hA : A.PosSemidef /- [standing] -/)
    (hIA : (1 - A).PosSemidef /- [standing] -/) :
    A.det ≤ 1 := by
  have he : ∀ i, hA.isHermitian.eigenvalues i ≤ 1 := by
    intro i
    let v := hA.isHermitian.eigenvectorBasis i
    have h := hIA.dotProduct_mulVec_nonneg (WithLp.ofLp v)
    have hv : dotProduct (WithLp.ofLp v) (WithLp.ofLp v) = 1 := by
      have hi : inner ℝ v v = 1 :=
        inner_self_eq_one_of_norm_eq_one (𝕜 := ℝ)
          (hA.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i)
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hi
      exact hi
    dsimp [v] at h hv
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, star_trivial,
      dotProduct_sub, Matrix.IsHermitian.mulVec_eigenvectorBasis,
      dotProduct_smul, hv, smul_eq_mul, mul_one] at h
    linarith
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  simpa using Finset.prod_le_prod₀
    (fun i _ => hA.eigenvalues_nonneg i) (fun i _ => he i)

/-- Positive definite upper endpoint: conjugate by its inverse square root. -/
theorem det_le_det_of_posDef {n : Type* /- [definition] -/} [Fintype n /- [standing] -/] [DecidableEq n /- [standing] -/]
    (A B : Matrix n n ℝ /- [definition] -/)
    (hA : A.PosSemidef /- [standing] -/)
    (hB : B.PosDef /- [standing] -/)
    (hBA : (B - A).PosSemidef /- [standing] -/) :
    A.det ≤ B.det := by
  let R := CFC.sqrt B
  have hR : R.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hRR : R * R = B := by
    simpa [R, pow_two] using CFC.sq_sqrt B
  have hdet : R.det * R.det = B.det := by rw [← Matrix.det_mul, hRR]
  have hR0 : R.det ≠ 0 := by
    intro h
    have := hB.det_pos
    rw [h, zero_mul] at hdet
    linarith
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR0
  let W := R⁻¹
  have hWR : W * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRW : R * W = 1 := Matrix.mul_nonsing_inv R hRu
  have hWstar : Wᴴ = W := by
    dsimp [W]
    rw [Matrix.conjTranspose_nonsing_inv, hR.isHermitian.eq]
  let C := Wᴴ * A * W
  have hC : C.PosSemidef := hA.conjTranspose_mul_mul_same W
  have hWBW : Wᴴ * B * W = 1 := by
    rw [hWstar, ← hRR]
    simp only [← mul_assoc, hWR, one_mul, hRW]
  have hIC : (1 - C).PosSemidef := by
    have h := hBA.conjTranspose_mul_mul_same W
    simpa only [Matrix.mul_sub, Matrix.sub_mul, hWBW] using h
  have hCdet := det_le_one C hC hIC
  have hAeq : R * C * R = A := by
    dsimp [C]
    rw [hWstar]
    calc R * (W * A * W) * R = (R * W) * A * (W * R) := by noncomm_ring
         _ = A := by rw [hRW, hWR]; simp
  have hAdet : A.det = B.det * C.det := by
    rw [← hAeq, Matrix.det_mul, Matrix.det_mul]
    nlinarith [hdet]
  rw [hAdet]
  nlinarith [hB.det_pos]

/-- Loewner monotonicity of finite determinants, including singular endpoints. -/
theorem det_mono {n : Type* /- [definition] -/} [Fintype n /- [standing] -/] [DecidableEq n /- [standing] -/]
    (A B : Matrix n n ℝ /- [definition] -/)
    (hA : A.PosSemidef /- [standing] -/)
    (hB : B.PosSemidef /- [standing] -/)
    (hBA : (B - A).PosSemidef /- [standing] -/) :
    A.det ≤ B.det := by
  have hlim : Filter.Tendsto (fun e : ℝ => (B + e • (1 : Matrix n n ℝ)).det)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds B.det) := by
    have hc : Continuous (fun e : ℝ => (B + e • (1 : Matrix n n ℝ)).det) :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  have hE : (e • (1 : Matrix n n ℝ)).PosDef := by
    convert Matrix.PosDef.diagonal (n := n) (d := fun _ => e) (fun _ => he) using 1
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> ring
  have hBE : (B + e • (1 : Matrix n n ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add hB hE
  apply det_le_det_of_posDef A _ hA hBE
  convert hBA.add hE.posSemidef using 1 <;> abel

/-- All finite-dimensional order premises hold on distinct positive diagonal matrices. -/
theorem matrix_order_joint_probe :
    let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun _ => 1/4)
    let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun _ => 1/2)
    A.PosSemidef ∧ B.PosDef ∧ (B-A).PosSemidef ∧
      (1-B).PosSemidef ∧ A.det < B.det ∧ B.det < 1 := by
  dsimp
  refine ⟨Matrix.PosSemidef.diagonal (by intro i; norm_num),
    Matrix.PosDef.diagonal (by intro i; norm_num), ?_, ?_, ?_, ?_⟩
  · convert Matrix.PosSemidef.diagonal (n := Fin 2) (d := fun _ => (1/4:ℝ))
      (by intro i; norm_num) using 1 <;> ext i j <;> simp [Matrix.diagonal] <;> split_ifs <;> norm_num
  · convert Matrix.PosSemidef.diagonal (n := Fin 2) (d := fun _ => (1/2:ℝ))
      (by intro i; norm_num) using 1 <;> ext i j <;> simp [Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> norm_num
  · norm_num [Matrix.det_diagonal, Fin.prod_univ_two]
  · norm_num [Matrix.det_diagonal, Fin.prod_univ_two]


end finite_matrix_helpers

noncomputable def compression {E ι : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/]
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (T : E →L[ℝ] E /- [definition] -/)
    (t : Finset ι /- [definition] -/) : Matrix t t ℝ :=
  fun i j => inner ℝ (b i) (T (b j))

theorem compression_quadratic {E ι : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/]
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (T : E →L[ℝ] E /- [definition] -/)
    (t : Finset ι /- [definition] -/)
    (x : t → ℝ /- [definition] -/) :
    dotProduct x ((compression b T t).mulVec x) =
      inner ℝ (∑ i : t, x i • b i) (T (∑ i : t, x i • b i)) := by
  simp only [map_sum, map_smul]
  rw [sum_inner]
  simp [compression, dotProduct, Matrix.mulVec, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem compression_positive {E ι : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/]
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (T : E →L[ℝ] E /- [definition] -/)
    (hT : T.IsPositive /- [standing] -/)
    (t : Finset ι /- [definition] -/) :
    (compression b T t).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change inner ℝ (b j) (T (b i)) = inner ℝ (b i) (T (b j))
    rw [← hT.inner_left_eq_inner_right, real_inner_comm]
  · intro x
    rw [star_trivial, compression_quadratic]
    exact hT.inner_nonneg_right _

theorem compression_one_sub {E ι : Type* /- [definition] -/}
    [DecidableEq ι /- [definition] -/]
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/]
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (T : E →L[ℝ] E /- [definition] -/)
    (t : Finset ι /- [definition] -/) :
    compression b (1 - T) t = 1 - compression b T t := by
  classical
  ext i j
  simp [compression, inner_sub_right, orthonormal_iff_ite.mp b.orthonormal,
    Matrix.one_apply, Subtype.val_inj]

theorem compression_sub {E ι : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/]
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (S T : E →L[ℝ] E /- [definition] -/)
    (t : Finset ι /- [definition] -/) :
    compression b (S-T) t = compression b S t - compression b T t := by
  ext i j
  simp [compression, inner_sub_right]

theorem positive_le_one_of_norm_le {E : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/] [InnerProductSpace ℝ E /- [standing] -/] [CompleteSpace E /- [standing] -/]
    (T : E →L[ℝ] E /- [definition] -/)
    (hT : T.IsPositive /- [standing] -/)
    (hNorm : ‖T‖ ≤ 1 /- [standing] -/) :
    T ≤ 1 := by
  apply (ContinuousLinearMap.le_def).mpr
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨(IsSelfAdjoint.one (E →L[ℝ] E)).sub hT.isSelfAdjoint, ?_⟩
  intro f
  have hn : ‖T f‖ ≤ ‖f‖ := (T.le_opNorm f).trans
    (by simpa using mul_le_mul_of_nonneg_right hNorm (norm_nonneg f))
  have hi := (real_inner_le_norm (T f) f).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg f))
  simpa [inner_sub_left, real_inner_self_eq_norm_sq, pow_two] using sub_nonneg.mpr hi

/-- A contraction bound on the shifted Airy kernel implies TW2 lies in [0, 1]. -/
theorem TW2R_mem_Icc_of_contraction
    (s : ℝ /- [definition] -/)
    (hNorm : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : TW2R s ∈ Icc (0 : ℝ) 1 := by
  classical
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  have hPos := isPositive_airyKernelShift s
  have hOne := (ContinuousLinearMap.le_def).mp
    (positive_le_one_of_norm_le _ hPos hNorm)
  have hfinite : ∀ t : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)),
      0 ≤ (1 - compression b (airyKernelShift s) t).det ∧
        (1 - compression b (airyKernelShift s) t).det ≤ 1 := by
    intro t
    have hc := compression_positive b _ hPos t
    have hi := compression_positive b _ hOne t
    rw [compression_one_sub] at hi
    exact ⟨hi.det_nonneg, det_le_one _ hi (by simpa using hc)⟩
  have hlim : Tendsto
      (fun t : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) =>
        (1 - compression b (airyKernelShift s) t).det) atTop (𝓝 (TW2R s)) := by
    refine (TW2R_finite_compressions_tendsto b s).congr' ?_
    filter_upwards [] with u
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [compression, Matrix.one_apply, hij]
  exact ⟨ge_of_tendsto hlim (Eventually.of_forall fun t => (hfinite t).1),
    le_of_tendsto hlim (Eventually.of_forall fun t => (hfinite t).2)⟩

/-- Contraction bounds at two ordered cutoffs imply order of the TW2 values. -/
theorem TW2R_le_of_contractions
    (s t : ℝ /- [definition] -/)
    (hst : s ≤ t /- [standing] -/)
    (hNormS : ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    (hNormT : ‖airyKernelShift t‖ ≤ 1 /- [standing] -/ )
    : TW2R s ≤ TW2R t := by
  classical
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  have hSone := (ContinuousLinearMap.le_def).mp
    (positive_le_one_of_norm_le _ (isPositive_airyKernelShift s) hNormS)
  have hTone := (ContinuousLinearMap.le_def).mp
    (positive_le_one_of_norm_le _ (isPositive_airyKernelShift t) hNormT)
  have hOrder := (ContinuousLinearMap.le_def).mp
    (airyKernelShift_loewner_antitone hst)
  have hfinite : ∀ u : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)),
      (1 - compression b (airyKernelShift s) u).det ≤
        (1 - compression b (airyKernelShift t) u).det := by
    intro u
    have hA := compression_positive b _ hSone u
    have hB := compression_positive b _ hTone u
    rw [compression_one_sub] at hA hB
    apply det_mono _ _ hA hB
    have h := compression_positive b _ hOrder u
    rw [compression_sub] at h
    convert h using 1 <;> abel
  have hlimS : Tendsto
      (fun u : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) =>
        (1 - compression b (airyKernelShift s) u).det) atTop (𝓝 (TW2R s)) := by
    refine (TW2R_finite_compressions_tendsto b s).congr' ?_
    filter_upwards [] with u
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [compression, Matrix.one_apply, hij]
  have hlimT : Tendsto
      (fun u : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) =>
        (1 - compression b (airyKernelShift t) u).det) atTop (𝓝 (TW2R t)) := by
    refine (TW2R_finite_compressions_tendsto b t).congr' ?_
    filter_upwards [] with u
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [compression, Matrix.one_apply, hij]
  exact le_of_tendsto_of_tendsto hlimS hlimT (Eventually.of_forall hfinite)

/-- Global contraction of the shifted Airy kernel implies range and monotonicity of TW2. -/
theorem TW2R_global_range_mono_of_contraction
    (hNorm : ∀ s : ℝ, ‖airyKernelShift s‖ ≤ 1 /- [standing] -/ )
    : (∀ s, TW2R s ∈ Icc (0 : ℝ) 1) ∧ Monotone TW2R :=
  ⟨fun s => TW2R_mem_Icc_of_contraction s (hNorm s),
    fun s t hst => TW2R_le_of_contractions s t hst (hNorm s) (hNorm t)⟩

/-- Unconditional right-tail range/order: the norm decay supplies contraction. -/
theorem TW2R_tail_range_mono
    : ∃ a : ℝ, ∀ s ≥ a,
      TW2R s ∈ Icc (0 : ℝ) 1 ∧ ∀ t ≥ s, TW2R s ≤ TW2R t := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp eventually_norm_airyKernelShift_lt_one
  refine ⟨a,fun s hs => ⟨TW2R_mem_Icc_of_contraction s (ha s hs).le,?_⟩⟩
  intro t hst
  exact TW2R_le_of_contractions s t hst (ha s hs).le (ha t (hs.trans hst)).le

theorem airyOperatorTW2_tail_range_mono
    : ∃ a : ℝ, ∀ s ≥ a,
      airyOperatorTW2 s ∈ Icc (0 : ℝ) 1 ∧
      ∀ t ≥ s, airyOperatorTW2 s ≤ airyOperatorTW2 t := by
  simpa only [← TW2R_eq_airyOperatorTW2] using TW2R_tail_range_mono

theorem airyOperatorTW1_continuous : Continuous airyOperatorTW1 := by
  have he : airyOperatorTW1 = TW1R := funext fun s => (TW1R_eq_airyOperatorTW1 s).symm
  rw [he]
  exact TW1R_continuous

theorem airyOperatorTW2_continuous : Continuous airyOperatorTW2 := by
  have he : airyOperatorTW2 = TW2R := funext fun s => (TW2R_eq_airyOperatorTW2 s).symm
  rw [he]
  exact TW2R_continuous

theorem airyOperatorTW1_tendsto_atTop_one :
    Tendsto airyOperatorTW1 atTop (𝓝 1) := by
  have he : airyOperatorTW1 = TW1R := funext fun s => (TW1R_eq_airyOperatorTW1 s).symm
  rw [he]
  exact TW1R_tendsto_atTop_one

theorem airyOperatorTW2_tendsto_atTop_one :
    Tendsto airyOperatorTW2 atTop (𝓝 1) := by
  have he : airyOperatorTW2 = TW2R := funext fun s => (TW2R_eq_airyOperatorTW2 s).symm
  rw [he]
  exact TW2R_tendsto_atTop_one

/-- Real-coupling operator continuity is now unconditional for both physical families. -/
theorem airy_operator_det_continuous_coupling
    (z : ℝ /- [definition] -/)
    : Continuous (fun s => realOperatorDet
        (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)) (airyHankelShift s) z) ∧
      Continuous (fun s => realOperatorDet
        (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)) (airyKernelShift s) z) :=
  ⟨airyHankel_realOperatorDet_continuous_coupling _ z,
    airyKernel_realOperatorDet_continuous_coupling _ z⟩

/-- Continuity in the projective HS-product trace gauge is retained alongside
continuity of the now identified canonical determinant. -/
theorem airyOperatorTW2_trace_continuity
    (t : ℝ /- [definition] -/)
    : Tendsto (fun s => traceNorm (airyKernelShift s - airyKernelShift t))
        (𝓝 t) (𝓝 0) ∧ ContinuousAt airyOperatorTW2 t :=
  ⟨tendsto_traceNorm_airyKernelShift_sub t, airyOperatorTW2_continuous.continuousAt⟩

/-- The pointwise range/order premises are jointly realized by actual Airy
operators at distinct levels on a right tail, with a genuine L2 unit input and both
physical determinant bridges. No placeholder or zero-dimensional structure is used. -/
theorem bridge_consequences_joint_probe
    : ∃ s t : ℝ, s < t ∧
      ‖shiftedUnitVector 0‖ = 1 ∧ airyAiReal 0 ≠ 0 ∧
      (airyKernelShift s).IsPositive ∧ (airyKernelShift t).IsPositive ∧
      ‖airyKernelShift s‖ ≤ 1 ∧ ‖airyKernelShift t‖ ≤ 1 ∧
      airyKernelShift t ≤ airyKernelShift s ∧
      IsTraceClass (airyHankelShift s) ∧ IsTraceClass (airyKernelShift s) ∧
      TW1R s = airyOperatorTW1 s ∧ TW2R s = airyOperatorTW2 s ∧
      TW2R s ∈ Icc (0 : ℝ) 1 ∧ TW2R s ≤ TW2R t ∧
      Tendsto (fun u => traceNorm (airyKernelShift u - airyKernelShift s))
        (𝓝 s) (𝓝 0) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp eventually_norm_airyKernelShift_lt_one
  let s := max a 0
  let t := s + 1
  have has : a ≤ s := le_max_left a 0
  have hst : s < t := by dsimp [t]; linarith
  have hS := (ha s has).le
  have hT := (ha t (has.trans hst.le)).le
  exact ⟨s,t,hst,shiftedUnitVector_norm 0,airyAiReal_zero_pos.ne',
    isPositive_airyKernelShift s,isPositive_airyKernelShift t,hS,hT,
    airyKernelShift_loewner_antitone hst.le,isTraceClass_airyHankelShift s,
    isTraceClass_airyKernelShift s,TW1R_eq_airyOperatorTW1 s,TW2R_eq_airyOperatorTW2 s,
    TW2R_mem_Icc_of_contraction s hS,TW2R_le_of_contractions s t hst.le hS hT,
    tendsto_traceNorm_airyKernelShift_sub s⟩

/-- Exact remaining TW1 upper-bound obligation, with the determinant bridge discharged. -/
theorem TW1R_le_one_iff_operator_bound
    (s : ℝ /- [definition] -/)
    : TW1R s ≤ 1 ↔ airyOperatorTW1 s ≤ 1 := by
  rw [TW1R_eq_airyOperatorTW1]

/-- Exact remaining left-endpoint obligation for TW1; no asymptotic is assumed here. -/
theorem TW1R_left_endpoint_iff_operator_limit
    : Tendsto TW1R atBot (𝓝 0) ↔ Tendsto airyOperatorTW1 atBot (𝓝 0) := by
  have he : TW1R = airyOperatorTW1 := funext TW1R_eq_airyOperatorTW1
  rw [he]

/-- Exact remaining left-endpoint obligation for TW2. -/
theorem TW2R_left_endpoint_iff_operator_limit
    : Tendsto TW2R atBot (𝓝 0) ↔ Tendsto airyOperatorTW2 atBot (𝓝 0) := by
  have he : TW2R = airyOperatorTW2 := funext TW2R_eq_airyOperatorTW2
  rw [he]

/-- Monotonicity of the order-one Airy determinant implies TW1 is at most one. -/
theorem TW1R_le_one_of_operator_monotone
    (hMono : Monotone airyOperatorTW1 /- [standing] -/ )
    (s : ℝ /- [definition] -/)
    : TW1R s ≤ 1 := by
  rw [TW1R_eq_airyOperatorTW1]
  apply ge_of_tendsto airyOperatorTW1_tendsto_atTop_one
  filter_upwards [eventually_ge_atTop s] with t hst
  exact hMono hst



open MeasureTheory FourierTransform RMTFoundations.Airy
open Set Filter Complex
open scoped InnerProductSpace InnerProduct TemperedDistribution
open scoped SchwartzMap ENNReal Topology ContDiff

open FourierTransform LineDeriv
open scoped SchwartzMap TemperedDistribution
open Asymptotics
open scoped Asymptotics
open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open Filter

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open FourierTransform
open scoped SchwartzMap

open RMTFoundations.Airy
open Set

theorem TW2R_mem_Icc_unconditional
    (s : ℝ /- [definition] -/) : TW2R s ∈ Icc (0 : ℝ) 1 := RMTFoundations.AiryBounds.TW2R_mem_Icc s

theorem TW2R_monotone_unconditional : Monotone TW2R := RMTFoundations.AiryBounds.TW2R_monotone

theorem airyOperatorTW2_mem_Icc
    (s : ℝ /- [definition] -/) : airyOperatorTW2 s ∈ Icc (0 : ℝ) 1 := by
  rw [← TW2R_eq_airyOperatorTW2]
  exact TW2R_mem_Icc_unconditional s

theorem airyOperatorTW2_monotone : Monotone airyOperatorTW2 := by
  intro s t hst
  simpa only [← TW2R_eq_airyOperatorTW2] using TW2R_monotone_unconditional hst

/-- Nondegenerate all-real theorem probe, including negative cutoffs. -/
theorem global_bridge_contraction_joint_probe
    (s : ℝ /- [definition] -/) :
    airyAiReal 0 > 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      ‖airyKernelShift s‖ ≤ 1 ∧ TW2R s ∈ Icc (0 : ℝ) 1 ∧
      TW2R s ≤ TW2R (s+1) ∧ TW2R s = airyOperatorTW2 s :=
  ⟨airyAiReal_zero_pos,shiftedUnitVector_norm 0,RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s,
    TW2R_mem_Icc_unconditional s,TW2R_monotone_unconditional (by linarith),
    TW2R_eq_airyOperatorTW2 s⟩

end RMTFoundations.AiryConsequences

#print axioms RMTFoundations.AiryConsequences.det_le_one
#print axioms RMTFoundations.AiryConsequences.det_le_det_of_posDef
#print axioms RMTFoundations.AiryConsequences.det_mono
#print axioms RMTFoundations.AiryConsequences.matrix_order_joint_probe
#print axioms RMTFoundations.AiryConsequences.compression
#print axioms RMTFoundations.AiryConsequences.compression_quadratic
#print axioms RMTFoundations.AiryConsequences.compression_positive
#print axioms RMTFoundations.AiryConsequences.compression_one_sub
#print axioms RMTFoundations.AiryConsequences.compression_sub
#print axioms RMTFoundations.AiryConsequences.positive_le_one_of_norm_le
#print axioms RMTFoundations.AiryConsequences.TW2R_mem_Icc_of_contraction
#print axioms RMTFoundations.AiryConsequences.TW2R_le_of_contractions
#print axioms RMTFoundations.AiryConsequences.TW2R_global_range_mono_of_contraction
#print axioms RMTFoundations.AiryConsequences.TW2R_tail_range_mono
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_tail_range_mono
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW1_continuous
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_continuous
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW1_tendsto_atTop_one
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_tendsto_atTop_one
#print axioms RMTFoundations.AiryConsequences.airy_operator_det_continuous_coupling
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_trace_continuity
#print axioms RMTFoundations.AiryConsequences.bridge_consequences_joint_probe
#print axioms RMTFoundations.AiryConsequences.TW1R_le_one_iff_operator_bound
#print axioms RMTFoundations.AiryConsequences.TW1R_left_endpoint_iff_operator_limit
#print axioms RMTFoundations.AiryConsequences.TW2R_left_endpoint_iff_operator_limit
#print axioms RMTFoundations.AiryConsequences.TW1R_le_one_of_operator_monotone
#print axioms RMTFoundations.AiryConsequences.TW2R_mem_Icc_unconditional
#print axioms RMTFoundations.AiryConsequences.TW2R_monotone_unconditional
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_mem_Icc
#print axioms RMTFoundations.AiryConsequences.airyOperatorTW2_monotone
#print axioms RMTFoundations.AiryConsequences.global_bridge_contraction_joint_probe
