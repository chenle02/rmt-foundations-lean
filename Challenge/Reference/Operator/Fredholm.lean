import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence



namespace RMTFoundations.Fredholm



open Filter Topology


/-- The Fredholm power series, with the plus convention. -/
noncomputable def fredholmSeries
    (c : ℕ → ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := ∑' n, c n * z ^ n

/-- Absolute convergence at every radius from a factorial coefficient estimate. -/
theorem factorial_weight_summable
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    (R : ℝ /- [definition] -/ )
    (hR : 0 ≤ R /- [standing] -/ )
    : Summable (fun n => ‖c n‖ * R ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hR n))
    (fun n => ?_) (Real.summable_pow_div_factorial (M * R))
  calc
    ‖c n‖ * R ^ n ≤ (M ^ n / (n.factorial : ℝ)) * R ^ n :=
      mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hR n)
    _ = (M * R) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring

/-- The norm series converges for every complex coupling, including outside the unit disk. -/
theorem fredholmSeries_absolute
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun n => ‖c n * z ^ n‖) := by
  simpa only [norm_mul, norm_pow] using
    factorial_weight_summable c M hM hc ‖z‖ (norm_nonneg z)

/-- A genuine sum, rather than Lean's arbitrary nonsummable `tsum` value. -/
theorem fredholmSeries_hasSum
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasSum (fun n => c n * z ^ n) (fredholmSeries c z) :=
  (fredholmSeries_absolute c M hM hc z).of_norm.hasSum

/-- The formal power series has infinite radius. -/
theorem fredholmSeries_radius_top
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  simpa only [FormalMultilinearSeries.ofScalars_norm] using
    factorial_weight_summable c M hM hc R R.coe_nonneg

/-- Analytic on the entire complex plane. -/
theorem fredholmSeries_entire
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (fredholmSeries c) Set.univ := by
  have hr := fredholmSeries_radius_top c M hM hc
  have h := (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars ℂ c).sum = fredholmSeries c := by
    ext z
    exact FormalMultilinearSeries.ofScalars_sum_eq c z
  rw [heq] at h
  simpa only [hr, Metric.eball_top] using h.analyticOnNhd

/-- Continuity in the coupling at every point. -/
theorem fredholmSeries_continuous
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    : Continuous (fredholmSeries c) :=
  (fredholmSeries_entire c M hM hc).continuous

/-- Normalization at zero is determined by the constant coefficient. -/
theorem fredholmSeries_zero
    (c : ℕ → ℂ /- [definition] -/ )
    : fredholmSeries c 0 = c 0 := by
  rw [fredholmSeries, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]


/-- Uniform convergence of truncations on every bounded disk. -/
theorem fredholmSeries_uniform_closedBall
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    (R : ℝ /- [definition] -/ )
    (hR : 0 ≤ R /- [standing] -/ )
    : TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, c n * z ^ n)
      (fredholmSeries c) atTop (Metric.closedBall 0 R) := by
  apply tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial (M * R))
  intro n z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [norm_mul, norm_pow]
  calc
    ‖c n‖ * ‖z‖ ^ n ≤ (M ^ n / (n.factorial : ℝ)) * R ^ n :=
      mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg _) hzR n)
        (pow_nonneg (norm_nonneg _) n) (div_nonneg (pow_nonneg hM n) (Nat.cast_nonneg _))
    _ = (M * R) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring

/-- Continuity for a family with continuous coefficients and a common factorial bound.
This is an analytic engine; applying it to trace norm requires proving the coefficient facts. -/
theorem fredholmSeries_family_continuous
    {X : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (c : X → ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ x n, ‖c x n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    (hcont : ∀ n, Continuous (fun x => c x n)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Continuous (fun x => fredholmSeries (c x) z) := by
  apply continuous_tsum (fun n => (hcont n).mul continuous_const)
    (Real.summable_pow_div_factorial (M * ‖z‖))
  intro n x
  change ‖c x n * z ^ n‖ ≤ (M * ‖z‖) ^ n / (n.factorial : ℝ)
  rw [norm_mul, norm_pow]
  calc
    ‖c x n‖ * ‖z‖ ^ n ≤ (M ^ n / (n.factorial : ℝ)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (hc x n) (pow_nonneg (norm_nonneg _) n)
    _ = (M * ‖z‖) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring

/-- Product of convergent series, with coefficients given by convolution.
This does not assert multiplicativity for operators without a coefficient identity. -/
theorem fredholmSeries_convolution
    (c d : ℕ → ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    (hc : Summable (fun n => ‖c n * z ^ n‖)  /- [standing] -/ )
    (hd : Summable (fun n => ‖d n * z ^ n‖)  /- [standing] -/ )
    : fredholmSeries (fun n => ∑ kl ∈ Finset.antidiagonal n, c kl.1 * d kl.2) z =
      fredholmSeries c z * fredholmSeries d z := by
  rw [fredholmSeries, fredholmSeries, fredholmSeries,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc hd]
  apply tsum_congr
  intro n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add]
  ring

/-- Nondegenerate, large-norm joint witness for every coefficient premise above.
The rank-one coefficient family allows arbitrary `a`, including `a = 2`. -/
def rankOneCoeff
    (a : ℂ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℂ := if n = 0 then 1 else if n = 1 then a else 0

theorem rankOneCoeff_bound
    (a : ℂ /- [definition] -/ )
    : ∀ n, ‖rankOneCoeff a n‖ ≤ (1 + ‖a‖) ^ n / (n.factorial : ℝ) := by
  intro n
  by_cases h0 : n = 0
  · subst n
    simp [rankOneCoeff]
  by_cases h1 : n = 1
  · subst n
    simp [rankOneCoeff]
  · simp only [rankOneCoeff, if_neg h0, if_neg h1, norm_zero]
    positivity

theorem rankOneCoeff_series
    (a z : ℂ /- [definition] -/ )
    : fredholmSeries (rankOneCoeff a) z = 1 + a * z := by
  rw [fredholmSeries, tsum_eq_sum (s := {0, 1})]
  · simp [rankOneCoeff]
  · intro n hn
    have h0 : n ≠ 0 := by intro h; apply hn; simp [h]
    have h1 : n ≠ 1 := by intro h; apply hn; simp [h]
    simp [rankOneCoeff, h0, h1]

/-- Simultaneously satisfies the convergence/entireness hypotheses with a nonzero determinant
outside the small-norm Plemelj disk. No new proof-carrying structure is introduced. -/
theorem entire_joint_probe
    : ∃ c : ℕ → ℂ, ∃ M : ℝ, 0 < M ∧ c 0 = 1 ∧ c 1 = 2 ∧
      (∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)) ∧
      fredholmSeries c 1 = 3 ∧ AnalyticOnNhd ℂ (fredholmSeries c) Set.univ := by
  refine ⟨rankOneCoeff 2, 1 + ‖(2 : ℂ)‖, by positivity, by simp [rankOneCoeff],
    by simp [rankOneCoeff], rankOneCoeff_bound 2, ?_, ?_⟩
  · rw [rankOneCoeff_series]; norm_num
  · exact fredholmSeries_entire _ _ (by positivity) (rankOneCoeff_bound 2)


/-- The product model for an absolutely summable diagonal. The operator connection
for general (possibly nonnormal) trace-class operators remains a separate obligation. -/
noncomputable def diagonalDet
    (a : ℕ → ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := ∏' i, (1 + z * a i)

/-- Every complex coupling has a genuinely convergent product. -/
theorem diagonalDet_hasProd
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasProd (fun i => 1 + z * a i) (diagonalDet a z) := by
  apply (multipliable_one_add_of_summable ?_).hasProd
  simpa only [norm_mul] using ha.mul_left ‖z‖

/-- The finite-subset Fredholm expansion is absolutely convergent everywhere. -/
theorem diagonalDet_absolute
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun s : Finset ℕ => ‖∏ i ∈ s, z * a i‖) := by
  simpa only [norm_prod, norm_mul] using
    summable_finsetProd_of_summable_nonneg
      (fun i => mul_nonneg (norm_nonneg z) (norm_nonneg (a i))) (ha.mul_left ‖z‖)

/-- Expansion over finite subsets, including all degrees. -/
theorem diagonalDet_eq_tsum
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : diagonalDet a z = ∑' s : Finset ℕ, ∏ i ∈ s, z * a i := by
  exact tprod_one_add (diagonalDet_absolute a ha z).of_norm

/-- Finite truncations converge without a small-norm premise. -/
theorem diagonalDet_truncations
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun N => ∏ i ∈ Finset.range N, (1 + z * a i)) atTop
      (𝓝 (diagonalDet a z)) :=
  (diagonalDet_hasProd a ha z).tendsto_prod_nat

/-- The determinant bound in the diagonal trace norm. -/
theorem diagonalDet_norm_le
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : ‖diagonalDet a z‖ ≤ Real.exp (‖z‖ * ∑' i, ‖a i‖) := by
  apply le_of_tendsto' (diagonalDet_truncations a ha z).norm
  intro N
  calc
    ‖∏ i ∈ Finset.range N, (1 + z * a i)‖
        ≤ ∏ i ∈ Finset.range N, (1 + ‖z‖ * ‖a i‖) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      simpa only [norm_one, norm_mul] using norm_add_le (1 : ℂ) (z * a i)
    _ ≤ Real.exp (∑ i ∈ Finset.range N, ‖z‖ * ‖a i‖) :=
      Real.prod_one_add_le_exp_sum _ (fun i => by positivity)
    _ ≤ Real.exp (‖z‖ * ∑' i, ‖a i‖) := by
      apply Real.exp_le_exp.mpr
      rw [← tsum_mul_left]
      exact (ha.mul_left ‖z‖).sum_le_tsum _ (fun i _ => by positivity)

/-- The exact logarithm identity on the nonvanishing locus. -/
theorem diagonalDet_eq_exp_log
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    (hz : ∀ i, 1 + z * a i ≠ 0 /- [standing] -/ )
    : diagonalDet a z = Complex.exp (∑' i, Complex.log (1 + z * a i)) := by
  exact (Complex.cexp_tsum_eq_tprod hz
    (Complex.summable_log_one_add_of_summable (ha.of_norm.mul_left z))).symm

/-- Multiplicativity for two diagonal perturbations of the identity. -/
theorem diagonalDet_multiplicative
    (a b : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hb : Summable (fun i => ‖b i‖)  /- [standing] -/ )
    : diagonalDet (fun i => a i + b i + a i * b i) 1 =
      diagonalDet a 1 * diagonalDet b 1 := by
  have heq : (fun i => 1 + (1 : ℂ) * (a i + b i + a i * b i)) =
      (fun i => (1 + (1 : ℂ) * a i) * (1 + (1 : ℂ) * b i)) := by
    funext i; ring
  rw [diagonalDet, heq]
  exact (diagonalDet_hasProd a ha 1).multipliable.tprod_mul
    (diagonalDet_hasProd b hb 1).multipliable

/-- Normalization at zero. -/
theorem diagonalDet_zero
    (a : ℕ → ℂ /- [definition] -/ )
    : diagonalDet a 0 = 1 := by simp [diagonalDet]

/-- A finite-rank diagonal witness beyond the Plemelj radius. -/
def singleDiagonal
    (w : ℂ /- [definition] -/ )
    (i : ℕ /- [definition] -/ )
    : ℂ := if i = 0 then w else 0

theorem singleDiagonal_summable
    (w : ℂ /- [definition] -/ )
    : Summable (fun i => ‖singleDiagonal w i‖) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [singleDiagonal, hi]

theorem singleDiagonal_det
    (w z : ℂ /- [definition] -/ )
    : diagonalDet (singleDiagonal w) z = 1 + z * w := by
  rw [diagonalDet, tprod_eq_prod (s := {0})]
  · simp [singleDiagonal]
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [singleDiagonal, hi]

/-- Joint nondegenerate witness: trace-norm mass 2, determinant 3 at coupling 1. -/
theorem diagonal_joint_probe
    : ∃ a : ℕ → ℂ, Summable (fun i => ‖a i‖) ∧ a 0 = 2 ∧
      diagonalDet a 1 = 3 ∧ diagonalDet a (-1 / 2) = 0 := by
  refine ⟨singleDiagonal 2, singleDiagonal_summable 2, by simp [singleDiagonal], ?_, ?_⟩
  · rw [singleDiagonal_det]; norm_num
  · rw [singleDiagonal_det]; norm_num


/-- Degree coefficients of the diagonal elementary-symmetric expansion. -/
noncomputable def diagonalCoeff
    (a : ℕ → ℂ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℂ := ∑' s : {s : Finset ℕ // s.card = n}, ∏ i ∈ s.val, a i

/-- Grouping the absolutely convergent expansion by cardinality. -/
theorem diagonalCoeff_hasSum
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasSum (fun n => diagonalCoeff a n * z ^ n) (diagonalDet a z) := by
  have hf := (diagonalDet_absolute a ha z).of_norm
  have hgroup := hf.hasSum.tsum_fiberwise Finset.card
  rw [← diagonalDet_eq_tsum a ha z] at hgroup
  refine hgroup.congr_fun (fun n => ?_)
  rw [diagonalCoeff, ← tsum_mul_right]
  apply tsum_congr
  intro s
  simp only [Finset.prod_mul_distrib, Finset.prod_const, s.property]
  ring

/-- The degree series is absolutely convergent at every complex coupling. -/
theorem diagonalCoeff_absolute
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun n => ‖diagonalCoeff a n * z ^ n‖) :=
  (diagonalCoeff_hasSum a ha z).summable.norm

/-- Agreement of the product and the entire degree series. -/
theorem diagonalDet_eq_fredholmSeries
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : diagonalDet a z = fredholmSeries (diagonalCoeff a) z :=
  (diagonalCoeff_hasSum a ha z).tsum_eq.symm

/-- Infinite radius follows from proved summability, without a coefficient-bound premise. -/
theorem diagonalCoeff_radius_top
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℂ (diagonalCoeff a)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  have h := diagonalCoeff_absolute a ha (R : ℝ)
  simpa only [norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using h

/-- Entire analyticity of the diagonal determinant, including its zeros. -/
theorem diagonalDet_entire
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (diagonalDet a) Set.univ := by
  have hr := diagonalCoeff_radius_top a ha
  have h := (FormalMultilinearSeries.ofScalars ℂ (diagonalCoeff a)).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars ℂ (diagonalCoeff a)).sum = diagonalDet a := by
    ext z
    exact (FormalMultilinearSeries.ofScalars_sum_eq (diagonalCoeff a) z).trans
      (diagonalDet_eq_fredholmSeries a ha z).symm
  rw [heq] at h
  simpa only [hr, Metric.eball_top] using h.analyticOnNhd


/-- A finite product bound used in trace-norm stability. -/
theorem finite_diagonal_norm_le
    (a b : ℕ → ℂ /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : ‖∏ i ∈ s, (1 + b i)‖ ≤ ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  have h := norm_add_le (1 : ℂ) (b i)
  simp only [norm_one] at h
  linarith [norm_nonneg (a i)]

/-- Finite-dimensional determinant stability with a dimension-free majorant. -/
theorem finite_diagonal_difference_le
    (a b : ℕ → ℂ /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖ ≤
      (∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) * ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx,
      Finset.sum_insert hx]
    let P : ℝ := ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)
    let D : ℝ := ∑ i ∈ s, ‖a i - b i‖
    let G : ℝ := 1 + ‖a x‖ + ‖b x‖
    have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => by positivity)
    have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hG : 1 ≤ G := by dsimp [G]; linarith [norm_nonneg (a x), norm_nonneg (b x)]
    have haG : ‖1 + a x‖ ≤ G := by
      have h := norm_add_le (1 : ℂ) (a x)
      simp only [norm_one] at h
      dsimp [G]; linarith [norm_nonneg (b x)]
    have hbP := finite_diagonal_norm_le a b s
    change ‖(1 + a x) * (∏ i ∈ s, (1 + a i)) -
      (1 + b x) * (∏ i ∈ s, (1 + b i))‖ ≤ G * P * (‖a x - b x‖ + D)
    rw [show (1 + a x) * (∏ i ∈ s, (1 + a i)) -
        (1 + b x) * (∏ i ∈ s, (1 + b i)) =
        (1 + a x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)) +
        (a x - b x) * (∏ i ∈ s, (1 + b i)) by ring]
    calc
      _ ≤ ‖1 + a x‖ * ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖ +
          ‖a x - b x‖ * ‖∏ i ∈ s, (1 + b i)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((1 + a x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)))
          ((a x - b x) * (∏ i ∈ s, (1 + b i)))
      _ ≤ G * (P * D) + ‖a x - b x‖ * P :=
        add_le_add (mul_le_mul haG ih (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left hbP (norm_nonneg _))
      _ ≤ G * (P * D) + (G * ‖a x - b x‖) * P := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (norm_nonneg _) hG) hP
      _ = G * P * (‖a x - b x‖ + D) := by ring

/-- Global stability in the diagonal trace norm; no small-norm restriction. -/
theorem diagonalDet_difference_le
    (a b : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hb : Summable (fun i => ‖b i‖)  /- [standing] -/ )
    : ‖diagonalDet a 1 - diagonalDet b 1‖ ≤
      Real.exp ((∑' i, ‖a i‖) + ∑' i, ‖b i‖) * ∑' i, ‖a i - b i‖ := by
  have hd : Summable (fun i => ‖a i - b i‖) :=
    (ha.add hb).of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_sub_le _ _)
  apply le_of_tendsto' ((diagonalDet_truncations a ha 1).sub
    (diagonalDet_truncations b hb 1)).norm
  intro N
  simp only [one_mul]
  have hsum : ∑ i ∈ Finset.range N, (‖a i‖ + ‖b i‖) ≤
      (∑' i, ‖a i‖) + ∑' i, ‖b i‖ := by
    rw [← ha.tsum_add hb]
    exact (ha.add hb).sum_le_tsum _ (fun i _ => by positivity)
  calc
    _ ≤ (∏ i ∈ Finset.range N, (1 + ‖a i‖ + ‖b i‖)) *
        ∑ i ∈ Finset.range N, ‖a i - b i‖ := finite_diagonal_difference_le a b _
    _ ≤ Real.exp ((∑' i, ‖a i‖) + ∑' i, ‖b i‖) * ∑' i, ‖a i - b i‖ := by
      apply mul_le_mul
      · have hprod : (∏ i ∈ Finset.range N, (1 + ‖a i‖ + ‖b i‖)) ≤
            Real.exp (∑ i ∈ Finset.range N, (‖a i‖ + ‖b i‖)) := by
          simpa only [add_assoc] using
            Real.prod_one_add_le_exp_sum (Finset.range N) (fun i =>
              add_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))
        exact hprod.trans (Real.exp_le_exp.mpr hsum)
      · exact hd.sum_le_tsum _ (fun i _ => norm_nonneg _)
      · exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
      · exact Real.exp_nonneg _

/-- The ℓ¹ topology is the diagonal trace-norm topology. -/
noncomputable def l1Det
    (a : lp (fun _ : ℕ => ℂ) 1 /- [definition] -/ )
    : ℂ := diagonalDet a 1

theorem l1_norm_eq
    (a : lp (fun _ : ℕ => ℂ) 1 /- [definition] -/ )
    : ‖a‖ = ∑' i, ‖a i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) a

theorem l1Det_difference_le
    (a b : lp (fun _ : ℕ => ℂ) 1 /- [definition] -/ )
    : ‖l1Det a - l1Det b‖ ≤ Real.exp (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have ha : Summable (fun i => ‖a i‖) := by simpa using a.property.summable (by norm_num)
  have hb : Summable (fun i => ‖b i‖) := by simpa using b.property.summable (by norm_num)
  simpa only [l1Det, l1_norm_eq, lp.coeFn_sub, Pi.sub_apply] using
    diagonalDet_difference_le a b ha hb

/-- Continuity at every ℓ¹ element, established by the global stability estimate. -/
theorem l1Det_continuous
    : Continuous l1Det := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : Tendsto (fun b : lp (fun _ : ℕ => ℂ) 1 =>
      Real.exp (‖b‖ + ‖a‖) * ‖b - a‖) (𝓝 a) (𝓝 0) := by
    have hcont : Continuous (fun b : lp (fun _ : ℕ => ℂ) 1 =>
        Real.exp (‖b‖ + ‖a‖) * ‖b - a‖) := by fun_prop
    simpa using hcont.tendsto a
  exact squeeze_zero (fun b => norm_nonneg _) (fun b => l1Det_difference_le b a) hbound


/-- Diagonal trace moments; their use below is justified by absolute double summability. -/
noncomputable def diagonalTracePower
    (a : ℕ → ℂ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℂ := ∑' i, a i ^ n

/-- The Plemelj double series is absolutely summable on the small operator-norm disk. -/
theorem diagonal_plemelj_double_absolute
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    (q : ℝ /- [definition] -/ )
    (hq : 0 ≤ q /- [standing] -/ )
    (hq1 : q < 1 /- [standing] -/ )
    (hsmall : ∀ i, ‖z * a i‖ ≤ q /- [standing] -/ )
    : Summable (fun p : ℕ × ℕ =>
      ‖(-z * a p.1) ^ (p.2 + 1) / ((p.2 + 1 : ℕ) : ℂ)‖) := by
  have hmajor : Summable (fun p : ℕ × ℕ => (‖z‖ * ‖a p.1‖) * q ^ p.2) :=
    (ha.mul_left ‖z‖).mul_of_nonneg (summable_geometric_of_lt_one hq hq1)
      (fun i => by positivity) (fun m => pow_nonneg hq m)
  refine hmajor.of_nonneg_of_le (fun p => norm_nonneg _) ?_
  intro p
  rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_natCast]
  calc
    (‖z‖ * ‖a p.1‖) ^ (p.2 + 1) / ((p.2 + 1 : ℕ) : ℝ)
        ≤ (‖z‖ * ‖a p.1‖) ^ (p.2 + 1) :=
      div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p.2))
    _ ≤ (‖z‖ * ‖a p.1‖) * q ^ p.2 := by
      rw [pow_succ, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      simpa only [norm_mul] using hsmall p.1

/-- Agreement of the global determinant with the small-norm Plemelj formula.
The plus convention here corresponds to the companion port's det₁ at argument `-z`. -/
theorem diagonalDet_eq_plemelj
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    (q : ℝ /- [definition] -/ )
    (hq : 0 ≤ q /- [standing] -/ )
    (hq1 : q < 1 /- [standing] -/ )
    (hsmall : ∀ i, ‖z * a i‖ ≤ q /- [standing] -/ )
    : diagonalDet a z = Complex.exp (-∑' m : ℕ,
      (-z) ^ (m + 1) * diagonalTracePower a (m + 1) / ((m + 1 : ℕ) : ℂ)) := by
  let F (i m : ℕ) : ℂ := (-z * a i) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  have hF : Summable (Function.uncurry F) :=
    (diagonal_plemelj_double_absolute a ha z q hq hq1 hsmall).of_norm
  have hlog : ∀ i, (∑' m, F i m) = -Complex.log (1 + z * a i) := by
    intro i
    have hzi : ‖z‖ * ‖a i‖ ≤ q := by simpa only [norm_mul] using hsmall i
    have hi : ‖-z * a i‖ < 1 := by
      simpa only [norm_mul, norm_neg] using hzi.trans_lt hq1
    have h := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hi)
    have hs : HasSum (F i) (-Complex.log (1 + z * a i)) := by
      simpa [F, neg_mul, sub_neg_eq_add] using h
    exact hs.tsum_eq
  have heach : ∀ m, (∑' i, F i m) =
      (-z) ^ (m + 1) * diagonalTracePower a (m + 1) / ((m + 1 : ℕ) : ℂ) := by
    intro m
    simp only [F, mul_pow, tsum_div_const, tsum_mul_left, diagonalTracePower]
  have hcomm : (∑' m, ∑' i, F i m) = ∑' i, ∑' m, F i m := hF.tsum_comm
  have hnonzero : ∀ i, 1 + z * a i ≠ 0 := by
    intro i hi
    have he : z * a i = -1 := by linear_combination hi
    have h := hsmall i
    rw [he] at h
    norm_num at h
    linarith
  rw [diagonalDet_eq_exp_log a ha z hnonzero]
  congr 1
  calc
    (∑' i, Complex.log (1 + z * a i)) = -(∑' i, ∑' m, F i m) := by
      simp only [hlog, tsum_neg, neg_neg]
    _ = -(∑' m, ∑' i, F i m) := by rw [hcomm]
    _ = _ := by simp only [heach]

/-- Nondegenerate ℓ¹ witness for the new continuity theorem. -/
theorem l1_joint_probe
    : ∃ a : lp (fun _ : ℕ => ℂ) 1, ‖a‖ = 2 ∧ l1Det a = 3 ∧
      AnalyticOnNhd ℂ (diagonalDet a) Set.univ := by
  let a : lp (fun _ : ℕ => ℂ) 1 := lp.single 1 0 2
  have heq : ∀ i, a i = singleDiagonal 2 i := by
    intro i
    by_cases hi : i = 0
    · subst i
      change (lp.single 1 0 (2 : ℂ) : lp (fun _ : ℕ => ℂ) 1) 0 = 2
      exact lp.single_apply_self (E := fun _ : ℕ => ℂ) 1 0 (2 : ℂ)
    · simpa only [singleDiagonal, if_neg hi] using lp.single_apply_ne (E := fun _ : ℕ => ℂ) 1 0 (2 : ℂ) hi
  refine ⟨a, ?_, ?_, ?_⟩
  · simp [a, lp.norm_single (by norm_num : (0 : ENNReal) < 1)]
  · change diagonalDet a 1 = 3
    have hf : (a : ℕ → ℂ) = singleDiagonal 2 := funext heq
    rw [hf, singleDiagonal_det]
    norm_num
  · exact diagonalDet_entire a (by simpa using a.property.summable (by norm_num))


/-- A nonzero small-norm witness satisfying every Plemelj premise jointly. -/
theorem plemelj_joint_probe
    : ∃ a : ℕ → ℂ, Summable (fun i => ‖a i‖) ∧ a 0 = 1 / 2 ∧
      (∀ i, ‖(1 : ℂ) * a i‖ ≤ (1 / 2 : ℝ)) ∧
      diagonalDet a 1 = 3 / 2 ∧
      diagonalDet a 1 = Complex.exp (-∑' m : ℕ,
        (-1 : ℂ) ^ (m + 1) * diagonalTracePower a (m + 1) / ((m + 1 : ℕ) : ℂ)) := by
  let a := singleDiagonal (1 / 2)
  have ha := singleDiagonal_summable (1 / 2)
  have hsmall : ∀ i, ‖(1 : ℂ) * a i‖ ≤ (1 / 2 : ℝ) := by
    intro i
    by_cases hi : i = 0 <;> simp [a, singleDiagonal, hi] <;> norm_num
  refine ⟨a, ha, by simp [a, singleDiagonal], hsmall, ?_, ?_⟩
  · rw [singleDiagonal_det]; norm_num
  · exact diagonalDet_eq_plemelj a ha 1 (1 / 2) (by norm_num) (by norm_num) hsmall

/-- An entire determinant with a zero cannot globally equal an exponential. -/
theorem entire_exp_obstruction
    : ¬ ∃ L : ℂ → ℂ, ∀ z, diagonalDet (singleDiagonal 2) z = Complex.exp (L z) := by
  rintro ⟨L, hL⟩
  have h := hL (-1 / 2)
  rw [singleDiagonal_det] at h
  norm_num at h
  exact Complex.exp_ne_zero _ h.symm


/-- Diagonal perturbations remain ℓ¹ under multiplication of the identities. -/
theorem diagonal_comp_summable
    (a b : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hb : Summable (fun i => ‖b i‖)  /- [standing] -/ )
    : Summable (fun i => ‖a i + b i + a i * b i‖) := by
  have hmajor := (ha.add hb).add (hb.mul_left (∑' i, ‖a i‖))
  apply hmajor.of_nonneg_of_le (fun i => norm_nonneg _)
  intro i
  have hai : ‖a i‖ ≤ ∑' j, ‖a j‖ := by
    simpa using ha.sum_le_tsum {i} (fun j _ => norm_nonneg _)
  calc
    ‖a i + b i + a i * b i‖ ≤ ‖a i + b i‖ + ‖a i * b i‖ := norm_add_le _ _
    _ ≤ (‖a i‖ + ‖b i‖) + (∑' j, ‖a j‖) * ‖b i‖ :=
      add_le_add (norm_add_le _ _)
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hai (norm_nonneg _))

/-- The truncation products are classical finite-dimensional determinants. -/
theorem diagonal_matrix_det
    (a : ℕ → ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    (N : ℕ /- [definition] -/ )
    : Matrix.det (1 + z • Matrix.diagonal (fun i : Fin N => a i)) =
      ∏ i ∈ Finset.range N, (1 + z * a i) := by
  have heq : (1 + z • Matrix.diagonal (fun i : Fin N => a i)) =
      Matrix.diagonal (fun i : Fin N => 1 + z * a i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [heq, Matrix.det_diagonal]
  exact (Finset.prod_range (fun i => (1 : ℂ) + z * a i)).symm

/-- Approximation by genuine matrix determinants. -/
theorem diagonal_matrix_det_tendsto
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun N => Matrix.det (1 + z • Matrix.diagonal (fun i : Fin N => a i)))
      atTop (𝓝 (diagonalDet a z)) := by
  simp_rw [diagonal_matrix_det]
  exact diagonalDet_truncations a ha z





open Filter Topology
open scoped InnerProductSpace
open InnerProductSpace


/-- Complex (and real) Hadamard inequality in an orthonormal coordinate system. -/
theorem orthonormal_det_bound
    {𝕜 : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [FiniteDimensional 𝕜 E /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (b : OrthonormalBasis (Fin n) 𝕜 E /- [definition] -/ )
    (v : Fin n → E /- [definition] -/ )
    : ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  classical
  have hd : Module.finrank 𝕜 E = Fintype.card (Fin n) := Module.finrank_eq_card_basis b.toBasis
  let e : OrthonormalBasis (Fin n) 𝕜 E := gramSchmidtOrthonormalBasis hd v
  have heq : b.toBasis.det v = b.toBasis.det e * e.toBasis.det v := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det e.toBasis]
    rfl
  rw [heq, norm_mul, b.det_to_matrix_orthonormalBasis, one_mul,
    gramSchmidtOrthonormalBasis_det hd v, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  simpa only [e.orthonormal.norm_eq_one i, one_mul] using norm_inner_le_norm (e i) (v i)

theorem orthonormal_det_bound_indexed
    {𝕜 : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [FiniteDimensional 𝕜 E /- [definition] -/ ]
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [LinearOrder ι /- [definition] -/ ]
    [LocallyFiniteOrderBot ι /- [definition] -/ ]
    [WellFoundedLT ι /- [definition] -/ ]
    (b : OrthonormalBasis ι 𝕜 E /- [definition] -/ )
    (v : ι → E /- [definition] -/ )
    : ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  classical
  have hd : Module.finrank 𝕜 E = Fintype.card ι := Module.finrank_eq_card_basis b.toBasis
  let e : OrthonormalBasis ι 𝕜 E := gramSchmidtOrthonormalBasis hd v
  have heq : b.toBasis.det v = b.toBasis.det e * e.toBasis.det v := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det e.toBasis]
    rfl
  rw [heq, norm_mul, b.det_to_matrix_orthonormalBasis, one_mul,
    gramSchmidtOrthonormalBasis_det hd v, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  simpa only [e.orthonormal.norm_eq_one i, one_mul] using norm_inner_le_norm (e i) (v i)


/-- Cross-Gram Hadamard bound in an arbitrary Hilbert space, without a dimension bound. -/
theorem crossGram_det_bound
    {𝕜 : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [LinearOrder ι /- [definition] -/ ]
    [LocallyFiniteOrderBot ι /- [definition] -/ ]
    [WellFoundedLT ι /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    : ‖Matrix.det (fun i j : ι => inner 𝕜 (u i) (v j))‖ ≤
      (∏ i, ‖u i‖) * ∏ i, ‖v i‖ := by
  classical
  let G : Matrix ι ι 𝕜 := fun i j => inner 𝕜 (u i) (v j)
  change ‖G.det‖ ≤ (∏ i, ‖u i‖) * ∏ i, ‖v i‖
  by_cases hG : G.det = 0
  · rw [hG, norm_zero]
    positivity
  let f : E →ₗ[𝕜] (ι → 𝕜) := LinearMap.pi (fun i => (innerSL 𝕜 (u i)).toLinearMap)
  have hv : LinearIndependent 𝕜 v := LinearIndependent.of_comp f
    (Matrix.linearIndependent_cols_of_det_ne_zero hG)
  let V := Submodule.span 𝕜 (Set.range v)
  letI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  let vv : ι → V := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  let uu : ι → V := fun i => V.orthogonalProjectionOnto (u i)
  have hd : Module.finrank 𝕜 V = Fintype.card ι := finrank_span_eq_card hv
  let b : OrthonormalBasis ι 𝕜 V := gramSchmidtOrthonormalBasis hd vv
  have hmat : G = (b.toBasis.toMatrix uu).conjTranspose * b.toBasis.toMatrix vv := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    simp only [RCLike.star_def]
    conv_rhs =>
      arg 2
      ext x
      rw [inner_conj_symm (uu i) (b x)]
    rw [b.sum_inner_mul_inner]
    exact (V.inner_orthogonalProjectionOnto_eq_of_mem_right (vv j) (u i)).symm
  rw [hmat, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star,
    ← Module.Basis.det_apply, ← Module.Basis.det_apply]
  calc
    ‖b.toBasis.det uu‖ * ‖b.toBasis.det vv‖ ≤ (∏ i, ‖uu i‖) * ∏ i, ‖vv i‖ :=
      mul_le_mul (orthonormal_det_bound_indexed b uu) (orthonormal_det_bound_indexed b vv)
        (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ (∏ i, ‖u i‖) * ∏ i, ‖v i‖ := by
      apply mul_le_mul
      · exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
          V.norm_orthogonalProjectionOnto_apply_le (u i))
      · exact le_rfl
      · positivity
      · positivity

noncomputable def nuclearOperator
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    : E →L[ℂ] E := ∑' i, rankOne ℂ (v i) (u i)

theorem nuclearOperator_absolute
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : Summable (fun i => ‖rankOne ℂ (v i) (u i)‖) := by
  simpa only [norm_rankOne, mul_comm] using huv

theorem nuclearOperator_hasSum
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : HasSum (fun i => rankOne ℂ (v i) (u i)) (nuclearOperator u v) :=
  (nuclearOperator_absolute u v huv).of_norm.hasSum

theorem hs_vectors_nuclear_mass
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (hu : Summable (fun i => ‖u i‖ ^ 2)  /- [standing] -/ )
    (hv : Summable (fun i => ‖v i‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖u i‖ * ‖v i‖) := by
  apply ((hu.add hv).div_const 2).of_nonneg_of_le (fun i => by positivity)
  intro i
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]

noncomputable def nuclearMinor
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : ℂ := Matrix.det (fun i j : s => inner ℂ (u i) (v j))

theorem nuclearMinor_bound
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : ‖nuclearMinor u v s‖ ≤ ∏ i ∈ s, (‖u i‖ * ‖v i‖) := by
  classical
  rw [nuclearMinor, ← Finset.prod_coe_sort s (fun i : ℕ => ‖u i‖ * ‖v i‖),
    Finset.prod_mul_distrib]
  convert crossGram_det_bound (𝕜 := ℂ) (fun i : s => u i) (fun i : s => v i) using 1
  congr 2 <;> exact Subsingleton.elim _ _

noncomputable def nuclearDet
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := ∑' s : Finset ℕ, nuclearMinor u v s * z ^ s.card

theorem nuclearDet_absolute
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun s : Finset ℕ => ‖nuclearMinor u v s * z ^ s.card‖) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (mul_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))))
    (huv.mul_left ‖z‖)
  apply hmajor.of_nonneg_of_le (fun s => norm_nonneg _)
  intro s
  rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
  exact (mul_le_mul_of_nonneg_right (nuclearMinor_bound u v s)
    (pow_nonneg (norm_nonneg z) s.card)).trans_eq (mul_comm _ _)

theorem nuclearDet_hasSum
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasSum (fun s : Finset ℕ => nuclearMinor u v s * z ^ s.card) (nuclearDet u v z) :=
  (nuclearDet_absolute u v huv z).of_norm.hasSum

noncomputable def nuclearCoeff
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℂ := ∑' s : {s : Finset ℕ // s.card = n}, nuclearMinor u v s.val

theorem nuclearCoeff_hasSum
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasSum (fun n => nuclearCoeff u v n * z ^ n) (nuclearDet u v z) := by
  have hgroup := (nuclearDet_hasSum u v huv z).tsum_fiberwise Finset.card
  refine hgroup.congr_fun (fun n => ?_)
  rw [nuclearCoeff, ← tsum_mul_right]
  apply tsum_congr
  intro s
  rw [s.property]

theorem nuclearCoeff_absolute
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun n => ‖nuclearCoeff u v n * z ^ n‖) :=
  (nuclearCoeff_hasSum u v huv z).summable.norm

theorem nuclearCoeff_radius_top
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℂ (nuclearCoeff u v)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  have h := nuclearCoeff_absolute u v huv (R : ℝ)
  simpa only [norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using h

theorem nuclearDet_entire
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (nuclearDet u v) Set.univ := by
  have hr := nuclearCoeff_radius_top u v huv
  have h := (FormalMultilinearSeries.ofScalars ℂ (nuclearCoeff u v)).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars ℂ (nuclearCoeff u v)).sum = nuclearDet u v := by
    ext z
    exact (FormalMultilinearSeries.ofScalars_sum_eq (nuclearCoeff u v) z).trans
      (nuclearCoeff_hasSum u v huv z).tsum_eq
  rw [heq] at h
  simpa only [hr, Metric.eball_top] using h.analyticOnNhd

theorem nuclearDet_norm_le
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : ‖nuclearDet u v z‖ ≤ ∏' i, (1 + ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (mul_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))))
    (huv.mul_left ‖z‖)
  calc
    ‖nuclearDet u v z‖ ≤ ∑' s : Finset ℕ, ‖nuclearMinor u v s * z ^ s.card‖ :=
      norm_tsum_le_tsum_norm (nuclearDet_absolute u v huv z)
    _ ≤ ∑' s : Finset ℕ, ∏ i ∈ s, (‖z‖ * (‖u i‖ * ‖v i‖)) := by
      apply Summable.tsum_le_tsum _ (nuclearDet_absolute u v huv z) hmajor
      intro s
      rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
      exact (mul_le_mul_of_nonneg_right (nuclearMinor_bound u v s)
        (pow_nonneg (norm_nonneg z) s.card)).trans_eq (mul_comm _ _)
    _ = ∏' i, (1 + ‖z‖ * (‖u i‖ * ‖v i‖)) := (tprod_one_add hmajor).symm

/-- Parseval, as a real absolutely convergent norm-square sum. -/
theorem hilbertBasis_norm_sq_hasSum
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (x : E /- [definition] -/ )
    : HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map,
    b.repr_apply_apply] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (b.repr x)

/-- The HS square sum is finite for the adjoint whenever it is finite for the operator. -/
theorem hs_adjoint_square_summable
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (B : E →L[ℂ] E /- [definition] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖B.adjoint (b i)‖ ^ 2) := by
  have hall : Summable (fun p : ℕ × ℕ => ‖inner ℂ (b p.2) (B (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (hilbertBasis_norm_sq_hasSum b (B (b i))).summable, ?_⟩
    simpa only [(hilbertBasis_norm_sq_hasSum b _).tsum_eq] using hB
  have hswap : Summable (fun i => ∑' j, ‖inner ℂ (b i) (B (b j))‖ ^ 2) :=
    hall.prod_symm.prod
  apply hswap.congr
  intro i
  rw [← (hilbertBasis_norm_sq_hasSum b (B.adjoint (b i))).tsum_eq]
  apply tsum_congr
  intro j
  rw [B.adjoint_inner_right, norm_inner_symm]

/-- The Gram-minor series attached to two HS factors, with the plus convention. -/
noncomputable def hsFactorDet
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := nuclearDet (fun i => B.adjoint (b i)) (fun i => A (b i)) z

/-- The series is entire for every pair of HS factors; there is no small-norm premise. -/
theorem hsFactorDet_entire
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (hsFactorDet b A B) Set.univ :=
  nuclearDet_entire _ _ (hs_vectors_nuclear_mass _ _
    (hs_adjoint_square_summable b B hB) hA)

/-- The nuclear expansion underlying the series is the actual product A ∘ B. -/
theorem hsFactor_nuclearOperator_eq_comp
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : nuclearOperator (fun i => B.adjoint (b i)) (fun i => A (b i)) = A ∘L B := by
  have huv := hs_vectors_nuclear_mass (fun i => B.adjoint (b i)) (fun i => A (b i))
    (hs_adjoint_square_summable b B hB) hA
  ext x
  have hleft := (nuclearOperator_hasSum _ _ huv).mapL (ContinuousLinearMap.apply ℂ E x)
  have hright := (b.hasSum_repr (B x)).mapL A
  apply hleft.unique
  simpa only [rankOne_apply, ContinuousLinearMap.apply_apply, map_smul,
    b.repr_apply_apply, B.adjoint_inner_left, ContinuousLinearMap.comp_apply] using hright

/-- A diagonal cross-Gram family has the classical diagonal minors. -/
theorem nuclearMinor_diagonal
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (hdiag : ∀ i j, inner ℂ (u i) (v j) = if i = j then a i else 0 /- [standing] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : nuclearMinor u v s = ∏ i ∈ s, a i := by
  classical
  have hmat : (fun i j : s => inner ℂ (u i) (v j) : Matrix s s ℂ) =
      Matrix.diagonal (fun i : s => a i) := by
    ext i j
    rw [hdiag, Matrix.diagonal_apply]
    simp only [Subtype.val_inj]
  rw [nuclearMinor, hmat, Matrix.det_diagonal, Finset.prod_coe_sort]

/-- Agreement with the entire ℓ¹ diagonal determinant, expressed as an infinite product. -/
theorem nuclearDet_diagonal
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (hdiag : ∀ i j, inner ℂ (u i) (v j) = if i = j then a i else 0 /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : nuclearDet u v z = ∏' i, (1 + z * a i) := by
  have hterms : (fun s : Finset ℕ => nuclearMinor u v s * z ^ s.card) =
      (fun s : Finset ℕ => ∏ i ∈ s, z * a i) := by
    ext s
    rw [nuclearMinor_diagonal u v a hdiag, Finset.prod_mul_distrib, Finset.prod_const]
    exact mul_comm _ _
  have hsum : Summable (fun s : Finset ℕ => ∏ i ∈ s, z * a i) := by
    rw [← hterms]
    exact (nuclearDet_absolute u v huv z).of_norm
  rw [nuclearDet, hterms]
  exact (tprod_one_add hsum).symm

/-- Continuity of every actual Gram minor under pointwise vector convergence. -/
theorem nuclearMinor_family_continuous
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    {X : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (u v : X → ℕ → E /- [definition] -/ )
    (hu : ∀ i, Continuous (fun x => u x i)  /- [standing] -/ )
    (hv : ∀ i, Continuous (fun x => v x i)  /- [standing] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : Continuous (fun x => nuclearMinor (u x) (v x) s) := by
  classical
  unfold nuclearMinor
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hu i).inner (hv j)

/-- Continuity under a genuine summable envelope for the nuclear vector products.
This lemma does not claim that an HS norm ball admits a pointwise envelope. -/
theorem nuclearDet_dominated_family_continuous
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    {X : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (u v : X → ℕ → E /- [definition] -/ )
    (hu : ∀ i, Continuous (fun x => u x i)  /- [standing] -/ )
    (hv : ∀ i, Continuous (fun x => v x i)  /- [standing] -/ )
    (w : ℕ → ℝ /- [definition] -/ )
    (hw : ∀ i, 0 ≤ w i /- [standing] -/ )
    (hsum : Summable w /- [standing] -/ )
    (hbound : ∀ x i, ‖u x i‖ * ‖v x i‖ ≤ w i /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Continuous (fun x => nuclearDet (u x) (v x) z) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (hw i)) (hsum.mul_left ‖z‖)
  apply continuous_tsum (fun s => (nuclearMinor_family_continuous u v hu hv s).mul
    continuous_const) hmajor
  intro s x
  change ‖nuclearMinor (u x) (v x) s * z ^ s.card‖ ≤ ∏ i ∈ s, (‖z‖ * w i)
  rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
  have hprod : ‖nuclearMinor (u x) (v x) s‖ ≤ ∏ i ∈ s, w i := by
    apply (nuclearMinor_bound (u x) (v x) s).trans
    exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hbound x i)
  exact (mul_le_mul_of_nonneg_right hprod (pow_nonneg (norm_nonneg z) s.card)).trans_eq
    (mul_comm _ _)

/-- Exact finite-dimensional principal-minor expansion at every complex coupling. -/
theorem matrix_det_principal_minors
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (M : Matrix ι ι ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : Matrix.det (1 + z • M) = ∑ s ∈ Finset.univ.powerset,
      Matrix.det (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) * z ^ s.card := by
  classical
  have hp : Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) =
      ∑ s ∈ Finset.univ.powerset,
        Polynomial.C (Matrix.det (M.submatrix (Subtype.val : s → ι)
          (Subtype.val : s → ι))) * Polynomial.X ^ s.card := by
    apply Polynomial.ext
    intro k
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]
  have he := congrArg (Polynomial.evalRingHom z) hp
  rw [RingHom.map_det] at he
  have hmap : (Polynomial.evalRingHom z).mapMatrix
      (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) = 1 + z • M := by
    ext i j
    change Polynomial.eval z ((if i = j then 1 else 0) +
      Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + z * M i j
    by_cases hij : i = j <;>
      simp only [hij, if_true, if_false, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X, Polynomial.eval_C]
  rw [hmap] at he
  simpa only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X] using he

/-- Concrete nonzero, large-norm joint witness for the nuclear and HS-vector premises. -/
theorem nuclear_joint_probe
    : ∃ u v : ℕ → ℂ,
      Summable (fun i => ‖u i‖ ^ 2) ∧ Summable (fun i => ‖v i‖ ^ 2) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧ nuclearDet u v 1 = 3 ∧
      nuclearDet u v (-1 / 2) = 0 ∧ AnalyticOnNhd ℂ (nuclearDet u v) Set.univ ∧
      nuclearOperator u v 1 = 2 := by
  let u : ℕ → ℂ := fun i => if i = 0 then 1 else 0
  let v : ℕ → ℂ := fun i => if i = 0 then 2 else 0
  have hu : Summable (fun i => ‖u i‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [u, hi]
  have hv : Summable (fun i => ‖v i‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [v, hi]
  have huv := hs_vectors_nuclear_mass u v hu hv
  have hdiag : ∀ i j, inner ℂ (u i) (v j) = if i = j then v i else 0 := by
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst i; subst j; simp [u, v]
    · subst i; simp [u, v, hj, Ne.symm hj]
    · subst j; simp [u, v, hi]
    · simp [u, v, hi, hj]
  have heval : ∀ z : ℂ, nuclearDet u v z = 1 + z * 2 := by
    intro z
    rw [nuclearDet_diagonal u v v huv hdiag, tprod_eq_prod (s := {0})]
    · simp [v]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [v, hi]
  refine ⟨u, v, hu, hv, huv, ?_, ?_, nuclearDet_entire u v huv, ?_⟩
  · rw [heval]; norm_num
  · rw [heval]; norm_num
  · have hop : nuclearOperator u v = rankOne ℂ (2 : ℂ) 1 := by
      rw [nuclearOperator, tsum_eq_sum (s := {0})]
      · simp [u, v]
      · intro i hi
        simp only [Finset.mem_singleton] at hi
        simp [u, v, hi]
    rw [hop, rankOne_apply]
    simp

/-- Identifying a principal minor when its finite index set is mapped into ℕ. -/
theorem nuclearMinor_subtype_map
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    (t : Finset s /- [definition] -/ )
    : nuclearMinor u v (t.map (Function.Embedding.subtype (· ∈ s))) =
      Matrix.det (fun i j : t => inner ℂ (u (i : s)) (v (j : s))) := by
  classical
  let emb : s ↪ ℕ := Function.Embedding.subtype (· ∈ s)
  let f : t → (t.map emb) := fun i => ⟨(i : s), Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun k : t.map emb => (k : ℕ)) hij
    · intro j
      obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.property
      refine ⟨⟨i, hi⟩, ?_⟩
      exact Subtype.ext hij
  let e : t ≃ (t.map emb) := Equiv.ofBijective f hf
  exact (Matrix.det_submatrix_equiv_self e
    (fun i j : t.map emb => inner ℂ (u i) (v j))).symm

/-- Every finite nuclear truncation is the usual finite matrix determinant. -/
theorem nuclearTruncation_eq_matrix_det
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : (∑ t ∈ s.powerset, nuclearMinor u v t * z ^ t.card) =
      Matrix.det ((1 : Matrix s s ℂ) + z • Matrix.of (fun i j : s => inner ℂ (u i) (v j))) := by
  classical
  let M : Matrix s s ℂ := fun i j => inner ℂ (u i) (v j)
  change (∑ t ∈ s.powerset, nuclearMinor u v t * z ^ t.card) = Matrix.det ((1 : Matrix s s ℂ) + z • M)
  rw [matrix_det_principal_minors M z]
  symm
  apply Finset.sum_bij (fun t _ => t.map (Function.Embedding.subtype (· ∈ s)))
  · intro t ht
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact hji ▸ j.property
  · intro t ht t' ht' h
    exact Finset.map_injective _ h
  · intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    refine ⟨t.subtype (· ∈ s), Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    ext i
    simp only [Finset.mem_map, Finset.mem_subtype]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact hji ▸ hj
    · intro hi
      exact ⟨⟨i, hts hi⟩, hi, rfl⟩
  · intro t ht
    rw [nuclearMinor_subtype_map, Finset.card_map]
    rfl

/-- Classical finite matrix determinants converge to the nuclear Gram-minor series. -/
theorem nuclearTruncation_matrix_det_tendsto
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun s : Finset ℕ => Matrix.det
        ((1 : Matrix s s ℂ) + z • Matrix.of (fun i j : s => inner ℂ (u i) (v j))))
      atTop (𝓝 (nuclearDet u v z)) := by
  have h := (nuclearDet_hasSum u v huv z).comp tendsto_finset_powerset_atTop_atTop
  simpa only [Function.comp_def, nuclearTruncation_eq_matrix_det] using h

/-- A nondegenerate infinite-dimensional Hilbert-space instance of both HS factor premises. -/
theorem hsFactor_joint_probe
    : ∃ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2),
      ∃ A B : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2) ∧
      ‖A (b 0)‖ = 2 ∧ ‖B (b 0)‖ = 1 ∧
      AnalyticOnNhd ℂ (hsFactorDet b A B) Set.univ ∧
      nuclearOperator (fun i => B.adjoint (b i)) (fun i => A (b i)) = A ∘L B := by
  let b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  let B := rankOne ℂ (b 0) (b 0)
  let A := (2 : ℂ) • B
  have hB : Summable (fun i => ‖B (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  have hA : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [A, B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  refine ⟨b, A, B, hA, hB, ?_, ?_, hsFactorDet_entire b A B hA hB,
    hsFactor_nuclearOperator_eq_comp b A B hA hB⟩
  · simp [A, B, rankOne_apply, norm_smul, orthonormal_iff_ite.mp b.orthonormal,
      b.orthonormal.norm_eq_one 0]
  · simp [B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal,
      b.orthonormal.norm_eq_one 0]

/-- The finite matrix approximations converge uniformly on every bounded coupling disk. -/
theorem nuclearTruncation_uniform_closedBall
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (R : ℝ /- [definition] -/ )
    (hR : 0 ≤ R /- [standing] -/ )
    : TendstoUniformlyOn (fun s : Finset ℕ => fun z => Matrix.det
        ((1 : Matrix s s ℂ) + z • Matrix.of (fun i j : s => inner ℂ (u i) (v j))))
      (nuclearDet u v) atTop (Metric.closedBall 0 R) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg hR (mul_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))))
    (huv.mul_left R)
  have h := tendstoUniformlyOn_tsum hmajor (f := fun s z => nuclearMinor u v s * z ^ s.card)
    (s := Metric.closedBall 0 R) (fun s z hz => by
      have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
      calc
        ‖nuclearMinor u v s‖ * ‖z‖ ^ s.card ≤
            (∏ i ∈ s, (‖u i‖ * ‖v i‖)) * R ^ s.card :=
          mul_le_mul (nuclearMinor_bound u v s)
            (pow_le_pow_left₀ (norm_nonneg z) hzR s.card)
            (pow_nonneg (norm_nonneg z) s.card) (Finset.prod_nonneg fun i _ => by positivity)
        _ = R ^ s.card * ∏ i ∈ s, (‖u i‖ * ‖v i‖) := mul_comm _ _)
  have hcomp : TendstoUniformlyOn
      (fun s : Finset ℕ => fun z => ∑ t ∈ s.powerset, nuclearMinor u v t * z ^ t.card)
      (nuclearDet u v) atTop (Metric.closedBall 0 R) := by
    intro U hU
    exact tendsto_finset_powerset_atTop_atTop.eventually (h U hU)
  simpa only [nuclearTruncation_eq_matrix_det] using hcomp

/-- Explicit absolute-convergence statement for two genuine HS factors. -/
theorem hsFactorDet_absolute
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun s : Finset ℕ => ‖nuclearMinor (fun i => B.adjoint (b i))
        (fun i => A (b i)) s * z ^ s.card‖) :=
  nuclearDet_absolute _ _ (hs_vectors_nuclear_mass _ _ (hs_adjoint_square_summable b B hB) hA) z

/-- The actual orthonormal diagonal operator expansion agrees with the ℓ¹ product. -/
theorem nuclearDet_orthonormal_diagonal
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (e : ℕ → E /- [definition] -/ )
    (he : Orthonormal ℂ e /- [standing] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : nuclearDet e (fun i => a i • e i) z = ∏' i, (1 + z * a i) := by
  have huv : Summable (fun i => ‖e i‖ * ‖a i • e i‖) := by
    simpa only [norm_smul, he.norm_eq_one, mul_one, one_mul] using ha
  apply nuclearDet_diagonal e (fun i => a i • e i) a huv _ z
  intro i j
  rw [inner_smul_right, orthonormal_iff_ite.mp he]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

/-- The Fredholm principal-minor series defined from the operator itself in a fixed Hilbert basis.
Neither a factorization witness nor a coefficient estimate is stored in this definition. -/
noncomputable def operatorDet
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := nuclearDet b (fun i => T (b i)) z

/-- The actual operator coefficients equal the cross-Gram coefficients of any HS factorization. -/
theorem operatorMinor_factorization
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : nuclearMinor b (fun i => (A ∘L B) (b i)) s =
      nuclearMinor (fun i => A.adjoint (b i)) (fun i => B (b i)) s := by
  unfold nuclearMinor
  congr 1
  ext i j
  exact (A.adjoint_inner_left (B (b j)) (b i)).symm

/-- Factorization witnesses disappear from the determinant value. The reversed pair is intentional:
Sylvester's finite-rank Gram matrix has the order BA, while the operator has order AB. -/
theorem operatorDet_eq_hsFactorDet
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b (A ∘L B) z = hsFactorDet b B A z := by
  unfold operatorDet hsFactorDet nuclearDet
  apply tsum_congr
  intro s
  rw [operatorMinor_factorization]

/-- Absolute convergence for every trace-class factorization and every coupling. -/
theorem operatorDet_absolute
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℂ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun s : Finset ℕ => ‖nuclearMinor b (fun i => T (b i)) s * z ^ s.card‖) := by
  obtain ⟨A, B, rfl, hA, hB⟩ := hT
  simpa only [operatorMinor_factorization] using hsFactorDet_absolute b B A hB hA z

/-- A trace-class operator's fixed-basis Fredholm determinant is entire, with no norm restriction. -/
theorem operatorDet_entire
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℂ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (operatorDet b T) Set.univ := by
  obtain ⟨A, B, rfl, hA, hB⟩ := hT
  have heq : operatorDet b (A ∘L B) = hsFactorDet b B A :=
    funext (operatorDet_eq_hsFactorDet b A B)
  rw [heq]
  exact hsFactorDet_entire b B A hB hA

/-- Equality of factor products gives equality of determinant values, without a small-norm premise. -/
theorem hsFactorDet_factorization_independent
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B C D : E →L[ℂ] E /- [definition] -/ )
    (hprod : A ∘L B = C ∘L D /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : hsFactorDet b B A z = hsFactorDet b D C z := by
  rw [← operatorDet_eq_hsFactorDet, ← operatorDet_eq_hsFactorDet, hprod]

/-- Zero vector columns give zero principal minors. -/
theorem nuclearMinor_zero_column
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    (j : ℕ /- [definition] -/ )
    (hj : j ∈ s /- [standing] -/ )
    (hvj : v j = 0 /- [standing] -/ )
    : nuclearMinor u v s = 0 := by
  classical
  apply Matrix.det_eq_zero_of_column_eq_zero (⟨j, hj⟩ : s)
  intro i
  simp only [hvj, inner_zero_right]

/-- Exact classical matrix determinant for a finitely supported nuclear representation. -/
theorem nuclearDet_finite_support
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    (hv : ∀ i, i ∉ s → v i = 0 /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : nuclearDet u v z = Matrix.det ((1 : Matrix s s ℂ) +
        z • Matrix.of (fun i j : s => inner ℂ (u i) (v j))) := by
  classical
  rw [nuclearDet, tsum_eq_sum (s := s.powerset)]
  · exact nuclearTruncation_eq_matrix_det u v s z
  · intro t ht
    have hts : ¬ t ⊆ s := by simpa only [Finset.mem_powerset] using ht
    obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hts
    rw [nuclearMinor_zero_column u v t j hjt (hv j hjs), zero_mul]

/-- Finite compressions of the operator itself converge to its entire determinant. -/
theorem operatorDet_matrix_det_tendsto
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℂ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun s : Finset ℕ => Matrix.det ((1 : Matrix s s ℂ) +
        z • Matrix.of (fun i j : s => inner ℂ (b i) (T (b j)))))
      atTop (𝓝 (operatorDet b T z)) := by
  have h := (operatorDet_absolute b T hT z).of_norm.hasSum.comp
    tendsto_finset_powerset_atTop_atTop
  simpa only [Function.comp_def, nuclearTruncation_eq_matrix_det, operatorDet,
    nuclearDet] using h

/-- Agreement with the ℓ¹ diagonal determinant for actual diagonal operators. -/
theorem operatorDet_diagonal
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b T z = ∏' i, (1 + z * a i) := by
  unfold operatorDet
  simp only [hdiag]
  exact nuclearDet_orthonormal_diagonal b b.orthonormal a ha z

/-- A concrete infinite-dimensional, norm-two operator satisfies every trace-class premise jointly.
Its determinant has a zero, so the entire determinant is not a globally exponentiated Plemelj sum. -/
theorem operator_joint_probe
    : ∃ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2),
      ∃ T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
      (∃ A B, T = A ∘L B ∧ Summable (fun i => ‖A (b i)‖ ^ 2) ∧
        Summable (fun i => ‖B (b i)‖ ^ 2)) ∧
      ‖T (b 0)‖ = 2 ∧ operatorDet b T 1 = 3 ∧ operatorDet b T (-1 / 2) = 0 ∧
      AnalyticOnNhd ℂ (operatorDet b T) Set.univ := by
  let b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  let B := rankOne ℂ (b 0) (b 0)
  let A := (2 : ℂ) • B
  let T := A ∘L B
  have hB : Summable (fun i => ‖B (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, Ne.symm hi]
  have hA : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [A, B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, Ne.symm hi]
  let a : ℕ → ℂ := fun i => if i = 0 then 2 else 0
  have ha : Summable (fun i => ‖a i‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [a, hi]
  have hdiag : ∀ i, T (b i) = a i • b i := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [T, A, B, a, rankOne_apply, b.orthonormal.norm_eq_one 0]
    · simp [T, A, B, a, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal,
        hi, Ne.symm hi]
  have hT : ∃ A B, T = A ∘L B ∧ Summable (fun i => ‖A (b i)‖ ^ 2) ∧
      Summable (fun i => ‖B (b i)‖ ^ 2) := ⟨A, B, rfl, hA, hB⟩
  have heval : ∀ z, operatorDet b T z = 1 + z * 2 := by
    intro z
    rw [operatorDet_diagonal b T a ha hdiag, tprod_eq_prod (s := {0})]
    · simp [a]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [a, hi]
  refine ⟨b, T, hT, ?_, ?_, ?_, operatorDet_entire b T hT⟩
  · rw [hdiag]; simp [a, norm_smul, b.orthonormal.norm_eq_one 0]
  · rw [heval]; norm_num
  · rw [heval]; norm_num



set_option maxHeartbeats 400000


/-- A summably close family in l2 has a genuine l2 envelope.
The envelope is constructed from the sum of coordinate norm sequences. -/
theorem l2_summable_distance_envelope
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    (u : ℕ → lp (fun _ : ℕ => E) 2 /- [definition] -/ )
    (u₀ : lp (fun _ : ℕ => E) 2 /- [definition] -/ )
    (hu : Summable (fun n => ‖u n - u₀‖)  /- [standing] -/ )
    : ∃ w : lp (fun _ : ℕ => ℝ) 2,
      (∀ i, 0 ≤ w i) ∧ (∀ n i, ‖u n i‖ ≤ w i) := by
  let d : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun n => lp.toNorm (u n - u₀)
  have hd : Summable (fun n => ‖d n‖) := by
    simpa only [d, lp.norm_toNorm] using hu
  have hds : Summable d := hd.of_norm
  let w : lp (fun _ : ℕ => ℝ) 2 := lp.toNorm u₀ + ∑' n, d n
  have heval (i : ℕ) : (∑' n, d n) i = ∑' n, ‖u n i - u₀ i‖ := by
    exact ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).map_tsum hds)
  have hi (i : ℕ) : Summable (fun n => ‖u n i - u₀ i‖) :=
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).summable hds)
  refine ⟨w, ?_, ?_⟩
  · intro i
    change 0 ≤ ‖u₀ i‖ + (∑' n, d n) i
    rw [heval]
    positivity
  · intro n i
    change ‖u n i‖ ≤ ‖u₀ i‖ + (∑' n, d n) i
    rw [heval]
    calc
      ‖u n i‖ ≤ ‖u₀ i‖ + ‖u n i - u₀ i‖ := by
        simpa only [add_sub_cancel] using norm_add_le (u₀ i) (u n i - u₀ i)
      _ ≤ ‖u₀ i‖ + ∑' k, ‖u k i - u₀ i‖ :=
        add_le_add_right (le_hasSum (hi i).hasSum n (fun k _ => norm_nonneg _)) _

/-- Dominated convergence for the actual Gram-minor Fredholm series. -/
theorem nuclearDet_dominated_tendsto
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (u v : ℕ → ℕ → E /- [definition] -/ )
    (u₀ v₀ : ℕ → E /- [definition] -/ )
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (u₀ i))  /- [standing] -/ )
    (hv : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (v₀ i))  /- [standing] -/ )
    (w : ℕ → ℝ /- [definition] -/ )
    (hw : ∀ i, 0 ≤ w i /- [standing] -/ )
    (hsum : Summable w /- [standing] -/ )
    (hbound : ∀ n i, ‖u n i‖ * ‖v n i‖ ≤ w i /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun n => nuclearDet (u n) (v n) z) atTop (𝓝 (nuclearDet u₀ v₀ z)) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (hw i)) (hsum.mul_left ‖z‖)
  apply tendsto_tsum_of_dominated_convergence hmajor
  · intro s
    have hmat : Tendsto (fun n => (fun i j : s => inner ℂ (u n i) (v n j)))
        atTop (𝓝 (fun i j : s => inner ℂ (u₀ i) (v₀ j))) :=
      tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => (hu i).inner (hv j)))
    have hdet : Continuous (Matrix.det : Matrix s s ℂ → ℂ) := continuous_id.matrix_det
    exact (hdet.tendsto _ |>.comp hmat).mul_const _
  · apply Eventually.of_forall
    intro n s
    change ‖nuclearMinor (u n) (v n) s * z ^ s.card‖ ≤ ∏ i ∈ s, (‖z‖ * w i)
    rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
    have hp : ‖nuclearMinor (u n) (v n) s‖ ≤ ∏ i ∈ s, w i := by
      apply (nuclearMinor_bound (u n) (v n) s).trans
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hbound n i)
    exact (mul_le_mul_of_nonneg_right hp (pow_nonneg (norm_nonneg z) s.card)).trans_eq
      (mul_comm _ _)

/-- Genuine joint l2-norm continuity of the Gram-minor determinant, without an envelope premise. -/
theorem nuclearDet_l2_continuous
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (z : ℂ /- [definition] -/ )
    : Continuous (fun p : lp (fun _ : ℕ => E) 2 × lp (fun _ : ℕ => E) 2 =>
      nuclearDet p.1 p.2 z) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro a ha
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have han := ha.comp hns
  obtain ⟨ms, hms, hclose⟩ := han.subseq_mem
    (V := fun n => Metric.ball p ((1 / (2 : ℝ)) ^ n))
    (fun n => Metric.ball_mem_nhds _ (by positivity))
  have hsum : Summable (fun n => ‖a (ns (ms n)) - p‖) := by
    apply summable_geometric_two.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    simpa only [dist_eq_norm, Function.comp_apply] using (Metric.mem_ball.mp (hclose n)).le
  have hu : Summable (fun n => ‖(a (ns (ms n))).1 - p.1‖) := by
    apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    exact norm_fst_le (a (ns (ms n)) - p)
  have hv : Summable (fun n => ‖(a (ns (ms n))).2 - p.2‖) := by
    apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    exact norm_snd_le (a (ns (ms n)) - p)
  obtain ⟨wu, hwu, hbu⟩ := l2_summable_distance_envelope
    (fun n => (a (ns (ms n))).1) p.1 hu
  obtain ⟨wv, hwv, hbv⟩ := l2_summable_distance_envelope
    (fun n => (a (ns (ms n))).2) p.2 hv
  have hwu2 : Summable (fun i => ‖wu i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) wu).summable
  have hwv2 : Summable (fun i => ‖wv i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) wv).summable
  have hwprod : Summable (fun i => wu i * wv i) := by
    apply ((hwu2.add hwv2).div_const 2).of_nonneg_of_le
      (fun i => mul_nonneg (hwu i) (hwv i))
    intro i
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (wu i - wv i)]
  have hall := han.comp hms.tendsto_atTop
  refine ⟨ms, nuclearDet_dominated_tendsto
    (fun n i => (a (ns (ms n))).1 i) (fun n i => (a (ns (ms n))).2 i)
    p.1 p.2 ?_ ?_ (fun i => wu i * wv i) (fun i => mul_nonneg (hwu i) (hwv i))
    hwprod (fun n i => mul_le_mul (hbu n i) (hbv n i) (norm_nonneg _) (hwu i)) z⟩
  · intro i
    exact ((lp.evalCLM ℂ (fun _ : ℕ => E) 2 i).continuous.comp continuous_fst).tendsto p
      |>.comp hall
  · intro i
    exact ((lp.evalCLM ℂ (fun _ : ℕ => E) 2 i).continuous.comp continuous_snd).tendsto p
      |>.comp hall


/-- The columns of a genuine HS operator as a point of the l2 Banach space. -/
noncomputable def hsColumns
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : lp (fun _ : ℕ => E) 2 :=
  ⟨fun i => A (b i), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hA)⟩

/-- The l2 column norm is exactly the usual HS square sum. -/
theorem hsColumns_norm_sq
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : ‖hsColumns b A hA‖ ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (hsColumns b A hA)).tsum_eq.symm

/-- The HS square sum is preserved by adjunction, proved by Parseval and Tonelli. -/
theorem hs_adjoint_square_tsum_eq
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : (∑' i, ‖A.adjoint (b i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  have hall : Summable (fun p : ℕ × ℕ => ‖inner ℂ (b p.2) (A (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (hilbertBasis_norm_sq_hasSum b (A (b i))).summable, ?_⟩
    simpa only [(hilbertBasis_norm_sq_hasSum b _).tsum_eq] using hA
  calc
    (∑' i, ‖A.adjoint (b i)‖ ^ 2) =
        ∑' i, ∑' j, ‖inner ℂ (b i) (A (b j))‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [← (hilbertBasis_norm_sq_hasSum b (A.adjoint (b i))).tsum_eq]
      apply tsum_congr
      intro j
      rw [A.adjoint_inner_right, norm_inner_symm]
    _ = ∑' j, ∑' i, ‖inner ℂ (b i) (A (b j))‖ ^ 2 := hall.tsum_comm
    _ = ∑' i, ‖A (b i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact (hilbertBasis_norm_sq_hasSum b (A (b i))).tsum_eq

/-- Differences of HS columns also have the expected HS square norm. -/
theorem hsColumns_difference_norm_sq
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : ‖hsColumns b A hA - hsColumns b B hB‖ ^ 2 =
      ∑' i, ‖(A - B) (b i)‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      (hsColumns b A hA - hsColumns b B hB)).tsum_eq.symm

/-- A difference of genuine HS operators is HS. -/
theorem hs_square_summable_sub
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖(A - B) (b i)‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      (hsColumns b A hA - hsColumns b B hB)).summable

/-- HS square convergence gives column convergence along any filter. -/
theorem hsColumns_tendsto_of_square
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : X → E →L[ℂ] E /- [definition] -/ )
    (A₀ : E →L[ℂ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconv : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    : Tendsto (fun x => hsColumns b (A x) (hA x)) l (𝓝 (hsColumns b A₀ hA₀)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have heq (x : X) : Real.sqrt (∑' i, ‖(A x - A₀) (b i)‖ ^ 2) =
      ‖hsColumns b (A x) (hA x) - hsColumns b A₀ hA₀‖ := by
    rw [← hsColumns_difference_norm_sq b (A x) A₀ (hA x) hA₀]
    exact Real.sqrt_sq (norm_nonneg _)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, heq, Real.sqrt_zero, dist_eq_norm] using hs

/-- Adjoint column convergence follows from genuine HS square convergence. -/
theorem hsColumns_adjoint_tendsto_of_square
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : X → E →L[ℂ] E /- [definition] -/ )
    (A₀ : E →L[ℂ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconv : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    : Tendsto (fun x => hsColumns b (A x).adjoint (hs_adjoint_square_summable b _ (hA x)))
      l (𝓝 (hsColumns b A₀.adjoint (hs_adjoint_square_summable b _ hA₀))) := by
  apply hsColumns_tendsto_of_square b (fun x => (A x).adjoint) A₀.adjoint
    (fun x => hs_adjoint_square_summable b _ (hA x)) (hs_adjoint_square_summable b _ hA₀) l
  convert hconv using 1
  congr 1
  ext x
  rw [← ContinuousLinearMap.adjoint.map_sub]
  exact hs_adjoint_square_tsum_eq b (A x - A₀) (hs_square_summable_sub b _ _ (hA x) hA₀)

/-- Joint HS-norm continuity of the factor determinant, stated along an arbitrary filter.
The hypotheses are the genuine HS square distances to the two limiting factors. -/
theorem hsFactorDet_tendsto_of_hs
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : X → E →L[ℂ] E /- [definition] -/ )
    (A₀ B₀ : E →L[ℂ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (hB₀ : Summable (fun i => ‖B₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconvA : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (hconvB : Tendsto (fun x => ∑' i, ‖(B x - B₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun x => hsFactorDet b (A x) (B x) z) l (𝓝 (hsFactorDet b A₀ B₀ z)) := by
  have hp := (hsColumns_adjoint_tendsto_of_square b B B₀ hB hB₀ l hconvB).prodMk_nhds
    (hsColumns_tendsto_of_square b A A₀ hA hA₀ l hconvA)
  have h := (nuclearDet_l2_continuous (E := E) z).tendsto
    (hsColumns b B₀.adjoint (hs_adjoint_square_summable b _ hB₀), hsColumns b A₀ hA₀)
    |>.comp hp
  simpa only [Function.comp_def, hsColumns, hsFactorDet] using h

/-- The operator determinant of AB converges under HS-norm convergence of A and B. -/
theorem operatorDet_comp_tendsto_of_hs
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : X → E →L[ℂ] E /- [definition] -/ )
    (A₀ B₀ : E →L[ℂ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (hB₀ : Summable (fun i => ‖B₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconvA : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (hconvB : Tendsto (fun x => ∑' i, ‖(B x - B₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun x => operatorDet b (A x ∘L B x) z) l (𝓝 (operatorDet b (A₀ ∘L B₀) z)) := by
  simpa only [operatorDet_eq_hsFactorDet] using
    hsFactorDet_tendsto_of_hs b B A B₀ A₀ hB hA hB₀ hA₀ l hconvB hconvA z



/-- Continuous families of HS factors give continuous Fredholm determinants.
Each square-distance premise is the genuine HS-norm convergence at that point. -/
theorem operatorDet_comp_family_continuous
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    [TopologicalSpace X /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : X → E →L[ℂ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hconvA : ∀ t, Tendsto (fun x => ∑' i, ‖(A x - A t) (b i)‖ ^ 2)
      (𝓝 t) (𝓝 0)  /- [standing] -/ )
    (hconvB : ∀ t, Tendsto (fun x => ∑' i, ‖(B x - B t) (b i)‖ ^ 2)
      (𝓝 t) (𝓝 0)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Continuous (fun x => operatorDet b (A x ∘L B x) z) :=
  continuous_iff_continuousAt.mpr (fun t =>
    operatorDet_comp_tendsto_of_hs b A B (A t) (B t) hA hB (hA t) (hB t)
      (𝓝 t) (hconvA t) (hconvB t) z)



/-- All HS continuity binders are jointly inhabited on infinite-dimensional l2,
with a norm-two factor and a norm-one factor. No event or coefficient premise is used. -/
theorem hs_continuity_joint_probe
    : ∃ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2),
      ∃ A B : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2) ∧
      ‖A (b 0)‖ = 2 ∧ ‖B (b 0)‖ = 1 ∧
      (Tendsto (fun _ : ℝ => ∑' i, ‖(A - A) (b i)‖ ^ 2) (𝓝 0) (𝓝 0)) ∧
      (Tendsto (fun _ : ℝ => ∑' i, ‖(B - B) (b i)‖ ^ 2) (𝓝 0) (𝓝 0)) ∧
      ∀ z, Tendsto (fun _ : ℝ => operatorDet b (A ∘L B) z)
        (𝓝 0) (𝓝 (operatorDet b (A ∘L B) z)) := by
  obtain ⟨b, A, B, hA, hB, hAn, hBn, _⟩ := hsFactor_joint_probe
  have hconvA : Tendsto (fun _ : ℝ => ∑' i, ‖(A - A) (b i)‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  have hconvB : Tendsto (fun _ : ℝ => ∑' i, ‖(B - B) (b i)‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  refine ⟨b, A, B, hA, hB, hAn, hBn, hconvA, hconvB, ?_⟩
  intro z
  exact operatorDet_comp_tendsto_of_hs b (fun _ : ℝ => A) (fun _ : ℝ => B) A B
    (fun _ => hA) (fun _ => hB) hA hB (𝓝 0) hconvA hconvB z




open scoped Classical

/-!
Real-Hilbert-space companion with the same actual Gram coefficients and plus convention.
The values can be expressed in the real Airy L2 construction.
The real determinant is real analytic on all of R; the complex engine remains unchanged.
-/

noncomputable def realNuclearOperator
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    : E →L[ℝ] E := ∑' i, rankOne ℝ (v i) (u i)

theorem realL2_summable_distance_envelope
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    (u : ℕ → lp (fun _ : ι => E) 2 /- [definition] -/ )
    (u₀ : lp (fun _ : ι => E) 2 /- [definition] -/ )
    (hu : Summable (fun n => ‖u n - u₀‖)  /- [standing] -/ )
    : ∃ w : lp (fun _ : ι => ℝ) 2,
      (∀ i, 0 ≤ w i) ∧ (∀ n i, ‖u n i‖ ≤ w i) := by
  let d : ℕ → lp (fun _ : ι => ℝ) 2 := fun n => lp.toNorm (u n - u₀)
  have hd : Summable (fun n => ‖d n‖) := by
    simpa only [d, lp.norm_toNorm] using hu
  have hds : Summable d := hd.of_norm
  let w : lp (fun _ : ι => ℝ) 2 := lp.toNorm u₀ + ∑' n, d n
  have heval (i : ι) : (∑' n, d n) i = ∑' n, ‖u n i - u₀ i‖ := by
    exact ((lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).map_tsum hds)
  have hi (i : ι) : Summable (fun n => ‖u n i - u₀ i‖) :=
    ((lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).summable hds)
  refine ⟨w, ?_, ?_⟩
  · intro i
    change 0 ≤ ‖u₀ i‖ + (∑' n, d n) i
    rw [heval]
    positivity
  · intro n i
    change ‖u n i‖ ≤ ‖u₀ i‖ + (∑' n, d n) i
    rw [heval]
    calc
      ‖u n i‖ ≤ ‖u₀ i‖ + ‖u n i - u₀ i‖ := by
        simpa only [add_sub_cancel] using norm_add_le (u₀ i) (u n i - u₀ i)
      _ ≤ ‖u₀ i‖ + ∑' k, ‖u k i - u₀ i‖ :=
        add_le_add_right (le_hasSum (hi i).hasSum n (fun k _ => norm_nonneg _)) _

theorem realNuclearOperator_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : Summable (fun i => ‖rankOne ℝ (v i) (u i)‖) := by
  simpa only [norm_rankOne, mul_comm] using huv

theorem realNuclearOperator_hasSum
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : HasSum (fun i => rankOne ℝ (v i) (u i)) (realNuclearOperator u v) :=
  (realNuclearOperator_absolute u v huv).of_norm.hasSum

theorem realHs_vectors_nuclear_mass
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (hu : Summable (fun i => ‖u i‖ ^ 2)  /- [standing] -/ )
    (hv : Summable (fun i => ‖v i‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖u i‖ * ‖v i‖) := by
  apply ((hu.add hv).div_const 2).of_nonneg_of_le (fun i => by positivity)
  intro i
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]

noncomputable def realNuclearMinor
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    : ℝ := Matrix.det (fun i j : s => inner ℝ (u i) (v j))

theorem realNuclearMinor_bound
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    : ‖realNuclearMinor u v s‖ ≤ ∏ i ∈ s, (‖u i‖ * ‖v i‖) := by
  classical
  let e := Fintype.equivFin s
  have h := crossGram_det_bound (𝕜 := ℝ)
    (fun i : Fin (Fintype.card s) => u (e.symm i))
    (fun i : Fin (Fintype.card s) => v (e.symm i))
  have hd : Matrix.det (fun i j : Fin (Fintype.card s) =>
      inner ℝ (u (e.symm i)) (v (e.symm j))) = realNuclearMinor u v s :=
    Matrix.det_reindex_self e (fun i j : s => inner ℝ (u i) (v j))
  rw [hd, e.symm.prod_comp (fun i : s => ‖u i‖),
    e.symm.prod_comp (fun i : s => ‖v i‖)] at h
  calc
    ‖realNuclearMinor u v s‖ ≤ (∏ i : s, ‖u i‖) * (∏ i : s, ‖v i‖) := h
    _ = ∏ i ∈ s, (‖u i‖ * ‖v i‖) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_coe_sort s (fun i => ‖u i‖ * ‖v i‖)

noncomputable def realNuclearDet
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : ℝ := ∑' s : Finset ι, realNuclearMinor u v s * z ^ s.card

theorem realNuclearDet_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun s : Finset ι => ‖realNuclearMinor u v s * z ^ s.card‖) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (mul_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))))
    (huv.mul_left ‖z‖)
  apply hmajor.of_nonneg_of_le (fun s => norm_nonneg _)
  intro s
  rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
  exact (mul_le_mul_of_nonneg_right (realNuclearMinor_bound u v s)
    (pow_nonneg (norm_nonneg z) s.card)).trans_eq (mul_comm _ _)

theorem realNuclearDet_hasSum
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : HasSum (fun s : Finset ι => realNuclearMinor u v s * z ^ s.card) (realNuclearDet u v z) :=
  (realNuclearDet_absolute u v huv z).of_norm.hasSum

noncomputable def realNuclearCoeff
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℝ := ∑' s : {s : Finset ι // s.card = n}, realNuclearMinor u v s.val

theorem realNuclearCoeff_hasSum
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : HasSum (fun n => realNuclearCoeff u v n * z ^ n) (realNuclearDet u v z) := by
  have hgroup := (realNuclearDet_hasSum u v huv z).tsum_fiberwise Finset.card
  refine hgroup.congr_fun (fun n => ?_)
  rw [realNuclearCoeff, ← tsum_mul_right]
  apply tsum_congr
  intro s
  rw [s.property]

theorem realNuclearCoeff_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun n => ‖realNuclearCoeff u v n * z ^ n‖) :=
  (realNuclearCoeff_hasSum u v huv z).summable.norm

theorem realNuclearCoeff_radius_top
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℝ (realNuclearCoeff u v)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  have h := realNuclearCoeff_absolute u v huv (R : ℝ)
  simpa only [norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm,
    Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using h

theorem realNuclearDet_entire
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    : AnalyticOnNhd ℝ (realNuclearDet u v) Set.univ := by
  have hr := realNuclearCoeff_radius_top u v huv
  have h := (FormalMultilinearSeries.ofScalars ℝ (realNuclearCoeff u v)).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars ℝ (realNuclearCoeff u v)).sum = realNuclearDet u v := by
    ext z
    exact (FormalMultilinearSeries.ofScalars_sum_eq (realNuclearCoeff u v) z).trans
      (realNuclearCoeff_hasSum u v huv z).tsum_eq
  rw [heq] at h
  simpa only [hr, Metric.eball_top] using h.analyticOnNhd

theorem realNuclearDet_norm_le
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : ‖realNuclearDet u v z‖ ≤ ∏' i, (1 + ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (mul_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))))
    (huv.mul_left ‖z‖)
  calc
    ‖realNuclearDet u v z‖ ≤ ∑' s : Finset ι, ‖realNuclearMinor u v s * z ^ s.card‖ :=
      norm_tsum_le_tsum_norm (realNuclearDet_absolute u v huv z)
    _ ≤ ∑' s : Finset ι, ∏ i ∈ s, (‖z‖ * (‖u i‖ * ‖v i‖)) := by
      apply Summable.tsum_le_tsum _ (realNuclearDet_absolute u v huv z) hmajor
      intro s
      rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
      exact (mul_le_mul_of_nonneg_right (realNuclearMinor_bound u v s)
        (pow_nonneg (norm_nonneg z) s.card)).trans_eq (mul_comm _ _)
    _ = ∏' i, (1 + ‖z‖ * (‖u i‖ * ‖v i‖)) := (tprod_one_add hmajor).symm

theorem realHilbertBasis_norm_sq_hasSum
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (x : E /- [definition] -/ )
    : HasSum (fun i => ‖inner ℝ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map,
    b.repr_apply_apply] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (b.repr x)

theorem realHs_adjoint_square_summable
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (B : E →L[ℝ] E /- [definition] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖B.adjoint (b i)‖ ^ 2) := by
  have hall : Summable (fun p : ι × ι => ‖inner ℝ (b p.2) (B (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (realHilbertBasis_norm_sq_hasSum b (B (b i))).summable, ?_⟩
    simpa only [(realHilbertBasis_norm_sq_hasSum b _).tsum_eq] using hB
  have hswap : Summable (fun i => ∑' j, ‖inner ℝ (b i) (B (b j))‖ ^ 2) :=
    hall.prod_symm.prod
  apply hswap.congr
  intro i
  rw [← (realHilbertBasis_norm_sq_hasSum b (B.adjoint (b i))).tsum_eq]
  apply tsum_congr
  intro j
  rw [B.adjoint_inner_right, norm_inner_symm]

noncomputable def realHSFactorDet
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : ℝ := realNuclearDet (fun i => B.adjoint (b i)) (fun i => A (b i)) z

theorem realHSFactorDet_entire
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : AnalyticOnNhd ℝ (realHSFactorDet b A B) Set.univ :=
  realNuclearDet_entire _ _ (realHs_vectors_nuclear_mass _ _
    (realHs_adjoint_square_summable b B hB) hA)

theorem realHsFactor_nuclearOperator_eq_comp
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : realNuclearOperator (fun i => B.adjoint (b i)) (fun i => A (b i)) = A ∘L B := by
  have huv := realHs_vectors_nuclear_mass (fun i => B.adjoint (b i)) (fun i => A (b i))
    (realHs_adjoint_square_summable b B hB) hA
  ext x
  have hleft := (realNuclearOperator_hasSum _ _ huv).mapL (ContinuousLinearMap.apply ℝ E x)
  have hright := (b.hasSum_repr (B x)).mapL A
  apply hleft.unique
  simpa only [rankOne_apply, ContinuousLinearMap.apply_apply, map_smul,
    b.repr_apply_apply, B.adjoint_inner_left, ContinuousLinearMap.comp_apply] using hright

theorem realMatrix_det_principal_minors
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (M : Matrix ι ι ℝ /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : Matrix.det (1 + z • M) = ∑ s ∈ Finset.univ.powerset,
      Matrix.det (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) * z ^ s.card := by
  classical
  have hp : Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C) =
      ∑ s ∈ Finset.univ.powerset,
        Polynomial.C (Matrix.det (M.submatrix (Subtype.val : s → ι)
          (Subtype.val : s → ι))) * Polynomial.X ^ s.card := by
    apply Polynomial.ext
    intro k
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]
  have he := congrArg (Polynomial.evalRingHom z) hp
  rw [RingHom.map_det] at he
  have hmap : (Polynomial.evalRingHom z).mapMatrix
      (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C) = 1 + z • M := by
    ext i j
    change Polynomial.eval z ((if i = j then 1 else 0) +
      Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + z * M i j
    by_cases hij : i = j <;>
      simp only [hij, if_true, if_false, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X, Polynomial.eval_C]
  rw [hmap] at he
  simpa only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X] using he

theorem realNuclearMinor_subtype_map
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    (t : Finset s /- [definition] -/ )
    : realNuclearMinor u v (t.map (Function.Embedding.subtype (· ∈ s))) =
      Matrix.det (fun i j : t => inner ℝ (u (i : s)) (v (j : s))) := by
  classical
  let emb : s ↪ ι := Function.Embedding.subtype (· ∈ s)
  let f : t → (t.map emb) := fun i => ⟨(i : s), Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun k : t.map emb => (k : ι)) hij
    · intro j
      obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.property
      refine ⟨⟨i, hi⟩, ?_⟩
      exact Subtype.ext hij
  let e : t ≃ (t.map emb) := Equiv.ofBijective f hf
  exact (Matrix.det_submatrix_equiv_self e
    (fun i j : t.map emb => inner ℝ (u i) (v j))).symm

theorem realNuclearTruncation_eq_matrix_det
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : (∑ t ∈ s.powerset, realNuclearMinor u v t * z ^ t.card) =
      Matrix.det ((1 : Matrix s s ℝ) + z • Matrix.of (fun i j : s => inner ℝ (u i) (v j))) := by
  classical
  let M : Matrix s s ℝ := fun i j => inner ℝ (u i) (v j)
  change (∑ t ∈ s.powerset, realNuclearMinor u v t * z ^ t.card) = Matrix.det ((1 : Matrix s s ℝ) + z • M)
  rw [realMatrix_det_principal_minors M z]
  symm
  apply Finset.sum_bij (fun t _ => t.map (Function.Embedding.subtype (· ∈ s)))
  · intro t ht
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact hji ▸ j.property
  · intro t ht t' ht' h
    exact Finset.map_injective _ h
  · intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    refine ⟨t.subtype (· ∈ s), Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    ext i
    simp only [Finset.mem_map, Finset.mem_subtype]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact hji ▸ hj
    · intro hi
      exact ⟨⟨i, hts hi⟩, hi, rfl⟩
  · intro t ht
    rw [realNuclearMinor_subtype_map, Finset.card_map]
    rfl

theorem realNuclearTruncation_matrix_det_tendsto
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ι → E /- [definition] -/ )
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Tendsto (fun s : Finset ι => Matrix.det
        ((1 : Matrix s s ℝ) + z • Matrix.of (fun i j : s => inner ℝ (u i) (v j))))
      atTop (𝓝 (realNuclearDet u v z)) := by
  have h := (realNuclearDet_hasSum u v huv z).comp tendsto_finset_powerset_atTop_atTop
  simpa only [Function.comp_def, realNuclearTruncation_eq_matrix_det] using h

theorem realHsFactor_joint_probe
    : ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∃ A B : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2) ∧
      ‖A (b 0)‖ = 2 ∧ ‖B (b 0)‖ = 1 ∧
      AnalyticOnNhd ℝ (realHSFactorDet b A B) Set.univ ∧
      realNuclearOperator (fun i => B.adjoint (b i)) (fun i => A (b i)) = A ∘L B := by
  let b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  let B := rankOne ℝ (b 0) (b 0)
  let A := (2 : ℝ) • B
  have hB : Summable (fun i => ‖B (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  have hA : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [A, B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  refine ⟨b, A, B, hA, hB, ?_, ?_, realHSFactorDet_entire b A B hA hB,
    realHsFactor_nuclearOperator_eq_comp b A B hA hB⟩
  · simp [A, B, rankOne_apply, norm_smul, orthonormal_iff_ite.mp b.orthonormal,
      b.orthonormal.norm_eq_one 0]
  · simp [B, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal,
      b.orthonormal.norm_eq_one 0]

theorem realHSFactorDet_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun s : Finset ι => ‖realNuclearMinor (fun i => B.adjoint (b i))
        (fun i => A (b i)) s * z ^ s.card‖) :=
  realNuclearDet_absolute _ _ (realHs_vectors_nuclear_mass _ _ (realHs_adjoint_square_summable b B hB) hA) z

noncomputable def realOperatorDet
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : ℝ := realNuclearDet b (fun i => T (b i)) z

theorem realOperatorMinor_factorization
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    : realNuclearMinor b (fun i => (A ∘L B) (b i)) s =
      realNuclearMinor (fun i => A.adjoint (b i)) (fun i => B (b i)) s := by
  unfold realNuclearMinor
  apply congrArg Matrix.det
  funext i j
  exact (A.adjoint_inner_left (B (b j)) (b i)).symm

theorem realOperatorDet_eq_hsFactorDet
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b (A ∘L B) z = realHSFactorDet b B A z := by
  unfold realOperatorDet realHSFactorDet realNuclearDet
  apply tsum_congr
  intro s
  rw [realOperatorMinor_factorization]

theorem realOperatorDet_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun s : Finset ι => ‖realNuclearMinor b (fun i => T (b i)) s * z ^ s.card‖) := by
  obtain ⟨A, B, rfl, hA, hB⟩ := hT
  simpa only [realOperatorMinor_factorization] using realHSFactorDet_absolute b B A hB hA z

theorem realOperatorDet_entire
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : AnalyticOnNhd ℝ (realOperatorDet b T) Set.univ := by
  obtain ⟨A, B, rfl, hA, hB⟩ := hT
  have heq : realOperatorDet b (A ∘L B) = realHSFactorDet b B A :=
    funext (realOperatorDet_eq_hsFactorDet b A B)
  rw [heq]
  exact realHSFactorDet_entire b B A hB hA

theorem realHSFactorDet_factorization_independent
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B C D : E →L[ℝ] E /- [definition] -/ )
    (hprod : A ∘L B = C ∘L D /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : realHSFactorDet b B A z = realHSFactorDet b D C z := by
  rw [← realOperatorDet_eq_hsFactorDet, ← realOperatorDet_eq_hsFactorDet, hprod]

theorem realNuclearDet_dominated_tendsto
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (u v : ℕ → ι → E /- [definition] -/ )
    (u₀ v₀ : ι → E /- [definition] -/ )
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (u₀ i))  /- [standing] -/ )
    (hv : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (v₀ i))  /- [standing] -/ )
    (w : ι → ℝ /- [definition] -/ )
    (hw : ∀ i, 0 ≤ w i /- [standing] -/ )
    (hsum : Summable w /- [standing] -/ )
    (hbound : ∀ n i, ‖u n i‖ * ‖v n i‖ ≤ w i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Tendsto (fun n => realNuclearDet (u n) (v n) z) atTop (𝓝 (realNuclearDet u₀ v₀ z)) := by
  have hmajor := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (hw i)) (hsum.mul_left ‖z‖)
  apply tendsto_tsum_of_dominated_convergence hmajor
  · intro s
    have hmat : Tendsto (fun n => (fun i j : s => inner ℝ (u n i) (v n j)))
        atTop (𝓝 (fun i j : s => inner ℝ (u₀ i) (v₀ j))) :=
      tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => (hu i).inner (hv j)))
    have hdet : Continuous (Matrix.det : Matrix s s ℝ → ℝ) := continuous_id.matrix_det
    exact (hdet.tendsto _ |>.comp hmat).mul_const _
  · apply Eventually.of_forall
    intro n s
    change ‖realNuclearMinor (u n) (v n) s * z ^ s.card‖ ≤ ∏ i ∈ s, (‖z‖ * w i)
    rw [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const]
    have hp : ‖realNuclearMinor (u n) (v n) s‖ ≤ ∏ i ∈ s, w i := by
      apply (realNuclearMinor_bound (u n) (v n) s).trans
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hbound n i)
    exact (mul_le_mul_of_nonneg_right hp (pow_nonneg (norm_nonneg z) s.card)).trans_eq
      (mul_comm _ _)

theorem realNuclearDet_l2_continuous
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (z : ℝ /- [definition] -/ )
    : Continuous (fun p : lp (fun _ : ι => E) 2 × lp (fun _ : ι => E) 2 =>
      realNuclearDet p.1 p.2 z) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro a ha
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have han := ha.comp hns
  obtain ⟨ms, hms, hclose⟩ := han.subseq_mem
    (V := fun n => Metric.ball p ((1 / (2 : ℝ)) ^ n))
    (fun n => Metric.ball_mem_nhds _ (by positivity))
  have hsum : Summable (fun n => ‖a (ns (ms n)) - p‖) := by
    apply summable_geometric_two.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    simpa only [dist_eq_norm, Function.comp_apply] using (Metric.mem_ball.mp (hclose n)).le
  have hu : Summable (fun n => ‖(a (ns (ms n))).1 - p.1‖) := by
    apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    exact norm_fst_le (a (ns (ms n)) - p)
  have hv : Summable (fun n => ‖(a (ns (ms n))).2 - p.2‖) := by
    apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    exact norm_snd_le (a (ns (ms n)) - p)
  obtain ⟨wu, hwu, hbu⟩ := realL2_summable_distance_envelope
    (fun n => (a (ns (ms n))).1) p.1 hu
  obtain ⟨wv, hwv, hbv⟩ := realL2_summable_distance_envelope
    (fun n => (a (ns (ms n))).2) p.2 hv
  have hwu2 : Summable (fun i => ‖wu i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) wu).summable
  have hwv2 : Summable (fun i => ‖wv i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) wv).summable
  have hwprod : Summable (fun i => wu i * wv i) := by
    apply ((hwu2.add hwv2).div_const 2).of_nonneg_of_le
      (fun i => mul_nonneg (hwu i) (hwv i))
    intro i
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (wu i - wv i)]
  have hall := han.comp hms.tendsto_atTop
  refine ⟨ms, realNuclearDet_dominated_tendsto
    (fun n i => (a (ns (ms n))).1 i) (fun n i => (a (ns (ms n))).2 i)
    p.1 p.2 ?_ ?_ (fun i => wu i * wv i) (fun i => mul_nonneg (hwu i) (hwv i))
    hwprod (fun n i => mul_le_mul (hbu n i) (hbv n i) (norm_nonneg _) (hwu i)) z⟩
  · intro i
    exact ((lp.evalCLM ℝ (fun _ : ι => E) 2 i).continuous.comp continuous_fst).tendsto p
      |>.comp hall
  · intro i
    exact ((lp.evalCLM ℝ (fun _ : ι => E) 2 i).continuous.comp continuous_snd).tendsto p
      |>.comp hall

noncomputable def realHsColumns
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : lp (fun _ : ι => E) 2 :=
  ⟨fun i => A (b i), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hA)⟩

theorem realHsColumns_norm_sq
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : ‖realHsColumns b A hA‖ ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, realHsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (realHsColumns b A hA)).tsum_eq.symm

theorem realHs_adjoint_square_tsum_eq
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : (∑' i, ‖A.adjoint (b i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  have hall : Summable (fun p : ι × ι => ‖inner ℝ (b p.2) (A (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (realHilbertBasis_norm_sq_hasSum b (A (b i))).summable, ?_⟩
    simpa only [(realHilbertBasis_norm_sq_hasSum b _).tsum_eq] using hA
  calc
    (∑' i, ‖A.adjoint (b i)‖ ^ 2) =
        ∑' i, ∑' j, ‖inner ℝ (b i) (A (b j))‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [← (realHilbertBasis_norm_sq_hasSum b (A.adjoint (b i))).tsum_eq]
      apply tsum_congr
      intro j
      rw [A.adjoint_inner_right, norm_inner_symm]
    _ = ∑' j, ∑' i, ‖inner ℝ (b i) (A (b j))‖ ^ 2 := hall.tsum_comm
    _ = ∑' i, ‖A (b i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact (realHilbertBasis_norm_sq_hasSum b (A (b i))).tsum_eq

theorem realHsColumns_difference_norm_sq
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : ‖realHsColumns b A hA - realHsColumns b B hB‖ ^ 2 =
      ∑' i, ‖(A - B) (b i)‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, realHsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      (realHsColumns b A hA - realHsColumns b B hB)).tsum_eq.symm

theorem realHs_square_summable_sub
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖(A - B) (b i)‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, realHsColumns, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      (realHsColumns b A hA - realHsColumns b B hB)).summable

theorem realHsColumns_tendsto_of_square
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : X → E →L[ℝ] E /- [definition] -/ )
    (A₀ : E →L[ℝ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconv : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    : Tendsto (fun x => realHsColumns b (A x) (hA x)) l (𝓝 (realHsColumns b A₀ hA₀)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have heq (x : X) : Real.sqrt (∑' i, ‖(A x - A₀) (b i)‖ ^ 2) =
      ‖realHsColumns b (A x) (hA x) - realHsColumns b A₀ hA₀‖ := by
    rw [← realHsColumns_difference_norm_sq b (A x) A₀ (hA x) hA₀]
    exact Real.sqrt_sq (norm_nonneg _)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, heq, Real.sqrt_zero, dist_eq_norm] using hs

theorem realHsColumns_adjoint_tendsto_of_square
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : X → E →L[ℝ] E /- [definition] -/ )
    (A₀ : E →L[ℝ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconv : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    : Tendsto (fun x => realHsColumns b (A x).adjoint (realHs_adjoint_square_summable b _ (hA x)))
      l (𝓝 (realHsColumns b A₀.adjoint (realHs_adjoint_square_summable b _ hA₀))) := by
  apply realHsColumns_tendsto_of_square b (fun x => (A x).adjoint) A₀.adjoint
    (fun x => realHs_adjoint_square_summable b _ (hA x)) (realHs_adjoint_square_summable b _ hA₀) l
  convert hconv using 1
  congr 1
  ext x
  rw [← ContinuousLinearMap.adjoint.map_sub]
  exact realHs_adjoint_square_tsum_eq b (A x - A₀) (realHs_square_summable_sub b _ _ (hA x) hA₀)

theorem realHSFactorDet_tendsto_of_hs
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : X → E →L[ℝ] E /- [definition] -/ )
    (A₀ B₀ : E →L[ℝ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (hB₀ : Summable (fun i => ‖B₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconvA : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (hconvB : Tendsto (fun x => ∑' i, ‖(B x - B₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Tendsto (fun x => realHSFactorDet b (A x) (B x) z) l (𝓝 (realHSFactorDet b A₀ B₀ z)) := by
  have hp := (realHsColumns_adjoint_tendsto_of_square b B B₀ hB hB₀ l hconvB).prodMk_nhds
    (realHsColumns_tendsto_of_square b A A₀ hA hA₀ l hconvA)
  have h := (realNuclearDet_l2_continuous (E := E) z).tendsto
    (realHsColumns b B₀.adjoint (realHs_adjoint_square_summable b _ hB₀), realHsColumns b A₀ hA₀)
    |>.comp hp
  simpa only [Function.comp_def, realHsColumns, realHSFactorDet] using h

theorem realOperatorDet_comp_tendsto_of_hs
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : X → E →L[ℝ] E /- [definition] -/ )
    (A₀ B₀ : E →L[ℝ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hA₀ : Summable (fun i => ‖A₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (hB₀ : Summable (fun i => ‖B₀ (b i)‖ ^ 2)  /- [standing] -/ )
    (l : Filter X /- [definition] -/ )
    (hconvA : Tendsto (fun x => ∑' i, ‖(A x - A₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (hconvB : Tendsto (fun x => ∑' i, ‖(B x - B₀) (b i)‖ ^ 2) l (𝓝 0)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Tendsto (fun x => realOperatorDet b (A x ∘L B x) z) l (𝓝 (realOperatorDet b (A₀ ∘L B₀) z)) := by
  simpa only [realOperatorDet_eq_hsFactorDet] using
    realHSFactorDet_tendsto_of_hs b B A B₀ A₀ hB hA hB₀ hA₀ l hconvB hconvA z



/-- Continuous families of HS factors give continuous Fredholm determinants.
Each square-distance premise is the genuine HS-norm convergence at that point. -/
theorem realOperatorDet_comp_family_continuous
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    [TopologicalSpace X /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : X → E →L[ℝ] E /- [definition] -/ )
    (hA : ∀ x, Summable (fun i => ‖A x (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : ∀ x, Summable (fun i => ‖B x (b i)‖ ^ 2)  /- [standing] -/ )
    (hconvA : ∀ t, Tendsto (fun x => ∑' i, ‖(A x - A t) (b i)‖ ^ 2)
      (𝓝 t) (𝓝 0)  /- [standing] -/ )
    (hconvB : ∀ t, Tendsto (fun x => ∑' i, ‖(B x - B t) (b i)‖ ^ 2)
      (𝓝 t) (𝓝 0)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Continuous (fun x => realOperatorDet b (A x ∘L B x) z) :=
  continuous_iff_continuousAt.mpr (fun t =>
    realOperatorDet_comp_tendsto_of_hs b A B (A t) (B t) hA hB (hA t) (hB t)
      (𝓝 t) (hconvA t) (hconvB t) z)



/-- All HS continuity binders are jointly inhabited on infinite-dimensional l2,
with a norm-two factor and a norm-one factor. No event or coefficient premise is used. -/
theorem realHs_continuity_joint_probe
    : ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∃ A B : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2) ∧
      ‖A (b 0)‖ = 2 ∧ ‖B (b 0)‖ = 1 ∧
      (Tendsto (fun _ : ℝ => ∑' i, ‖(A - A) (b i)‖ ^ 2) (𝓝 0) (𝓝 0)) ∧
      (Tendsto (fun _ : ℝ => ∑' i, ‖(B - B) (b i)‖ ^ 2) (𝓝 0) (𝓝 0)) ∧
      ∀ z, Tendsto (fun _ : ℝ => realOperatorDet b (A ∘L B) z)
        (𝓝 0) (𝓝 (realOperatorDet b (A ∘L B) z)) := by
  obtain ⟨b, A, B, hA, hB, hAn, hBn, _⟩ := realHsFactor_joint_probe
  have hconvA : Tendsto (fun _ : ℝ => ∑' i, ‖(A - A) (b i)‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  have hconvB : Tendsto (fun _ : ℝ => ∑' i, ‖(B - B) (b i)‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  refine ⟨b, A, B, hA, hB, hAn, hBn, hconvA, hconvB, ?_⟩
  intro z
  exact realOperatorDet_comp_tendsto_of_hs b (fun _ : ℝ => A) (fun _ : ℝ => B) A B
    (fun _ => hA) (fun _ => hB) hA hB (𝓝 0) hconvA hconvB z



theorem realOperatorDet_matrix_det_tendsto
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Tendsto (fun s : Finset ι => Matrix.det ((1 : Matrix s s ℝ) +
        z • Matrix.of (fun i j : s => inner ℝ (b i) (T (b j)))))
      atTop (𝓝 (realOperatorDet b T z)) := by
  have h := (realOperatorDet_absolute b T hT z).of_norm.hasSum.comp
    tendsto_finset_powerset_atTop_atTop
  simpa only [Function.comp_def, realNuclearTruncation_eq_matrix_det, realOperatorDet,
    realNuclearDet] using h





/-- Parseval and Tonelli identify the two square sums even across different bases. -/
theorem hs_adjoint_other_basis
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖A.adjoint (c i)‖ ^ 2) ∧
      (∑' i, ‖A.adjoint (c i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  have hall : Summable (fun p : ℕ × ℕ => ‖inner ℂ (c p.2) (A (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (hilbertBasis_norm_sq_hasSum c (A (b i))).summable, ?_⟩
    simpa only [(hilbertBasis_norm_sq_hasSum c _).tsum_eq] using hA
  have heq (i : ℕ) :
      (∑' j, ‖inner ℂ (c i) (A (b j))‖ ^ 2) = ‖A.adjoint (c i)‖ ^ 2 := by
    rw [← (hilbertBasis_norm_sq_hasSum b (A.adjoint (c i))).tsum_eq]
    apply tsum_congr
    intro j
    rw [A.adjoint_inner_right, norm_inner_symm]
  refine ⟨?_, ?_⟩
  · have hswap : Summable (fun i => ∑' j, ‖inner ℂ (c i) (A (b j))‖ ^ 2) :=
      hall.prod_symm.prod
    exact hswap.congr heq
  · calc
      (∑' i, ‖A.adjoint (c i)‖ ^ 2) =
          ∑' i, ∑' j, ‖inner ℂ (c i) (A (b j))‖ ^ 2 := by simp only [heq]
      _ = ∑' j, ∑' i, ‖inner ℂ (c i) (A (b j))‖ ^ 2 := hall.tsum_comm
      _ = ∑' j, ‖A (b j)‖ ^ 2 := by
        apply tsum_congr
        intro j
        exact (hilbertBasis_norm_sq_hasSum c (A (b j))).tsum_eq

/-- Genuine HS membership is unchanged by choosing a different Hilbert basis. -/
theorem hs_square_summable_basis
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖A (c i)‖ ^ 2) := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    hs_adjoint_square_summable c A.adjoint (hs_adjoint_other_basis b c A hA).1

/-- The HS norm computed from columns is basis independent. -/
theorem hs_square_tsum_basis_eq
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : (∑' i, ‖A (c i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 :=
  (hs_adjoint_square_tsum_eq c A (hs_square_summable_basis b c A hA)).symm.trans
    (hs_adjoint_other_basis b c A hA).2

/-- Finite orthogonal projection, written as an actual sum of rank-one operators. -/
noncomputable def basisProjection
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : E →L[ℂ] E := ∑ i ∈ s, rankOne ℂ (b i) (b i)

/-- The finite projection retains exactly its selected basis columns. -/
theorem basisProjection_apply_basis
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    (j : ℕ /- [definition] -/ )
    : basisProjection b s (b j) = if j ∈ s then b j else 0 := by
  classical
  simp [basisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
    orthonormal_iff_ite.mp b.orthonormal]

/-- Strong convergence of the finite basis projections to the identity. -/
theorem basisProjection_tendsto
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (x : E /- [definition] -/ )
    : Tendsto (fun s : Finset ℕ => basisProjection b s x) atTop (𝓝 x) := by
  simpa only [basisProjection, ContinuousLinearMap.sum_apply, rankOne_apply, HasSum, SummationFilter.unconditional, HilbertBasis.repr_apply_apply]
    using b.hasSum_repr x


/-- A right finite-basis compression is Hilbert--Schmidt. -/
theorem basisProjection_comp_hs
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : Summable (fun i => ‖(A ∘L basisProjection b s) (b i)‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := s)
  intro i hi
  simp [ContinuousLinearMap.comp_apply, basisProjection_apply_basis, hi]

/-- The genuine HS square-distance of a finite right compression is the omitted tail. -/
theorem basisProjection_comp_square_distance
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (s : Finset ℕ /- [definition] -/ )
    : (∑' i, ‖(A ∘L basisProjection b s - A) (b i)‖ ^ 2) =
      (∑' i, ‖A (b i)‖ ^ 2) - ∑ i ∈ s, ‖A (b i)‖ ^ 2 := by
  classical
  let f : ℕ → ℝ := fun i => ‖A (b i)‖ ^ 2
  let g : ℕ → ℝ := fun i => if i ∈ s then f i else 0
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := s)
    intro i hi
    simp [g, hi]
  have hterm : (fun i => ‖(A ∘L basisProjection b s - A) (b i)‖ ^ 2) =
      fun i => f i - g i := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [g, f, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        basisProjection_apply_basis, hi]
  have hgsum : (∑' i, g i) = ∑ i ∈ s, f i := by
    rw [tsum_eq_sum (s := s) (f := g)]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [g, hi]
    · intro i hi
      simp [g, hi]
  rw [hterm, hA.tsum_sub hg, hgsum]

/-- Finite right compressions converge in the genuine HS norm of any selected basis. -/
theorem basisProjection_comp_hs_tendsto
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Tendsto (fun s : Finset ℕ => ∑' i, ‖(A ∘L basisProjection c s - A) (b i)‖ ^ 2)
      atTop (𝓝 0) := by
  have hAc := hs_square_summable_basis b c A hA
  have heq (s : Finset ℕ) :
      (∑' i, ‖(A ∘L basisProjection c s - A) (b i)‖ ^ 2) =
        (∑' i, ‖A (c i)‖ ^ 2) - ∑ i ∈ s, ‖A (c i)‖ ^ 2 := by
    rw [hs_square_tsum_basis_eq c b _ (hs_square_summable_sub c _ _
      (basisProjection_comp_hs c A s) hAc), basisProjection_comp_square_distance c A hAc s]
  simpa only [heq, sub_self] using
    (tendsto_const_nhds.sub hAc.hasSum :
      Tendsto (fun s : Finset ℕ => (∑' i, ‖A (c i)‖ ^ 2) - ∑ i ∈ s, ‖A (c i)‖ ^ 2)
        atTop (𝓝 ((∑' i, ‖A (c i)‖ ^ 2) - ∑' i, ‖A (c i)‖ ^ 2)))


/-- Rectangular Sylvester identity for two actual finite Hilbert-basis compressions. -/
theorem basisProjection_finite_sylvester
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (s t : Finset ℕ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : Matrix.det ((1 : Matrix s s ℂ) + z • Matrix.of (fun i j : s =>
        inner ℂ (b i) ((A ∘L basisProjection c t ∘L B) (b j)))) =
      Matrix.det ((1 : Matrix t t ℂ) + z • Matrix.of (fun i j : t =>
        inner ℂ (c i) ((B ∘L basisProjection b s ∘L A) (c j)))) := by
  classical
  let M : Matrix s t ℂ := fun i j => inner ℂ (b i) (A (c j))
  let N : Matrix t s ℂ := fun i j => inner ℂ (c i) (B (b j))
  have hMN : Matrix.of (fun i j : s =>
      inner ℂ (b i) ((A ∘L basisProjection c t ∘L B) (b j))) = M * N := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, M, N, ContinuousLinearMap.comp_apply,
      basisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
      map_sum, map_smul, inner_sum, inner_smul_right]
    rw [← Finset.sum_coe_sort t]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  have hNM : Matrix.of (fun i j : t =>
      inner ℂ (c i) ((B ∘L basisProjection b s ∘L A) (c j))) = N * M := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, M, N, ContinuousLinearMap.comp_apply,
      basisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
      map_sum, map_smul, inner_sum, inner_smul_right]
    rw [← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hMN, hNM]
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using
    Matrix.det_one_add_mul_comm (z • M) N


/-- The determinant of an actual finite-rank factorization is a finite Gram determinant.
No assumption that its range is spanned by the chosen basis is made. -/
theorem operatorDet_finite_projection
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (t : Finset ℕ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b (A ∘L basisProjection c t ∘L B) z =
      Matrix.det ((1 : Matrix t t ℂ) + z • Matrix.of (fun i j : t =>
        inner ℂ (c i) ((B ∘L A) (c j)))) := by
  classical
  have hAP := hs_square_summable_basis c b (A ∘L basisProjection c t)
    (basisProjection_comp_hs c A t)
  have hT : ∃ U V : E →L[ℂ] E, A ∘L basisProjection c t ∘L B = U ∘L V ∧
      Summable (fun i => ‖U (b i)‖ ^ 2) ∧ Summable (fun i => ‖V (b i)‖ ^ 2) :=
    ⟨A ∘L basisProjection c t, B, rfl, hAP, hB⟩
  have hleft := operatorDet_matrix_det_tendsto b _ hT z
  have hmat : Tendsto (fun s : Finset ℕ =>
      Matrix.of (fun i j : t => inner ℂ (c i) ((B ∘L basisProjection b s ∘L A) (c j))))
      atTop (𝓝 (Matrix.of (fun i j : t => inner ℂ (c i) ((B ∘L A) (c j))))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.inner
      (B.continuous.tendsto _ |>.comp (basisProjection_tendsto b (A (c j))))
  have hdet : Continuous (fun M : Matrix t t ℂ => Matrix.det ((1 : Matrix t t ℂ) + z • M)) :=
    by fun_prop
  have hright := (hdet.tendsto _).comp hmat
  have heq : (fun s : Finset ℕ => Matrix.det ((1 : Matrix s s ℂ) + z •
      Matrix.of (fun i j : s => inner ℂ (b i) ((A ∘L basisProjection c t ∘L B) (b j))))) =
      (fun s : Finset ℕ => Matrix.det ((1 : Matrix t t ℂ) + z •
        Matrix.of (fun i j : t => inner ℂ (c i) ((B ∘L basisProjection b s ∘L A) (c j))))) :=
    funext (fun s => basisProjection_finite_sylvester b c A B s t z)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Sylvester's identity across two arbitrary Hilbert bases for genuine HS factors.
Taking equal bases gives the usual operator Sylvester identity. -/
theorem operatorDet_sylvester_bases
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b (A ∘L B) z = operatorDet c (B ∘L A) z := by
  have hAc := hs_square_summable_basis b c A hA
  have hBc := hs_square_summable_basis b c B hB
  have hT : ∃ U V : E →L[ℂ] E, B ∘L A = U ∘L V ∧
      Summable (fun i => ‖U (c i)‖ ^ 2) ∧ Summable (fun i => ‖V (c i)‖ ^ 2) :=
    ⟨B, A, rfl, hBc, hAc⟩
  have hleft := operatorDet_comp_tendsto_of_hs b
    (fun t : Finset ℕ => A ∘L basisProjection c t) (fun _ => B) A B
    (fun t => hs_square_summable_basis c b _ (basisProjection_comp_hs c A t))
    (fun _ => hB) hA hB atTop (basisProjection_comp_hs_tendsto b c A hA)
    (by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : Finset ℕ => (0 : ℝ)) atTop (𝓝 0))) z
  have hright := operatorDet_matrix_det_tendsto c _ hT z
  have heq : (fun t : Finset ℕ => operatorDet b (A ∘L basisProjection c t ∘L B) z) =
      (fun t : Finset ℕ => Matrix.det ((1 : Matrix t t ℂ) + z • Matrix.of
        (fun i j : t => inner ℂ (c i) ((B ∘L A) (c j))))) :=
    funext (fun t => operatorDet_finite_projection b c A B hB t z)
  simp only [ContinuousLinearMap.comp_assoc] at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The operator determinant is basis independent for every actual HS-factorized trace-class operator. -/
theorem operatorDet_basis_independent
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (A B : E →L[ℂ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b (A ∘L B) z = operatorDet c (A ∘L B) z :=
  (operatorDet_sylvester_bases b c A B hA hB z).trans
    (operatorDet_sylvester_bases c c B A (hs_square_summable_basis b c B hB)
      (hs_square_summable_basis b c A hA) z)




/-- Parseval and Tonelli identify the two square sums even across different bases. -/
theorem realHs_adjoint_other_basis
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖A.adjoint (c i)‖ ^ 2) ∧
      (∑' i, ‖A.adjoint (c i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  have hall : Summable (fun p : ι × ι => ‖inner ℝ (c p.2) (A (b p.1))‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun i => (realHilbertBasis_norm_sq_hasSum c (A (b i))).summable, ?_⟩
    simpa only [(realHilbertBasis_norm_sq_hasSum c _).tsum_eq] using hA
  have heq (i : ι) :
      (∑' j, ‖inner ℝ (c i) (A (b j))‖ ^ 2) = ‖A.adjoint (c i)‖ ^ 2 := by
    rw [← (realHilbertBasis_norm_sq_hasSum b (A.adjoint (c i))).tsum_eq]
    apply tsum_congr
    intro j
    rw [A.adjoint_inner_right, norm_inner_symm]
  refine ⟨?_, ?_⟩
  · have hswap : Summable (fun i => ∑' j, ‖inner ℝ (c i) (A (b j))‖ ^ 2) :=
      hall.prod_symm.prod
    exact hswap.congr heq
  · calc
      (∑' i, ‖A.adjoint (c i)‖ ^ 2) =
          ∑' i, ∑' j, ‖inner ℝ (c i) (A (b j))‖ ^ 2 := by simp only [heq]
      _ = ∑' j, ∑' i, ‖inner ℝ (c i) (A (b j))‖ ^ 2 := hall.tsum_comm
      _ = ∑' j, ‖A (b j)‖ ^ 2 := by
        apply tsum_congr
        intro j
        exact (realHilbertBasis_norm_sq_hasSum c (A (b j))).tsum_eq

/-- Genuine HS membership is unchanged by choosing a different Hilbert basis. -/
theorem realHs_square_summable_basis
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Summable (fun i => ‖A (c i)‖ ^ 2) := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    realHs_adjoint_square_summable c A.adjoint (realHs_adjoint_other_basis b c A hA).1

/-- The HS norm computed from columns is basis independent. -/
theorem realHs_square_tsum_basis_eq
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : (∑' i, ‖A (c i)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 :=
  (realHs_adjoint_square_tsum_eq c A (realHs_square_summable_basis b c A hA)).symm.trans
    (realHs_adjoint_other_basis b c A hA).2

/-- Finite orthogonal projection, written as an actual sum of rank-one operators. -/
noncomputable def realBasisProjection
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    : E →L[ℝ] E := ∑ i ∈ s, rankOne ℝ (b i) (b i)

/-- The finite projection retains exactly its selected basis columns. -/
theorem realBasisProjection_apply_basis
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    (j : ι /- [definition] -/ )
    : realBasisProjection b s (b j) = if j ∈ s then b j else 0 := by
  classical
  simp [realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
    orthonormal_iff_ite.mp b.orthonormal]

/-- Strong convergence of the finite basis projections to the identity. -/
theorem realBasisProjection_tendsto
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (x : E /- [definition] -/ )
    : Tendsto (fun s : Finset ι => realBasisProjection b s x) atTop (𝓝 x) := by
  simpa only [realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply, HasSum, SummationFilter.unconditional, HilbertBasis.repr_apply_apply]
    using b.hasSum_repr x


/-- A right finite-basis compression is Hilbert--Schmidt. -/
theorem realBasisProjection_comp_hs
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    : Summable (fun i => ‖(A ∘L realBasisProjection b s) (b i)‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := s)
  intro i hi
  simp [ContinuousLinearMap.comp_apply, realBasisProjection_apply_basis, hi]

/-- The genuine HS square-distance of a finite right compression is the omitted tail. -/
theorem realBasisProjection_comp_square_distance
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (s : Finset ι /- [definition] -/ )
    : (∑' i, ‖(A ∘L realBasisProjection b s - A) (b i)‖ ^ 2) =
      (∑' i, ‖A (b i)‖ ^ 2) - ∑ i ∈ s, ‖A (b i)‖ ^ 2 := by
  classical
  let f : ι → ℝ := fun i => ‖A (b i)‖ ^ 2
  let g : ι → ℝ := fun i => if i ∈ s then f i else 0
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := s)
    intro i hi
    simp [g, hi]
  have hterm : (fun i => ‖(A ∘L realBasisProjection b s - A) (b i)‖ ^ 2) =
      fun i => f i - g i := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [g, f, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        realBasisProjection_apply_basis, hi]
  have hgsum : (∑' i, g i) = ∑ i ∈ s, f i := by
    rw [tsum_eq_sum (s := s) (f := g)]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [g, hi]
    · intro i hi
      simp [g, hi]
  rw [hterm, hA.tsum_sub hg, hgsum]

/-- Finite right compressions converge in the genuine HS norm of any selected basis. -/
theorem realBasisProjection_comp_hs_tendsto
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    : Tendsto (fun s : Finset ι => ∑' i, ‖(A ∘L realBasisProjection c s - A) (b i)‖ ^ 2)
      atTop (𝓝 0) := by
  have hAc := realHs_square_summable_basis b c A hA
  have heq (s : Finset ι) :
      (∑' i, ‖(A ∘L realBasisProjection c s - A) (b i)‖ ^ 2) =
        (∑' i, ‖A (c i)‖ ^ 2) - ∑ i ∈ s, ‖A (c i)‖ ^ 2 := by
    rw [realHs_square_tsum_basis_eq c b _ (realHs_square_summable_sub c _ _
      (realBasisProjection_comp_hs c A s) hAc), realBasisProjection_comp_square_distance c A hAc s]
  simpa only [heq, sub_self] using
    (tendsto_const_nhds.sub hAc.hasSum :
      Tendsto (fun s : Finset ι => (∑' i, ‖A (c i)‖ ^ 2) - ∑ i ∈ s, ‖A (c i)‖ ^ 2)
        atTop (𝓝 ((∑' i, ‖A (c i)‖ ^ 2) - ∑' i, ‖A (c i)‖ ^ 2)))


/-- Rectangular Sylvester identity for two actual finite Hilbert-basis compressions. -/
theorem realBasisProjection_finite_sylvester
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (s t : Finset ι /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : Matrix.det ((1 : Matrix s s ℝ) + z • Matrix.of (fun i j : s =>
        inner ℝ (b i) ((A ∘L realBasisProjection c t ∘L B) (b j)))) =
      Matrix.det ((1 : Matrix t t ℝ) + z • Matrix.of (fun i j : t =>
        inner ℝ (c i) ((B ∘L realBasisProjection b s ∘L A) (c j)))) := by
  classical
  let M : Matrix s t ℝ := fun i j => inner ℝ (b i) (A (c j))
  let N : Matrix t s ℝ := fun i j => inner ℝ (c i) (B (b j))
  have hMN : Matrix.of (fun i j : s =>
      inner ℝ (b i) ((A ∘L realBasisProjection c t ∘L B) (b j))) = M * N := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, M, N, ContinuousLinearMap.comp_apply,
      realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
      map_sum, map_smul, inner_sum, inner_smul_right]
    rw [← Finset.sum_coe_sort t]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  have hNM : Matrix.of (fun i j : t =>
      inner ℝ (c i) ((B ∘L realBasisProjection b s ∘L A) (c j))) = N * M := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, M, N, ContinuousLinearMap.comp_apply,
      realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply,
      map_sum, map_smul, inner_sum, inner_smul_right]
    rw [← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hMN, hNM]
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using
    Matrix.det_one_add_mul_comm (z • M) N


/-- The determinant of an actual finite-rank factorization is a finite Gram determinant.
No assumption that its range is spanned by the chosen basis is made. -/
theorem realOperatorDet_finite_projection
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (t : Finset ι /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b (A ∘L realBasisProjection c t ∘L B) z =
      Matrix.det ((1 : Matrix t t ℝ) + z • Matrix.of (fun i j : t =>
        inner ℝ (c i) ((B ∘L A) (c j)))) := by
  classical
  have hAP := realHs_square_summable_basis c b (A ∘L realBasisProjection c t)
    (realBasisProjection_comp_hs c A t)
  have hT : ∃ U V : E →L[ℝ] E, A ∘L realBasisProjection c t ∘L B = U ∘L V ∧
      Summable (fun i => ‖U (b i)‖ ^ 2) ∧ Summable (fun i => ‖V (b i)‖ ^ 2) :=
    ⟨A ∘L realBasisProjection c t, B, rfl, hAP, hB⟩
  have hleft := realOperatorDet_matrix_det_tendsto b _ hT z
  have hmat : Tendsto (fun s : Finset ι =>
      Matrix.of (fun i j : t => inner ℝ (c i) ((B ∘L realBasisProjection b s ∘L A) (c j))))
      atTop (𝓝 (Matrix.of (fun i j : t => inner ℝ (c i) ((B ∘L A) (c j))))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.inner
      (B.continuous.tendsto _ |>.comp (realBasisProjection_tendsto b (A (c j))))
  have hdet : Continuous (fun M : Matrix t t ℝ => Matrix.det ((1 : Matrix t t ℝ) + z • M)) :=
    by fun_prop
  have hright := (hdet.tendsto _).comp hmat
  have heq : (fun s : Finset ι => Matrix.det ((1 : Matrix s s ℝ) + z •
      Matrix.of (fun i j : s => inner ℝ (b i) ((A ∘L realBasisProjection c t ∘L B) (b j))))) =
      (fun s : Finset ι => Matrix.det ((1 : Matrix t t ℝ) + z •
        Matrix.of (fun i j : t => inner ℝ (c i) ((B ∘L realBasisProjection b s ∘L A) (c j))))) :=
    funext (fun s => realBasisProjection_finite_sylvester b c A B s t z)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Sylvester's identity across two arbitrary Hilbert bases for genuine HS factors.
Taking equal bases gives the usual operator Sylvester identity. -/
theorem realOperatorDet_sylvester_bases
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b (A ∘L B) z = realOperatorDet c (B ∘L A) z := by
  have hAc := realHs_square_summable_basis b c A hA
  have hBc := realHs_square_summable_basis b c B hB
  have hT : ∃ U V : E →L[ℝ] E, B ∘L A = U ∘L V ∧
      Summable (fun i => ‖U (c i)‖ ^ 2) ∧ Summable (fun i => ‖V (c i)‖ ^ 2) :=
    ⟨B, A, rfl, hBc, hAc⟩
  have hleft := realOperatorDet_comp_tendsto_of_hs b
    (fun t : Finset ι => A ∘L realBasisProjection c t) (fun _ => B) A B
    (fun t => realHs_square_summable_basis c b _ (realBasisProjection_comp_hs c A t))
    (fun _ => hB) hA hB atTop (realBasisProjection_comp_hs_tendsto b c A hA)
    (by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : Finset ι => (0 : ℝ)) atTop (𝓝 0))) z
  have hright := realOperatorDet_matrix_det_tendsto c _ hT z
  have heq : (fun t : Finset ι => realOperatorDet b (A ∘L realBasisProjection c t ∘L B) z) =
      (fun t : Finset ι => Matrix.det ((1 : Matrix t t ℝ) + z • Matrix.of
        (fun i j : t => inner ℝ (c i) ((B ∘L A) (c j))))) :=
    funext (fun t => realOperatorDet_finite_projection b c A B hB t z)
  simp only [ContinuousLinearMap.comp_assoc] at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The operator determinant is basis independent for every actual HS-factorized trace-class operator. -/
theorem realOperatorDet_basis_independent
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b c : HilbertBasis ι ℝ E /- [definition] -/ )
    (A B : E →L[ℝ] E /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b (A ∘L B) z = realOperatorDet c (A ∘L B) z :=
  (realOperatorDet_sylvester_bases b c A B hA hB z).trans
    (realOperatorDet_sylvester_bases c c B A (realHs_square_summable_basis b c B hB)
      (realHs_square_summable_basis b c A hA) z)



open MeasureTheory

/-!
Actual Gram-kernel Fredholm integral coefficients. All bounds are proved from
measurability and integrable row-norm mass, with no assumed coefficient estimate.
Identification with the operator determinant requires a separate Andreief theorem.
-/

noncomputable def kernelGramMinor
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    : 𝕜 := Matrix.det (fun i j : Fin n => inner 𝕜 (r (x i)) (c (x j)))

theorem kernelGramMinor_bound
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    : ‖kernelGramMinor (𝕜 := 𝕜) r c n x‖ ≤ ∏ i, (‖r (x i)‖ * ‖c (x i)‖) := by
  have h := crossGram_det_bound (𝕜 := 𝕜)
    (fun i : Fin n => r (x i)) (fun i : Fin n => c (x i))
  simpa only [kernelGramMinor, Finset.prod_mul_distrib] using h

theorem kernelGramMinor_aestronglyMeasurable
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : AEStronglyMeasurable (kernelGramMinor (𝕜 := 𝕜) r c n)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm : AEMeasurable (fun x : Fin n → X =>
      fun i j : Fin n => inner 𝕜 (r (x i)) (c (x j)))
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply aemeasurable_pi_lambda
    intro i
    apply aemeasurable_pi_lambda
    intro j
    exact ((hr.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)).inner
      (hc.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ j))).aemeasurable
  exact (continuous_id.matrix_det : Continuous
    (Matrix.det : Matrix (Fin n) (Fin n) 𝕜 → 𝕜)).comp_aestronglyMeasurable
      hm.aestronglyMeasurable

theorem kernelGramMinor_integrable
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : Integrable (kernelGramMinor (𝕜 := 𝕜) r c n) (Measure.pi (fun _ : Fin n => μ)) :=
  (Integrable.fintype_prod (fun _ : Fin n => hm)).mono'
    (kernelGramMinor_aestronglyMeasurable (𝕜 := 𝕜) μ r c hr hc n)
    (Filter.Eventually.of_forall (kernelGramMinor_bound (𝕜 := 𝕜) r c n))

theorem kernelGramMinor_integral_bound
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : ‖∫ x : Fin n → X, kernelGramMinor (𝕜 := 𝕜) r c n x ∂(Measure.pi (fun _ => μ))‖ ≤
      (∫ x, ‖r x‖ * ‖c x‖ ∂μ) ^ n := by
  calc
    _ ≤ ∫ x : Fin n → X, ‖kernelGramMinor (𝕜 := 𝕜) r c n x‖ ∂(Measure.pi (fun _ => μ)) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Fin n → X, ∏ i, (‖r (x i)‖ * ‖c (x i)‖)
        ∂(Measure.pi (fun _ => μ)) := by
      exact integral_mono (kernelGramMinor_integrable (𝕜 := 𝕜) μ r c hr hc hm n).norm
        (Integrable.fintype_prod (fun _ : Fin n => hm)) (kernelGramMinor_bound (𝕜 := 𝕜) r c n)
    _ = _ := by simpa using
      (integral_fintype_prod_eq_pow (ι := Fin n) (fun x => ‖r x‖ * ‖c x‖))

noncomputable def kernelFredholmCoeff
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : 𝕜 := (∫ x : Fin n → X, kernelGramMinor (𝕜 := 𝕜) r c n x ∂(Measure.pi (fun _ => μ))) /
      (n.factorial : 𝕜)

theorem kernelFredholmCoeff_bound
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : ‖kernelFredholmCoeff (𝕜 := 𝕜) μ r c n‖ ≤
      (∫ x, ‖r x‖ * ‖c x‖ ∂μ) ^ n / (n.factorial : ℝ) := by
  rw [kernelFredholmCoeff, norm_div, RCLike.norm_natCast]
  exact div_le_div_of_nonneg_right
    (kernelGramMinor_integral_bound (𝕜 := 𝕜) μ r c hr hc hm n) (by positivity)

noncomputable def kernelFredholmSeries
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (z : 𝕜 /- [definition] -/ )
    : 𝕜 := ∑' n, kernelFredholmCoeff (𝕜 := 𝕜) μ r c n * z ^ n

theorem kernelFredholmSeries_absolute
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (z : 𝕜 /- [definition] -/ )
    : Summable (fun n => ‖kernelFredholmCoeff (𝕜 := 𝕜) μ r c n * z ^ n‖) := by
  let M : ℝ := ∫ x, ‖r x‖ * ‖c x‖ ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  apply (Real.summable_pow_div_factorial (M * ‖z‖)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (M ^ n / (n.factorial : ℝ)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (kernelFredholmCoeff_bound (𝕜 := 𝕜) μ r c hr hc hm n)
        (pow_nonneg (norm_nonneg _) n)
    _ = _ := by rw [mul_pow]; ring

theorem kernelFredholmCoeff_radius_top
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars 𝕜 (kernelFredholmCoeff (𝕜 := 𝕜) μ r c)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using
    kernelFredholmSeries_absolute (𝕜 := 𝕜) μ r c hr hc hm (RCLike.ofReal (R : ℝ) : 𝕜)

theorem kernelFredholmSeries_entire
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : AEStronglyMeasurable r μ /- [standing] -/ )
    (hc : AEStronglyMeasurable c μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    : AnalyticOnNhd 𝕜 (kernelFredholmSeries (𝕜 := 𝕜) μ r c) Set.univ := by
  have hradius := kernelFredholmCoeff_radius_top (𝕜 := 𝕜) μ r c hr hc hm
  have h := (FormalMultilinearSeries.ofScalars 𝕜 (kernelFredholmCoeff (𝕜 := 𝕜) μ r c)).hasFPowerSeriesOnBall
    (by rw [hradius]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars 𝕜 (kernelFredholmCoeff (𝕜 := 𝕜) μ r c)).sum =
      kernelFredholmSeries (𝕜 := 𝕜) μ r c := by
    ext z
    exact FormalMultilinearSeries.ofScalars_sum_eq (kernelFredholmCoeff (𝕜 := 𝕜) μ r c) z
  rw [heq] at h
  simpa only [hradius, Metric.eball_top] using h.analyticOnNhd

theorem kernelFredholmSeries_memLp_entire
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    : AnalyticOnNhd 𝕜 (kernelFredholmSeries (𝕜 := 𝕜) μ r c) Set.univ := by
  exact kernelFredholmSeries_entire (𝕜 := 𝕜) μ r c hr.aestronglyMeasurable hc.aestronglyMeasurable
    (hr.norm.integrable_mul hc.norm)

theorem kernelFredholmCoeff_zero
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    : kernelFredholmCoeff (𝕜 := 𝕜) μ r c 0 = 1 := by
  change (∫ x : Fin 0 → X,
    Matrix.det (Matrix.of (fun i j : Fin 0 => inner 𝕜 (r (x i)) (c (x j))))
    ∂(Measure.pi (fun _ => μ))) / (Nat.factorial 0 : 𝕜) = 1
  simp only [Matrix.det_fin_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  simp [integral_const, measureReal_def, Measure.pi_empty_univ]

theorem kernelFredholmSeries_zero
    {𝕜 E X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : MeasureTheory.Measure X /- [definition] -/ )
    [MeasureTheory.SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    : kernelFredholmSeries (𝕜 := 𝕜) μ r c 0 = 1 := by
  rw [kernelFredholmSeries, tsum_eq_single 0]
  · simp [kernelFredholmCoeff_zero]
  · intro n hn
    simp [zero_pow hn]

theorem kernel_joint_probe
    : ∃ r c : ℝ → ℂ, MemLp r 2 (Measure.dirac (0 : ℝ)) ∧
      MemLp c 2 (Measure.dirac (0 : ℝ)) ∧
      ‖r 0‖ = 1 ∧ ‖c 0‖ = 2 ∧ inner ℂ (r 0) (c 0) = 2 ∧
      AnalyticOnNhd ℂ (kernelFredholmSeries (𝕜 := ℂ) (Measure.dirac (0 : ℝ)) r c) Set.univ := by
  let r : ℝ → ℂ := fun _ => 1
  let c : ℝ → ℂ := fun _ => 2
  have hr : MemLp r 2 (Measure.dirac (0 : ℝ)) := memLp_const _
  have hc : MemLp c 2 (Measure.dirac (0 : ℝ)) := memLp_const _
  refine ⟨r, c, hr, hc, ?_, ?_, ?_, kernelFredholmSeries_memLp_entire (𝕜 := ℂ) _ r c hr hc⟩
  · simp [r]
  · simp [c, Complex.norm_ofNat]
  · simp [r, c, inner]



open MeasureTheory

/-- The finite double-permutation contraction used in Andreief's identity. -/
theorem det_pair_permutation_sum
    {𝕜 : Type* /- [definition] -/ }
    [CommRing 𝕜 /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (M : Matrix (Fin n) (Fin n) 𝕜 /- [definition] -/ )
    : (∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, M (σ i) (τ i)) = (n.factorial : 𝕜) * M.det := by
  classical
  have heach (σ : Equiv.Perm (Fin n)) :
      (∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, M (σ i) (τ i)) = M.det := by
    have hd : (∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
        ∏ i, M (σ i) (τ i)) = ((Equiv.Perm.sign σ : ℤ) : 𝕜) * M.det := by
      calc
        _ = ((M.submatrix σ id).transpose).det := by
          rw [Matrix.det_apply']
          rfl
        _ = _ := by rw [Matrix.det_transpose, Matrix.det_permute]
    have hs : ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign σ : ℤ) : 𝕜) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    calc
      _ = ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
          (∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
            ∏ i, M (σ i) (τ i)) := by simp only [Finset.mul_sum, mul_assoc]
      _ = _ := by rw [hd, ← mul_assoc, hs, one_mul]
  simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

theorem det_product_leibniz
    {𝕜 X : Type* /- [definition] -/ }
    [CommRing 𝕜 /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (f g : Fin n → X → 𝕜 /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    : Matrix.det (fun i j : Fin n => f i (x j)) *
        Matrix.det (fun i j : Fin n => g i (x j)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, (f (σ i) (x i) * g (τ i) (x i)) := by
  classical
  change Matrix.det (Matrix.of (fun i j : Fin n => f i (x j))) *
    Matrix.det (Matrix.of (fun i j : Fin n => g i (x j))) = _
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.of_apply]
  ring

/-- Genuine cross-product integrability suffices; L2 feature families supply it by Holder. -/
theorem det_product_integrable
    {𝕜 X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (f g : Fin n → X → 𝕜 /- [definition] -/ )
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ /- [standing] -/ )
    : Integrable (fun x : Fin n → X =>
      Matrix.det (fun i j : Fin n => f i (x j)) *
        Matrix.det (fun i j : Fin n => g i (x j)))
      (Measure.pi (fun _ => μ)) := by
  simp_rw [det_product_leibniz]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  exact (Integrable.fintype_prod (fun i : Fin n => hfg (σ i) (τ i))).const_mul _

/-- Finite Andreief/Fubini identity with the exact factorial. -/
theorem integral_det_product
    {𝕜 X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (f g : Fin n → X → 𝕜 /- [definition] -/ )
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ /- [standing] -/ )
    : (∫ x : Fin n → X, Matrix.det (fun i j : Fin n => f i (x j)) *
        Matrix.det (fun i j : Fin n => g i (x j)) ∂(Measure.pi (fun _ => μ))) =
      (n.factorial : 𝕜) * Matrix.det (fun i j : Fin n => ∫ x, f i x * g j x ∂μ) := by
  classical
  let M : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.of (fun i j => ∫ x, f i x * g j x ∂μ)
  change (∫ x : Fin n → X, Matrix.det (fun i j : Fin n => f i (x j)) *
      Matrix.det (fun i j : Fin n => g i (x j)) ∂(Measure.pi (fun _ => μ))) =
    (n.factorial : 𝕜) * M.det
  have ht (σ τ : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → X =>
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, (f (σ i) (x i) * g (τ i) (x i)))
      (Measure.pi (fun _ => μ)) :=
    (Integrable.fintype_prod (fun i : Fin n => hfg (σ i) (τ i))).const_mul _
  calc
    _ = ∫ x : Fin n → X, ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, (f (σ i) (x i) * g (τ i) (x i))
        ∂(Measure.pi (fun _ => μ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (det_product_leibniz n f g))
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) *
          ∏ i, (∫ x, f (σ i) x * g (τ i) x ∂μ) := by
      rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => ht σ τ))]
      apply Finset.sum_congr rfl
      intro σ _
      rw [integral_finsetSum _ (fun τ _ => ht σ τ)]
      apply Finset.sum_congr rfl
      intro τ _
      rw [integral_const_mul]
      exact congrArg (fun w : 𝕜 =>
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) * w)
        (integral_fintype_prod_eq_prod
          (fun i : Fin n => fun x : X => f (σ i) x * g (τ i) x)
          (μ := fun _ : Fin n => μ))
    _ = _ := det_pair_permutation_sum n M

/-- The finite identity has jointly satisfiable premises with a nonzero Gram matrix with value two. -/
theorem andreief_joint_probe
    : ∃ f g : Fin 1 → ℝ → ℂ,
      (∀ i j, Integrable (fun x => f i x * g j x) (Measure.dirac (0 : ℝ))) ∧
      Matrix.det (fun i j : Fin 1 =>
        ∫ x, f i x * g j x ∂(Measure.dirac (0 : ℝ))) = 2 ∧
      (∫ x : Fin 1 → ℝ, Matrix.det (fun i j : Fin 1 => f i (x j)) *
        Matrix.det (fun i j : Fin 1 => g i (x j))
        ∂(Measure.pi (fun _ => Measure.dirac (0 : ℝ)))) = 2 := by
  let f : Fin 1 → ℝ → ℂ := fun _ _ => 1
  let g : Fin 1 → ℝ → ℂ := fun _ _ => 2
  have hfg : ∀ i j, Integrable (fun x => f i x * g j x) (Measure.dirac (0 : ℝ)) := by
    intro i j
    simpa only [f, g, one_mul] using
      (integrable_const (2 : ℂ) : Integrable (fun _ : ℝ => (2 : ℂ)) (Measure.dirac (0 : ℝ)))
  have hd : Matrix.det (fun i j : Fin 1 =>
      ∫ x, f i x * g j x ∂(Measure.dirac (0 : ℝ))) = 2 := by
    change Matrix.det (Matrix.of (fun i j : Fin 1 =>
      ∫ x, f i x * g j x ∂(Measure.dirac (0 : ℝ)))) = 2
    rw [Matrix.det_fin_one]
    simp [f, g]
  refine ⟨f, g, hfg, hd, ?_⟩
  rw [integral_det_product _ 1 f g hfg, hd]
  norm_num




/-- Coefficient form of rectangular Sylvester: the actual principal-minor sums agree. -/
theorem matrix_principal_minor_sylvester
    {R ι κ : Type* /- [definition] -/ }
    [CommRing R /- [definition] -/ ]
    [Fintype ι /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    (A : Matrix ι κ R /- [definition] -/ )
    (B : Matrix κ ι R /- [definition] -/ )
    (k : ℕ /- [definition] -/ )
    : (∑ s ∈ Finset.univ.powersetCard k,
      ((A * B).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det) =
      ∑ s ∈ Finset.univ.powersetCard k,
      ((B * A).submatrix (Subtype.val : s → κ) (Subtype.val : s → κ)).det := by
  have h := Matrix.det_one_add_mul_comm
    ((Polynomial.X : Polynomial R) • A.map Polynomial.C) (B.map Polynomial.C)
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul] at h
  have hc := congrArg (fun p : Polynomial R => p.coeff k) h
  simpa only [Matrix.coeff_det_one_add_X_smul_eq_sum_minors] using hc

/-- Cauchy-Binet as a sum of actual principal minors of the reversed product.
This avoids imposing an order on the feature index type. -/
theorem matrix_det_rectangular_principal_minors
    {R κ : Type* /- [definition] -/ }
    [CommRing R /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (A : Matrix (Fin n) κ R /- [definition] -/ )
    (B : Matrix κ (Fin n) R /- [definition] -/ )
    : (A * B).det = ∑ s ∈ Finset.univ.powersetCard n,
      ((B * A).submatrix (Subtype.val : s → κ) (Subtype.val : s → κ)).det := by
  have h := matrix_principal_minor_sylvester A B n
  have hu : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [hu, Finset.sum_singleton] at h
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i)
  have hd : ((A * B).submatrix (Subtype.val : ↥(Finset.univ : Finset (Fin n)) → Fin n)
      (Subtype.val : ↥(Finset.univ : Finset (Fin n)) → Fin n)).det = (A * B).det :=
    Matrix.det_submatrix_equiv_self e (A * B)
  exact hd.symm.trans h


/-- The genuine operator series agrees with the previously compiled entire diagonal determinant. -/
theorem operatorDet_eq_diagonalDet
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : operatorDet b T z = diagonalDet a z :=
  operatorDet_diagonal b T a ha hdiag z

/-- Operator-level Plemelj agreement on the diagonal small-norm disk.
The general nondiagonal cycle/trace bridge remains a separate proof obligation. -/
theorem operatorDet_diagonal_eq_plemelj
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℂ E /- [definition] -/ ]
    (b : HilbertBasis ℕ ℂ E /- [definition] -/ )
    (T : E →L[ℂ] E /- [definition] -/ )
    (a : ℕ → ℂ /- [definition] -/ )
    (ha : Summable (fun i => ‖a i‖)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = a i • b i /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    (q : ℝ /- [definition] -/ )
    (hq : 0 ≤ q /- [standing] -/ )
    (hq1 : q < 1 /- [standing] -/ )
    (hsmall : ∀ i, ‖z * a i‖ ≤ q /- [standing] -/ )
    : operatorDet b T z = Complex.exp (-∑' m : ℕ,
      (-z) ^ (m + 1) * diagonalTracePower a (m + 1) / ((m + 1 : ℕ) : ℂ)) := by
  rw [operatorDet_eq_diagonalDet b T a ha hdiag]
  exact diagonalDet_eq_plemelj a ha z q hq hq1 hsmall


/-- The reversed feature product factors after reindexing a cardinal-n feature set. -/
theorem det_reverse_features_factor
    {𝕜 κ X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (e : κ ≃ Fin n /- [definition] -/ )
    (f g : κ → X → 𝕜 /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    : Matrix.det (fun i j : κ => ∑ l : Fin n, f i (x l) * g j (x l)) =
      Matrix.det (fun i j : Fin n => f (e.symm i) (x j)) *
        Matrix.det (fun i j : Fin n => g (e.symm i) (x j)) := by
  classical
  let M : Matrix κ κ 𝕜 := fun i j => ∑ l : Fin n, f i (x l) * g j (x l)
  rw [← Matrix.det_submatrix_equiv_self e.symm M]
  let F : Matrix (Fin n) (Fin n) 𝕜 := fun i j => f (e.symm i) (x j)
  let G : Matrix (Fin n) (Fin n) 𝕜 := fun i j => g (e.symm i) (x j)
  have hm : M.submatrix e.symm e.symm = F * G.transpose := by
    ext i j
    change (∑ l : Fin n, f (e.symm i) (x l) * g (e.symm j) (x l)) = _
    rw [Matrix.mul_apply]
    rfl
  rw [hm, Matrix.det_mul, Matrix.det_transpose]

theorem det_reverse_features_integrable
    {𝕜 κ X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (e : κ ≃ Fin n /- [definition] -/ )
    (f g : κ → X → 𝕜 /- [definition] -/ )
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ /- [standing] -/ )
    : Integrable (fun x : Fin n → X =>
      Matrix.det (fun i j : κ => ∑ l : Fin n, f i (x l) * g j (x l)))
      (Measure.pi (fun _ => μ)) := by
  simp_rw [det_reverse_features_factor n e f g]
  exact det_product_integrable μ n (fun i => f (e.symm i)) (fun i => g (e.symm i))
    (fun i j => hfg _ _)

/-- Andreief for a reindexed feature set, including the empty-set case. -/
theorem integral_det_reverse_features
    {𝕜 κ X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (n : ℕ /- [definition] -/ )
    (e : κ ≃ Fin n /- [definition] -/ )
    (f g : κ → X → 𝕜 /- [definition] -/ )
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ /- [standing] -/ )
    : (∫ x : Fin n → X,
      Matrix.det (fun i j : κ => ∑ l : Fin n, f i (x l) * g j (x l))
      ∂(Measure.pi (fun _ => μ))) =
      (n.factorial : 𝕜) * Matrix.det (fun i j : κ => ∫ x, f i x * g j x ∂μ) := by
  simp_rw [det_reverse_features_factor n e f g]
  rw [integral_det_product μ n _ _ (fun i j => hfg _ _)]
  congr 1
  exact Matrix.det_submatrix_equiv_self e.symm
    (fun i j : κ => ∫ x, f i x * g j x ∂μ)

/-- Finite-feature Fredholm coefficients are the actual integrated principal minors.
This identity is derived from Cauchy-Binet and Andreief, with no determinant-equality premise. -/
theorem finite_feature_coefficient
    {𝕜 κ X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (f g : κ → X → 𝕜 /- [definition] -/ )
    (hgf : ∀ i j, Integrable (fun x => g i x * f j x) μ /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : (∫ x : Fin n → X,
        Matrix.det (fun i j : Fin n => ∑ l : κ, f l (x i) * g l (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : 𝕜) =
      ∑ s ∈ Finset.univ.powersetCard n,
        Matrix.det (fun i j : s => ∫ x, g i.val x * f j.val x ∂μ) := by
  classical
  have he (s : Finset κ) (hs : s ∈ Finset.univ.powersetCard n) : Nonempty (s ≃ Fin n) := by
    apply Fintype.card_eq.mp
    simpa using (Finset.mem_powersetCard.mp hs).2
  have hid (x : Fin n → X) :
      Matrix.det (fun i j : Fin n => ∑ l : κ, f l (x i) * g l (x j)) =
        ∑ s ∈ Finset.univ.powersetCard n,
          Matrix.det (fun i j : s => ∑ l : Fin n, g i.val (x l) * f j.val (x l)) :=
    matrix_det_rectangular_principal_minors n (fun i l => f l (x i)) (fun l j => g l (x j))
  simp_rw [hid]
  rw [integral_finsetSum _ (fun s hs => det_reverse_features_integrable μ n
    (Classical.choice (he s hs)) (fun i : s => g i.val) (fun i : s => f i.val)
    (fun i j => hgf _ _))]
  have hi (s : Finset κ) (hs : s ∈ Finset.univ.powersetCard n) :=
    integral_det_reverse_features μ n (Classical.choice (he s hs))
      (fun i : s => g i.val) (fun i : s => f i.val) (fun i j => hgf _ _)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hi s hs]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)



/-- A polynomial's coefficient series is its classical evaluation. -/
theorem polynomial_coeff_tsum
    {𝕜 : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    (P : Polynomial 𝕜 /- [definition] -/ )
    (z : 𝕜 /- [definition] -/ )
    : (∑' n, P.coeff n * z ^ n) = P.eval z := by
  classical
  rw [tsum_eq_sum (s := P.support)]
  · rw [Polynomial.eval_eq_sum]
    rfl
  · intro n hn
    have hz : P.coeff n = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hn
    rw [hz, zero_mul]

/-- The entire finite-feature Fredholm series is a classical matrix determinant,
at every coupling and without a norm restriction. -/
theorem finite_feature_series
    {𝕜 κ X : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [Fintype κ /- [definition] -/ ]
    [DecidableEq κ /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (f g : κ → X → 𝕜 /- [definition] -/ )
    (hgf : ∀ i j, Integrable (fun x => g i x * f j x) μ /- [standing] -/ )
    (z : 𝕜 /- [definition] -/ )
    : (∑' n, ((∫ x : Fin n → X,
        Matrix.det (fun i j : Fin n => ∑ l : κ, f l (x i) * g l (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : 𝕜)) * z ^ n) =
      Matrix.det ((1 : Matrix κ κ 𝕜) +
        z • Matrix.of (fun i j : κ => ∫ x, g i x * f j x ∂μ)) := by
  classical
  let M : Matrix κ κ 𝕜 := Matrix.of (fun i j => ∫ x, g i x * f j x ∂μ)
  let P : Polynomial 𝕜 := Matrix.det
    ((1 : Matrix κ κ (Polynomial 𝕜)) + (Polynomial.X : Polynomial 𝕜) • M.map Polynomial.C)
  have hcoeff (n : ℕ) : P.coeff n =
      (∫ x : Fin n → X,
        Matrix.det (fun i j : Fin n => ∑ l : κ, f l (x i) * g l (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : 𝕜) := by
    rw [finite_feature_coefficient μ f g hgf n]
    exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors M n
  have heval : P.eval z = Matrix.det ((1 : Matrix κ κ 𝕜) + z • M) := by
    change (Polynomial.evalRingHom z)
      (Matrix.det (1 + (Polynomial.X : Polynomial 𝕜) • M.map Polynomial.C)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval z ((if i = j then 1 else 0) +
      Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + z * M i j
    by_cases hij : i = j <;>
      simp only [hij, if_true, if_false, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X, Polynomial.eval_C]
  simpa only [hcoeff, M] using (polynomial_coeff_tsum P z).trans heval

/-- Dominated convergence of actual Gram Fredholm coefficients under contracting row approximations. -/
theorem kernelFredholmCoeff_dominated_tendsto
    {𝕜 E X J : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (l : Filter J /- [definition] -/ )
    [l.IsCountablyGenerated /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (rj cj : J → X → E /- [definition] -/ )
    (hrj : ∀ j, AEStronglyMeasurable (rj j) μ /- [standing] -/ )
    (hcj : ∀ j, AEStronglyMeasurable (cj j) μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (hbr : ∀ j x, ‖rj j x‖ ≤ ‖r x‖ /- [standing] -/ )
    (hbc : ∀ j x, ‖cj j x‖ ≤ ‖c x‖ /- [standing] -/ )
    (htr : ∀ x, Tendsto (fun j => rj j x) l (𝓝 (r x))  /- [standing] -/ )
    (htc : ∀ x, Tendsto (fun j => cj j x) l (𝓝 (c x))  /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : Tendsto (fun j => kernelFredholmCoeff (𝕜 := 𝕜) μ (rj j) (cj j) n)
      l (𝓝 (kernelFredholmCoeff (𝕜 := 𝕜) μ r c n)) := by
  have hminor (x : Fin n → X) : Tendsto
      (fun j => kernelGramMinor (𝕜 := 𝕜) (rj j) (cj j) n x)
      l (𝓝 (kernelGramMinor (𝕜 := 𝕜) r c n x)) := by
    apply (continuous_id.matrix_det : Continuous
      (Matrix.det : Matrix (Fin n) (Fin n) 𝕜 → 𝕜)).continuousAt.tendsto.comp
    exact tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2
      (fun k => (htr (x i)).inner (htc (x k))))
  have hi : Tendsto (fun j => ∫ x : Fin n → X,
      kernelGramMinor (𝕜 := 𝕜) (rj j) (cj j) n x ∂(Measure.pi (fun _ => μ)))
      l (𝓝 (∫ x : Fin n → X, kernelGramMinor (𝕜 := 𝕜) r c n x
        ∂(Measure.pi (fun _ => μ)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : Fin n → X => ∏ i, (‖r (x i)‖ * ‖c (x i)‖))
    · exact Filter.Eventually.of_forall (fun j =>
        kernelGramMinor_aestronglyMeasurable (𝕜 := 𝕜) μ _ _ (hrj j) (hcj j) n)
    · apply Filter.Eventually.of_forall
      intro j
      apply Filter.Eventually.of_forall
      intro x
      exact (kernelGramMinor_bound (𝕜 := 𝕜) _ _ n x).trans
        (Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ =>
          mul_le_mul (hbr j (x i)) (hbc j (x i)) (norm_nonneg _) (norm_nonneg _)))
    · exact Integrable.fintype_prod (fun _ : Fin n => hm)
    · exact Filter.Eventually.of_forall hminor
  exact hi.div_const _

/-- The full entire series commutes with contracting row approximation at every coupling. -/
theorem kernelFredholmSeries_dominated_tendsto
    {𝕜 E X J : Type* /- [definition] -/ }
    [RCLike 𝕜 /- [definition] -/ ]
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace 𝕜 E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (l : Filter J /- [definition] -/ )
    [l.IsCountablyGenerated /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (rj cj : J → X → E /- [definition] -/ )
    (hrj : ∀ j, AEStronglyMeasurable (rj j) μ /- [standing] -/ )
    (hcj : ∀ j, AEStronglyMeasurable (cj j) μ /- [standing] -/ )
    (hm : Integrable (fun x => ‖r x‖ * ‖c x‖) μ /- [standing] -/ )
    (hbr : ∀ j x, ‖rj j x‖ ≤ ‖r x‖ /- [standing] -/ )
    (hbc : ∀ j x, ‖cj j x‖ ≤ ‖c x‖ /- [standing] -/ )
    (htr : ∀ x, Tendsto (fun j => rj j x) l (𝓝 (r x))  /- [standing] -/ )
    (htc : ∀ x, Tendsto (fun j => cj j x) l (𝓝 (c x))  /- [standing] -/ )
    (z : 𝕜 /- [definition] -/ )
    : Tendsto (fun j => kernelFredholmSeries (𝕜 := 𝕜) μ (rj j) (cj j) z)
      l (𝓝 (kernelFredholmSeries (𝕜 := 𝕜) μ r c z)) := by
  let M : ℝ := ∫ x, ‖r x‖ * ‖c x‖ ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hmass (j : J) : Integrable (fun x => ‖rj j x‖ * ‖cj j x‖) μ :=
    hm.mono' ((hrj j).norm.mul (hcj j).norm) (Filter.Eventually.of_forall
      (fun x => by simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using
        (mul_le_mul (hbr j x) (hbc j x) (norm_nonneg _) (norm_nonneg _))))
  have hmass_le (j : J) : (∫ x, ‖rj j x‖ * ‖cj j x‖ ∂μ) ≤ M :=
    integral_mono (hmass j) hm (fun x =>
      mul_le_mul (hbr j x) (hbc j x) (norm_nonneg _) (norm_nonneg _))
  apply tendsto_tsum_of_dominated_convergence
    (Real.summable_pow_div_factorial (M * ‖z‖))
    (fun n => (kernelFredholmCoeff_dominated_tendsto μ l r c rj cj hrj hcj
      hm hbr hbc htr htc n).mul tendsto_const_nhds)
  apply Filter.Eventually.of_forall
  intro j n
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((∫ x, ‖rj j x‖ * ‖cj j x‖ ∂μ) ^ n / (n.factorial : ℝ)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right
        (kernelFredholmCoeff_bound (𝕜 := 𝕜) μ _ _ (hrj j) (hcj j) (hmass j) n) (by positivity)
    _ ≤ (M ^ n / (n.factorial : ℝ)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (integral_nonneg (fun _ => by positivity)) (hmass_le j) n)
          (by positivity)) (by positivity)
    _ = _ := by rw [mul_pow]; ring


theorem realBasisProjection_inner
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    (x y : E /- [definition] -/ )
    : inner ℝ (realBasisProjection b s x) (realBasisProjection b s y) =
      ∑ i ∈ s, inner ℝ x (b i) * inner ℝ (b i) y := by
  simp only [realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply]
  rw [b.orthonormal.inner_sum]
  simp only [starRingEnd_apply, star_trivial, real_inner_comm x]

theorem realBasisProjection_norm_le
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ )
    (x : E /- [definition] -/ )
    : ‖realBasisProjection b s x‖ ≤ ‖x‖ := by
  have hn : ‖realBasisProjection b s x‖ ^ 2 = ∑ i ∈ s, ‖inner ℝ (b i) x‖ ^ 2 := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℝ E, realBasisProjection_inner]
    simp only [RCLike.re_to_real, real_inner_comm x, Real.norm_eq_abs]
    simp only [sq_abs]
    simp only [pow_two]
  have hb := b.orthonormal.sum_inner_products_le x (s := s)
  nlinarith [norm_nonneg (realBasisProjection b s x), norm_nonneg x]

/-- The Fredholm series of the finite projected row families is exactly a finite matrix determinant. -/
theorem kernelFredholmSeries_real_projection
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (s : Finset ι /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : kernelFredholmSeries (𝕜 := ℝ) μ
        (fun x => realBasisProjection b s (r x)) (fun x => realBasisProjection b s (c x)) z =
      Matrix.det ((1 : Matrix s s ℝ) + z • Matrix.of
        (fun i j : s => ∫ x, inner ℝ (b i.val) (c x) * inner ℝ (r x) (b j.val) ∂μ)) := by
  classical
  have hi (x y : X) : inner ℝ (realBasisProjection b s (r x)) (realBasisProjection b s (c y)) =
      ∑ i : s, inner ℝ (r x) (b i.val) * inner ℝ (b i.val) (c y) := by
    exact (realBasisProjection_inner b s (r x) (c y)).trans
      (Finset.sum_coe_sort s (fun i => inner ℝ (r x) (b i) * inner ℝ (b i) (c y))).symm
  unfold kernelFredholmSeries kernelFredholmCoeff kernelGramMinor
  simp_rw [hi]
  exact finite_feature_series μ (fun i : s => fun x => inner ℝ (r x) (b i.val))
    (fun i : s => fun x => inner ℝ (b i.val) (c x))
    (fun i j => (hc.const_inner (b i.val)).integrable_mul (hr.inner_const (b j.val))) z

/-- A genuine matrix-entry integral identifies the Gram-kernel series with the trace-class operator
series. The premise specifies the operator action, not a determinant or coefficient equality. -/
theorem kernelFredholmSeries_eq_realOperatorDet_of_entries
    {E X ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧ Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (hentry : ∀ i j, inner ℝ (b i) (T (b j)) =
      ∫ x, inner ℝ (b i) (c x) * inner ℝ (r x) (b j) ∂μ /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : kernelFredholmSeries (𝕜 := ℝ) μ r c z = realOperatorDet b T z := by
  have hleft := kernelFredholmSeries_dominated_tendsto (𝕜 := ℝ) μ
    (atTop : Filter (Finset ι)) r c
    (fun s x => realBasisProjection b s (r x)) (fun s x => realBasisProjection b s (c x))
    (fun s => (realBasisProjection b s).continuous.comp_aestronglyMeasurable hr.aestronglyMeasurable)
    (fun s => (realBasisProjection b s).continuous.comp_aestronglyMeasurable hc.aestronglyMeasurable)
    (hr.norm.integrable_mul hc.norm)
    (fun s x => realBasisProjection_norm_le b s (r x))
    (fun s x => realBasisProjection_norm_le b s (c x))
    (fun x => realBasisProjection_tendsto b (r x))
    (fun x => realBasisProjection_tendsto b (c x)) z
  have heq (s : Finset ι) : kernelFredholmSeries (𝕜 := ℝ) μ
      (fun x => realBasisProjection b s (r x)) (fun x => realBasisProjection b s (c x)) z =
      Matrix.det ((1 : Matrix s s ℝ) + z • Matrix.of
        (fun i j : s => inner ℝ (b i.val) (T (b j.val)))) := by
    rw [kernelFredholmSeries_real_projection μ b r c hr hc s z]
    simp_rw [hentry]
  simp_rw [heq] at hleft
  exact tendsto_nhds_unique hleft (realOperatorDet_matrix_det_tendsto b T hT z)

/-- The Gram-kernel series of genuine L2 row representatives is the operator determinant of AB.
The two evaluation assumptions are the usual kernel-application identities, with no spectral
or determinant identity among the hypotheses. They hold almost everywhere. -/
theorem kernelFredholmSeries_eq_realOperatorDet_comp
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (hevalA : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    (hevalBadj : ∀ f, ∀ᵐ x ∂μ, (B.adjoint f) x = inner ℝ (c x) f /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : kernelFredholmSeries (𝕜 := ℝ) μ r c z = realOperatorDet b (A ∘L B) z := by
  have he (i j : ι) : inner ℝ (b i) ((B ∘L A) (b j)) =
      ∫ x, inner ℝ (b i) (c x) * inner ℝ (r x) (b j) ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← B.adjoint_inner_left (A (b j)) (b i), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hevalBadj (b i), hevalA (b j)] with x hi hj
    simp only [hi, hj, RCLike.inner_apply, starRingEnd_apply, star_trivial, real_inner_comm (b i), mul_comm]
  have hT : ∃ U V : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, B ∘L A = U ∘L V ∧
      Summable (fun i => ‖U (b i)‖ ^ 2) ∧ Summable (fun i => ‖V (b i)‖ ^ 2) :=
    ⟨B, A, rfl, hB, hA⟩
  exact (kernelFredholmSeries_eq_realOperatorDet_of_entries μ b r c hr hc (B ∘L A) hT he z).trans
    (realOperatorDet_sylvester_bases b b B A hB hA z)

/-- The symmetric HS case used for H_s squared, at all real couplings including minus one. -/
theorem kernelFredholmSeries_gram_eq_realOperatorDet_square
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (H : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hH : Summable (fun i => ‖H (b i)‖ ^ 2)  /- [standing] -/ )
    (hself : H.adjoint = H /- [standing] -/ )
    (r : X → Lp ℝ 2 μ /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (heval : ∀ f, ∀ᵐ x ∂μ, (H f) x = inner ℝ (r x) f /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : kernelFredholmSeries (𝕜 := ℝ) μ r r z = realOperatorDet b (H ∘L H) z := by
  apply kernelFredholmSeries_eq_realOperatorDet_comp μ b H H hH hH r r hr hr heval
  simpa only [hself] using heval

/-- The literal kernel-integral series agrees with the Gram series on a full-measure set.
Its left side is the defining expression of TWC's kernelFredholm at a real coupling. -/
theorem kernelIntegralSeries_eq_gram
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (k : X → X → ℝ /- [definition] -/ )
    (S : Set X /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hk : ∀ x ∈ S, ∀ y ∈ S, k x y = inner ℝ (r x) (c y)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : (∑' n, ((((∫ x : Fin n → X, Matrix.det (fun i j : Fin n => k (x i) (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : ℝ)) : ℝ) : ℂ) * (z : ℂ) ^ n) =
      (kernelFredholmSeries (𝕜 := ℝ) μ r c z : ℂ) := by
  have he (n : ℕ) : (∫ x : Fin n → X, Matrix.det (fun i j : Fin n => k (x i) (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : ℝ) = kernelFredholmCoeff (𝕜 := ℝ) μ r c n := by
    unfold kernelFredholmCoeff
    congr 1
    apply integral_congr_ae
    have hs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ i, x i ∈ S :=
      eventually_all.2 (fun i => Measure.tendsto_eval_ae_ae.eventually hS)
    filter_upwards [hs] with x hx
    unfold kernelGramMinor
    congr 1
    funext i j
    exact hk (x i) (hx i) (x j) (hx j)
  simp_rw [he]
  have hsum := (kernelFredholmSeries_absolute (𝕜 := ℝ) μ r c hr.aestronglyMeasurable
    hc.aestronglyMeasurable (hr.norm.integrable_mul hc.norm) z).of_norm
  have h := Complex.ofRealCLM.map_tsum hsum
  simpa only [kernelFredholmSeries, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow] using h.symm

/-- Kernel/operator identification for genuine HS integral factors, at every real coupling.
The integral series uses n! normalization and the order-two determinant sign convention. -/
theorem kernelIntegralSeries_eq_realOperatorDet_comp
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (hevalA : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    (hevalBadj : ∀ f, ∀ᵐ x ∂μ, (B.adjoint f) x = inner ℝ (c x) f /- [standing] -/ )
    (k : X → X → ℝ /- [definition] -/ )
    (S : Set X /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hk : ∀ x ∈ S, ∀ y ∈ S, k x y = inner ℝ (r x) (c y)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : (∑' n, ((((∫ x : Fin n → X, Matrix.det (fun i j : Fin n => k (x i) (x j))
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : ℝ)) : ℝ) : ℂ) * (z : ℂ) ^ n) =
      (realOperatorDet b (A ∘L B) z : ℂ) := by
  rw [kernelIntegralSeries_eq_gram μ r c hr hc k S hS hk z,
    kernelFredholmSeries_eq_realOperatorDet_comp μ b A B hA hB r c hr hc hevalA hevalBadj z]

/-- All kernel/operator hypotheses coexist on an actual nonzero L2 instance outside the unit disk. -/
theorem kernel_operator_all_binder_probe
    : ∃ b : HilbertBasis (Fin 1) ℝ (Lp ℝ 2 (Measure.dirac (0 : ℝ))),
      ∃ H : Lp ℝ 2 (Measure.dirac (0 : ℝ)) →L[ℝ] Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      ∃ r : ℝ → Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      Summable (fun i => ‖H (b i)‖ ^ 2) ∧ H.adjoint = H ∧
      MemLp r 2 (Measure.dirac (0 : ℝ)) ∧ ‖H (b 0)‖ = 2 ∧ ‖r 0‖ = 2 ∧
      (∀ f, ∀ᵐ x ∂Measure.dirac (0 : ℝ), (H f) x = inner ℝ (r x) f) ∧
      (∀ y, ∀ᵐ t ∂Measure.dirac (0 : ℝ), (r y) t = 2) ∧
      kernelFredholmSeries (𝕜 := ℝ) (Measure.dirac (0 : ℝ)) r r (-1) =
        realOperatorDet b (H ∘L H) (-1) := by
  let μ : Measure ℝ := Measure.dirac 0
  let h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1
  let e : (Lp ℝ 2 μ) := h1.toLp (fun _ => 1)
  have heae : (e : ℝ → ℝ) =ᵐ[μ] (fun _ => 1) := h1.coeFn_toLp
  have he0 : e 0 = 1 := by simpa only [μ, Filter.EventuallyEq, MeasureTheory.ae_dirac_eq, Filter.eventually_pure] using heae
  have hi (f : (Lp ℝ 2 μ)) : inner ℝ e f = f 0 := by
    rw [L2.inner_def]
    simp [μ, he0, RCLike.inner_apply]
  have hfn (f : (Lp ℝ 2 μ)) : f = (f 0) • e := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (f 0) e, heae, ae_eq_dirac (f : ℝ → ℝ)] with x hx he hf
    simpa only [Pi.smul_apply, he, hf, smul_eq_mul, mul_one, Function.const_apply] using hx.symm
  have he1 : ‖e‖ = 1 := by
    have ht := hi e
    rw [real_inner_self_eq_norm_sq, he0] at ht
    nlinarith [norm_nonneg e]
  let v : Fin 1 → (Lp ℝ 2 μ) := fun _ => e
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, v, hi, he0, he1]
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply top_le_iff.mp
    intro f _
    rw [hfn f]
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self (0 : Fin 1))
  let b : HilbertBasis (Fin 1) ℝ (Lp ℝ 2 μ) := HilbertBasis.mk hv (by
    rw [hspan]
    exact Submodule.le_topologicalClosure (⊤ : Submodule ℝ (Lp ℝ 2 μ)))
  have hb (i : Fin 1) : b i = e := by simp [b, v]
  let H : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ) := (2 : ℝ) • rankOne ℝ e e
  let r : ℝ → (Lp ℝ 2 μ) := fun _ => (2 : ℝ) • e
  have hH : Summable (fun i => ‖H (b i)‖ ^ 2) := (hasSum_fintype _).summable
  have hself : H.adjoint = H := by simp [H]
  have hr : MemLp r 2 μ := memLp_const _
  have hev (f : (Lp ℝ 2 μ)) : ∀ᵐ x ∂μ, (H f) x = inner ℝ (r x) f := by
    have hh : H f = (2 * inner ℝ e f) • e := by simp [H, rankOne_apply, smul_smul]
    rw [hh]
    filter_upwards [Lp.coeFn_smul (2 * inner ℝ e f) e, heae] with x hx he
    simp [hx, he, r, inner_smul_left]
  have hrow (y : ℝ) : ∀ᵐ t ∂μ, (r y) t = 2 := by
    filter_upwards [Lp.coeFn_smul (2 : ℝ) e, heae] with t ht he
    simpa [r, Pi.smul_apply, he] using ht
  refine ⟨b, H, r, hH, hself, hr, ?_, ?_, hev, hrow, ?_⟩
  · simp [H, hb, rankOne_apply, hi, he0, norm_smul, he1]
  · simp [r, norm_smul, he1]
  · exact kernelFredholmSeries_gram_eq_realOperatorDet_square μ b H hH hself r hr hev (-1)

/-- A pair of actual L2 row representatives turns the convolution kernel into a Gram kernel.
The equality holds on a full-measure set in each variable, including the diagonal. -/
theorem convolutionKernel_eq_gram
    {X : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    (a d : X → X → ℝ /- [definition] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (S : Set X /- [definition] -/ )
    (hra : ∀ x ∈ S, ∀ᵐ t ∂μ, (r x) t = a x t /- [standing] -/ )
    (hcd : ∀ y ∈ S, ∀ᵐ t ∂μ, (c y) t = d t y /- [standing] -/ )
    (x : X /- [definition] -/ )
    (hx : x ∈ S /- [standing] -/ )
    (y : X /- [definition] -/ )
    (hy : y ∈ S /- [standing] -/ )
    : (∫ t, a x t * d t y ∂μ) = inner ℝ (r x) (c y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hra x hx, hcd y hy] with t ht ht'
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ht, ht', mul_comm]

/-- The kernel-level Fredholm integral series of the convolution of two genuine HS kernels
is the operator determinant of AB, at every real coupling. This includes z = -1 on L2(0,infinity).
No determinant, coefficient equality, or imported bound is assumed. -/
theorem kernelIntegralSeries_convolution_eq_realOperatorDet_comp
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (a d : X → X → ℝ /- [definition] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (S : Set X /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hra : ∀ x ∈ S, ∀ᵐ t ∂μ, (r x) t = a x t /- [standing] -/ )
    (hcd : ∀ y ∈ S, ∀ᵐ t ∂μ, (c y) t = d t y /- [standing] -/ )
    (happlyA : ∀ f, ∀ᵐ x ∂μ, (A f) x = ∫ t, a x t * f t ∂μ /- [standing] -/ )
    (happlyBadj : ∀ f, ∀ᵐ y ∂μ, (B.adjoint f) y = ∫ t, d t y * f t ∂μ /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : (∑' n, ((((∫ x : Fin n → X,
        Matrix.det (fun i j : Fin n => ∫ t, a (x i) t * d t (x j) ∂μ)
        ∂(Measure.pi (fun _ => μ))) / (n.factorial : ℝ)) : ℝ) : ℂ) * (z : ℂ) ^ n) =
      (realOperatorDet b (A ∘L B) z : ℂ) := by
  have hevA (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f := by
    filter_upwards [hS, happlyA f] with x hx hAx
    rw [hAx, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hra x hx] with t ht
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ht, mul_comm]
  have hevBadj (f : Lp ℝ 2 μ) : ∀ᵐ y ∂μ, (B.adjoint f) y = inner ℝ (c y) f := by
    filter_upwards [hS, happlyBadj f] with y hy hBy
    rw [hBy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcd y hy] with t ht
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ht, mul_comm]
  exact kernelIntegralSeries_eq_realOperatorDet_comp μ b A B hA hB r c hr hc hevA hevBadj
    (fun x y => ∫ t, a x t * d t y ∂μ) S hS
    (fun x hx y hy => convolutionKernel_eq_gram μ a d r c S hra hcd x hx y hy) z

/-- All genuine convolution-application premises have one simultaneous nonzero L2 witness. -/
theorem convolution_operator_all_binder_probe
    : ∃ b : HilbertBasis (Fin 1) ℝ (Lp ℝ 2 (Measure.dirac (0 : ℝ))),
      ∃ H : Lp ℝ 2 (Measure.dirac (0 : ℝ)) →L[ℝ] Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      ∃ r : ℝ → Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      Summable (fun i => ‖H (b i)‖ ^ 2) ∧ H.adjoint = H ∧
      MemLp r 2 (Measure.dirac (0 : ℝ)) ∧ ‖H (b 0)‖ = 2 ∧ ‖r 0‖ = 2 ∧
      (∀ y, ∀ᵐ t ∂Measure.dirac (0 : ℝ), (r y) t = 2) ∧
      (∀ f, ∀ᵐ x ∂Measure.dirac (0 : ℝ), (H f) x = ∫ t, (2 : ℝ) * f t ∂Measure.dirac (0 : ℝ)) ∧
      (∑' n, ((((∫ x : Fin n → ℝ,
        Matrix.det (fun i j : Fin n => ∫ t : ℝ, (2 : ℝ) * 2 ∂Measure.dirac (0 : ℝ))
        ∂(Measure.pi (fun _ => Measure.dirac (0 : ℝ)))) / (n.factorial : ℝ)) : ℝ) : ℂ) * (-1 : ℂ) ^ n) =
        (realOperatorDet b (H ∘L H) (-1) : ℂ) := by
  obtain ⟨b, H, r, hH, hself, hr, hnorm, hrnorm, hev, hrow, _⟩ := kernel_operator_all_binder_probe
  have hap (f : Lp ℝ 2 (Measure.dirac (0 : ℝ))) : ∀ᵐ x ∂Measure.dirac (0 : ℝ),
      (H f) x = ∫ t, (2 : ℝ) * f t ∂Measure.dirac (0 : ℝ) := by
    filter_upwards [hev f] with x hx
    rw [hx, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrow x] with t ht
    simp [RCLike.inner_apply, ht, mul_comm]
  refine ⟨b, H, r, hH, hself, hr, hnorm, hrnorm, hrow, hap, ?_⟩
  have h := kernelIntegralSeries_convolution_eq_realOperatorDet_comp
    (Measure.dirac (0 : ℝ)) b H H hH hH (fun _ _ => 2) (fun _ _ => 2) r r hr hr
    Set.univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun x _ => hrow x) (fun y _ => hrow y) hap (by simpa only [hself] using hap) (-1)
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using h


end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.fredholmSeries
#print axioms RMTFoundations.Fredholm.factorial_weight_summable
#print axioms RMTFoundations.Fredholm.fredholmSeries_absolute
#print axioms RMTFoundations.Fredholm.fredholmSeries_hasSum
#print axioms RMTFoundations.Fredholm.fredholmSeries_radius_top
#print axioms RMTFoundations.Fredholm.fredholmSeries_entire
#print axioms RMTFoundations.Fredholm.fredholmSeries_continuous
#print axioms RMTFoundations.Fredholm.fredholmSeries_zero
#print axioms RMTFoundations.Fredholm.fredholmSeries_uniform_closedBall
#print axioms RMTFoundations.Fredholm.fredholmSeries_family_continuous
#print axioms RMTFoundations.Fredholm.fredholmSeries_convolution
#print axioms RMTFoundations.Fredholm.rankOneCoeff
#print axioms RMTFoundations.Fredholm.rankOneCoeff_bound
#print axioms RMTFoundations.Fredholm.rankOneCoeff_series
#print axioms RMTFoundations.Fredholm.entire_joint_probe
#print axioms RMTFoundations.Fredholm.diagonalDet
#print axioms RMTFoundations.Fredholm.diagonalDet_hasProd
#print axioms RMTFoundations.Fredholm.diagonalDet_absolute
#print axioms RMTFoundations.Fredholm.diagonalDet_eq_tsum
#print axioms RMTFoundations.Fredholm.diagonalDet_truncations
#print axioms RMTFoundations.Fredholm.diagonalDet_norm_le
#print axioms RMTFoundations.Fredholm.diagonalDet_eq_exp_log
#print axioms RMTFoundations.Fredholm.diagonalDet_multiplicative
#print axioms RMTFoundations.Fredholm.diagonalDet_zero
#print axioms RMTFoundations.Fredholm.singleDiagonal
#print axioms RMTFoundations.Fredholm.singleDiagonal_summable
#print axioms RMTFoundations.Fredholm.singleDiagonal_det
#print axioms RMTFoundations.Fredholm.diagonal_joint_probe
#print axioms RMTFoundations.Fredholm.diagonalCoeff
#print axioms RMTFoundations.Fredholm.diagonalCoeff_hasSum
#print axioms RMTFoundations.Fredholm.diagonalCoeff_absolute
#print axioms RMTFoundations.Fredholm.diagonalDet_eq_fredholmSeries
#print axioms RMTFoundations.Fredholm.diagonalCoeff_radius_top
#print axioms RMTFoundations.Fredholm.diagonalDet_entire
#print axioms RMTFoundations.Fredholm.finite_diagonal_norm_le
#print axioms RMTFoundations.Fredholm.finite_diagonal_difference_le
#print axioms RMTFoundations.Fredholm.diagonalDet_difference_le
#print axioms RMTFoundations.Fredholm.l1Det
#print axioms RMTFoundations.Fredholm.l1_norm_eq
#print axioms RMTFoundations.Fredholm.l1Det_difference_le
#print axioms RMTFoundations.Fredholm.l1Det_continuous
#print axioms RMTFoundations.Fredholm.diagonalTracePower
#print axioms RMTFoundations.Fredholm.diagonal_plemelj_double_absolute
#print axioms RMTFoundations.Fredholm.diagonalDet_eq_plemelj
#print axioms RMTFoundations.Fredholm.l1_joint_probe
#print axioms RMTFoundations.Fredholm.plemelj_joint_probe
#print axioms RMTFoundations.Fredholm.entire_exp_obstruction
#print axioms RMTFoundations.Fredholm.diagonal_comp_summable
#print axioms RMTFoundations.Fredholm.diagonal_matrix_det
#print axioms RMTFoundations.Fredholm.diagonal_matrix_det_tendsto
#print axioms RMTFoundations.Fredholm.orthonormal_det_bound
#print axioms RMTFoundations.Fredholm.orthonormal_det_bound_indexed
#print axioms RMTFoundations.Fredholm.crossGram_det_bound
#print axioms RMTFoundations.Fredholm.nuclearOperator
#print axioms RMTFoundations.Fredholm.nuclearOperator_absolute
#print axioms RMTFoundations.Fredholm.nuclearOperator_hasSum
#print axioms RMTFoundations.Fredholm.hs_vectors_nuclear_mass
#print axioms RMTFoundations.Fredholm.nuclearMinor
#print axioms RMTFoundations.Fredholm.nuclearMinor_bound
#print axioms RMTFoundations.Fredholm.nuclearDet
#print axioms RMTFoundations.Fredholm.nuclearDet_absolute
#print axioms RMTFoundations.Fredholm.nuclearDet_hasSum
#print axioms RMTFoundations.Fredholm.nuclearCoeff
#print axioms RMTFoundations.Fredholm.nuclearCoeff_hasSum
#print axioms RMTFoundations.Fredholm.nuclearCoeff_absolute
#print axioms RMTFoundations.Fredholm.nuclearCoeff_radius_top
#print axioms RMTFoundations.Fredholm.nuclearDet_entire
#print axioms RMTFoundations.Fredholm.nuclearDet_norm_le
#print axioms RMTFoundations.Fredholm.hilbertBasis_norm_sq_hasSum
#print axioms RMTFoundations.Fredholm.hs_adjoint_square_summable
#print axioms RMTFoundations.Fredholm.hsFactorDet
#print axioms RMTFoundations.Fredholm.hsFactorDet_entire
#print axioms RMTFoundations.Fredholm.hsFactor_nuclearOperator_eq_comp
#print axioms RMTFoundations.Fredholm.nuclearMinor_diagonal
#print axioms RMTFoundations.Fredholm.nuclearDet_diagonal
#print axioms RMTFoundations.Fredholm.nuclearMinor_family_continuous
#print axioms RMTFoundations.Fredholm.nuclearDet_dominated_family_continuous
#print axioms RMTFoundations.Fredholm.matrix_det_principal_minors
#print axioms RMTFoundations.Fredholm.nuclear_joint_probe
#print axioms RMTFoundations.Fredholm.nuclearMinor_subtype_map
#print axioms RMTFoundations.Fredholm.nuclearTruncation_eq_matrix_det
#print axioms RMTFoundations.Fredholm.nuclearTruncation_matrix_det_tendsto
#print axioms RMTFoundations.Fredholm.hsFactor_joint_probe
#print axioms RMTFoundations.Fredholm.nuclearTruncation_uniform_closedBall
#print axioms RMTFoundations.Fredholm.hsFactorDet_absolute
#print axioms RMTFoundations.Fredholm.nuclearDet_orthonormal_diagonal
#print axioms RMTFoundations.Fredholm.operatorDet
#print axioms RMTFoundations.Fredholm.operatorMinor_factorization
#print axioms RMTFoundations.Fredholm.operatorDet_eq_hsFactorDet
#print axioms RMTFoundations.Fredholm.operatorDet_absolute
#print axioms RMTFoundations.Fredholm.operatorDet_entire
#print axioms RMTFoundations.Fredholm.hsFactorDet_factorization_independent
#print axioms RMTFoundations.Fredholm.nuclearMinor_zero_column
#print axioms RMTFoundations.Fredholm.nuclearDet_finite_support
#print axioms RMTFoundations.Fredholm.operatorDet_matrix_det_tendsto
#print axioms RMTFoundations.Fredholm.operatorDet_diagonal
#print axioms RMTFoundations.Fredholm.operator_joint_probe
#print axioms RMTFoundations.Fredholm.l2_summable_distance_envelope
#print axioms RMTFoundations.Fredholm.nuclearDet_dominated_tendsto
#print axioms RMTFoundations.Fredholm.nuclearDet_l2_continuous
#print axioms RMTFoundations.Fredholm.hsColumns
#print axioms RMTFoundations.Fredholm.hsColumns_norm_sq
#print axioms RMTFoundations.Fredholm.hs_adjoint_square_tsum_eq
#print axioms RMTFoundations.Fredholm.hsColumns_difference_norm_sq
#print axioms RMTFoundations.Fredholm.hs_square_summable_sub
#print axioms RMTFoundations.Fredholm.hsColumns_tendsto_of_square
#print axioms RMTFoundations.Fredholm.hsColumns_adjoint_tendsto_of_square
#print axioms RMTFoundations.Fredholm.hsFactorDet_tendsto_of_hs
#print axioms RMTFoundations.Fredholm.operatorDet_comp_tendsto_of_hs
#print axioms RMTFoundations.Fredholm.operatorDet_comp_family_continuous
#print axioms RMTFoundations.Fredholm.hs_continuity_joint_probe
#print axioms RMTFoundations.Fredholm.realNuclearOperator
#print axioms RMTFoundations.Fredholm.realL2_summable_distance_envelope
#print axioms RMTFoundations.Fredholm.realNuclearOperator_absolute
#print axioms RMTFoundations.Fredholm.realNuclearOperator_hasSum
#print axioms RMTFoundations.Fredholm.realHs_vectors_nuclear_mass
#print axioms RMTFoundations.Fredholm.realNuclearMinor
#print axioms RMTFoundations.Fredholm.realNuclearMinor_bound
#print axioms RMTFoundations.Fredholm.realNuclearDet
#print axioms RMTFoundations.Fredholm.realNuclearDet_absolute
#print axioms RMTFoundations.Fredholm.realNuclearDet_hasSum
#print axioms RMTFoundations.Fredholm.realNuclearCoeff
#print axioms RMTFoundations.Fredholm.realNuclearCoeff_hasSum
#print axioms RMTFoundations.Fredholm.realNuclearCoeff_absolute
#print axioms RMTFoundations.Fredholm.realNuclearCoeff_radius_top
#print axioms RMTFoundations.Fredholm.realNuclearDet_entire
#print axioms RMTFoundations.Fredholm.realNuclearDet_norm_le
#print axioms RMTFoundations.Fredholm.realHilbertBasis_norm_sq_hasSum
#print axioms RMTFoundations.Fredholm.realHs_adjoint_square_summable
#print axioms RMTFoundations.Fredholm.realHSFactorDet
#print axioms RMTFoundations.Fredholm.realHSFactorDet_entire
#print axioms RMTFoundations.Fredholm.realHsFactor_nuclearOperator_eq_comp
#print axioms RMTFoundations.Fredholm.realMatrix_det_principal_minors
#print axioms RMTFoundations.Fredholm.realNuclearMinor_subtype_map
#print axioms RMTFoundations.Fredholm.realNuclearTruncation_eq_matrix_det
#print axioms RMTFoundations.Fredholm.realNuclearTruncation_matrix_det_tendsto
#print axioms RMTFoundations.Fredholm.realHsFactor_joint_probe
#print axioms RMTFoundations.Fredholm.realHSFactorDet_absolute
#print axioms RMTFoundations.Fredholm.realOperatorDet
#print axioms RMTFoundations.Fredholm.realOperatorMinor_factorization
#print axioms RMTFoundations.Fredholm.realOperatorDet_eq_hsFactorDet
#print axioms RMTFoundations.Fredholm.realOperatorDet_absolute
#print axioms RMTFoundations.Fredholm.realOperatorDet_entire
#print axioms RMTFoundations.Fredholm.realHSFactorDet_factorization_independent
#print axioms RMTFoundations.Fredholm.realNuclearDet_dominated_tendsto
#print axioms RMTFoundations.Fredholm.realNuclearDet_l2_continuous
#print axioms RMTFoundations.Fredholm.realHsColumns
#print axioms RMTFoundations.Fredholm.realHsColumns_norm_sq
#print axioms RMTFoundations.Fredholm.realHs_adjoint_square_tsum_eq
#print axioms RMTFoundations.Fredholm.realHsColumns_difference_norm_sq
#print axioms RMTFoundations.Fredholm.realHs_square_summable_sub
#print axioms RMTFoundations.Fredholm.realHsColumns_tendsto_of_square
#print axioms RMTFoundations.Fredholm.realHsColumns_adjoint_tendsto_of_square
#print axioms RMTFoundations.Fredholm.realHSFactorDet_tendsto_of_hs
#print axioms RMTFoundations.Fredholm.realOperatorDet_comp_tendsto_of_hs
#print axioms RMTFoundations.Fredholm.realOperatorDet_comp_family_continuous
#print axioms RMTFoundations.Fredholm.realHs_continuity_joint_probe
#print axioms RMTFoundations.Fredholm.realOperatorDet_matrix_det_tendsto
#print axioms RMTFoundations.Fredholm.hs_adjoint_other_basis
#print axioms RMTFoundations.Fredholm.hs_square_summable_basis
#print axioms RMTFoundations.Fredholm.hs_square_tsum_basis_eq
#print axioms RMTFoundations.Fredholm.basisProjection
#print axioms RMTFoundations.Fredholm.basisProjection_apply_basis
#print axioms RMTFoundations.Fredholm.basisProjection_tendsto
#print axioms RMTFoundations.Fredholm.basisProjection_comp_hs
#print axioms RMTFoundations.Fredholm.basisProjection_comp_square_distance
#print axioms RMTFoundations.Fredholm.basisProjection_comp_hs_tendsto
#print axioms RMTFoundations.Fredholm.basisProjection_finite_sylvester
#print axioms RMTFoundations.Fredholm.operatorDet_finite_projection
#print axioms RMTFoundations.Fredholm.operatorDet_sylvester_bases
#print axioms RMTFoundations.Fredholm.operatorDet_basis_independent
#print axioms RMTFoundations.Fredholm.realHs_adjoint_other_basis
#print axioms RMTFoundations.Fredholm.realHs_square_summable_basis
#print axioms RMTFoundations.Fredholm.realHs_square_tsum_basis_eq
#print axioms RMTFoundations.Fredholm.realBasisProjection
#print axioms RMTFoundations.Fredholm.realBasisProjection_apply_basis
#print axioms RMTFoundations.Fredholm.realBasisProjection_tendsto
#print axioms RMTFoundations.Fredholm.realBasisProjection_comp_hs
#print axioms RMTFoundations.Fredholm.realBasisProjection_comp_square_distance
#print axioms RMTFoundations.Fredholm.realBasisProjection_comp_hs_tendsto
#print axioms RMTFoundations.Fredholm.realBasisProjection_finite_sylvester
#print axioms RMTFoundations.Fredholm.realOperatorDet_finite_projection
#print axioms RMTFoundations.Fredholm.realOperatorDet_sylvester_bases
#print axioms RMTFoundations.Fredholm.realOperatorDet_basis_independent
#print axioms RMTFoundations.Fredholm.kernelGramMinor
#print axioms RMTFoundations.Fredholm.kernelGramMinor_bound
#print axioms RMTFoundations.Fredholm.kernelGramMinor_aestronglyMeasurable
#print axioms RMTFoundations.Fredholm.kernelGramMinor_integrable
#print axioms RMTFoundations.Fredholm.kernelGramMinor_integral_bound
#print axioms RMTFoundations.Fredholm.kernelFredholmCoeff
#print axioms RMTFoundations.Fredholm.kernelFredholmCoeff_bound
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_absolute
#print axioms RMTFoundations.Fredholm.kernelFredholmCoeff_radius_top
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_entire
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_memLp_entire
#print axioms RMTFoundations.Fredholm.kernelFredholmCoeff_zero
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_zero
#print axioms RMTFoundations.Fredholm.kernel_joint_probe
#print axioms RMTFoundations.Fredholm.det_pair_permutation_sum
#print axioms RMTFoundations.Fredholm.det_product_leibniz
#print axioms RMTFoundations.Fredholm.det_product_integrable
#print axioms RMTFoundations.Fredholm.integral_det_product
#print axioms RMTFoundations.Fredholm.andreief_joint_probe
#print axioms RMTFoundations.Fredholm.matrix_principal_minor_sylvester
#print axioms RMTFoundations.Fredholm.matrix_det_rectangular_principal_minors
#print axioms RMTFoundations.Fredholm.operatorDet_eq_diagonalDet
#print axioms RMTFoundations.Fredholm.operatorDet_diagonal_eq_plemelj
#print axioms RMTFoundations.Fredholm.det_reverse_features_factor
#print axioms RMTFoundations.Fredholm.det_reverse_features_integrable
#print axioms RMTFoundations.Fredholm.integral_det_reverse_features
#print axioms RMTFoundations.Fredholm.finite_feature_coefficient
#print axioms RMTFoundations.Fredholm.polynomial_coeff_tsum
#print axioms RMTFoundations.Fredholm.finite_feature_series
#print axioms RMTFoundations.Fredholm.kernelFredholmCoeff_dominated_tendsto
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_dominated_tendsto
#print axioms RMTFoundations.Fredholm.realBasisProjection_inner
#print axioms RMTFoundations.Fredholm.realBasisProjection_norm_le
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_real_projection
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_eq_realOperatorDet_of_entries
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_eq_realOperatorDet_comp
#print axioms RMTFoundations.Fredholm.kernelFredholmSeries_gram_eq_realOperatorDet_square
#print axioms RMTFoundations.Fredholm.kernelIntegralSeries_eq_gram
#print axioms RMTFoundations.Fredholm.kernelIntegralSeries_eq_realOperatorDet_comp
#print axioms RMTFoundations.Fredholm.kernel_operator_all_binder_probe
#print axioms RMTFoundations.Fredholm.convolutionKernel_eq_gram
#print axioms RMTFoundations.Fredholm.kernelIntegralSeries_convolution_eq_realOperatorDet_comp
#print axioms RMTFoundations.Fredholm.convolution_operator_all_binder_probe
