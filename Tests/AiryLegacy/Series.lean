import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Pow

/-

# Real power series of infinite radius of convergence

## What is proved here

* `summable_seriesTerm`, `seriesSum_zero`: the series converges everywhere and its value at `0`
  is `c 0`;
* `hasEntireCoeffs_mul_nat`, `hasEntireCoeffs_shift`, `hasEntireCoeffs_derivCoeffs`: the class is
  closed under multiplying the coefficients by `n`, under shifting the index, and hence under
  passing to the coefficient sequence `n ↦ (n + 1) * c (n + 1)` of the formally differentiated
  series;
* `hasDerivAt_seriesSum`: **term-by-term differentiation**.  The sum is differentiable at every
  real point with derivative the sum of the differentiated series.  This is obtained from
  mathlib's `hasDerivAt_tsum_of_isPreconnected` on the ball of radius `|x| + 1`.

## What is NOT proved here

* nothing is claimed about the radius of convergence as an `ℝ≥0∞`-valued invariant, and no
  connection is made with `FormalMultilinearSeries.radius`; `HasEntireCoeffs` is used directly.
* real-analyticity (`AnalyticAt`) of `seriesSum` is not proved; only the `HasDerivAt` statement,
  which is what the Airy equation needs.
* no statement about uniqueness of coefficients, Cauchy products, or composition.

-/

namespace RMTFoundations.Airy

/-- `HasEntireCoeffs c` says that the real power series with coefficients `c` converges
absolutely at every real point: `∑ |c n| * r ^ n < ∞` for every `r ≥ 0`. -/
def HasEntireCoeffs (c : ℕ → ℝ /- [definition] -/ ) : Prop := ∀ r : ℝ, 0 ≤ r → Summable fun n => |c n| * r ^ n

/-- The sum of the power series with coefficients `c`. -/
noncomputable def seriesSum (c : ℕ → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ := ∑' n, c n * x ^ n

variable {c : ℕ → ℝ /- [definition] -/ }

theorem summable_abs_seriesTerm (hc : HasEntireCoeffs c /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    Summable fun n => |c n * x ^ n| := by
  refine (hc |x| (abs_nonneg x)).congr fun n => ?_
  rw [abs_mul, abs_pow]

theorem summable_seriesTerm (hc : HasEntireCoeffs c /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    Summable fun n => c n * x ^ n :=
  summable_abs_iff.1 (summable_abs_seriesTerm hc x)

/-- The value of the series at the origin is the constant coefficient. -/
theorem seriesSum_zero (hc : HasEntireCoeffs c /- [standing] -/ ) : seriesSum c 0 = c 0 := by
  have h := (summable_seriesTerm hc 0).tsum_eq_zero_add
  have htail : ∀ n : ℕ, c (n + 1) * (0 : ℝ) ^ (n + 1) = 0 := by
    intro n
    rw [pow_succ, mul_zero, mul_zero]
  rw [seriesSum, h, tsum_congr htail, tsum_zero, add_zero, pow_zero, mul_one]

/-- Multiplying the coefficients by `n` preserves convergence at every point.  This is the
statement that the formally differentiated series has the same (infinite) radius. -/
theorem hasEntireCoeffs_mul_nat (hc : HasEntireCoeffs c /- [standing] -/ ) :
    HasEntireCoeffs fun n => (n : ℝ) * c n := by
  intro r hr
  have hR : (0 : ℝ) < r + 1 := by linarith
  have hS := hc (r + 1) hR.le
  have hq0 : (0 : ℝ) ≤ r / (r + 1) := div_nonneg hr hR.le
  have hq1 : r / (r + 1) < 1 := by
    rw [div_lt_one hR]; linarith
  have htend := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) * (r / (r + 1)) ^ n ≤ 1 :=
    htend.eventually_le_const zero_lt_one
  refine Summable.of_norm_bounded_eventually hS ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  have hpow : (r / (r + 1)) ^ n * (r + 1) ^ n = r ^ n := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero n (ne_of_gt hR)
  have habs : |((n : ℝ) * c n)| * r ^ n = (|c n| * (r + 1) ^ n) * ((n : ℝ) * (r / (r + 1)) ^ n) := by
    rw [abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |c n| * r ^ n
        = |c n| * ((r / (r + 1)) ^ n * (r + 1) ^ n) * (n : ℝ) := by rw [hpow]; ring
      _ = (|c n| * (r + 1) ^ n) * ((n : ℝ) * (r / (r + 1)) ^ n) := by ring
  have hnn : 0 ≤ |((n : ℝ) * c n)| * r ^ n := mul_nonneg (abs_nonneg _) (pow_nonneg hr n)
  have hbase : 0 ≤ |c n| * (r + 1) ^ n := mul_nonneg (abs_nonneg _) (pow_nonneg hR.le n)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, habs]
  calc (|c n| * (r + 1) ^ n) * ((n : ℝ) * (r / (r + 1)) ^ n)
      ≤ (|c n| * (r + 1) ^ n) * 1 := mul_le_mul_of_nonneg_left hn hbase
    _ = |c n| * (r + 1) ^ n := mul_one _

/-- Shifting the index preserves convergence at every point. -/
theorem hasEntireCoeffs_shift (hc : HasEntireCoeffs c /- [standing] -/ ) : HasEntireCoeffs fun n => c (n + 1) := by
  intro r hr
  have hR : (0 : ℝ) < r + 1 := by linarith
  have hS : Summable fun n : ℕ => |c (n + 1)| * (r + 1) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 (hc (r + 1) hR.le)
  have hS' : Summable fun n : ℕ => (r + 1)⁻¹ * (|c (n + 1)| * (r + 1) ^ (n + 1)) :=
    hS.mul_left _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n => ?_) hS'
  have hne : (r + 1) ≠ 0 := ne_of_gt hR
  have heq : (r + 1)⁻¹ * (|c (n + 1)| * (r + 1) ^ (n + 1)) = |c (n + 1)| * (r + 1) ^ n :=
    calc (r + 1)⁻¹ * (|c (n + 1)| * (r + 1) ^ (n + 1))
        = ((r + 1)⁻¹ * (r + 1)) * (|c (n + 1)| * (r + 1) ^ n) := by rw [pow_succ]; ring
      _ = 1 * (|c (n + 1)| * (r + 1) ^ n) := by rw [inv_mul_cancel₀ hne]
      _ = |c (n + 1)| * (r + 1) ^ n := one_mul _
  rw [heq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) n) (abs_nonneg _)

/-- The coefficient sequence of the formally differentiated series. -/
theorem hasEntireCoeffs_derivCoeffs (hc : HasEntireCoeffs c /- [standing] -/ ) :
    HasEntireCoeffs fun n => ((n : ℝ) + 1) * c (n + 1) := by
  have h := hasEntireCoeffs_shift (hasEntireCoeffs_mul_nat hc)
  refine fun r hr => (h r hr).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]

/-- Term-by-term differentiation: the sum of an everywhere-convergent real power series is
differentiable at every point, with derivative the sum of the differentiated series. -/
theorem hasDerivAt_seriesSum (hc : HasEntireCoeffs c /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    HasDerivAt (seriesSum c) (seriesSum (fun n => ((n : ℝ) + 1) * c (n + 1)) x) x := by
  set R : ℝ := |x| + 1 with hRdef
  have hxa : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hmemball : ∀ y : ℝ, y ∈ Metric.ball (0 : ℝ) R → |y| ≤ R := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    exact hy.le
  -- the summable majorant for the differentiated terms on the ball
  have hu : Summable fun n : ℕ => (n : ℝ) * |c n| * R ^ n := by
    refine (hasEntireCoeffs_mul_nat hc R hR0.le).congr fun n => ?_
    rw [abs_mul, Nat.abs_cast]
  have hg : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun z : ℝ => c n * z ^ n) ((n : ℝ) * c n * y ^ (n - 1)) y := by
    intro n y _
    have h := (hasDerivAt_pow n y).const_mul (c n)
    have he : c n * ((n : ℝ) * y ^ (n - 1)) = (n : ℝ) * c n * y ^ (n - 1) := by ring
    rwa [he] at h
  have hg' : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℝ) R,
      ‖(n : ℝ) * c n * y ^ (n - 1)‖ ≤ (n : ℝ) * |c n| * R ^ n := by
    intro n y hy
    have hyR := hmemball y hy
    have h1 : ‖(n : ℝ) * c n * y ^ (n - 1)‖ = (n : ℝ) * |c n| * |y| ^ (n - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast, abs_pow]
    have h2 : |y| ^ (n - 1) ≤ R ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg y) hyR (n - 1)
    have h3 : R ^ (n - 1) ≤ R ^ n := pow_le_pow_right₀ hR1 (Nat.sub_le n 1)
    have h4 : (0 : ℝ) ≤ (n : ℝ) * |c n| := mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
    rw [h1]
    exact mul_le_mul_of_nonneg_left (le_trans h2 h3) h4
  have hzero : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_self]
    exact hR0
  have hxmem : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]
    linarith
  have key := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    ((convex_ball (0 : ℝ) R).isPreconnected) hg hg' hzero (summable_seriesTerm hc 0) hxmem
  -- rewrite the derivative series in shifted form
  have hsummable : Summable fun n : ℕ => (n : ℝ) * c n * x ^ (n - 1) := by
    refine Summable.of_norm_bounded hu fun n => ?_
    exact hg' n x hxmem
  have hshift : ∑' n : ℕ, (n : ℝ) * c n * x ^ (n - 1)
      = seriesSum (fun n => ((n : ℝ) + 1) * c (n + 1)) x := by
    rw [hsummable.tsum_eq_zero_add]
    have hzero0 : ((0 : ℕ) : ℝ) * c 0 * x ^ (0 - 1) = 0 := by
      rw [Nat.cast_zero, zero_mul, zero_mul]
    rw [hzero0, zero_add, seriesSum]
    refine tsum_congr fun n => ?_
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [← hshift]
  exact key

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.HasEntireCoeffs
#print axioms RMTFoundations.Airy.seriesSum
#print axioms RMTFoundations.Airy.summable_abs_seriesTerm
#print axioms RMTFoundations.Airy.summable_seriesTerm
#print axioms RMTFoundations.Airy.seriesSum_zero
#print axioms RMTFoundations.Airy.hasEntireCoeffs_mul_nat
#print axioms RMTFoundations.Airy.hasEntireCoeffs_shift
#print axioms RMTFoundations.Airy.hasEntireCoeffs_derivCoeffs
#print axioms RMTFoundations.Airy.hasDerivAt_seriesSum
