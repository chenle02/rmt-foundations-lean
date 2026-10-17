import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import RMTFoundations.Concentration.Chernoff

/-!
# Bernstein's inequality

Mathlib has no inequality of Bernstein or Bennett type: its concentration
material is the sub-Gaussian / Hoeffding family, which is insensitive to the
variance.  This file builds the variance-sensitive layer.

The shape of the argument is the classical one.  A centred random variable
bounded by `M` with second moment at most `v` has

`mgf X μ t ≤ exp (v * t ^ 2 / (2 * (1 - M * t / 3)))`  for `0 ≤ t`, `M * t < 3`,

and optimising the Chernoff bound over `t` turns that into

`ℙ(X ≥ ε) ≤ exp (- ε ^ 2 / (2 * (v + M * ε / 3)))`.

## What is proved here

* `exp_le_one_add_add_sq_div` — the pointwise real inequality
  `exp u ≤ 1 + u + u ^ 2 / (2 * (1 - b / 3))` for `|u| ≤ b < 3`.  This is the
  analytic core; it is proved from the exponential series and the elementary
  bound `2 * 3 ^ n ≤ (n + 2)!`.
* `two_mul_three_pow_le_factorial` — that factorial bound.
* `HasBernsteinMGF` — the predicate "`X` has a Bernstein-type mgf bound with
  variance proxy `v` and range proxy `M`", modelled on mathlib's
  `ProbabilityTheory.HasSubgaussianMGF`.
* `HasBernsteinMGF.measure_ge_le` — **Bernstein's inequality** in the stated
  form, for `0 < v` and `0 ≤ ε`.
* `HasBernsteinMGF.measure_le_le`, `HasBernsteinMGF.measure_abs_ge_le` — the
  lower-tail and two-sided forms.
* `HasBernsteinMGF.of_hasSubgaussianMGF` — a sub-Gaussian variable is Bernstein
  with `M = 0`; the Bernstein bound then specialises to the sub-Gaussian one.
* `hasBernsteinMGF_of_abs_le` — the hypothesis is discharged for a centred
  variable with `|X| ≤ M` a.e. and `μ[X ^ 2] ≤ v`.
* `HasBernsteinMGF.add_of_indepFun`, `HasBernsteinMGF.sum_of_iIndepFun` —
  additivity of the variance proxy under independence, with a common `M`.
* `measure_sum_ge_le_bernstein` — the headline: for independent centred
  variables bounded by `M` with variances summing to at most `v`,
  `ℙ(∑ X i ≥ ε) ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3)))`.

## What is NOT proved here

* No Bennett inequality.  The sharper mgf bound
  `exp (v * (exp (M * t) - 1 - M * t) / M ^ 2)` (which needs the monotonicity of
  `u ↦ (exp u - 1 - u) / u ^ 2`) is not established, so the Bennett form
  `exp (-(v / M ^ 2) * h (M * ε / v))` is absent.
* No matching *lower* bound on the probability: everything here is a one-sided
  estimate, and there is no claim that the constants `2` and `3` are optimal.
  (`HasBernsteinMGF.measure_le_le` bounds the lower *tail*; it is still an upper
  bound on a probability.)
* `HasBernsteinMGF` constrains the mgf only on `0 ≤ t` with `M * t < 3`.  It
  therefore says nothing about the lower tail on its own; the lower-tail
  statement below is about `-X`, and the caller must supply that hypothesis.
* No Hanson–Wright inequality, no matrix Bernstein, no McDiarmid.
* `hasBernsteinMGF_of_abs_le` requires a two-sided a.e. bound `|X| ≤ M`.  The
  one-sided version (`X ≤ M` only), which is what Bennett actually needs, is
  not proved.
-/

namespace RMTFoundations.Concentration

open MeasureTheory Real Finset
open scoped Nat
open ProbabilityTheory

variable {Ω : Type* /- [definition] -/ } {mΩ : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ } {X : Ω → ℝ /- [definition] -/ } {t ε v M : ℝ /- [definition] -/ }

section PointwiseExp

/-- `2 * 3 ^ n ≤ (n + 2)!`.  This is the elementary fact behind the `3` in the
Bernstein denominator: the exponential tail `∑_{k ≥ 2} u ^ k / k !` is dominated
by a geometric series of ratio `|u| / 3`. -/
theorem two_mul_three_pow_le_factorial (n : ℕ /- [definition] -/ ) : 2 * 3 ^ n ≤ (n + 2)! := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hstep : (n + 3)! = (n + 3) * (n + 2)! := Nat.factorial_succ (n + 2)
    calc 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
      _ ≤ (n + 3) * (n + 2)! := Nat.mul_le_mul (by omega) ih
      _ = (n + 3)! := hstep.symm

/-- The pointwise inequality at the heart of Bernstein's inequality:
for `|u| ≤ b` with `0 ≤ b < 3`,
`exp u ≤ 1 + u + u ^ 2 / (2 * (1 - b / 3))`.

Compare `Real.add_one_le_exp`, which is the reverse inequality without the
quadratic term.  Mathlib has no bound of this shape. -/
theorem exp_le_one_add_add_sq_div {b u : ℝ /- [definition] -/ } (hb : 0 ≤ b /- [standing] -/ ) (hb3 : b < 3 /- [standing] -/ ) (hu : |u| ≤ b /- [standing] -/ ) :
    exp u ≤ 1 + u + u ^ 2 / (2 * (1 - b / 3)) := by
  have hden : 0 < 1 - b / 3 := by linarith
  have hr : (0 : ℝ) ≤ b / 3 := by linarith
  have hr1 : b / 3 < 1 := by linarith
  -- the exponential series
  have hsum : Summable fun n : ℕ ↦ u ^ n / n ! := Real.summable_pow_div_factorial u
  have hexp : exp u = ∑' n : ℕ, u ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- split off the first two terms
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfirst : ∑ i ∈ range 2, u ^ i / (i ! : ℝ) = 1 + u := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  -- the tail is summable, and dominated by a geometric series
  have htail : Summable fun n : ℕ ↦ u ^ (n + 2) / ((n + 2)! : ℝ) :=
    (summable_nat_add_iff 2).2 hsum
  have hgeom : Summable fun n : ℕ ↦ u ^ 2 / 2 * (b / 3) ^ n :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ n : ℕ, u ^ (n + 2) / ((n + 2)! : ℝ) ≤ u ^ 2 / 2 * (b / 3) ^ n := by
    intro n
    have hfac : (2 : ℝ) * 3 ^ n ≤ ((n + 2)! : ℝ) := by
      have := two_mul_three_pow_le_factorial n
      have hc : ((2 * 3 ^ n : ℕ) : ℝ) ≤ (((n + 2)! : ℕ) : ℝ) := Nat.cast_le.2 this
      push_cast at hc
      exact hc
    have hfacpos : (0 : ℝ) < ((n + 2)! : ℝ) := by
      have : 0 < (n + 2)! := Nat.factorial_pos _
      exact_mod_cast this
    have habs : u ^ (n + 2) ≤ u ^ 2 * b ^ n := by
      have h1 : u ^ (n + 2) ≤ |u ^ (n + 2)| := le_abs_self _
      have h2 : |u ^ (n + 2)| = |u| ^ 2 * |u| ^ n := by
        rw [abs_pow]; ring
      have h3 : |u| ^ 2 = u ^ 2 := sq_abs u
      have h4 : |u| ^ n ≤ b ^ n := pow_le_pow_left₀ (abs_nonneg u) hu n
      have h5 : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
      calc u ^ (n + 2) ≤ |u| ^ 2 * |u| ^ n := by rw [← h2]; exact h1
        _ = u ^ 2 * |u| ^ n := by rw [h3]
        _ ≤ u ^ 2 * b ^ n := by gcongr
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    calc u ^ (n + 2) / ((n + 2)! : ℝ)
        ≤ (u ^ 2 * b ^ n) / ((n + 2)! : ℝ) := by gcongr
      _ ≤ (u ^ 2 * b ^ n) / (2 * 3 ^ n) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = u ^ 2 / 2 * (b / 3) ^ n := by
          rw [div_pow, div_mul_div_comm]
  have hle : ∑' n : ℕ, u ^ (n + 2) / ((n + 2)! : ℝ) ≤ ∑' n : ℕ, u ^ 2 / 2 * (b / 3) ^ n :=
    htail.tsum_le_tsum hterm hgeom
  have hgval : ∑' n : ℕ, u ^ 2 / 2 * (b / 3) ^ n = u ^ 2 / 2 * (1 - b / 3)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]
  have hfinal : u ^ 2 / 2 * (1 - b / 3)⁻¹ = u ^ 2 / (2 * (1 - b / 3)) := by
    rw [inv_eq_one_div, div_mul_div_comm, mul_one]
  rw [hexp, ← hsplit, hfirst]
  rw [hgval] at hle
  rw [hfinal] at hle
  linarith

end PointwiseExp

section Definition

/-- `X` has a **Bernstein-type moment generating function** with variance proxy
`v` and range proxy `M` if, on the interval `0 ≤ t` with `M * t < 3`,
`mgf X μ t ≤ exp (v * t ^ 2 / (2 * (1 - M * t / 3)))`.

Modelled on `ProbabilityTheory.HasSubgaussianMGF`, which is the special case
`M = 0`.  Unlike the sub-Gaussian predicate this constrains only the right
half-line, because that is all Bernstein's inequality needs and all that a
one-sided moment bound gives. -/
structure HasBernsteinMGF (X : Ω → ℝ /- [definition] -/ ) (v M : ℝ /- [definition] -/ ) (μ : Measure Ω /- [definition] -/ ) : Prop where
  variance_nonneg : 0 ≤ v
  range_nonneg : 0 ≤ M
  integrable_exp_mul : ∀ t : ℝ, 0 ≤ t → M * t < 3 → Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, 0 ≤ t → M * t < 3 → mgf X μ t ≤ exp (v * t ^ 2 / (2 * (1 - M * t / 3)))

end Definition

section TailBound

/-- **Bernstein's inequality.**  If `X` has a Bernstein mgf bound with positive
variance proxy `v` and range proxy `M`, then
`ℙ(X ≥ ε) ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3)))`. -/
theorem HasBernsteinMGF.measure_ge_le [IsFiniteMeasure μ /- [standing] -/ ] (h : HasBernsteinMGF X v M μ /- [standing] -/ )
    (hv : 0 < v /- [standing] -/ ) (hε : 0 ≤ ε /- [standing] -/ ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3))) := by
  have hMε : 0 ≤ M * ε / 3 := by
    have := h.range_nonneg
    positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = v + M * ε / 3 := ⟨_, rfl⟩
  rw [← hD]
  have hDpos : 0 < D := by rw [hD]; linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / D := ⟨_, rfl⟩
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have hMt : M * t < 3 := by
    rw [ht, mul_div_assoc', div_lt_iff₀ hDpos, hD]
    linarith
  have hden : 1 - M * t / 3 = v / D := by
    have h1 : M * t / 3 = M * ε / 3 / D := by rw [ht]; ring
    have h2 : D - M * ε / 3 = v := by rw [hD]; ring
    rw [h1, ← h2, sub_div, div_self hDne]
  have hdenpos : 0 < 1 - M * t / 3 := by rw [hden]; positivity
  have hvne : v ≠ 0 := ne_of_gt hv
  have hexpo : -t * ε + v * t ^ 2 / (2 * (1 - M * t / 3)) = -ε ^ 2 / (2 * D) := by
    rw [hden, ht]
    field_simp
    ring
  calc μ.real {ω | ε ≤ X ω}
      ≤ exp (-t * ε) * mgf X μ t :=
        measure_ge_le_exp_mul_mgf ε htnn (h.integrable_exp_mul t htnn hMt)
    _ ≤ exp (-t * ε) * exp (v * t ^ 2 / (2 * (1 - M * t / 3))) := by
        have := h.mgf_le t htnn hMt
        have hpos : (0 : ℝ) < exp (-t * ε) := exp_pos _
        exact mul_le_mul_of_nonneg_left this hpos.le
    _ = exp (-t * ε + v * t ^ 2 / (2 * (1 - M * t / 3))) := (exp_add _ _).symm
    _ = exp (-ε ^ 2 / (2 * D)) := by rw [hexpo]

/-- **Bernstein's inequality**, lower tail: stated for `-X`, since
`HasBernsteinMGF` is a one-sided hypothesis. -/
theorem HasBernsteinMGF.measure_le_le [IsFiniteMeasure μ /- [standing] -/ ]
    (h : HasBernsteinMGF (fun ω ↦ -X ω) v M μ /- [standing] -/ ) (hv : 0 < v /- [standing] -/ ) (hε : 0 ≤ ε /- [standing] -/ ) :
    μ.real {ω | X ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3))) := by
  have hset : {ω | X ω ≤ -ε} = {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hω <;> linarith
  rw [hset]
  exact h.measure_ge_le hv hε

/-- **Bernstein's inequality**, two-sided. -/
theorem HasBernsteinMGF.measure_abs_ge_le [IsFiniteMeasure μ /- [standing] -/ ]
    (h : HasBernsteinMGF X v M μ /- [standing] -/ ) (h' : HasBernsteinMGF (fun ω ↦ -X ω) v M μ /- [definition] -/ )
    (hv : 0 < v /- [standing] -/ ) (hε : 0 ≤ ε /- [standing] -/ ) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * (v + M * ε / 3))) := by
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | X ω ≤ -ε} := by
    intro ω hω
    rcases abs_cases (X ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · refine Or.inl ?_
      rw [Set.mem_setOf_eq]
      rw [Set.mem_setOf_eq, h1] at hω
      exact hω
    · refine Or.inr ?_
      rw [Set.mem_setOf_eq]
      rw [Set.mem_setOf_eq, h1] at hω
      linarith
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | X ω ≤ -ε}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | X ω ≤ -ε} := measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3))) + exp (-ε ^ 2 / (2 * (v + M * ε / 3))) := by
        gcongr
        · exact h.measure_ge_le hv hε
        · exact h'.measure_le_le hv hε
    _ = 2 * exp (-ε ^ 2 / (2 * (v + M * ε / 3))) := by ring

end TailBound

section SubGaussian

/-- A sub-Gaussian variable is Bernstein with range proxy `M = 0`: the two mgf
bounds then coincide.  This identifies `HasSubgaussianMGF` as the `M = 0`
boundary of `HasBernsteinMGF`. -/
theorem HasBernsteinMGF.of_hasSubgaussianMGF {c : NNReal /- [definition] -/ }
    (h : HasSubgaussianMGF X c μ /- [standing] -/ ) : HasBernsteinMGF X (c : ℝ) 0 μ where
  variance_nonneg := c.coe_nonneg
  range_nonneg := le_rfl
  integrable_exp_mul t _ _ := h.integrable_exp_mul t
  mgf_le t _ _ := by
    have hb := h.mgf_le t
    have heq : (c : ℝ) * t ^ 2 / (2 * (1 - 0 * t / 3)) = (c : ℝ) * t ^ 2 / 2 := by
      rw [zero_mul, zero_div, sub_zero, mul_one]
    rw [heq]
    exact hb

end SubGaussian

section FromBoundedness

/-- A centred random variable with `|X| ≤ M` almost everywhere and second moment
at most `v` has a Bernstein mgf bound with proxies `v` and `M`.

This is where `exp_le_one_add_add_sq_div` is used: no exchange of integral and
infinite sum is needed, because the series bound is applied pointwise before
integrating. -/
theorem hasBernsteinMGF_of_abs_le [IsProbabilityMeasure μ /- [standing] -/ ] (hM : 0 ≤ M /- [standing] -/ )
    (hX : AEMeasurable X μ /- [standing] -/ ) (hbdd : ∀ᵐ ω ∂μ, |X ω| ≤ M /- [standing] -/ )
    (hmean : ∫ ω, X ω ∂μ = 0 /- [standing] -/ ) (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ v /- [standing] -/ ) :
    HasBernsteinMGF X v M μ := by
  have hXint : Integrable X μ := by
    refine Integrable.of_mem_Icc (-M) M hX ?_
    filter_upwards [hbdd] with ω hω
    exact ⟨neg_le_of_abs_le hω, le_of_abs_le hω⟩
  have hXsq : Integrable (fun ω ↦ X ω ^ 2) μ := by
    refine Integrable.of_mem_Icc 0 (M ^ 2) (hX.pow_const 2) ?_
    filter_upwards [hbdd] with ω hω
    refine ⟨sq_nonneg _, ?_⟩
    have h1 : |X ω| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hω 2
    rwa [sq_abs] at h1
  have hv0 : 0 ≤ v := by
    refine le_trans ?_ hvar
    exact integral_nonneg fun ω ↦ sq_nonneg _
  refine ⟨hv0, hM, ?_, ?_⟩
  · intro t ht _
    refine integrable_exp_mul_of_le t M ht hX ?_
    filter_upwards [hbdd] with ω hω
    exact le_of_abs_le hω
  · intro t ht hMt
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = M * t := ⟨_, rfl⟩
    have hbnn : 0 ≤ b := by rw [hb]; positivity
    have hMt' : b < 3 := by rw [hb]; exact hMt
    have hden : 0 < 1 - b / 3 := by linarith
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (2 * (1 - b / 3)) := ⟨_, rfl⟩
    have hcnn : 0 ≤ c := by rw [hc]; positivity
    have hptwise : ∀ᵐ ω ∂μ, exp (t * X ω) ≤ 1 + t * X ω + c * (t * X ω) ^ 2 := by
      filter_upwards [hbdd] with ω hω
      have habs : |t * X ω| ≤ b := by
        rw [abs_mul, abs_of_nonneg ht, hb]
        calc t * |X ω| ≤ t * M := by gcongr
          _ = M * t := by ring
      have hpw := exp_le_one_add_add_sq_div hbnn hMt' habs
      rw [hc]
      calc exp (t * X ω) ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - b / 3)) := hpw
        _ = 1 + t * X ω + 1 / (2 * (1 - b / 3)) * (t * X ω) ^ 2 := by ring
    have hrhs : Integrable (fun ω ↦ 1 + t * X ω + c * (t * X ω) ^ 2) μ := by
      have h1 : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const 1
      have h2 : Integrable (fun ω ↦ t * X ω) μ := hXint.const_mul t
      have h3 : Integrable (fun ω ↦ c * (t * X ω) ^ 2) μ := by
        have : Integrable (fun ω ↦ c * t ^ 2 * X ω ^ 2) μ := hXsq.const_mul (c * t ^ 2)
        refine this.congr ?_
        filter_upwards with ω
        ring
      exact (h1.add h2).add h3
    have hlhs : Integrable (fun ω ↦ exp (t * X ω)) μ := by
      refine integrable_exp_mul_of_le t M ht hX ?_
      filter_upwards [hbdd] with ω hω
      exact le_of_abs_le hω
    have hint : mgf X μ t ≤ ∫ ω, (1 + t * X ω + c * (t * X ω) ^ 2) ∂μ :=
      integral_mono_ae hlhs hrhs hptwise
    have hcalc : ∫ ω, (1 + t * X ω + c * (t * X ω) ^ 2) ∂μ
        = 1 + c * t ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
      have h1 : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const 1
      have h2 : Integrable (fun ω ↦ t * X ω) μ := hXint.const_mul t
      have h3 : Integrable (fun ω ↦ c * t ^ 2 * X ω ^ 2) μ := hXsq.const_mul (c * t ^ 2)
      have heq : (fun ω ↦ 1 + t * X ω + c * (t * X ω) ^ 2)
          = fun ω ↦ ((1 : ℝ) + t * X ω) + c * t ^ 2 * X ω ^ 2 := by
        funext ω
        ring
      have e1 : ∫ ω, ((1 : ℝ) + t * X ω) + c * t ^ 2 * X ω ^ 2 ∂μ
          = (∫ ω, ((1 : ℝ) + t * X ω) ∂μ) + ∫ ω, c * t ^ 2 * X ω ^ 2 ∂μ :=
        integral_add (h1.add h2) h3
      have e2 : ∫ ω, ((1 : ℝ) + t * X ω) ∂μ
          = (∫ _ω, (1 : ℝ) ∂μ) + ∫ ω, t * X ω ∂μ := integral_add h1 h2
      rw [heq, e1, e2, integral_const, integral_const_mul, integral_const_mul, hmean,
        probReal_univ]
      ring
    have hfin : 1 + c * t ^ 2 * ∫ ω, X ω ^ 2 ∂μ ≤ 1 + c * t ^ 2 * v := by
      have hct : 0 ≤ c * t ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hvar hct]
    have hexp : 1 + c * t ^ 2 * v ≤ exp (v * t ^ 2 / (2 * (1 - b / 3))) := by
      have hlin := Real.add_one_le_exp (c * t ^ 2 * v)
      have hdne : (2 : ℝ) * (1 - b / 3) ≠ 0 := by positivity
      have heq : c * t ^ 2 * v = v * t ^ 2 / (2 * (1 - b / 3)) := by
        rw [hc]
        field_simp
      rw [← heq]
      linarith
    calc mgf X μ t ≤ ∫ ω, (1 + t * X ω + c * (t * X ω) ^ 2) ∂μ := hint
      _ = 1 + c * t ^ 2 * ∫ ω, X ω ^ 2 ∂μ := hcalc
      _ ≤ 1 + c * t ^ 2 * v := hfin
      _ ≤ exp (v * t ^ 2 / (2 * (1 - b / 3))) := hexp
      _ = exp (v * t ^ 2 / (2 * (1 - M * t / 3))) := by rw [hb]

end FromBoundedness


section Independence

/-- The zero random variable is Bernstein with both proxies `0`. -/
theorem hasBernsteinMGF_zero [IsProbabilityMeasure μ /- [standing] -/ ] (hM : 0 ≤ M /- [standing] -/ ) :
    HasBernsteinMGF (fun _ : Ω ↦ (0 : ℝ)) 0 M μ where
  variance_nonneg := le_rfl
  range_nonneg := hM
  integrable_exp_mul t _ _ := by
    have heq : (fun _ : Ω ↦ exp (t * (0 : ℝ))) = fun _ : Ω ↦ (1 : ℝ) := by
      funext ω
      rw [mul_zero, Real.exp_zero]
    rw [heq]
    exact integrable_const 1
  mgf_le t _ _ := by
    have hm : mgf (fun _ : Ω ↦ (0 : ℝ)) μ t = 1 := by
      rw [mgf_const, mul_zero, Real.exp_zero]
    rw [hm, zero_mul, zero_div, Real.exp_zero]

/-- The variance proxies add under independence, the range proxy being common.
This is the Bernstein analogue of
`ProbabilityTheory.HasSubgaussianMGF.add_of_indepFun`. -/
theorem HasBernsteinMGF.add_of_indepFun {Y : Ω → ℝ /- [definition] -/ } {v₁ v₂ : ℝ /- [definition] -/ }
    (hX : HasBernsteinMGF X v₁ M μ /- [standing] -/ ) (hY : HasBernsteinMGF Y v₂ M μ /- [standing] -/ )
    (hindep : IndepFun X Y μ /- [standing] -/ ) :
    HasBernsteinMGF (fun ω ↦ X ω + Y ω) (v₁ + v₂) M μ where
  variance_nonneg := add_nonneg hX.variance_nonneg hY.variance_nonneg
  range_nonneg := hX.range_nonneg
  integrable_exp_mul t ht hMt := by
    have h1 := hX.integrable_exp_mul t ht hMt
    have h2 := hY.integrable_exp_mul t ht hMt
    have hi : IndepFun (fun ω ↦ exp (t * X ω)) (fun ω ↦ exp (t * Y ω)) μ :=
      hindep.comp (measurable_id.const_mul t).exp (measurable_id.const_mul t).exp
    have heq : (fun ω ↦ exp (t * (X ω + Y ω)))
        = fun ω ↦ exp (t * X ω) * exp (t * Y ω) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hi.integrable_mul h1 h2
  mgf_le t ht hMt := by
    have hsum : mgf (fun ω ↦ X ω + Y ω) μ t = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t ht hMt).1 (hY.integrable_exp_mul t ht hMt).1
    have h1 : mgf X μ t * mgf Y μ t
        ≤ exp (v₁ * t ^ 2 / (2 * (1 - M * t / 3)))
          * exp (v₂ * t ^ 2 / (2 * (1 - M * t / 3))) :=
      mul_le_mul (hX.mgf_le t ht hMt) (hY.mgf_le t ht hMt) mgf_nonneg (exp_pos _).le
    have h2 : exp (v₁ * t ^ 2 / (2 * (1 - M * t / 3)))
          * exp (v₂ * t ^ 2 / (2 * (1 - M * t / 3)))
        = exp ((v₁ + v₂) * t ^ 2 / (2 * (1 - M * t / 3))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsum, ← h2]
    exact h1

/-- Variance proxies add over a finite family of independent variables sharing a
range proxy `M`. -/
theorem HasBernsteinMGF.sum_of_iIndepFun {ι : Type* /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ]
    {Y : ι → Ω → ℝ /- [definition] -/ } {vv : ι → ℝ /- [definition] -/ } (h_indep : iIndepFun Y μ /- [standing] -/ ) (h_meas : ∀ i, Measurable (Y i)  /- [standing] -/ )
    (hM : 0 ≤ M /- [standing] -/ ) {s : Finset ι /- [definition] -/ } (h_bern : ∀ i ∈ s, HasBernsteinMGF (Y i) (vv i) M μ /- [standing] -/ ) :
    HasBernsteinMGF (fun ω ↦ ∑ i ∈ s, Y i ω) (∑ i ∈ s, vv i) M μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact hasBernsteinMGF_zero hM
  | insert i s his ih =>
      have hrec : HasBernsteinMGF (fun ω ↦ ∑ j ∈ s, Y j ω) (∑ j ∈ s, vv j) M μ :=
        ih fun j hj ↦ h_bern j (Finset.mem_insert_of_mem hj)
      have hindep' : IndepFun (Y i) (fun ω ↦ ∑ j ∈ s, Y j ω) μ := by
        have h := (h_indep.indepFun_finsetSum_of_notMem h_meas his).symm
        have heq : (∑ j ∈ s, Y j) = fun ω ↦ ∑ j ∈ s, Y j ω := by
          funext ω
          rw [Finset.sum_apply]
        rwa [heq] at h
      have hadd := (h_bern i (Finset.mem_insert_self i s)).add_of_indepFun hrec hindep'
      have hfun : (fun ω ↦ ∑ j ∈ insert i s, Y j ω)
          = fun ω ↦ Y i ω + ∑ j ∈ s, Y j ω := by
        funext ω
        rw [Finset.sum_insert his]
      rw [hfun, Finset.sum_insert his]
      exact hadd

/-- **Bernstein's inequality for a sum of independent bounded centred variables.**
If the `Y i`, `i ∈ s`, are independent, centred, bounded in absolute value by
`M`, and have second moments summing to at most `∑ i ∈ s, vv i =: v > 0`, then
`ℙ(∑ Y i ≥ ε) ≤ exp (-ε ^ 2 / (2 * (v + M * ε / 3)))`. -/
theorem measure_sum_ge_le_bernstein {ι : Type* /- [definition] -/ } [IsProbabilityMeasure μ /- [standing] -/ ]
    {Y : ι → Ω → ℝ /- [definition] -/ } {vv : ι → ℝ /- [definition] -/ } {s : Finset ι /- [definition] -/ }
    (h_indep : iIndepFun Y μ /- [standing] -/ ) (h_meas : ∀ i, Measurable (Y i)  /- [standing] -/ ) (hM : 0 ≤ M /- [standing] -/ )
    (hbdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ M /- [standing] -/ )
    (hmean : ∀ i ∈ s, ∫ ω, Y i ω ∂μ = 0 /- [standing] -/ )
    (hvar : ∀ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ ≤ vv i /- [standing] -/ )
    (hv : 0 < ∑ i ∈ s, vv i /- [standing] -/ ) (hε : 0 ≤ ε /- [standing] -/ ) :
    μ.real {ω | ε ≤ ∑ i ∈ s, Y i ω}
      ≤ exp (-ε ^ 2 / (2 * ((∑ i ∈ s, vv i) + M * ε / 3))) := by
  have hb : ∀ i ∈ s, HasBernsteinMGF (Y i) (vv i) M μ := fun i hi ↦
    hasBernsteinMGF_of_abs_le hM (h_meas i).aemeasurable (hbdd i hi) (hmean i hi) (hvar i hi)
  exact (HasBernsteinMGF.sum_of_iIndepFun h_indep h_meas hM hb).measure_ge_le hv hε

end Independence

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.two_mul_three_pow_le_factorial
#print axioms RMTFoundations.Concentration.exp_le_one_add_add_sq_div
#print axioms RMTFoundations.Concentration.HasBernsteinMGF
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.measure_ge_le
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.measure_le_le
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.measure_abs_ge_le
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.of_hasSubgaussianMGF
#print axioms RMTFoundations.Concentration.hasBernsteinMGF_of_abs_le
#print axioms RMTFoundations.Concentration.hasBernsteinMGF_zero
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.add_of_indepFun
#print axioms RMTFoundations.Concentration.HasBernsteinMGF.sum_of_iIndepFun
#print axioms RMTFoundations.Concentration.measure_sum_ge_le_bernstein
