import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Moments of the semicircle law

The semicircle law on `[-2, 2]` has density `√(4 - x ^ 2) / (2 * π)`.  Its
moments are the input to the moment method: the odd ones vanish and the `2k`-th
one is `catalan k`.  Mathlib has neither the measure nor its moments.

Here the moments are taken in the most elementary possible form, as an interval
integral, so that nothing depends on constructing the measure itself.

## What is proved here

* `semicircleMoment` — the definition
  `(1 / (2 * π)) * ∫ x in (-2)..2, x ^ m * √(4 - x ^ 2)`.
* `integral_sqrt_four_sub_sq` — the total mass integral
  `∫ x in (-2)..2, √(4 - x ^ 2) = 2 * π`, obtained from mathlib's
  `integral_sqrt_one_sub_sq` by rescaling.
* `semicircleMoment_zero` — the normalisation `semicircleMoment 0 = 1`, which
  is `catalan 0`; in particular the density above really is a probability
  density.
* `semicircleMoment_odd` — **the odd moments vanish**:
  `semicircleMoment (2 * m + 1) = 0`, by the symmetry `x ↦ -x`.

* `sqrt_four_sub_two_mul_sq`, `integral_pow_mul_sqrt_one_sub_sq`,
  `semicircleMoment_eq` — the rescaling `x = 2 u` and the substitution
  `u = sin θ`, reducing every moment to `∫ sin ^ m * cos ^ 2` on `[-π/2, π/2]`.
* `integral_sin_pow_symm`, `integral_sin_pow_mul_cos_sq` — Wallis' recursion on
  the symmetric interval, where the boundary terms vanish.
* `catalan_succ_mul` — the two-term recursion
  `(k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k`, from mathlib's
  `succ_mul_catalan_eq_centralBinom` and `Nat.succ_mul_centralBinom_succ`.
  Mathlib states only the convolution recursion `catalan_succ`.
* `semicircleMoment_two_mul` — **the even moments are the Catalan numbers**:
  `semicircleMoment (2 * k) = catalan k`.

## What is NOT proved here

* No semicircle *measure* is constructed, so there is no statement about a
  probability measure, its Stieltjes transform, or its support; the moments here
  are bare interval integrals.
* No connection is made to `nonCrossingPairings` in the sibling file: the fact
  that `catalan k` *also* counts non-crossing pair partitions of `2 k` points is
  not proved there, so the two `catalan k` here and there are not linked by any
  theorem.
* Nothing about random matrices: no `E [tr (H ^ k)]` expansion, no convergence
  of empirical spectral measures, no semicircle law.
-/

namespace RMTFoundations.Concentration

open Real intervalIntegral

/-- The `m`-th moment of the semicircle law on `[-2, 2]`, written as an
elementary interval integral against the density `√(4 - x ^ 2) / (2 * π)`. -/
noncomputable def semicircleMoment (m : ℕ /- [definition] -/ ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-2 : ℝ)..2, x ^ m * √(4 - x ^ 2)

/-- The semicircle density integrates to `2 * π` before normalisation.  This is
mathlib's `integral_sqrt_one_sub_sq` rescaled by `2`. -/
theorem integral_sqrt_four_sub_sq : ∫ x in (-2 : ℝ)..2, √(4 - x ^ 2) = 2 * π := by
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hpt : ∀ u : ℝ, √(4 - (2 * u) ^ 2) = 2 * √(1 - u ^ 2) := by
    intro u
    have h4 : (4 : ℝ) - (2 * u) ^ 2 = 4 * (1 - u ^ 2) := by ring
    rw [h4, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  have hsm := smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := (1 : ℝ))
    (f := fun y : ℝ ↦ √(4 - y ^ 2)) 2
  rw [show (2 : ℝ) * (-1) = -2 by norm_num, show (2 : ℝ) * 1 = 2 by norm_num] at hsm
  have hinner : ∫ u in (-1 : ℝ)..1, √(4 - (2 * u) ^ 2) = π := by
    have hfun : ∫ u in (-1 : ℝ)..1, √(4 - (2 * u) ^ 2)
        = ∫ u in (-1 : ℝ)..1, 2 * √(1 - u ^ 2) :=
      integral_congr fun u _ ↦ hpt u
    rw [hfun, integral_const_mul, integral_sqrt_one_sub_sq]
    ring
  rw [hinner] at hsm
  rw [← hsm, smul_eq_mul]

/-- The semicircle law is a probability law: its zeroth moment is `1`, which is
`catalan 0`. -/
theorem semicircleMoment_zero : semicircleMoment 0 = catalan 0 := by
  rw [catalan_zero, Nat.cast_one, semicircleMoment]
  have hfun : ∫ x in (-2 : ℝ)..2, x ^ 0 * √(4 - x ^ 2) = ∫ x in (-2 : ℝ)..2, √(4 - x ^ 2) :=
    integral_congr fun x _ ↦ by rw [pow_zero, one_mul]
  rw [hfun, integral_sqrt_four_sub_sq]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The odd moments of the semicircle law vanish.**  The integrand is an odd
function on a symmetric interval. -/
theorem semicircleMoment_odd (m : ℕ /- [definition] -/ ) : semicircleMoment (2 * m + 1) = 0 := by
  have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
  have key : (∫ x in (-2 : ℝ)..2, x ^ (2 * m + 1) * √(4 - x ^ 2))
      = -∫ x in (-2 : ℝ)..2, x ^ (2 * m + 1) * √(4 - x ^ 2) := by
    have hcn : (∫ x in (-2 : ℝ)..2, (-x) ^ (2 * m + 1) * √(4 - (-x) ^ 2))
        = ∫ x in (-(2 : ℝ))..(-(-2 : ℝ)), x ^ (2 * m + 1) * √(4 - x ^ 2) :=
      integral_comp_neg (f := fun y : ℝ ↦ y ^ (2 * m + 1) * √(4 - y ^ 2))
    rw [neg_neg] at hcn
    calc (∫ x in (-2 : ℝ)..2, x ^ (2 * m + 1) * √(4 - x ^ 2))
        = ∫ x in (-2 : ℝ)..2, (-x) ^ (2 * m + 1) * √(4 - (-x) ^ 2) := hcn.symm
      _ = ∫ x in (-2 : ℝ)..2, -(x ^ (2 * m + 1) * √(4 - x ^ 2)) := by
          refine integral_congr fun x _ ↦ ?_
          rw [hodd.neg_pow, neg_sq]
          ring
      _ = -∫ x in (-2 : ℝ)..2, x ^ (2 * m + 1) * √(4 - x ^ 2) := integral_neg
  have hzero : (∫ x in (-2 : ℝ)..2, x ^ (2 * m + 1) * √(4 - x ^ 2)) = 0 := by linarith
  rw [semicircleMoment, hzero, mul_zero]


section EvenMoments

/-- `√(4 - (2 u) ^ 2) = 2 * √(1 - u ^ 2)`: the rescaling used to pass from the
interval `[-2, 2]` to `[-1, 1]`. -/
theorem sqrt_four_sub_two_mul_sq (u : ℝ /- [definition] -/ ) : √(4 - (2 * u) ^ 2) = 2 * √(1 - u ^ 2) := by
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h4 : (4 : ℝ) - (2 * u) ^ 2 = 4 * (1 - u ^ 2) := by ring
  rw [h4, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]

/-- The substitution `u = sin θ` on `[-1, 1]`. -/
theorem integral_pow_mul_sqrt_one_sub_sq (m : ℕ /- [definition] -/ ) :
    (∫ x in (-1 : ℝ)..1, x ^ m * √(1 - x ^ 2))
      = ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ m * Real.cos x ^ 2 := by
  calc (∫ x in (-1 : ℝ)..1, x ^ m * √(1 - x ^ 2))
      = ∫ x in Real.sin (-(π / 2))..Real.sin (π / 2), x ^ m * √(1 - x ^ 2) := by
        rw [Real.sin_neg, Real.sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ m * √(1 - Real.sin x ^ 2) * Real.cos x :=
        (integral_comp_mul_deriv (fun x _ ↦ Real.hasDerivAt_sin x)
          Real.continuousOn_cos (by fun_prop)).symm
    _ = ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ m * Real.cos x ^ 2 := by
        refine integral_congr_ae (MeasureTheory.ae_of_all _ fun x h ↦ ?_)
        rw [Set.uIoc_of_le (neg_le_self (le_of_lt (half_pos Real.pi_pos))), Set.mem_Ioc] at h
        rw [← Real.cos_eq_sqrt_one_sub_sin_sq (le_of_lt h.1) h.2]
        ring

/-- The moment integral after the substitution: the whole dependence on `m` sits
in `∫ sin ^ m * cos ^ 2` over `[-π/2, π/2]`. -/
theorem semicircleMoment_eq (m : ℕ /- [definition] -/ ) :
    semicircleMoment m
      = 1 / (2 * π) * 2 ^ (m + 2) * ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ m * Real.cos x ^ 2 := by
  have hsm := smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := (1 : ℝ))
    (f := fun y : ℝ ↦ y ^ m * √(4 - y ^ 2)) 2
  rw [show (2 : ℝ) * (-1) = -2 by norm_num, show (2 : ℝ) * 1 = 2 by norm_num] at hsm
  have hin : (∫ u in (-1 : ℝ)..1, (2 * u) ^ m * √(4 - (2 * u) ^ 2))
      = 2 ^ (m + 1) * ∫ u in (-1 : ℝ)..1, u ^ m * √(1 - u ^ 2) := by
    rw [← integral_const_mul]
    refine integral_congr fun u _ ↦ ?_
    rw [sqrt_four_sub_two_mul_sq u, mul_pow]
    ring
  have hscale : (∫ x in (-2 : ℝ)..2, x ^ m * √(4 - x ^ 2))
      = 2 ^ (m + 2) * ∫ u in (-1 : ℝ)..1, u ^ m * √(1 - u ^ 2) := by
    rw [← hsm, smul_eq_mul, hin]
    ring
  rw [semicircleMoment, hscale, integral_pow_mul_sqrt_one_sub_sq]
  ring

/-- Wallis' recursion, specialised to the symmetric interval `[-π/2, π/2]`
where the boundary terms vanish. -/
theorem integral_sin_pow_symm (n : ℕ /- [definition] -/ ) :
    (∫ x in (-(π / 2))..(π / 2), Real.sin x ^ (n + 2))
      = ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ n := by
  have hc1 : Real.cos (π / 2) = 0 := Real.cos_pi_div_two
  have hc2 : Real.cos (-(π / 2)) = 0 := by rw [Real.cos_neg, Real.cos_pi_div_two]
  rw [integral_sin_pow, hc1, hc2]
  ring

/-- `∫ sin ^ n * cos ^ 2 = (∫ sin ^ n) / (n + 2)` on `[-π/2, π/2]`. -/
theorem integral_sin_pow_mul_cos_sq (n : ℕ /- [definition] -/ ) :
    (∫ x in (-(π / 2))..(π / 2), Real.sin x ^ n * Real.cos x ^ 2)
      = (∫ x in (-(π / 2))..(π / 2), Real.sin x ^ n) / ((n : ℝ) + 2) := by
  have hi1 : IntervalIntegrable (fun x : ℝ ↦ Real.sin x ^ n) MeasureTheory.volume
      (-(π / 2)) (π / 2) := (by fun_prop : Continuous fun x : ℝ ↦ Real.sin x ^ n)
    |>.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ ↦ Real.sin x ^ (n + 2)) MeasureTheory.volume
      (-(π / 2)) (π / 2) := (by fun_prop : Continuous fun x : ℝ ↦ Real.sin x ^ (n + 2))
    |>.intervalIntegrable _ _
  have hsplit : (∫ x in (-(π / 2))..(π / 2), Real.sin x ^ n * Real.cos x ^ 2)
      = (∫ x in (-(π / 2))..(π / 2), Real.sin x ^ n)
        - ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ (n + 2) := by
    rw [← integral_sub hi1 hi2]
    refine integral_congr fun x _ ↦ ?_
    have hpy : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      have := Real.sin_sq_add_cos_sq x
      linarith
    rw [hpy, pow_add]
    ring
  have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [hsplit, integral_sin_pow_symm]
  field_simp
  ring

/-- The Catalan two-term recursion, in the form needed below. -/
theorem catalan_succ_mul (k : ℕ /- [definition] -/ ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 : (k + 1 + 1) * catalan (k + 1) = Nat.centralBinom (k + 1) :=
    succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 : (k + 1) * Nat.centralBinom (k + 1) = 2 * (2 * k + 1) * Nat.centralBinom k :=
    Nat.succ_mul_centralBinom_succ k
  have h3 : (k + 1) * catalan k = Nat.centralBinom k := succ_mul_catalan_eq_centralBinom k
  refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) ?_
  calc (k + 1) * ((k + 2) * catalan (k + 1))
      = (k + 1) * Nat.centralBinom (k + 1) := by rw [← h1]
    _ = 2 * (2 * k + 1) * Nat.centralBinom k := h2
    _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h3]
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring

/-- **The even moments of the semicircle law are the Catalan numbers**:
`semicircleMoment (2 * k) = catalan k`. -/
theorem semicircleMoment_two_mul (k : ℕ /- [definition] -/ ) : semicircleMoment (2 * k) = catalan k := by
  induction k with
  | zero =>
      rw [Nat.mul_zero]
      exact semicircleMoment_zero
  | succ k ih =>
      have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
      have hne1 : ((2 * k : ℕ) : ℝ) + 2 ≠ 0 := by positivity
      have hne2 : ((2 * k + 2 : ℕ) : ℝ) + 2 ≠ 0 := by positivity
      have hpi : π ≠ 0 := Real.pi_ne_zero
      have hstep : ((k : ℝ) + 2) * semicircleMoment (2 * (k + 1))
          = 2 * (2 * (k : ℝ) + 1) * semicircleMoment (2 * k) := by
        rw [hexp, semicircleMoment_eq, semicircleMoment_eq,
          integral_sin_pow_mul_cos_sq, integral_sin_pow_mul_cos_sq, integral_sin_pow_symm]
        push_cast
        field_simp
        ring
      have hcat : ((k : ℝ) + 2) * (catalan (k + 1) : ℝ)
          = 2 * (2 * (k : ℝ) + 1) * (catalan k : ℝ) := by
        have := catalan_succ_mul k
        have hc : (((k + 2) * catalan (k + 1) : ℕ) : ℝ) = ((2 * (2 * k + 1) * catalan k : ℕ) : ℝ) := by
          rw [this]
        push_cast at hc
        linarith
      have hknz : ((k : ℝ) + 2) ≠ 0 := by positivity
      have := hstep
      rw [ih] at this
      rw [← hcat] at this
      exact mul_left_cancel₀ hknz this

end EvenMoments

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.semicircleMoment
#print axioms RMTFoundations.Concentration.integral_sqrt_four_sub_sq
#print axioms RMTFoundations.Concentration.semicircleMoment_zero
#print axioms RMTFoundations.Concentration.semicircleMoment_odd
#print axioms RMTFoundations.Concentration.sqrt_four_sub_two_mul_sq
#print axioms RMTFoundations.Concentration.integral_pow_mul_sqrt_one_sub_sq
#print axioms RMTFoundations.Concentration.semicircleMoment_eq
#print axioms RMTFoundations.Concentration.integral_sin_pow_symm
#print axioms RMTFoundations.Concentration.integral_sin_pow_mul_cos_sq
#print axioms RMTFoundations.Concentration.catalan_succ_mul
#print axioms RMTFoundations.Concentration.semicircleMoment_two_mul
