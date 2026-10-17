import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; adapted by this project.
Derivative and weighted-pairing proofs adapted from TauCeti commit
197f368a2da83d4c66df6c5a27e52633c021afe3. These are known Hermite identities.
-/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjection
open MeasureTheory Polynomial Real
/-- **Lowering (derivative) identity for the Hermite polynomials.** Differentiating the
`(n + 1)`-st probabilists' Hermite polynomial lowers the index:
`H'_{n+1} = (n + 1) · Hₙ`.

This is not a `simp` lemma because its left-hand side is already reduced by the `n`-indexed
form `derivative_hermite`. -/
theorem derivative_hermite_succ (n : ℕ /- [definition] -/) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      derivative (hermite (n + 1 + 1))
          = derivative (X * hermite (n + 1) - derivative (hermite (n + 1))) := by
            rw [hermite_succ]
      _ = hermite (n + 1) + X * ((n + 1) • hermite n) -
            derivative ((n + 1) • hermite n) := by
            simp only [derivative_sub, derivative_mul, derivative_X, one_mul, ih, derivative_smul]
      _ = (n + 1 + 1) • hermite (n + 1) := by
            rw [hermite_succ n]
            simp only [derivative_smul]
            ring_nf

/-- The Hermite derivative identity restated at index `n`: `H'ₙ = n · Hₙ₋₁`. For `n = 0` both sides
vanish (`H₀ = 1`). -/
@[simp]
theorem derivative_hermite (n : ℕ /- [definition] -/) :
    derivative (hermite n) = n • hermite (n - 1) := by
  cases n with
  | zero => simp [hermite_zero]
  | succ n => simpa using derivative_hermite_succ n

/-- Iterating the lowering identity: the `k`-th derivative of `Hₙ` is the descending factorial
`n (n-1) ⋯ (n-k+1)` times `H_{n-k}`. For `k > n` the descending factorial is `0` and both sides
vanish. -/
@[simp]
theorem iterate_derivative_hermite (n k : ℕ /- [definition] -/) :
    derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_smul, derivative_hermite, smul_smul,
      Nat.descFactorial_succ, Nat.sub_sub, mul_comm]

/-- **Three-term recurrence for the Hermite polynomials.** Eliminating the derivative from Mathlib's
defining recursion `hermite_succ` gives the classical relation `H_{n+2} = X·H_{n+1} - (n+1)·Hₙ`,
i.e. `H_{m+1} = X·H_m - m·H_{m-1}`. -/
theorem hermite_add_two (n : ℕ /- [definition] -/) :
    hermite (n + 2) = X * hermite (n + 1) - (n + 1) • hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]

theorem polynomial_gaussian_integrable (p : ℝ[X] /- [definition] -/) :
    Integrable (fun x : ℝ => p.eval x * exp (-(x^2/2))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => 
    refine (hp.add hq).congr (Filter.Eventually.of_forall ?_)
    intro x
    simp [eval_add,add_mul]
  | monomial n a =>
    have hi := integrable_rpow_mul_exp_neg_mul_sq (b:=1/2) (s:=(n:ℝ))
      (by norm_num) (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
    simpa [eval_monomial,Real.rpow_natCast,mul_assoc,div_eq_mul_inv,mul_comm,mul_left_comm] using hi.const_mul a

theorem integrable_aeval_mul_gaussian (p : ℤ[X] /- [definition] -/) :
    Integrable (fun x : ℝ => aeval x p * Real.exp (-(x ^ 2 / 2))) := by
  have h := polynomial_gaussian_integrable (p.map (Int.castRingHom ℝ))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [eval_map, aeval_def, algebraMap_int_eq]

/-- The Rodrigues-type step behind the recursion, at the level of `aeval`: from Mathlib's defining
recursion `hermite (n+1) = X · hermite n - derivative (hermite n)`,
`H'ₙ(x) = x · Hₙ(x) - H_{n+1}(x)`. -/
theorem aeval_derivative_hermite (n : ℕ /- [definition] -/) (x : ℝ /- [definition] -/) :
    aeval x (derivative (hermite n)) = x * aeval x (hermite n) - aeval x (hermite (n + 1)) := by
  have h : derivative (hermite n) = X * hermite n - hermite (n + 1) := by
    rw [hermite_succ n]; ring
  rw [h, map_sub, map_mul, aeval_X]

/-- A product of two `aeval`s of polynomials against the Gaussian weight `e^{-x²/2}` is
Lebesgue-integrable. -/
theorem integrable_aeval_mul_aeval_mul_gaussian (p q : ℤ[X] /- [definition] -/) :
    Integrable (fun x : ℝ => aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2))) := by
  have e : (fun x : ℝ => aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2)))
      = fun x : ℝ => aeval x (p * q) * Real.exp (-(x ^ 2 / 2)) := by
    ext x; rw [map_mul]
  rw [e]; exact integrable_aeval_mul_gaussian _

/-- **One-step weighted-pairing recursion** (target A1): the weighted pairing of `p` with `H_{n+1}`
equals the weighted pairing of its derivative `p'` with `Hₙ`,
`∫ p · H_{n+1} · e^{-x²/2} = ∫ p' · Hₙ · e^{-x²/2}`. -/
theorem integral_aeval_mul_hermite_succ (p : ℤ[X] /- [definition] -/) (n : ℕ /- [definition] -/) :
    (∫ x : ℝ, aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => aeval x p * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      (aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
        - aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
      have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-(2 * x / 2)) x := (hsq.div_const 2).neg
      rwa [show -(2 * x / 2) = -x from by ring] at h2
    have hw' : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (Real.exp (-(x ^ 2 / 2)) * -x) x :=
      h1.exp
    have hbase := ((p.hasDerivAt_aeval x).mul ((hermite n).hasDerivAt_aeval x)).mul hw'
    have hval : aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
        - aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))
        = (aeval x (derivative p) * aeval x (hermite n)
            + aeval x p * aeval x (derivative (hermite n))) * Real.exp (-(x ^ 2 / 2))
          + aeval x p * aeval x (hermite n) * (Real.exp (-(x ^ 2 / 2)) * -x) := by
      rw [aeval_derivative_hermite]; ring
    rw [hval]
    exact hbase
  have ht1 := integrable_aeval_mul_aeval_mul_gaussian (derivative p) (hermite n)
  have ht2 := integrable_aeval_mul_aeval_mul_gaussian p (hermite (n + 1))
  have hf := integrable_aeval_mul_aeval_mul_gaussian p (hermite n)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (ht1.sub ht2) hf
  rw [integral_sub ht1 ht2] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- **Iterated recursion**: pairing `p` with `Hₙ` against the Gaussian weight equals pairing the
`n`-th derivative of `p` with `H₀ = 1`, i.e. `∫ p · Hₙ · e^{-x²/2} = ∫ (dⁿ/dxⁿ p) · e^{-x²/2}`. -/
theorem integral_aeval_mul_hermite (p : ℤ[X] /- [definition] -/) (n : ℕ /- [definition] -/) :
    (∫ x : ℝ, aeval x p * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (derivative^[n] p) * Real.exp (-(x ^ 2 / 2)) := by
  induction n generalizing p with
  | zero => simp only [Function.iterate_zero, id_eq, hermite_zero, map_one, mul_one]
  | succ n ih =>
    rw [integral_aeval_mul_hermite_succ, ih (derivative p), Function.iterate_succ_apply]

/-- The Gaussian integral of the bare weight: `∫ x, e^{-x²/2} = √(2π)`. -/
theorem integral_gaussian_half :
    (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2)
  have e : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = fun x : ℝ => Real.exp (-(x ^ 2 / 2)) := by
    ext x; rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) from by ring]
  rw [e] at h
  rw [h, show π / (1 / 2) = 2 * π from by ring]

/-- Commuting the two factors under the integral. -/
theorem integral_hermite_swap (m n : ℕ /- [definition] -/) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (hermite n) * aeval x (hermite m) * Real.exp (-(x ^ 2 / 2)) := by
  congr 1; ext x; ring

/-- **The Hermite orthogonality relation, Lebesgue form** (milestone A1):
`∫ x, Hₘ(x) · Hₙ(x) · e^{-x²/2} = if m = n then n! · √(2π) else 0`. -/
theorem integral_hermite_mul_hermite_mul_gaussian (m n : ℕ /- [definition] -/) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = if m = n then (n.factorial : ℝ) * Real.sqrt (2 * π) else 0 := by
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_neg h.ne, integral_aeval_mul_hermite, iterate_derivative_hermite,
      Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp
  · rw [if_pos rfl, integral_aeval_mul_hermite]
    have hconst : (fun x : ℝ => aeval x (derivative^[m] (hermite m)) * Real.exp (-(x ^ 2 / 2)))
        = fun x : ℝ => (m.factorial : ℝ) * Real.exp (-(x ^ 2 / 2)) := by
      ext x
      rw [iterate_derivative_hermite, Nat.sub_self, Nat.descFactorial_self, hermite_zero]
      simp [nsmul_eq_mul]
    rw [hconst, integral_const_mul, integral_gaussian_half]
  · rw [if_neg h.ne', integral_hermite_swap, integral_aeval_mul_hermite,
      iterate_derivative_hermite, Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp



end RMTFoundations.TracyWidom.GUEProjection

#print axioms RMTFoundations.TracyWidom.GUEProjection.derivative_hermite_succ
#print axioms RMTFoundations.TracyWidom.GUEProjection.derivative_hermite
#print axioms RMTFoundations.TracyWidom.GUEProjection.iterate_derivative_hermite
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_add_two
#print axioms RMTFoundations.TracyWidom.GUEProjection.polynomial_gaussian_integrable
#print axioms RMTFoundations.TracyWidom.GUEProjection.integrable_aeval_mul_gaussian
#print axioms RMTFoundations.TracyWidom.GUEProjection.aeval_derivative_hermite
#print axioms RMTFoundations.TracyWidom.GUEProjection.integrable_aeval_mul_aeval_mul_gaussian
#print axioms RMTFoundations.TracyWidom.GUEProjection.integral_aeval_mul_hermite_succ
#print axioms RMTFoundations.TracyWidom.GUEProjection.integral_aeval_mul_hermite
#print axioms RMTFoundations.TracyWidom.GUEProjection.integral_gaussian_half
#print axioms RMTFoundations.TracyWidom.GUEProjection.integral_hermite_swap
#print axioms RMTFoundations.TracyWidom.GUEProjection.integral_hermite_mul_hermite_mul_gaussian
