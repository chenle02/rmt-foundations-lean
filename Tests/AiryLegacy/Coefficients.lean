import Tests.AiryLegacy.Series
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The power series coefficients of a solution of `y'' = x y`

If `y = ∑ a n x ^ n` solves `y'' = x y` then comparing coefficients of `x ^ n` gives
`(n + 2) (n + 1) a (n + 2) = a (n - 1)`, i.e. `(n + 3) (n + 2) a (n + 3) = a n` together with
`a 2 = 0`.  `RMTFoundations.Airy.airyCoeff a₀ a₁` is the sequence defined by that recursion with
`a 0 = a₀`, `a 1 = a₁` and `a 2 = 0`.

## What is proved here

* `airyCoeff_add_three`, `airyCoeff_recursion`: the defining recursion, in the two forms
  `a (n + 3) = a n / ((n + 3) (n + 2))` and `(n + 3) (n + 2) a (n + 3) = a n`;
* `airyCoeff_abs_le`: the explicit decay bound `|a n| ≤ max |a₀| |a₁| / (n / 2)!`, where `n / 2`
  is natural division.  The three-step recursion loses one factorial factor per two indices,
  and this is the cleanest bound that survives an induction in steps of three;
* `hasEntireCoeffs_airyCoeff`: consequently the series has **infinite radius of convergence** —
  `∑ |a n| r ^ n` converges for every `r ≥ 0`.  The majorant `∑ M r ^ n / (n / 2)!` is summed by
  splitting into even and odd indices, each of which is a scaled exponential series.

## What is NOT proved here

* nothing about the *true* Airy coefficients as values of the Gamma function, and no closed form
  for `airyCoeff` (the recursion is the definition).
* no lower bound on `|a n|`, hence nothing about the exact radius being infinite *and* the
  coefficients being nonzero infinitely often.
-/

namespace RMTFoundations.Airy

/-- The coefficients of the formal power series solution of `y'' = x y` with initial data
`y 0 = a₀` and `y' 0 = a₁`.  The recursion `a (n + 3) = a n / ((n + 3) (n + 2))` is exactly the
statement that the coefficient of `x ^ (n + 1)` in `y''` equals that of `x ^ (n + 1)` in `x y`. -/
noncomputable def airyCoeff (a₀ a₁ : ℝ /- [definition] -/ ) : ℕ → ℝ
  | 0 => a₀
  | 1 => a₁
  | 2 => 0
  | n + 3 => airyCoeff a₀ a₁ n / (((n : ℝ) + 3) * ((n : ℝ) + 2))

variable (a₀ a₁ : ℝ /- [definition] -/ )

theorem airyCoeff_zero : airyCoeff a₀ a₁ 0 = a₀ := rfl

theorem airyCoeff_one : airyCoeff a₀ a₁ 1 = a₁ := rfl

theorem airyCoeff_two : airyCoeff a₀ a₁ 2 = 0 := rfl

theorem airyCoeff_add_three (n : ℕ /- [definition] -/ ) :
    airyCoeff a₀ a₁ (n + 3) = airyCoeff a₀ a₁ n / (((n : ℝ) + 3) * ((n : ℝ) + 2)) := rfl

/-- The coefficient recursion of the Airy equation, in product form. -/
theorem airyCoeff_recursion (n : ℕ /- [definition] -/ ) :
    (((n : ℝ) + 3) * ((n : ℝ) + 2)) * airyCoeff a₀ a₁ (n + 3) = airyCoeff a₀ a₁ n := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 3) * ((n : ℝ) + 2) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  rw [airyCoeff_add_three, mul_div_cancel₀]
  exact ne_of_gt hpos

/-- The decay bound driving convergence: `|a n| ≤ M / (n / 2)!` with `M = max |a₀| |a₁|` and
natural division in the exponent of the factorial. -/
theorem airyCoeff_abs_le (n : ℕ /- [definition] -/ ) :
    |airyCoeff a₀ a₁ n| ≤ max |a₀| |a₁| / (((n / 2).factorial : ℕ) : ℝ) := by
  have hM : (0 : ℝ) ≤ max |a₀| |a₁| := le_trans (abs_nonneg a₀) (le_max_left _ _)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [airyCoeff_zero]
      have : ((0 : ℕ) / 2).factorial = 1 := rfl
      rw [this, Nat.cast_one, div_one]
      exact le_max_left _ _
    | 1 =>
      rw [airyCoeff_one]
      have : ((1 : ℕ) / 2).factorial = 1 := rfl
      rw [this, Nat.cast_one, div_one]
      exact le_max_right _ _
    | 2 =>
      rw [airyCoeff_two]
      have : ((2 : ℕ) / 2).factorial = 1 := rfl
      rw [this, Nat.cast_one, div_one, abs_zero]
      exact hM
    | m + 3 =>
      have hIH := ih m (by omega)
      have hfac : ((m + 3) / 2).factorial ≤ (m / 2).factorial * ((m + 3) * (m + 2)) := by
        have h1 : (m + 3) / 2 ≤ m / 2 + 2 := by omega
        have h2 : ((m + 3) / 2).factorial ≤ (m / 2 + 2).factorial := Nat.factorial_le h1
        have h3 : (m / 2 + 2).factorial = (m / 2 + 2) * ((m / 2 + 1) * (m / 2).factorial) := by
          rw [Nat.factorial_succ, Nat.factorial_succ]
        have h4 : (m / 2 + 2) * (m / 2 + 1) ≤ (m + 3) * (m + 2) := by
          have hm : m / 2 ≤ m := by omega
          exact Nat.mul_le_mul (by omega) (by omega)
        calc ((m + 3) / 2).factorial ≤ (m / 2 + 2).factorial := h2
          _ = ((m / 2 + 2) * (m / 2 + 1)) * (m / 2).factorial := by rw [h3]; ring
          _ ≤ ((m + 3) * (m + 2)) * (m / 2).factorial :=
              Nat.mul_le_mul_right _ h4
          _ = (m / 2).factorial * ((m + 3) * (m + 2)) := by ring
      have hfacR : (((m + 3) / 2).factorial : ℝ)
          ≤ ((m / 2).factorial : ℝ) * (((m : ℝ) + 3) * ((m : ℝ) + 2)) := by
        have := (Nat.cast_le (α := ℝ)).2 hfac
        push_cast at this
        linarith
      have hposm : (0 : ℝ) < ((m : ℝ) + 3) * ((m : ℝ) + 2) := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      have hfacpos : (0 : ℝ) < ((m / 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos (m / 2)
      have hfacpos' : (0 : ℝ) < (((m + 3) / 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos ((m + 3) / 2)
      rw [airyCoeff_add_three, abs_div, abs_of_pos hposm]
      have step1 : |airyCoeff a₀ a₁ m| / (((m : ℝ) + 3) * ((m : ℝ) + 2))
          ≤ (max |a₀| |a₁| / ((m / 2).factorial : ℝ)) / (((m : ℝ) + 3) * ((m : ℝ) + 2)) :=
        (div_le_div_iff_of_pos_right hposm).2 hIH
      have step2 : (max |a₀| |a₁| / ((m / 2).factorial : ℝ)) / (((m : ℝ) + 3) * ((m : ℝ) + 2))
          = max |a₀| |a₁| / (((m / 2).factorial : ℝ) * (((m : ℝ) + 3) * ((m : ℝ) + 2))) := by
        rw [div_div]
      have step3 : max |a₀| |a₁| / (((m / 2).factorial : ℝ) * (((m : ℝ) + 3) * ((m : ℝ) + 2)))
          ≤ max |a₀| |a₁| / (((m + 3) / 2).factorial : ℝ) :=
        div_le_div_of_nonneg_left hM hfacpos' hfacR
      exact le_trans step1 (le_trans (le_of_eq step2) step3)

/-- The majorant `∑ M r ^ n / (n / 2)!` converges: split into even and odd indices, each giving a
scaled exponential series in `r ^ 2`. -/
theorem summable_airyMajorant (M r : ℝ /- [definition] -/ ) :
    Summable fun n : ℕ => M / (((n / 2).factorial : ℕ) : ℝ) * r ^ n := by
  refine Summable.even_add_odd ?_ ?_
  · refine ((Real.summable_pow_div_factorial (r ^ 2)).mul_left M).congr fun k => ?_
    show M * ((r ^ 2) ^ k / (k.factorial : ℝ))
        = M / (((2 * k / 2).factorial : ℕ) : ℝ) * r ^ (2 * k)
    have h1 : 2 * k / 2 = k := by omega
    have h2 : (r ^ 2) ^ k = r ^ (2 * k) := (pow_mul r 2 k).symm
    rw [h1, h2]
    ring
  · refine ((Real.summable_pow_div_factorial (r ^ 2)).mul_left (M * r)).congr fun k => ?_
    show M * r * ((r ^ 2) ^ k / (k.factorial : ℝ))
        = M / ((((2 * k + 1) / 2).factorial : ℕ) : ℝ) * r ^ (2 * k + 1)
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (r ^ 2) ^ k = r ^ (2 * k) := (pow_mul r 2 k).symm
    have h3 : r ^ (2 * k + 1) = r ^ (2 * k) * r := pow_succ r (2 * k)
    rw [h1, h2, h3]
    ring

/-- The Airy power series converges absolutely at every real point: the formal solution is an
entire series. -/
theorem hasEntireCoeffs_airyCoeff : HasEntireCoeffs (airyCoeff a₀ a₁) := by
  intro r hr
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n => ?_) (summable_airyMajorant (max |a₀| |a₁|) r)
  exact mul_le_mul_of_nonneg_right (airyCoeff_abs_le a₀ a₁ n) (pow_nonneg hr n)

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.airyCoeff
#print axioms RMTFoundations.Airy.airyCoeff_zero
#print axioms RMTFoundations.Airy.airyCoeff_one
#print axioms RMTFoundations.Airy.airyCoeff_two
#print axioms RMTFoundations.Airy.airyCoeff_add_three
#print axioms RMTFoundations.Airy.airyCoeff_recursion
#print axioms RMTFoundations.Airy.airyCoeff_abs_le
#print axioms RMTFoundations.Airy.summable_airyMajorant
#print axioms RMTFoundations.Airy.hasEntireCoeffs_airyCoeff
