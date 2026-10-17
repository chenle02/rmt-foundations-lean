import Mathlib

namespace RMTFoundations.Airy

noncomputable section source0
/- Origin: upstream/RegularizedHypergeometric.lean (see NOTICE). -/
open Complex
/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/


/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function, that is
the coefficients are divides by `∏ i, Gamma (b i)`, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

This definition is valid for all values of `c`, whereas the usual hypergeometric function has a
pole for `c = -k` and `k : ℕ`. To our knowledge the regularized hypergeometric function only appears
in the literature only for the Gaussian case, it is implicit in the definition of the Bessel
function (`p = 0` and `q = 1`).
To recover the usual hypergeometric function, simply multiply by `∏ i, Gamma (b i)`.

## Definitions
For the general case we have
* `complex_regularizedHGFunCoeff`: the coefficients
* `complex_regularizedHGFunSeries`: the formal multilinear series
* `complex_regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `complex_regularizedGaussHGFunSeries`: the formal multilinear series
* `complex_regularizedGaussHGFun`: the function

## Results

Convergence:
* `complex_radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `complex_radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `complex_radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `complex_radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/



open Filter

open scoped Nat Real Topology

variable {p q : ℕ /- [definition] -/ }

variable {a : Multiset ℂ /- [definition] -/ } {b : Multiset ℂ /- [definition] -/ } {n m : ℕ /- [definition] -/ } {j k : ℂ /- [definition] -/ }

/-- The coefficients of the regularized hypergeometric series. -/
noncomputable def complex_regularizedHGFunCoeff (a : Multiset ℂ /- [definition] -/ ) (b : Multiset ℂ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)



theorem complex_regularizedHGFunCoeff_eq_zero_iff :
    complex_regularizedHGFunCoeff a b n = 0 ↔
    (∃ j ∈ a, ∃ k < n, j = -k) ∨ ∃ j ∈ b, ∃ (m : ℕ), j + n = -m := by
  apply Complex.regularizedHGFunCoeff_eq_zero_iff <;> assumption

variable (a b n m /- [definition] -/ ) in
theorem complex_regularizedHGFunCoeff_eq_zero_right (hb : -(n : ℂ) - m ∈ b := by grind [Nat.factorial_ne_zero, Complex.Gamma_eq_zero_iff, Complex.Gamma_add_one, complex_regularizedHGFunCoeff_eq_zero_iff]  /- [standing] -/ ) :
    complex_regularizedHGFunCoeff a b n = 0 := by
  apply Complex.regularizedHGFunCoeff_eq_zero_right <;> assumption

variable (a b n m /- [definition] -/ ) in
theorem complex_regularizedHGFunCoeff_eq_zero_left (ha : -(m : ℂ) ∈ a := by grind [Nat.factorial_ne_zero, Complex.Gamma_eq_zero_iff, Complex.Gamma_add_one, complex_regularizedHGFunCoeff_eq_zero_iff]  /- [standing] -/ )
    (hm : m < n := by grind [Nat.factorial_ne_zero, Complex.Gamma_eq_zero_iff, Complex.Gamma_add_one, complex_regularizedHGFunCoeff_eq_zero_iff]  /- [standing] -/ ) :
  complex_regularizedHGFunCoeff a b n = 0 := by
  apply Complex.regularizedHGFunCoeff_eq_zero_left <;> assumption

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem complex_regularizedHGFunCoeff_add_one (hb : ∀ k ∈ b, k ≠ -n /- [standing] -/ ) :
    complex_regularizedHGFunCoeff a b (n + 1) = complex_regularizedHGFunCoeff a b n *
      ((a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod  * (n + 1))) := by
  apply Complex.regularizedHGFunCoeff_add_one <;> assumption

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem complex_regularizedHGFunCoeff_add_one_div_self (h : complex_regularizedHGFunCoeff a b n ≠ 0 /- [standing] -/ ) :
    complex_regularizedHGFunCoeff a b (n + 1) / complex_regularizedHGFunCoeff a b n =
      (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) := by
  apply Complex.regularizedHGFunCoeff_add_one_div_self <;> assumption

@[simp]
theorem complex_regularizedHGFunCoeff_zero_neg_nat_add_one (n i : ℕ /- [definition] -/ ) :
    complex_regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) = complex_regularizedHGFunCoeff 0 {(n : ℂ) + 1} i := by
  apply Complex.regularizedHGFunCoeff_zero_neg_nat_add_one <;> assumption

theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset ℂ /- [definition] -/ ) (hn : n ≠ 0 /- [standing] -/ ) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

theorem complex_multiset_prod_div_multiset_prod_mul (a : Multiset ℂ /- [definition] -/ ) (b : Multiset ℂ /- [definition] -/ ) (hn : n ≠ 0 /- [standing] -/ ) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn, multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : ℤ)) *
        (a.map (fun x : ℂ ↦ (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind [Nat.factorial_ne_zero, Complex.Gamma_eq_zero_iff, Complex.Gamma_add_one, complex_regularizedHGFunCoeff_eq_zero_iff]
    _ = _ := by ring

variable (a b /- [definition] -/ ) in
/-- The regularized hypergeometric series. -/
noncomputable def complex_regularizedHGFunSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (complex_regularizedHGFunCoeff a b)

@[simp]
theorem complex_regularizedHGFunSeries_coeff :
    (complex_regularizedHGFunSeries a b).coeff = complex_regularizedHGFunCoeff a b := by
  apply Complex.regularizedHGFunSeries_coeff <;> assumption

@[simp]
theorem complex_regularizedHGFunSeries_eq_zero :
    complex_regularizedHGFunSeries a b n = 0 ↔ complex_regularizedHGFunCoeff a b n = 0 := by
  apply Complex.regularizedHGFunSeries_eq_zero <;> assumption

variable (a b /- [definition] -/ ) in
/-- The regularized hypergeometric function. -/
noncomputable def complex_regularizedHGFun (z : ℂ /- [definition] -/ ) : ℂ := (complex_regularizedHGFunSeries a b).sum z

@[simp]
theorem complex_regularizedHGFun_zero : complex_regularizedHGFun a b 0 = complex_regularizedHGFunCoeff a b 0 := by
  apply Complex.regularizedHGFun_zero <;> assumption

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem complex_radius_regularizedHGFunSeries_eq_top_of_finite (ha : j ∈ a /- [standing] -/ ) (hj : j = -n /- [standing] -/ ) :
    (complex_regularizedHGFunSeries a b).radius = ⊤ := by
  apply Complex.radius_regularizedHGFunSeries_eq_top_of_finite <;> assumption

variable (b /- [definition] -/ ) in
/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem complex_eventually_atTop_regularizedHGFunCoeff_ne_zero (h : ∀ j ∈ a, ∀ (k : ℕ), j ≠ -↑k /- [standing] -/ ) :
    ∀ᶠ (n : ℕ) in atTop, complex_regularizedHGFunCoeff a b n ≠ 0 := by
  apply Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero <;> assumption

variable (a /- [definition] -/ ) in
theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b /- [definition] -/ ) in
theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/

theorem complex_radius_regularizedHGFunSeries_eq_top (h : a.card ≤ b.card /- [standing] -/ ) :
    (complex_regularizedHGFunSeries a b).radius = ⊤ := by
  apply Complex.radius_regularizedHGFunSeries_eq_top <;> assumption

@[simp]
theorem complex_radius_regularizedHGFunSeries_zero_eq_top : (complex_regularizedHGFunSeries 0 b).radius = ⊤ := by
  apply Complex.radius_regularizedHGFunSeries_zero_eq_top <;> assumption

theorem complex_analyticOnNhd_regularizedHGFun_of_card_le (h : a.card ≤ b.card /- [standing] -/ ) :
    AnalyticOnNhd ℂ (complex_regularizedHGFun a b) .univ := by
  apply Complex.analyticOnNhd_regularizedHGFun_of_card_le <;> assumption

theorem complex_analyticAt_regularizedHGFun_of_card_le (h : a.card ≤ b.card /- [standing] -/ ) (z : ℂ /- [definition] -/ ) :
    AnalyticAt ℂ (complex_regularizedHGFun a b) z := by
  apply Complex.analyticAt_regularizedHGFun_of_card_le <;> assumption

theorem complex_analyticOnNhd_regularizedHGFun_zero : AnalyticOnNhd ℂ (complex_regularizedHGFun 0 b) .univ := by
  apply Complex.analyticOnNhd_regularizedHGFun_zero <;> assumption

theorem complex_analyticAt_regularizedHGFun_zero (z : ℂ /- [definition] -/ ) : AnalyticAt ℂ (complex_regularizedHGFun 0 b) z := by
  apply Complex.analyticAt_regularizedHGFun_zero <;> assumption

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/

theorem complex_radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1 /- [standing] -/ )
    (h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k /- [standing] -/ ) :
    (complex_regularizedHGFunSeries a b).radius = 1 := by
  apply Complex.radius_regularizedHGFunSeries_eq_one <;> assumption

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius greater or equal
to `1`. -/
theorem complex_radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1 /- [standing] -/ ) :
    1 ≤ (complex_regularizedHGFunSeries a b).radius := by
  apply Complex.radius_regularizedHGFunSeries_ge_one <;> assumption

theorem complex_analyticOnNhd_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1 /- [standing] -/ ) :
    AnalyticOnNhd ℂ (complex_regularizedHGFun a b) (Metric.eball 0 1) := by
  apply Complex.analyticOnNhd_regularizedHGFun_of_card_eq_add_one <;> assumption

theorem complex_analyticAt_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1 /- [standing] -/ ) {z : ℂ /- [definition] -/ }
    (hz : ‖z‖ < 1 /- [standing] -/ ) :
    AnalyticAt ℂ (complex_regularizedHGFun a b) z := by
  apply Complex.analyticAt_regularizedHGFun_of_card_eq_add_one <;> assumption

theorem complex_regularizedHGFun_zero_singleton_neg_nat_add_one (n : ℕ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) :
    complex_regularizedHGFun 0 {-(n : ℂ) + 1} z = z ^ n * complex_regularizedHGFun 0 {(n : ℂ) + 1} z := by
  apply Complex.regularizedHGFun_zero_singleton_neg_nat_add_one <;> assumption

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp]
theorem complex_regularizedHGFunSeries_zero_zero :
    complex_regularizedHGFunSeries 0 0 = NormedSpace.expSeries ℂ ℂ := by
  apply Complex.regularizedHGFunSeries_zero_zero <;> assumption

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp]
theorem complex_regularizedHGFun_zero_zero : complex_regularizedHGFun 0 0 = exp := by
  apply Complex.regularizedHGFun_zero_zero <;> assumption

end ZeroZero

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
noncomputable def complex_regularizedGaussHGFunSeries (a b c : ℂ /- [definition] -/ ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  complex_regularizedHGFunSeries {a, b} {c}

/-- The regularized Gaussian hypergeometric function. -/
noncomputable def complex_regularizedGaussHGFun (a b c z : ℂ /- [definition] -/ ) : ℂ :=
  (complex_regularizedGaussHGFunSeries a b c).sum z

variable {a b c z : ℂ /- [definition] -/ }

variable (a b c /- [definition] -/ ) in
theorem complex_regularizedGaussHGFunSeries_symm :
    complex_regularizedGaussHGFunSeries a b c = complex_regularizedGaussHGFunSeries b a c := by
  apply Complex.regularizedGaussHGFunSeries_symm <;> assumption

variable (a b c /- [definition] -/ ) in
theorem complex_regularizedGaussHGFun_symm :
    complex_regularizedGaussHGFun a b c = complex_regularizedGaussHGFun b a c := by
  apply Complex.regularizedGaussHGFun_symm <;> assumption

theorem complex_Gamma_add_nat_mul (c : ℂ /- [definition] -/ ) (hc : ∀ k : ℕ, c ≠ -k /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    Gamma (c + n) = (ascPochhammer ℂ n).eval c * Gamma c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : c + (n : ℂ) ≠ 0 := by
      intro h
      exact hc n (by linear_combination h)
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih,
      ascPochhammer_succ_eval]
    ring

theorem complex_Gamma_add_nat_div_Gamma_eq (c : ℂ /- [definition] -/ ) (hc : ∀ k : ℕ, c ≠ -k /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    Gamma (c + n) / Gamma c = (ascPochhammer ℂ n).eval c := by
  apply Complex.Gamma_add_nat_div_Gamma_eq <;> assumption

theorem complex_coeff_regularizedGaussHGFunSeries :
    (complex_regularizedGaussHGFunSeries a b c).coeff n =
    ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) / (n ! * Gamma (c + n)) := by
  apply Complex.coeff_regularizedGaussHGFunSeries <;> assumption

theorem complex_Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : ∀ k : ℕ, c ≠ -k /- [standing] -/ ) {n : ℕ /- [definition] -/ } :
    (Gamma c)⁻¹ * (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      (complex_regularizedGaussHGFunSeries a b c).coeff n := by
  apply Complex.Gamma_inv_mul_ordinaryHypergeometricSeries_eq <;> assumption

theorem complex_ordinaryHypergeometric_div_Gamma_eq (hc : ∀ k : ℕ, c ≠ -k /- [standing] -/ ) :
    ordinaryHypergeometric a b c z / Gamma c = complex_regularizedGaussHGFun a b c z := by
  apply Complex.ordinaryHypergeometric_div_Gamma_eq <;> assumption

variable (b c /- [definition] -/ ) in
@[simp]
theorem complex_radius_regularizedGaussHGFunSeries_eq_top_of_left (k : ℕ /- [definition] -/ ) :
    (complex_regularizedGaussHGFunSeries (-k) b c).radius = ⊤ := by
  apply Complex.radius_regularizedGaussHGFunSeries_eq_top_of_left <;> assumption

variable (a c /- [definition] -/ ) in
@[simp]
theorem complex_radius_regularizedGaussHGFunSeries_eq_top_of_right (k : ℕ /- [definition] -/ ) :
    (complex_regularizedGaussHGFunSeries a (-k) c).radius = ⊤ := by
  apply Complex.radius_regularizedGaussHGFunSeries_eq_top_of_right <;> assumption

variable (c /- [definition] -/ ) in

theorem complex_radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k /- [standing] -/ ) :
    (complex_regularizedGaussHGFunSeries a b c).radius = 1 := by
  apply Complex.radius_regularizedGaussHGFunSeries_eq_one <;> assumption

variable (a b c /- [definition] -/ ) in
theorem complex_radius_regularizedGaussHGFunSeries_ge_one :
    1 ≤ (complex_regularizedGaussHGFunSeries a b c).radius := by
  apply Complex.radius_regularizedGaussHGFunSeries_ge_one <;> assumption

end Gaussian


end source0

noncomputable section source1
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # Airy functions

We introduce the Airy functions `Ai` and `Bi` as entire functions on `ℂ`, via the
classical hypergeometric representations (DLMF 9.4.1–9.4.2): with `ζ = z³ / 9`,

$$ Ai(z) = 3^{-2/3}\,{}_0F_1(; 2/3; \zeta) - 3^{-1/3} \frac{z}{\Gamma(1/3)}\,{}_0F_1(;4/3;\zeta)
          \cdot \Gamma(4/3) / \Gamma(4/3) $$

More precisely, writing `₀F̃₁(; b; w) = ₀F₁(; b; w) / Γ(b)` for the regularized
hypergeometric function (`complex_regularizedHGFun 0 {b} w` in Mathlib), and using
`Γ(4/3) = Γ(1/3) / 3`,

* `complex_airyAi z = 3^(-2/3) · ₀F̃₁(; 2/3; z³/9) − 3^(−4/3) · z · ₀F̃₁(; 4/3; z³/9)`
  (DLMF 9.4.1 with `c₁ = 3^(−2/3)/Γ(2/3)`, `c₂ = 3^(−1/3)/Γ(1/3)`),
* `complex_airyBi z = 3^(−1/6) · ₀F̃₁(; 2/3; z³/9) + 3^(−5/6) · z · ₀F̃₁(; 4/3; z³/9)`
  (DLMF 9.4.2 with `c₃ = 3^(−1/6)/Γ(2/3)`, `c₄ = 3^(1/6)/Γ(1/3)`).

Both are entire functions since `₀F̃₁(; b; ·)` is entire
(`complex_analyticOnNhd_regularizedHGFun_zero`).

## Main results in this file

* `complex_analyticOnNhd_airyAi`, `complex_analyticOnNhd_airyBi`: `Ai` and `Bi` are entire.
* `complex_airyAi_zero`, `complex_airyBi_zero`: the values at `0`,
  `Ai(0) = 3^(−2/3) / Γ(2/3)` and `Bi(0) = 3^(−1/6) / Γ(2/3)`.

## TODO

* The Airy differential equation `y'' = z y` for both functions (via
  `d/dw ₀F̃₁(; b; w) = ₀F̃₁(; b + 1; w)` and the series recurrences).
* Real-valuedness on `ℝ` and the real versions `Real.airyAi`, `Real.airyBi`.
* The values of the derivatives at `0`: `Ai'(0) = −3^(−1/3)/Γ(1/3)`,
  `Bi'(0) = 3^(1/6)/Γ(1/3)`.
* Asymptotics: `Ai(x) ~ exp(−⅔x^{3/2}) / (2√π x^{1/4})` as `x → +∞` (DLMF 9.7.1).
-/

open Nat FormalMultilinearSeries


local notation "F̃₀₁(" b ")" => complex_regularizedHGFun 0 {(b : ℂ)}

/-- The Airy function of the first kind, `Ai(z)`.

Defined by the hypergeometric representation DLMF 9.4.1 with `ζ = z³/9`: using the
regularized `₀F̃₁(; b; w) = ₀F₁(; b; w) / Γ(b)`,
`Ai(z) = 3^(−2/3) · ₀F̃₁(; 2/3; z³/9) − 3^(−4/3) · z · ₀F̃₁(; 4/3; z³/9)`.
(The power of the second prefactor uses `Γ(4/3) = Γ(1/3)/3`.) -/
noncomputable def complex_airyAi (z : ℂ /- [definition] -/ ) : ℂ :=
  (3 : ℂ) ^ (-2 / 3 : ℂ) * F̃₀₁(2 / 3) (z ^ 3 / 9) -
    (3 : ℂ) ^ (-4 / 3 : ℂ) * z * F̃₀₁(4 / 3) (z ^ 3 / 9)

/-- The Airy function of the second kind, `Bi(z)`.

Defined by the hypergeometric representation DLMF 9.4.2 with `ζ = z³/9`:
`Bi(z) = 3^(−1/6) · ₀F̃₁(; 2/3; z³/9) + 3^(−5/6) · z · ₀F̃₁(; 4/3; z³/9)`. -/
noncomputable def complex_airyBi (z : ℂ /- [definition] -/ ) : ℂ :=
  (3 : ℂ) ^ (-1 / 6 : ℂ) * F̃₀₁(2 / 3) (z ^ 3 / 9) +
    (3 : ℂ) ^ (-5 / 6 : ℂ) * z * F̃₀₁(4 / 3) (z ^ 3 / 9)

theorem complex_airyAi_def :
    complex_airyAi = fun z : ℂ ↦ (3 : ℂ) ^ (-2 / 3 : ℂ) * F̃₀₁(2 / 3) (z ^ 3 / 9) -
      (3 : ℂ) ^ (-4 / 3 : ℂ) * z * F̃₀₁(4 / 3) (z ^ 3 / 9) := rfl

theorem complex_airyBi_def :
    complex_airyBi = fun z : ℂ ↦ (3 : ℂ) ^ (-1 / 6 : ℂ) * F̃₀₁(2 / 3) (z ^ 3 / 9) +
      (3 : ℂ) ^ (-5 / 6 : ℂ) * z * F̃₀₁(4 / 3) (z ^ 3 / 9) := rfl

/-- `Ai` is analytic everywhere, i.e. it is an entire function. -/
theorem complex_analyticAt_airyAi (z : ℂ /- [definition] -/ ) : AnalyticAt ℂ complex_airyAi z := by
  unfold complex_airyAi
  have ha : AnalyticAt ℂ (fun w : ℂ => w ^ 3 / 9) z := by fun_prop
  have h0 := (complex_analyticAt_regularizedHGFun_zero (b := {2 / 3}) (z ^ 3 / 9)).comp (f := fun w : ℂ => w ^ 3 / 9) (x := z) ha
  have h1 := (complex_analyticAt_regularizedHGFun_zero (b := {4 / 3}) (z ^ 3 / 9)).comp (f := fun w : ℂ => w ^ 3 / 9) (x := z) ha
  exact (analyticAt_const.mul h0).sub ((analyticAt_const.mul analyticAt_id).mul h1)

/-- `Ai` is entire. -/
theorem complex_analyticOnNhd_airyAi : AnalyticOnNhd ℂ complex_airyAi .univ :=
  fun z _ ↦ complex_analyticAt_airyAi z

/-- `Bi` is analytic everywhere, i.e. it is an entire function. -/
theorem complex_analyticAt_airyBi (z : ℂ /- [definition] -/ ) : AnalyticAt ℂ complex_airyBi z := by
  unfold complex_airyBi
  have ha : AnalyticAt ℂ (fun w : ℂ => w ^ 3 / 9) z := by fun_prop
  have h0 := (complex_analyticAt_regularizedHGFun_zero (b := {2 / 3}) (z ^ 3 / 9)).comp (f := fun w : ℂ => w ^ 3 / 9) (x := z) ha
  have h1 := (complex_analyticAt_regularizedHGFun_zero (b := {4 / 3}) (z ^ 3 / 9)).comp (f := fun w : ℂ => w ^ 3 / 9) (x := z) ha
  exact (analyticAt_const.mul h0).add ((analyticAt_const.mul analyticAt_id).mul h1)

/-- `Bi` is entire. -/
theorem complex_analyticOnNhd_airyBi : AnalyticOnNhd ℂ complex_airyBi .univ :=
  fun z _ ↦ complex_analyticAt_airyBi z

/-- The value `Ai(0) = 3^(−2/3) / Γ(2/3)` (DLMF 9.2.3). -/
theorem complex_airyAi_zero : complex_airyAi 0 = (3 : ℂ) ^ (-2 / 3 : ℂ) / Complex.Gamma (2 / 3) := by
  simp [complex_airyAi, complex_regularizedHGFun_zero, complex_regularizedHGFunCoeff, div_eq_mul_inv]

/-- The value `Bi(0) = 3^(−1/6) / Γ(2/3)` (DLMF 9.2.5). -/
theorem complex_airyBi_zero : complex_airyBi 0 = (3 : ℂ) ^ (-1 / 6 : ℂ) / Complex.Gamma (2 / 3) := by
  simp [complex_airyBi, complex_regularizedHGFun_zero, complex_regularizedHGFunCoeff, div_eq_mul_inv]


end source1

noncomputable section source2
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # The Airy differential equation

We prove that the Airy functions `complex_airyAi` and `complex_airyBi` satisfy the Airy differential equation `y'' = z y`,
and that they commute with complex conjugation (so they are real-valued on the real axis).

Everything is bootstrapped from the corresponding statements for the regularized
hypergeometric function `₀F̃₁(; b; w) = ∑' n, w ^ n / (n ! * Γ(b + n))`
(`complex_regularizedHGFun 0 {b} w` in Mathlib):

* `complex_regularizedHGFunCoeff_zero_singleton_succ`: the coefficient identity
  `(n + 1) * c_b (n + 1) = c_{b+1} n` (this is `Γ(b + n + 1) = (b + n) Γ(b + n)` in disguise,
  but formulated so that it holds for all `b`, even at the poles of `Γ`);
* `complex_radius_regularizedHGFunSeries_zero_singleton_succ`: the series for `b + 1` is
  again entire (its radius of convergence is `⊤`);
* `complex_hasDerivAt_regularizedHGFun_zero_singleton`: the term-by-term derivative
  identity `d/dw ₀F̃₁(; b; w) = ₀F̃₁(; b + 1; w)`, proved by locally uniform approximation
  by partial sums (`hasDerivAt_of_tendstoLocallyUniformlyOn`);
* `complex_regularizedHGFun_zero_singleton_recurrence`:
  `w * ₀F̃₁(; b + 2; w) + b * ₀F̃₁(; b + 1; w) = ₀F̃₁(; b; w)` for `b ∉ {0, -1, -2, ...}`,
  from `Γ(s + 1) = s Γ(s)`;
* `complex_iteratedDeriv_two_airyAi`, `complex_iteratedDeriv_two_airyBi`: the Airy ODE
  `iteratedDeriv 2 complex_airyAi z = z * complex_airyAi z` (and the same for `complex_airyBi`);
* `complex_airyAi_conj`, `complex_airyBi_conj`: `Ai, Bi` commute with `star`.

For the ODE, write `u_b z := ₀F̃₁(; b; z³/9)`.  The chain rule and the two hypergeometric
identities above give `u_b'' z = z * u_b z + (2/3 - b) * z * u_{b+1} z`; at `b = 2/3` the
second term vanishes, while for `b = 4/3` it is exactly what is needed for
`(z * u_{4/3})'' = z * (z * u_{4/3})`, and the Airy equation follows.
-/

open scoped Nat

open FormalMultilinearSeries Filter


/-- The power series expansion of the regularized hypergeometric function with a singleton
lower parameter: `₀F̃₁(; b; w) = ∑' n, w ^ n / (n ! * Γ (b + n))`. -/
theorem complex_regularizedHGFun_zero_singleton_eq_tsum (b : ℂ /- [definition] -/ ) (w : ℂ /- [definition] -/ ) :
    complex_regularizedHGFun 0 {b} w = ∑' n, complex_regularizedHGFunCoeff 0 {b} n * w ^ n := by
  show ∑' n, (complex_regularizedHGFunSeries 0 {b}) n (fun _ => w) = _
  apply tsum_congr
  intro n
  simp [complex_regularizedHGFunSeries, smul_eq_mul]
  ring

/-- The key coefficient identity `(n + 1) * c_b (n + 1) = c_{b + 1} n` for the regularized
`₀F₁` coefficients.  Note that this holds for *all* `b : ℂ`, even at the poles of `Γ`
(where both sides vanish), since we use the regularized coefficients. -/
theorem complex_regularizedHGFunCoeff_zero_singleton_succ (b : ℂ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) :
    (n + 1 : ℂ) * complex_regularizedHGFunCoeff 0 {b} (n + 1) = complex_regularizedHGFunCoeff 0 {b + 1} n := by
  have hfact : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsucc : ((n : ℂ) + 1) ≠ 0 := by
    rw [show ((n : ℂ) + 1) = ((((n : ℝ)) + 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [complex_regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show b + ((n : ℂ) + 1) = b + 1 + ↑n by ring]
  by_cases hΓ : Complex.Gamma (b + 1 + (n : ℂ)) = 0
  · simp [hΓ]
  · field_simp [hΓ, hfact, hsucc]

/-- The radius of convergence of the `₀F̃₁(; b + 1; ·)` series is infinite: shifting the
parameter of an entire `₀F̃₁` series preserves entireness. -/
theorem complex_radius_regularizedHGFunSeries_zero_singleton_succ (b : ℂ /- [definition] -/ ) :
    (complex_regularizedHGFunSeries 0 {b + 1}).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r => ?_
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hs1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hq_norm : ∀ n : ℕ, ‖complex_regularizedHGFunSeries 0 {b + 1} n‖
      = ‖complex_regularizedHGFunCoeff 0 {b + 1} n‖ := by
    intro n
    simp [complex_regularizedHGFunSeries, FormalMultilinearSeries.ofScalars, norm_smul]
  have hp_coeff_le : ∀ n : ℕ, ‖complex_regularizedHGFunCoeff 0 {b} n‖
      ≤ ‖complex_regularizedHGFunSeries 0 {b} n‖ := by
    intro n
    have h1 : (complex_regularizedHGFunSeries 0 {b}) n (fun _ => (1 : ℂ))
        = complex_regularizedHGFunCoeff 0 {b} n := by
      simp [complex_regularizedHGFunSeries, smul_eq_mul]
    rw [← h1]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
    simp
  have hcoeff_norm : ∀ n : ℕ, ‖complex_regularizedHGFunCoeff 0 {b + 1} n‖
      = (n + 1 : ℝ) * ‖complex_regularizedHGFunCoeff 0 {b} (n + 1)‖ := by
    intro n
    rw [← complex_regularizedHGFunCoeff_zero_singleton_succ b n, norm_mul]
    congr 1
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by norm_cast, RCLike.norm_natCast,
      Nat.cast_add_one]
  have hA : Summable fun n : ℕ => ‖complex_regularizedHGFunSeries 0 {b} n‖ * ((r : ℝ) + 1) ^ n := by
    have h := (complex_regularizedHGFunSeries 0 {b}).summable_norm_mul_pow (r := r + 1) (by
      rw [complex_radius_regularizedHGFunSeries_zero_eq_top]
      exact ENNReal.coe_lt_top)
    simpa using h
  have hA' : Summable fun n : ℕ => ‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hA
  set C : ℝ := ∑' m : ℕ, ‖complex_regularizedHGFunSeries 0 {b} (m + 1)‖ * ((r : ℝ) + 1) ^ (m + 1)
    with hC_def
  have hC : ∀ n : ℕ, ‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) ≤ C :=
    fun n => hA'.le_tsum n (fun m _ => by positivity)
  have ht : Summable fun n : ℕ =>
      (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n * (C / ((r : ℝ) + 1)) := by
    have ht1 : ‖(r : ℝ) / ((r : ℝ) + 1)‖ < 1 := by
      rw [norm_div, Real.norm_of_nonneg hr0, Real.norm_of_nonneg hs1.le]
      exact (div_lt_one hs1).2 (lt_add_one _)
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ((r : ℝ) / ((r : ℝ) + 1)) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 ht1
    have h2 : Summable fun n : ℕ => ((r : ℝ) / ((r : ℝ) + 1)) ^ n :=
      summable_geometric_of_norm_lt_one ht1
    refine ((h1.add h2).mul_right (C / ((r : ℝ) + 1))).congr fun n => ?_
    ring
  have hbound : ∀ n : ℕ, (n + 1 : ℝ) * ‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n
      ≤ (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n * (C / ((r : ℝ) + 1)) := by
    intro n
    have hs2 : ((r : ℝ) + 1) ^ (n + 1) ≠ 0 := pow_ne_zero _ hs1.ne'
    have he : (n + 1 : ℝ) * ‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n
        = (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n
          * (‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) / ((r : ℝ) + 1)) := by
      rw [div_pow]
      field_simp [hs2, hs1.ne']
      ring
    rw [he]
    have hnn2 : (0 : ℝ) ≤ (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n := by positivity
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hs1).2 (hC n)) hnn2
  have hkey : ∀ n : ℕ, ‖complex_regularizedHGFunSeries 0 {b + 1} n‖ * (r : ℝ) ^ n
      ≤ (n + 1 : ℝ) * ‖complex_regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n := by
    intro n
    rw [hq_norm n, hcoeff_norm n]
    have h1 := hp_coeff_le (n + 1)
    have hnn : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
    have hnr : (0 : ℝ) ≤ (r : ℝ) ^ n := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hnn) hnr
  exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => (hkey n).trans (hbound n)) ht

/-- The derivative of the `(n + 1)`-th partial sum of the `₀F̃₁(; b; ·)` series is the `n`-th
partial sum of the `₀F̃₁(; b + 1; ·)` series. -/
theorem complex_hasDerivAt_partialSum_regularizedHGFunSeries_zero_singleton (b : ℂ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) (x : ℂ /- [definition] -/ ) :
    HasDerivAt (fun w => (complex_regularizedHGFunSeries 0 {b}).partialSum (n + 1) w)
      ((complex_regularizedHGFunSeries 0 {b + 1}).partialSum n x) x := by
  have hsum := HasDerivAt.sum (u := Finset.range (n + 1))
    (fun k (_ : k ∈ Finset.range (n + 1)) =>
      ((hasDerivAt_pow k x).const_mul (complex_regularizedHGFunCoeff 0 {b} k)))
  have h1 : (fun w => (complex_regularizedHGFunSeries 0 {b}).partialSum (n + 1) w)
      = ∑ k ∈ Finset.range (n + 1), fun w => complex_regularizedHGFunCoeff 0 {b} k * w ^ k := by
    funext w
    rw [Finset.sum_apply]
    simp only [FormalMultilinearSeries.partialSum, complex_regularizedHGFunSeries]
    apply Finset.sum_congr rfl
    intro k _
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have h2 : (complex_regularizedHGFunSeries 0 {b + 1}).partialSum n x
      = ∑ k ∈ Finset.range (n + 1), complex_regularizedHGFunCoeff 0 {b} k * ((k : ℂ) * x ^ (k - 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
    simp only [FormalMultilinearSeries.partialSum, complex_regularizedHGFunSeries]
    apply Finset.sum_congr rfl
    intro k _
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    calc complex_regularizedHGFunCoeff 0 {b + 1} k * x ^ k
        = ((↑k + 1) * complex_regularizedHGFunCoeff 0 {b} (k + 1)) * x ^ k := by
          rw [complex_regularizedHGFunCoeff_zero_singleton_succ]
      _ = complex_regularizedHGFunCoeff 0 {b} (k + 1) * ((↑k + 1) * x ^ k) := by ring
  rw [h1, h2]
  exact hsum

/-- The fundamental derivative identity for the regularized `₀F₁` function with a singleton
lower parameter: `d/dw ₀F̃₁(; b; w) = ₀F̃₁(; b + 1; w)`.  Proved by locally uniform
term-by-term differentiation of the defining power series. -/
theorem complex_hasDerivAt_regularizedHGFun_zero_singleton (b : ℂ /- [definition] -/ ) (w : ℂ /- [definition] -/ ) :
    HasDerivAt (complex_regularizedHGFun 0 {b}) (complex_regularizedHGFun 0 {b + 1} w) w := by
  show HasDerivAt (complex_regularizedHGFunSeries 0 {b}).sum ((complex_regularizedHGFunSeries 0 {b + 1}).sum w) w
  have hr : (complex_regularizedHGFunSeries 0 {b + 1}).radius = ⊤ :=
    complex_radius_regularizedHGFunSeries_zero_singleton_succ b
  have hball := (complex_regularizedHGFunSeries 0 {b + 1}).hasFPowerSeriesOnBall (by
    rw [hr]; exact ENNReal.zero_lt_top)
  have hUL : TendstoLocallyUniformlyOn
      (fun n y => (complex_regularizedHGFunSeries 0 {b + 1}).partialSum n y)
      (complex_regularizedHGFunSeries 0 {b + 1}).sum atTop (Set.univ : Set ℂ) := by
    have h := hball.tendstoLocallyUniformlyOn'
    rw [hr, Metric.eball_top_eq_univ] at h
    simpa only [sub_zero] using h
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (isOpen_univ) (hUL)
    (f := fun n w => (complex_regularizedHGFunSeries 0 {b}).partialSum (n + 1) w) ?_ ?_ (Set.mem_univ w)
  · exact Filter.Eventually.of_forall fun n x _ =>
      complex_hasDerivAt_partialSum_regularizedHGFunSeries_zero_singleton b n x
  · intro x _
    have hx : x ∈ Metric.eball (0 : ℂ) (complex_regularizedHGFunSeries 0 {b}).radius := by
      rw [complex_radius_regularizedHGFunSeries_zero_eq_top, Metric.eball_top_eq_univ]
      exact Set.mem_univ x
    have h := ((complex_regularizedHGFunSeries 0 {b}).hasSum hx).tendsto_sum_nat
    simpa [Function.comp_def, FormalMultilinearSeries.partialSum] using
      h.comp (Filter.tendsto_add_atTop_nat 1)

/-- The `₀F̃₁` three-term recurrence `w * ₀F̃₁(; b + 2; w) + b * ₀F̃₁(; b + 1; w) = ₀F̃₁(; b; w)`,
valid when `b` is not a nonpositive integer.  This is `Γ(s + 1) = s Γ(s)` at the level of
power series coefficients. -/
theorem complex_regularizedHGFun_zero_singleton_recurrence (b : ℂ /- [definition] -/ ) (hb : ∀ n : ℕ, b + (n : ℂ) ≠ 0 /- [standing] -/ )
    (w : ℂ /- [definition] -/ ) :
    w * complex_regularizedHGFun 0 {b + 2} w + b * complex_regularizedHGFun 0 {b + 1} w
      = complex_regularizedHGFun 0 {b} w := by
  have hb0 : b ≠ 0 := by
    have h := hb 0
    simpa using h
  have hs : ∀ n : ℕ, b + 1 + (n : ℂ) ≠ 0 := by
    intro n
    have h := hb (n + 1)
    push_cast at h
    rwa [show b + 1 + (n : ℂ) = b + (↑n + 1) by ring]
  have hcoeff : ∀ n : ℕ, complex_regularizedHGFunCoeff 0 {b + 2} n
      + b * complex_regularizedHGFunCoeff 0 {b + 1} (n + 1) = complex_regularizedHGFunCoeff 0 {b} (n + 1) := by
    intro n
    have hfact : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hsucc : ((n : ℂ) + 1) ≠ 0 := by
      rw [show ((n : ℂ) + 1) = ((((n : ℝ)) + 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [complex_regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [show b + 2 + (n : ℂ) = (b + 1 + ↑n) + 1 by ring,
      show b + 1 + (↑n + 1) = (b + 1 + ↑n) + 1 by ring,
      show b + (↑n + 1) = b + 1 + ↑n by ring,
      Complex.Gamma_add_one (b + 1 + ↑n) (hs n)]
    by_cases hG : Complex.Gamma (b + 1 + (n : ℂ)) = 0
    · simp [hG]
    · field_simp [hG, hs n, hfact, hsucc]
      ring
  have h0 : b * complex_regularizedHGFunCoeff 0 {b + 1} 0 = complex_regularizedHGFunCoeff 0 {b} 0 := by
    simp only [complex_regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
    rw [Complex.Gamma_add_one b hb0]
    by_cases hG : Complex.Gamma b = 0
    · simp [hG]
    · field_simp [hG, hb0]
  have hr1 : (complex_regularizedHGFunSeries 0 {b + 1}).radius = ⊤ :=
    complex_radius_regularizedHGFunSeries_zero_singleton_succ b
  have hr2 : (complex_regularizedHGFunSeries 0 {b + 2}).radius = ⊤ := by
    rw [show b + 2 = b + 1 + 1 by ring]
    exact complex_radius_regularizedHGFunSeries_zero_singleton_succ (b + 1)
  have hs_b : Summable fun n => complex_regularizedHGFunCoeff 0 {b} n * w ^ n := by
    apply ((complex_regularizedHGFunSeries 0 {b}).summable (x := w) (by
      rw [complex_radius_regularizedHGFunSeries_zero_eq_top, Metric.eball_top_eq_univ]
      exact Set.mem_univ w)).congr
    intro n
    simp [complex_regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs_b1 : Summable fun n => complex_regularizedHGFunCoeff 0 {b + 1} n * w ^ n := by
    apply ((complex_regularizedHGFunSeries 0 {b + 1}).summable (x := w) (by
      rw [hr1, Metric.eball_top_eq_univ]; exact Set.mem_univ w)).congr
    intro n
    simp [complex_regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs_b2 : Summable fun n => complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ n := by
    apply ((complex_regularizedHGFunSeries 0 {b + 2}).summable (x := w) (by
      rw [hr2, Metric.eball_top_eq_univ]; exact Set.mem_univ w)).congr
    intro n
    simp [complex_regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs1shift : Summable fun n => b * (complex_regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1)) :=
    ((summable_nat_add_iff 1).2 hs_b1).mul_left b
  have hs2shift : Summable fun n => complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) := by
    refine (hs_b2.mul_right w).congr fun n => ?_
    rw [pow_succ']; ring
  rw [complex_regularizedHGFun_zero_singleton_eq_tsum b, complex_regularizedHGFun_zero_singleton_eq_tsum (b + 1),
    complex_regularizedHGFun_zero_singleton_eq_tsum (b + 2), ← tsum_mul_left, ← tsum_mul_left]
  have hw2 : (∑' n, w * (complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ n))
      = ∑' n, complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) :=
    tsum_congr fun n => by rw [pow_succ']; ring
  rw [hw2]
  have hsplit0 : (∑' n, complex_regularizedHGFunCoeff 0 {b} n * w ^ n)
      = complex_regularizedHGFunCoeff 0 {b} 0 + ∑' n, complex_regularizedHGFunCoeff 0 {b} (n + 1) * w ^ (n + 1) := by
    have h := tsum_eq_zero_add' (f := fun n => complex_regularizedHGFunCoeff 0 {b} n * w ^ n)
      ((summable_nat_add_iff 1).2 hs_b)
    simpa using h
  have hsplit1 : (∑' n, b * (complex_regularizedHGFunCoeff 0 {b + 1} n * w ^ n))
      = complex_regularizedHGFunCoeff 0 {b} 0
        + ∑' n, b * (complex_regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1)) := by
    have h := tsum_eq_zero_add' (f := fun n => b * (complex_regularizedHGFunCoeff 0 {b + 1} n * w ^ n))
      hs1shift
    have h0' : b * (complex_regularizedHGFunCoeff 0 {b + 1} 0 * w ^ 0) = complex_regularizedHGFunCoeff 0 {b} 0 := by
      simp only [pow_zero, mul_one]
      exact h0
    rwa [h0'] at h
  rw [hsplit0, hsplit1, add_comm (∑' n, complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1)) _,
    add_assoc, add_left_cancel_iff, ← Summable.tsum_add hs1shift hs2shift]
  apply tsum_congr
  intro n
  calc b * (complex_regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1))
        + complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1)
      = (b * complex_regularizedHGFunCoeff 0 {b + 1} (n + 1)) * w ^ (n + 1)
        + complex_regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) := by ring
    _ = (complex_regularizedHGFunCoeff 0 {b + 2} n + b * complex_regularizedHGFunCoeff 0 {b + 1} (n + 1))
        * w ^ (n + 1) := by ring
    _ = complex_regularizedHGFunCoeff 0 {b} (n + 1) * w ^ (n + 1) := by rw [hcoeff n]

section AiryODE

/-- The derivative of `z ↦ z ^ 3 / 9`. -/
theorem complex_hasDerivAt_cube_div_nine (z : ℂ /- [definition] -/ ) :
    HasDerivAt (fun z : ℂ => z ^ 3 / 9) (3 * z ^ 2 / 9) z := by
  convert! (hasDerivAt_pow 3 z).div_const 9 using 1

theorem complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) :
    HasDerivAt (fun z => complex_regularizedHGFun 0 {b} (z ^ 3 / 9))
      (3 * z ^ 2 / 9 * complex_regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  convert! (complex_hasDerivAt_regularizedHGFun_zero_singleton b (z ^ 3 / 9)).comp z
    (complex_hasDerivAt_cube_div_nine z) using 1 <;> ring

theorem complex_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ /- [definition] -/ ) :
    deriv (fun z => complex_regularizedHGFun 0 {b} (z ^ 3 / 9))
      = fun z => 3 * z ^ 2 / 9 * complex_regularizedHGFun 0 {b + 1} (z ^ 3 / 9) :=
  funext fun z => (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine b z).deriv

theorem complex_hasDerivAt_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ /- [definition] -/ )
    (hb : ∀ n : ℕ, b + (n : ℂ) ≠ 0 /- [standing] -/ ) (z : ℂ /- [definition] -/ ) :
    HasDerivAt (deriv (fun z => complex_regularizedHGFun 0 {b} (z ^ 3 / 9)))
      (z * complex_regularizedHGFun 0 {b} (z ^ 3 / 9) +
        (2 / 3 - b) * z * complex_regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  rw [complex_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine b]
  have key := (((hasDerivAt_pow 2 z).const_mul 3).div_const 9).fun_mul
    (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (b + 1) z)
  convert! key using 1
  have hrec := complex_regularizedHGFun_zero_singleton_recurrence b hb (z ^ 3 / 9)
  rw [show b + 1 + 1 = b + 2 by ring, ← hrec]
  ring

theorem complex_two_thirds_add_nat_ne_zero (n : ℕ /- [definition] -/ ) : (2 / 3 : ℂ) + (n : ℂ) ≠ 0 := by
  rw [show (2 / 3 : ℂ) + (n : ℂ) = (((2 / 3 + n : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem complex_four_thirds_add_nat_ne_zero (n : ℕ /- [definition] -/ ) : (4 / 3 : ℂ) + (n : ℂ) ≠ 0 := by
  rw [show (4 / 3 : ℂ) + (n : ℂ) = (((4 / 3 + n : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem complex_hasDerivAt_deriv_u_two_thirds (z : ℂ /- [definition] -/ ) :
    HasDerivAt (deriv (fun z => complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)))
      (z * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := complex_hasDerivAt_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
    (fun n => complex_two_thirds_add_nat_ne_zero n) z
  convert! h using 1
  simp [sub_self]

theorem complex_hasDerivAt_z_mul_four_thirds (z : ℂ /- [definition] -/ ) :
    HasDerivAt (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
      (complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) +
        z * (3 * z ^ 2 / 9 * complex_regularizedHGFun 0 {(4 / 3 : ℂ) + 1} (z ^ 3 / 9))) z := by
  convert! (hasDerivAt_id' (x := z)).fun_mul
    (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (4 / 3 : ℂ) z) using 1
  ring

theorem complex_deriv_z_mul_four_thirds :
    deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
      = fun z => complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) +
          z * (3 * z ^ 2 / 9 * complex_regularizedHGFun 0 {(4 / 3 : ℂ) + 1} (z ^ 3 / 9)) :=
  funext fun z => (complex_hasDerivAt_z_mul_four_thirds z).deriv

theorem complex_hasDerivAt_deriv_z_mul_four_thirds (z : ℂ /- [definition] -/ ) :
    HasDerivAt (deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)))
      (z * (z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z := by
  rw [complex_deriv_z_mul_four_thirds]
  have key := (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (4 / 3 : ℂ) z).fun_add
    ((hasDerivAt_id' (x := z)).fun_mul (((hasDerivAt_pow 2 z).const_mul 3 |>.div_const 9).fun_mul
      (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine ((4 / 3 : ℂ) + 1) z)))
  convert! key using 1
  have hrec := complex_regularizedHGFun_zero_singleton_recurrence (4 / 3 : ℂ)
    (fun n => complex_four_thirds_add_nat_ne_zero n) (z ^ 3 / 9)
  rw [show (4 / 3 : ℂ) + 1 + 1 = 4 / 3 + 2 by ring, ← hrec]
  ring


theorem complex_airyAi_eq : complex_airyAi = fun w => (3 : ℂ) ^ (-2 / 3 : ℂ)
      * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (w ^ 3 / 9)
    - (3 : ℂ) ^ (-4 / 3 : ℂ) * (w * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (w ^ 3 / 9)) := by
  funext w
  simp only [complex_airyAi]
  ring

theorem complex_airyBi_eq : complex_airyBi = fun w => (3 : ℂ) ^ (-1 / 6 : ℂ)
      * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (w ^ 3 / 9)
    + (3 : ℂ) ^ (-5 / 6 : ℂ) * (w * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (w ^ 3 / 9)) := by
  funext w
  simp only [complex_airyBi]
  ring

theorem complex_deriv_airyAi :
    deriv complex_airyAi = fun w => (3 : ℂ) ^ (-2 / 3 : ℂ)
        * deriv (fun z => complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) w
      - (3 : ℂ) ^ (-4 / 3 : ℂ)
        * deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) w := by
  funext w
  rw [complex_airyAi_eq]
  rw [deriv_fun_sub ((complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt.const_mul _)
    ((complex_hasDerivAt_z_mul_four_thirds w).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt,
    deriv_const_mul _ (complex_hasDerivAt_z_mul_four_thirds w).differentiableAt]

theorem complex_deriv_airyBi :
    deriv complex_airyBi = fun w => (3 : ℂ) ^ (-1 / 6 : ℂ)
        * deriv (fun z => complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) w
      + (3 : ℂ) ^ (-5 / 6 : ℂ)
        * deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) w := by
  funext w
  rw [complex_airyBi_eq]
  rw [deriv_fun_add ((complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt.const_mul _)
    ((complex_hasDerivAt_z_mul_four_thirds w).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt,
    deriv_const_mul _ (complex_hasDerivAt_z_mul_four_thirds w).differentiableAt]

theorem complex_iteratedDeriv_two_airyAi (z : ℂ /- [definition] -/ ) : iteratedDeriv 2 complex_airyAi z = z * complex_airyAi z := by
  have hdu23 : deriv (deriv (fun z => complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) :=
    (complex_hasDerivAt_deriv_u_two_thirds z).deriv
  have hds : deriv (deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * (z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) :=
    (complex_hasDerivAt_deriv_z_mul_four_thirds z).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, complex_deriv_airyAi]
  rw [deriv_fun_sub ((complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _)
    ((complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt,
    deriv_const_mul _ (complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt, hdu23, hds]
  simp only [complex_airyAi_eq]
  ring

theorem complex_iteratedDeriv_two_airyBi (z : ℂ /- [definition] -/ ) : iteratedDeriv 2 complex_airyBi z = z * complex_airyBi z := by
  have hdu23 : deriv (deriv (fun z => complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) :=
    (complex_hasDerivAt_deriv_u_two_thirds z).deriv
  have hds : deriv (deriv (fun z => z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * (z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) :=
    (complex_hasDerivAt_deriv_z_mul_four_thirds z).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, complex_deriv_airyBi]
  rw [deriv_fun_add ((complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _)
    ((complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt,
    deriv_const_mul _ (complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt, hdu23, hds]
  simp only [complex_airyBi_eq]
  ring


/-- The regularized `₀F₁` coefficient with a real (cast) lower parameter is real, hence
`star`-invariant. -/
theorem complex_star_regularizedHGFunCoeff_zero_singleton_real (t : ℝ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) :
    star (complex_regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n)
      = complex_regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n := by
  have hG : Complex.Gamma (((t : ℝ) : ℂ) + (n : ℂ)) = ((Real.Gamma (t + n) : ℝ) : ℂ) := by
    rw [show ((t : ℝ) : ℂ) + (n : ℂ) = ((t + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have e : complex_regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n
      = ((1 / (n ! * Real.Gamma (t + n)) : ℝ) : ℂ) := by
    simp only [complex_regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
      Multiset.map_singleton, Multiset.prod_singleton]
    rw [hG]
    push_cast
    ring
  rw [e, Complex.star_def, Complex.conj_ofReal]

/-- `₀F̃₁(; b; ·)` with a real parameter `b` commutes with complex conjugation. -/
theorem complex_regularizedHGFun_zero_singleton_real_conj (t : ℝ /- [definition] -/ ) (w : ℂ /- [definition] -/ ) :
    star (complex_regularizedHGFun 0 {((t : ℝ) : ℂ)} w) = complex_regularizedHGFun 0 {((t : ℝ) : ℂ)} (star w) := by
  rw [complex_regularizedHGFun_zero_singleton_eq_tsum, complex_regularizedHGFun_zero_singleton_eq_tsum, tsum_star]
  apply tsum_congr
  intro n
  rw [star_mul', star_pow, complex_star_regularizedHGFunCoeff_zero_singleton_real]

theorem complex_airyAi_conj (z : ℂ /- [definition] -/ ) : complex_airyAi (star z) = star (complex_airyAi z) := by
  have hF23 : ∀ w : ℂ, star (complex_regularizedHGFun 0 {(2 / 3 : ℂ)} w)
      = complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (star w) := by
    intro w
    have h := complex_regularizedHGFun_zero_singleton_real_conj (2 / 3 : ℝ) w
    rwa [show ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) by norm_num] at h
  have hF43 : ∀ w : ℂ, star (complex_regularizedHGFun 0 {(4 / 3 : ℂ)} w)
      = complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (star w) := by
    intro w
    have h := complex_regularizedHGFun_zero_singleton_real_conj (4 / 3 : ℝ) w
    rwa [show ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) by norm_num] at h
  have hc23 : ((3 : ℂ) ^ (-2 / 3 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-2 / 3 : ℝ)) := by
    rw [show (-2 / 3 : ℂ) = ((-2 / 3 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-2 / 3)]
  have hc43 : ((3 : ℂ) ^ (-4 / 3 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-4 / 3 : ℝ)) := by
    rw [show (-4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-4 / 3)]
  have hz39 : star (z ^ 3 / 9) = (star z) ^ 3 / 9 := by
    rw [star_div₀, star_pow, star_ofNat]
  show (3 : ℂ) ^ (-2 / 3 : ℂ) * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} ((star z) ^ 3 / 9)
      - (3 : ℂ) ^ (-4 / 3 : ℂ) * (star z) * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} ((star z) ^ 3 / 9)
    = star ((3 : ℂ) ^ (-2 / 3 : ℂ) * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
      - (3 : ℂ) ^ (-4 / 3 : ℂ) * z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
  rw [hc23, hc43, star_sub, star_mul', star_mul', star_mul', hF23, hF43, hz39, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_ofReal]

theorem complex_airyBi_conj (z : ℂ /- [definition] -/ ) : complex_airyBi (star z) = star (complex_airyBi z) := by
  have hF23 : ∀ w : ℂ, star (complex_regularizedHGFun 0 {(2 / 3 : ℂ)} w)
      = complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (star w) := by
    intro w
    have h := complex_regularizedHGFun_zero_singleton_real_conj (2 / 3 : ℝ) w
    rwa [show ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) by norm_num] at h
  have hF43 : ∀ w : ℂ, star (complex_regularizedHGFun 0 {(4 / 3 : ℂ)} w)
      = complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (star w) := by
    intro w
    have h := complex_regularizedHGFun_zero_singleton_real_conj (4 / 3 : ℝ) w
    rwa [show ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) by norm_num] at h
  have hc16 : ((3 : ℂ) ^ (-1 / 6 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-1 / 6 : ℝ)) := by
    rw [show (-1 / 6 : ℂ) = ((-1 / 6 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-1 / 6)]
  have hc56 : ((3 : ℂ) ^ (-5 / 6 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-5 / 6 : ℝ)) := by
    rw [show (-5 / 6 : ℂ) = ((-5 / 6 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-5 / 6)]
  have hz39 : star (z ^ 3 / 9) = (star z) ^ 3 / 9 := by
    rw [star_div₀, star_pow, star_ofNat]
  show (3 : ℂ) ^ (-1 / 6 : ℂ) * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} ((star z) ^ 3 / 9)
      + (3 : ℂ) ^ (-5 / 6 : ℂ) * (star z) * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} ((star z) ^ 3 / 9)
    = star ((3 : ℂ) ^ (-1 / 6 : ℂ) * complex_regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
      + (3 : ℂ) ^ (-5 / 6 : ℂ) * z * complex_regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
  rw [hc16, hc56, star_add, star_mul', star_mul', star_mul', hF23, hF43, hz39, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_ofReal]

end AiryODE


end source2

noncomputable section source3
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # Real-valued Airy functions

The Airy functions `complex_airyAi` and `complex_airyBi` are real-valued on the real axis
(all coefficients of their defining `₀F̃₁` series are real, cf. `complex_airyAi_conj` and
`complex_airyBi_conj`).  This file introduces the
real restrictions `airyAiReal, airyBiReal : ℝ → ℝ`, transfers the Airy differential
equation to them, and evaluates the derivatives at the origin.

## Main results

* `airyAiReal_ofReal`, `airyBiReal_ofReal`: `↑(airyAiReal x) = complex_airyAi ↑x`
  (and the `Bi` analogue): the real functions really are the restrictions.
* `hasDerivAt_airyAiReal`, `hasDerivAt_airyBiReal`: real differentiability, with derivative
  the real part of the complex derivative (`HasDerivAt.real_of_complex`).
* `iteratedDeriv_two_airyAiReal`, `iteratedDeriv_two_airyBiReal`: the real Airy ODE
  `iteratedDeriv 2 airyAiReal x = x * airyAiReal x`.
* `complex_deriv_airyAi_zero`, `complex_deriv_airyBi_zero`: the derivative values at `0`,
  `Ai'(0) = -3^(-4/3)/Γ(4/3)` and `Bi'(0) = 3^(-5/6)/Γ(4/3)` (DLMF 9.2, using
  `Γ(4/3) = Γ(1/3)/3`), and the real versions `deriv_airyAiReal_zero`, `deriv_airyBiReal_zero`.
* `airyAiReal_zero_pos`, `deriv_airyAiReal_zero_neg`, `airyBiReal_zero_pos`,
  `deriv_airyBiReal_zero_pos`: signs at the origin.
* `complex_Gamma_four_thirds`, `real_Gamma_four_thirds`: `Γ(4/3) = Γ(1/3)/3`.
-/

open scoped Topology


/-- For real `t`, the complex power `(3 : ℂ) ^ (t : ℂ)` is the cast of the real power
`3 ^ t`. -/
theorem complex_three_cpow_ofReal (t : ℝ /- [definition] -/ ) : (3 : ℂ) ^ (t : ℂ) = ((3 ^ t : ℝ) : ℂ) := by
  rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) t]

/-- `Γ(4/3) = Γ(1/3)/3` (complex). -/
theorem complex_Gamma_four_thirds : Complex.Gamma (4/3 : ℂ) = Complex.Gamma (1/3 : ℂ) / 3 := by
  have h := Complex.Gamma_add_one (1/3 : ℂ) (by norm_num)
  rw [show (1/3 : ℂ) + 1 = 4/3 by norm_num] at h
  rw [h]
  ring

/-- The singleton regularized hypergeometric function at `0`: `₀F̃₁(; b; 0) = 1/Γ(b)`. -/
theorem complex_regularizedHGFun_zero_singleton_apply_zero (b : ℂ /- [definition] -/ ) :
    complex_regularizedHGFun 0 {b} 0 = 1 / Complex.Gamma b := by
  rw [complex_regularizedHGFun_zero]
  simp [complex_regularizedHGFunCoeff]

/-- The derivative of `Ai` at `0`: `Ai'(0) = -3^(-4/3)/Γ(4/3)` (DLMF 9.2.4, using
`Γ(4/3) = Γ(1/3)/3`; the first hypergeometric summand contributes `0` since its derivative
carries a factor `z²/3`). -/
theorem complex_deriv_airyAi_zero :
    deriv complex_airyAi 0 = -((3 : ℂ)^(-4/3 : ℂ) / Complex.Gamma (4/3 : ℂ)) := by
  have h03 : (0 : ℂ)^3/9 = 0 := by norm_num
  have h1 := complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2/3 : ℂ) 0
  have h2 := complex_hasDerivAt_z_mul_four_thirds 0
  have h := (h1.const_mul ((3:ℂ)^(-2/3 : ℂ))).sub (h2.const_mul ((3:ℂ)^(-4/3 : ℂ)))
  rw [complex_airyAi_eq]
  convert! h.deriv using 1
  rw [h03, complex_regularizedHGFun_zero_singleton_apply_zero (4/3 : ℂ)]
  ring

/-- The derivative of `Bi` at `0`: `Bi'(0) = 3^(-5/6)/Γ(4/3)` (DLMF 9.2.4). -/
theorem complex_deriv_airyBi_zero :
    deriv complex_airyBi 0 = (3 : ℂ)^(-5/6 : ℂ) / Complex.Gamma (4/3 : ℂ) := by
  have h03 : (0 : ℂ)^3/9 = 0 := by norm_num
  have h1 := complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2/3 : ℂ) 0
  have h2 := complex_hasDerivAt_z_mul_four_thirds 0
  have h := (h1.const_mul ((3:ℂ)^(-1/6 : ℂ))).add (h2.const_mul ((3:ℂ)^(-5/6 : ℂ)))
  rw [complex_airyBi_eq]
  convert! h.deriv using 1
  rw [h03, complex_regularizedHGFun_zero_singleton_apply_zero (4/3 : ℂ)]
  ring

/-- `deriv (deriv complex_airyAi)` exists everywhere (it equals `z * complex_airyAi z`). -/
theorem complex_differentiableAt_deriv_airyAi (z : ℂ /- [definition] -/ ) : DifferentiableAt ℂ (deriv complex_airyAi) z := by
  rw [complex_deriv_airyAi]
  exact ((complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _).sub
    ((complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)

/-- `deriv (deriv complex_airyBi)` exists everywhere. -/
theorem complex_differentiableAt_deriv_airyBi (z : ℂ /- [definition] -/ ) : DifferentiableAt ℂ (deriv complex_airyBi) z := by
  rw [complex_deriv_airyBi]
  exact ((complex_hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _).add
    ((complex_hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)


/-- The real-valued Airy function of the first kind on `ℝ`.  It equals `complex_airyAi` at
real points (`airyAiReal_ofReal`). -/
noncomputable def airyAiReal (x : ℝ /- [definition] -/ ) : ℝ := (complex_airyAi (x : ℂ)).re

/-- The real-valued Airy function of the second kind on `ℝ`. -/
noncomputable def airyBiReal (x : ℝ /- [definition] -/ ) : ℝ := (complex_airyBi (x : ℂ)).re

/-- `Ai` is real-valued on the real axis: `↑(airyAiReal x) = complex_airyAi ↑x`. -/
theorem airyAiReal_ofReal (x : ℝ /- [definition] -/ ) : ((airyAiReal x : ℝ) : ℂ) = complex_airyAi (x : ℂ) := by
  have h : star (complex_airyAi (x : ℂ)) = complex_airyAi (x : ℂ) := by
    have h' := complex_airyAi_conj (x : ℂ)
    rw [show star (x : ℂ) = (x : ℂ) by simp] at h'
    exact h'.symm
  have him : (complex_airyAi (x : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im h
    have h3 : (star (complex_airyAi (x : ℂ))).im = -(complex_airyAi (x : ℂ)).im := by
      simp
    linarith
  unfold airyAiReal
  rw [Complex.ext_iff]
  constructor <;> simp [him]

/-- `Bi` is real-valued on the real axis: `↑(airyBiReal x) = complex_airyBi ↑x`. -/
theorem airyBiReal_ofReal (x : ℝ /- [definition] -/ ) : ((airyBiReal x : ℝ) : ℂ) = complex_airyBi (x : ℂ) := by
  have h : star (complex_airyBi (x : ℂ)) = complex_airyBi (x : ℂ) := by
    have h' := complex_airyBi_conj (x : ℂ)
    rw [show star (x : ℂ) = (x : ℂ) by simp] at h'
    exact h'.symm
  have him : (complex_airyBi (x : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im h
    have h3 : (star (complex_airyBi (x : ℂ))).im = -(complex_airyBi (x : ℂ)).im := by
      simp
    linarith
  unfold airyBiReal
  rw [Complex.ext_iff]
  constructor <;> simp [him]

/-- Real differentiability of `airyAiReal`: the derivative is the real part of the complex
derivative. -/
theorem hasDerivAt_airyAiReal (x : ℝ /- [definition] -/ ) :
    HasDerivAt airyAiReal ((deriv complex_airyAi (x : ℂ)).re) x := by
  show HasDerivAt (fun y : ℝ => (complex_airyAi (y : ℂ)).re) _ _
  exact ((complex_analyticAt_airyAi _).differentiableAt.hasDerivAt).real_of_complex

/-- Real differentiability of `airyBiReal`. -/
theorem hasDerivAt_airyBiReal (x : ℝ /- [definition] -/ ) :
    HasDerivAt airyBiReal ((deriv complex_airyBi (x : ℂ)).re) x := by
  show HasDerivAt (fun y : ℝ => (complex_airyBi (y : ℂ)).re) _ _
  exact ((complex_analyticAt_airyBi _).differentiableAt.hasDerivAt).real_of_complex

/-- The derivative of `airyAiReal`, as a function. -/
theorem deriv_airyAiReal :
    deriv airyAiReal = fun x : ℝ => (deriv complex_airyAi (x : ℂ)).re :=
  funext fun x => (hasDerivAt_airyAiReal x).deriv

/-- The derivative of `airyBiReal`, as a function. -/
theorem deriv_airyBiReal :
    deriv airyBiReal = fun x : ℝ => (deriv complex_airyBi (x : ℂ)).re :=
  funext fun x => (hasDerivAt_airyBiReal x).deriv

/-- The derivative of `deriv airyAiReal` is the real part of the second complex
derivative. -/
theorem hasDerivAt_deriv_airyAiReal (x : ℝ /- [definition] -/ ) :
    HasDerivAt (deriv airyAiReal) ((deriv (deriv complex_airyAi) (x : ℂ)).re) x := by
  rw [deriv_airyAiReal]
  exact (complex_differentiableAt_deriv_airyAi _).hasDerivAt.real_of_complex

/-- The derivative of `deriv airyBiReal`. -/
theorem hasDerivAt_deriv_airyBiReal (x : ℝ /- [definition] -/ ) :
    HasDerivAt (deriv airyBiReal) ((deriv (deriv complex_airyBi) (x : ℂ)).re) x := by
  rw [deriv_airyBiReal]
  exact (complex_differentiableAt_deriv_airyBi _).hasDerivAt.real_of_complex

/-- The real Airy differential equation for `Ai`: `Ai'' = x · Ai` on `ℝ`. -/
theorem iteratedDeriv_two_airyAiReal (x : ℝ /- [definition] -/ ) :
    iteratedDeriv 2 airyAiReal x = x * airyAiReal x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_airyAiReal x).deriv]
  have h := complex_iteratedDeriv_two_airyAi (x : ℂ)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [h, Complex.mul_re]
  simp [airyAiReal]

/-- The real Airy differential equation for `Bi`: `Bi'' = x · Bi` on `ℝ`. -/
theorem iteratedDeriv_two_airyBiReal (x : ℝ /- [definition] -/ ) :
    iteratedDeriv 2 airyBiReal x = x * airyBiReal x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_airyBiReal x).deriv]
  have h := complex_iteratedDeriv_two_airyBi (x : ℂ)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [h, Complex.mul_re]
  simp [airyBiReal]

/-- The value `Ai'(0) = -3^(-4/3)/Γ(4/3)`, real version. -/
theorem deriv_airyAiReal_zero : deriv airyAiReal 0 = -(3 ^ (-4/3 : ℝ) / Real.Gamma (4/3)) := by
  have hval : (3 : ℂ)^(-4/3 : ℂ) / Complex.Gamma (4/3 : ℂ)
      = ((3 ^ (-4/3 : ℝ) / Real.Gamma (4/3) : ℝ) : ℂ) := by
    rw [show (-4/3 : ℂ) = ((-4/3 : ℝ) : ℂ) by norm_num, complex_three_cpow_ofReal,
      show (4/3 : ℂ) = ((4/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  rw [(hasDerivAt_airyAiReal 0).deriv, show ((0 : ℝ) : ℂ) = (0 : ℂ) by norm_cast,
    complex_deriv_airyAi_zero, hval]
  simp

/-- The value `Bi'(0) = 3^(-5/6)/Γ(4/3)`, real version. -/
theorem deriv_airyBiReal_zero : deriv airyBiReal 0 = 3 ^ (-5/6 : ℝ) / Real.Gamma (4/3) := by
  have hval : (3 : ℂ)^(-5/6 : ℂ) / Complex.Gamma (4/3 : ℂ)
      = ((3 ^ (-5/6 : ℝ) / Real.Gamma (4/3) : ℝ) : ℂ) := by
    rw [show (-5/6 : ℂ) = ((-5/6 : ℝ) : ℂ) by norm_num, complex_three_cpow_ofReal,
      show (4/3 : ℂ) = ((4/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  rw [(hasDerivAt_airyBiReal 0).deriv, show ((0 : ℝ) : ℂ) = (0 : ℂ) by norm_cast,
    complex_deriv_airyBi_zero, hval]
  simp

/-- The value `Ai(0) = 3^(-2/3)/Γ(2/3)`, real version. -/
theorem airyAiReal_zero : airyAiReal 0 = 3 ^ (-2/3 : ℝ) / Real.Gamma (2/3) := by
  have h1 : complex_airyAi 0 = ((3 ^ (-2/3 : ℝ) / Real.Gamma (2/3) : ℝ) : ℂ) := by
    rw [complex_airyAi_zero]
    rw [show (-2/3 : ℂ) = ((-2/3 : ℝ) : ℂ) by norm_num, complex_three_cpow_ofReal,
      show (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  show (complex_airyAi 0).re = 3 ^ (-2/3 : ℝ) / Real.Gamma (2/3)
  rw [h1, Complex.ofReal_re]

/-- The value `Bi(0) = 3^(-1/6)/Γ(2/3)`, real version. -/
theorem airyBiReal_zero : airyBiReal 0 = 3 ^ (-1/6 : ℝ) / Real.Gamma (2/3) := by
  have h1 : complex_airyBi 0 = ((3 ^ (-1/6 : ℝ) / Real.Gamma (2/3) : ℝ) : ℂ) := by
    rw [complex_airyBi_zero]
    rw [show (-1/6 : ℂ) = ((-1/6 : ℝ) : ℂ) by norm_num, complex_three_cpow_ofReal,
      show (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  show (complex_airyBi 0).re = 3 ^ (-1/6 : ℝ) / Real.Gamma (2/3)
  rw [h1, Complex.ofReal_re]

/-- `Γ(4/3) = Γ(1/3)/3` (real). -/
theorem real_Gamma_four_thirds : Real.Gamma (4/3) = Real.Gamma (1/3) / 3 := by
  have h := Real.Gamma_add_one (by norm_num : (1/3 : ℝ) ≠ 0)
  rw [show (1/3 : ℝ) + 1 = 4/3 by norm_num] at h
  rw [h]
  ring

/-- `Ai(0) > 0`. -/
theorem airyAiReal_zero_pos : 0 < airyAiReal 0 := by
  rw [airyAiReal_zero]
  positivity

/-- `Ai'(0) < 0`. -/
theorem deriv_airyAiReal_zero_neg : deriv airyAiReal 0 < 0 := by
  rw [deriv_airyAiReal_zero]
  exact neg_lt_zero.mpr (by positivity)

/-- `Bi(0) > 0`. -/
theorem airyBiReal_zero_pos : 0 < airyBiReal 0 := by
  rw [airyBiReal_zero]
  positivity

/-- `Bi'(0) > 0`. -/
theorem deriv_airyBiReal_zero_pos : 0 < deriv airyBiReal 0 := by
  rw [deriv_airyBiReal_zero]
  positivity

end source3

noncomputable section source4
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-
! # Gaussian tail asymptotics (the Mills ratio)

We study the Gaussian tail integral with temperature parameter `T > 0`,

`G_T(b) = ∫_b^∞ exp(-d²/(4T)) dd`,     (`gaussianTail T b`)

which is the integral form of the Mills ratio.  The classical two-term expansion

`G_T(b) = (2T/b) exp(-b²/(4T)) (1 - 2T/b² + O_T(b⁻⁴))`     as `b → ∞`

is proved here in exact `=O` form (`gaussianTail_asymptotic`), together with the standard
Mills upper bound `G_T(b) ≤ (2T/b) exp(-b²/(4T))` and the asymptotic equivalence
`G_T(b) ~ (2T/b) exp(-b²/(4T))`.

## Main results

## Proof outline

Writing `φ(d) = exp(-d²/(4T))`, one has `φ'(d) = -(d/(2T)) φ(d)`, so that on `(b, ∞)`
`φ(d) = (2T/d) · (-φ'(d)) ≤ (2T/b) · (-φ'(d))`; integrating gives the Mills bound by FTC.
For the expansion, two successive integrations by parts with `u = -(2T)/d` and `u = -(2T)/d³`
give the exact identities `G_T = (2T/b)φ(b) - 2T ∫ φ/d²` and
`∫ φ/d² = (2T/b³)φ(b) - 6T ∫ φ/d⁴`; combining,
`G_T(b) - (2T/b)φ(b)(1 - 2T/b²) = 12 T² ∫_b^∞ φ(d)/d⁴ dd`, and the remainder integral is
nonnegative and bounded by `G_T(b)/b⁴ ≤ (2T/b)φ(b)/b⁴`.

-/

open Asymptotics Filter MeasureTheory Set

open scoped Asymptotics Topology

/-- The Gaussian tail integral with temperature `T`: `G_T(b) = ∫_b^∞ exp(-d²/(4T)) dd`. -/
noncomputable def gaussianTail (T b : ℝ /- [definition] -/ ) : ℝ := ∫ d in Set.Ioi b, Real.exp (- d^2 / (4 * T))

/-- The derivative of `d ↦ exp(-d²/(4T))` is `-(d/(2T)) exp(-d²/(4T))`. -/
theorem hasDerivAt_exp_neg_sq_div (hT : 0 < T /- [standing] -/ ) (d : ℝ /- [definition] -/ ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x^2/(4*T))) (-(d/(2*T)) * Real.exp (-d^2/(4*T))) d := by
  have h := (Real.hasDerivAt_exp (-d^2/(4*T))).comp d
    (((hasDerivAt_pow 2 d).neg).div_const (4*T))
  convert! h using 1
  field_simp [hT.ne']
  ring

/-- The integrand `exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_exp_neg_sq_div_Ioi (hT : 0 < T /- [standing] -/ ) (b : ℝ /- [definition] -/ ) :
    IntegrableOn (fun d : ℝ => Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have h : (fun d : ℝ => Real.exp (-d^2/(4*T))) = fun d => Real.exp (-(4*T)⁻¹ * d^2) := by
    funext d
    congr 1
    ring
  rw [h]
  exact (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).integrableOn

/-- The derivative factor `(d/(2T)) exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_mul_exp_neg_sq_div_Ioi (hT : 0 < T /- [standing] -/ ) (b : ℝ /- [definition] -/ ) :
    IntegrableOn (fun d : ℝ => (d/(2*T)) * Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have h : (fun d : ℝ => (d/(2*T)) * Real.exp (-d^2/(4*T)))
      = fun d => (2*T)⁻¹ * (d * Real.exp (-(4*T)⁻¹ * d^2)) := by
    funext d
    have e1 : -d^2/(4*T) = -(4*T)⁻¹ * d^2 := by ring
    rw [e1]
    ring
  rw [h]
  exact ((integrable_mul_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).const_mul _).integrableOn

/-- The derivative `-(d/(2T)) exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_neg_mul_exp_neg_sq_div_Ioi (hT : 0 < T /- [standing] -/ ) (b : ℝ /- [definition] -/ ) :
    IntegrableOn (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have hfun : (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = fun d => -((d/(2*T)) * Real.exp (-d^2/(4*T))) := funext fun d => neg_mul _ _
  rw [hfun]
  exact (integrableOn_mul_exp_neg_sq_div_Ioi hT b).neg

/-- `exp(-d²/(4T)) → 0` as `d → ∞` for `0 < T`. -/
theorem tendsto_exp_neg_sq_div_atTop (hT : 0 < T /- [standing] -/ ) :
    Tendsto (fun d : ℝ => Real.exp (-d^2/(4*T))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun d : ℝ => d^2 * (4*T)⁻¹) atTop atTop :=
    Tendsto.atTop_mul_const (by positivity : (0:ℝ) < (4*T)⁻¹) (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun d : ℝ => -(d^2 * (4*T)⁻¹)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h3 := Real.tendsto_exp_atBot.comp h2
  refine h3.congr' (Eventually.of_forall fun d => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

/-- FTC on `(b, ∞)`: `∫_b^∞ -(d/(2T)) exp(-d²/(4T)) dd = -exp(-b²/(4T))`. -/
theorem integral_Ioi_neg_mul_exp_neg_sq_div (hT : 0 < T /- [standing] -/ ) (b : ℝ /- [definition] -/ ) :
    ∫ d in Set.Ioi b, -(d/(2*T)) * Real.exp (-d^2/(4*T)) = - Real.exp (-b^2/(4*T)) := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (f' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) (a := b) (m := 0)
    (fun x _ => hasDerivAt_exp_neg_sq_div hT x)
    (integrableOn_neg_mul_exp_neg_sq_div_Ioi hT b)
    (tendsto_exp_neg_sq_div_atTop hT)
  rwa [zero_sub] at h

/-- The Mills upper bound: `G_T(b) ≤ (2T/b) exp(-b²/(4T))` for `0 < T`, `0 < b`.

On `(b, ∞)`, `φ(d) = (2T/d) · (-φ'(d)) ≤ (2T/b) · (-φ'(d))`, and `∫ -φ' = φ(b)` by FTC. -/
theorem gaussianTail_le (hT : 0 < T /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) :
    gaussianTail T b ≤ (2*T/b) * Real.exp (-b^2/(4*T)) := by
  have hpt : ∀ d ∈ Set.Ioi b, Real.exp (-d^2/(4*T))
      ≤ (2*T/b) * (-( -(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
    intro d hd
    have hd0 : (0:ℝ) < d := hb.trans hd
    have hnn : (0:ℝ) ≤ - (-(d/(2*T)) * Real.exp (-d^2/(4*T))) := by
      simp only [neg_mul, neg_neg]
      positivity
    have heq : Real.exp (-d^2/(4*T)) = (2*T/d) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
      field_simp [hT.ne', hd0.ne']
    have hmono : (2*T/d) ≤ (2*T/b) := by
      rw [show (2:ℝ)*T/d = (2*T) * (1/d) by ring, show (2:ℝ)*T/b = (2*T) * (1/b) by ring]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hb hd.le) (by positivity)
    calc Real.exp (-d^2/(4*T))
        = (2*T/d) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := heq
      _ ≤ (2*T/b) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) :=
        mul_le_mul_of_nonneg_right hmono hnn
  calc gaussianTail T b = ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) := rfl
    _ ≤ ∫ d in Set.Ioi b, (2*T/b) * (-(-(d/(2*T)) * Real.exp (-d^2/(4*T)))) :=
        setIntegral_mono_on (integrableOn_exp_neg_sq_div_Ioi hT b)
          (Integrable.const_mul ((integrableOn_neg_mul_exp_neg_sq_div_Ioi hT b).neg) _)
          measurableSet_Ioi hpt
    _ = (2*T/b) * (∫ d in Set.Ioi b, -(-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
        rw [integral_const_mul]
    _ = (2*T/b) * Real.exp (-b^2/(4*T)) := by
        rw [integral_neg, integral_Ioi_neg_mul_exp_neg_sq_div hT b, neg_neg]

/-- `exp(-d²/(4T))/dᵏ` is integrable on `(b, ∞)` for `0 < T`, `0 < b` (comparison with
`exp(-d²/(4T))/bᵏ`). -/
theorem integrableOn_exp_neg_sq_div_div_pow (hT : 0 < T /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) (k : ℕ /- [definition] -/ ) :
    IntegrableOn (fun d : ℝ => Real.exp (-d^2/(4*T)) / d^k) (Set.Ioi b) := by
  have hg : MeasureTheory.Integrable (fun d : ℝ => Real.exp (-d^2/(4*T)) * (b^k)⁻¹)
      (volume.restrict (Set.Ioi b)) :=
    MeasureTheory.Integrable.mul_const (integrableOn_exp_neg_sq_div_Ioi hT b) _
  apply hg.mono' ?_ ?_
  · have hφ : Continuous fun d : ℝ => Real.exp (-d^2/(4*T)) := by fun_prop
    have hp : Continuous fun d : ℝ => d^k := by fun_prop
    have hcon : ContinuousOn (fun d : ℝ => Real.exp (-d^2/(4*T)) / d^k) (Set.Ioi b) := by
      apply ContinuousOn.div hφ.continuousOn hp.continuousOn
      intro x hx
      exact pow_ne_zero k (hb.trans hx).ne'
    exact hcon.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with d hd
    have hd0 : (0:ℝ) < d := hb.trans hd
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) (pow_nonneg hd0.le _))]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (pow_pos hd0 k) (pow_pos hb k)).2 (pow_le_pow_left₀ hb.le hd.le k))
      (Real.exp_nonneg _)

/-- Integration by parts on `[b, X]`: with `u = -(2T)/d` and `v = exp(-d²/(4T))`,
`∫_b^X φ = -(2T/X)φ(X) + (2T/b)φ(b) - 2T ∫_b^X φ(d)/d² dd`. -/
theorem intervalIntegral_exp_neg_sq_div (hT : 0 < T /- [standing] -/ ) {b X : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) (hbX : b ≤ X /- [standing] -/ ) :
    ∫ d in b..X, Real.exp (-d^2/(4*T))
      = -(2*T/X) * Real.exp (-X^2/(4*T)) + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
  have hu : ∀ x ∈ Set.uIcc b X, HasDerivAt (fun d : ℝ => -(2*T/d)) (2*T/x^2) x := by
    intro x hx
    rw [Set.uIcc_of_le hbX] at hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    have h := ((hasDerivAt_const x (2*T)).div (hasDerivAt_id' x) hx0).neg
    convert! h using 1
    field_simp [hx0]
    ring
  have hv : ∀ x ∈ Set.uIcc b X,
      HasDerivAt (fun d : ℝ => Real.exp (-d^2/(4*T))) (-(x/(2*T)) * Real.exp (-x^2/(4*T))) x :=
    fun x _ => hasDerivAt_exp_neg_sq_div hT x
  have hu' : IntervalIntegrable (fun d : ℝ => 2*T/d^2) volume b X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbX]
    have hp : Continuous fun d : ℝ => d^2 := by fun_prop
    exact continuousOn_const.div hp.continuousOn
      (fun x hx => pow_ne_zero 2 (hb.trans_le hx.1).ne')
  have hv' : IntervalIntegrable (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) volume b X := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))).continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun d : ℝ => -(2*T/d)) (u' := fun d : ℝ => 2*T/d^2)
    (v := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (v' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) hu hv hu' hv'
  have h1 : ∫ d in b..X, -(2*T/d) * (-(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = ∫ d in b..X, Real.exp (-d^2/(4*T)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    field_simp [hT.ne', hx0]
  have h2 : ∫ d in b..X, (2*T/d^2) * Real.exp (-d^2/(4*T))
      = 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    ring
  rw [h1, h2] at hibp
  linear_combination hibp

/-- One integration by parts for the Gaussian tail:
`G_T(b) = (2T/b) exp(-b²/(4T)) - 2T ∫_b^∞ exp(-d²/(4T))/d² dd`. -/
theorem gaussianTail_eq (hT : 0 < T /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) :
    gaussianTail T b = (2*T/b) * Real.exp (-b^2/(4*T))
      - 2*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2 := by
  have hlimI : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T))) atTop
      (𝓝 (gaussianTail T b)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_Ioi hT b) tendsto_id
  have hlimR : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 2) tendsto_id
  have hlimB : Tendsto (fun X : ℝ => -(2*T/X) * Real.exp (-X^2/(4*T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => 2*T/X) atTop (𝓝 0) := by
      have heq : (fun X : ℝ => 2*T/X) = fun X => (2*T) * X⁻¹ :=
        funext fun X => div_eq_mul_inv _ _
      rw [heq]
      simpa using tendsto_inv_atTop_zero.const_mul (2*T)
    have h3 := ((h1.neg).mul (tendsto_exp_neg_sq_div_atTop hT))
    rw [neg_zero, zero_mul] at h3
    exact h3
  have h_eq : ∀ᶠ X : ℝ in atTop, ∫ d in b..X, Real.exp (-d^2/(4*T))
      = -(2*T/X) * Real.exp (-X^2/(4*T)) + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 :=
    (eventually_gt_atTop b).mono fun X hX => intervalIntegral_exp_neg_sq_div hT hb hX.le
  have hlimAll : Tendsto (fun X : ℝ => -(2*T/X) * Real.exp (-X^2/(4*T))
      + (2*T/b) * Real.exp (-b^2/(4*T))
      - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (0 + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    (hlimB.add tendsto_const_nhds).sub (hlimR.const_mul (2*T))
  have hfin := tendsto_nhds_unique (Tendsto.congr' h_eq hlimI) hlimAll
  rwa [zero_add] at hfin

/-- A second integration by parts on `[b, X]`: with `u = -(2T)/d³`,
`∫_b^X φ(d)/d² dd = -(2T/X³)φ(X) + (2T/b³)φ(b) - 6T ∫_b^X φ(d)/d⁴ dd`. -/
theorem intervalIntegral_exp_neg_sq_div_div_sq (hT : 0 < T /- [standing] -/ ) {b X : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) (hbX : b ≤ X /- [standing] -/ ) :
    ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2
      = -(2*T/X^3) * Real.exp (-X^2/(4*T)) + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 := by
  have hu : ∀ x ∈ Set.uIcc b X, HasDerivAt (fun d : ℝ => -(2*T/d^3)) (6*T/x^4) x := by
    intro x hx
    rw [Set.uIcc_of_le hbX] at hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    have h := ((hasDerivAt_const x (2*T)).div ((hasDerivAt_pow 3 x)) (pow_ne_zero 3 hx0)).neg
    convert! h using 1
    field_simp [hx0]
    ring
  have hv : ∀ x ∈ Set.uIcc b X,
      HasDerivAt (fun d : ℝ => Real.exp (-d^2/(4*T))) (-(x/(2*T)) * Real.exp (-x^2/(4*T))) x :=
    fun x _ => hasDerivAt_exp_neg_sq_div hT x
  have hu' : IntervalIntegrable (fun d : ℝ => 6*T/d^4) volume b X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbX]
    have hp : Continuous fun d : ℝ => d^4 := by fun_prop
    exact continuousOn_const.div hp.continuousOn
      (fun x hx => pow_ne_zero 4 (hb.trans_le hx.1).ne')
  have hv' : IntervalIntegrable (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) volume b X := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))).continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun d : ℝ => -(2*T/d^3)) (u' := fun d : ℝ => 6*T/d^4)
    (v := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (v' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) hu hv hu' hv'
  have h1 : ∫ d in b..X, -(2*T/d^3) * (-(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    field_simp [hT.ne', hx0]
  have h2 : ∫ d in b..X, (6*T/d^4) * Real.exp (-d^2/(4*T))
      = 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    ring
  rw [h1, h2] at hibp
  linear_combination hibp

/-- The second IBP for the Gaussian tail:
`∫_b^∞ φ(d)/d² dd = (2T/b³) φ(b) - 6T ∫_b^∞ φ(d)/d⁴ dd`. -/
theorem integral_Ioi_exp_neg_sq_div_div_sq (hT : 0 < T /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) :
    ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2
      = (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 := by
  have hlimI : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 2) tendsto_id
  have hlimR : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 4) tendsto_id
  have hlimB : Tendsto (fun X : ℝ => -(2*T/X^3) * Real.exp (-X^2/(4*T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => 2*T/X^3) atTop (𝓝 0) := by
      have heq : (fun X : ℝ => 2*T/X^3) = fun X => (2*T) * (X^3)⁻¹ :=
        funext fun X => div_eq_mul_inv _ _
      rw [heq]
      have hbase : Tendsto (fun X : ℝ => (X^3)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0))
      simpa using hbase.const_mul (2*T)
    have h3 := ((h1.neg).mul (tendsto_exp_neg_sq_div_atTop hT))
    rw [neg_zero, zero_mul] at h3
    exact h3
  have h_eq : ∀ᶠ X : ℝ in atTop, ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2
      = -(2*T/X^3) * Real.exp (-X^2/(4*T)) + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 :=
    (eventually_gt_atTop b).mono fun X hX => intervalIntegral_exp_neg_sq_div_div_sq hT hb hX.le
  have hlimAll : Tendsto (fun X : ℝ => -(2*T/X^3) * Real.exp (-X^2/(4*T))
      + (2*T/b^3) * Real.exp (-b^2/(4*T))
      - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4) atTop
      (𝓝 (0 + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4)) :=
    (hlimB.add tendsto_const_nhds).sub (hlimR.const_mul (6*T))
  have hfin := tendsto_nhds_unique (Tendsto.congr' h_eq hlimI) hlimAll
  rwa [zero_add] at hfin

/-- The exact two-term error identity for the Gaussian tail:
`G_T(b) - (2T/b) exp(-b²/(4T)) (1 - 2T/b²) = 12 T² ∫_b^∞ exp(-d²/(4T))/d⁴ dd`. -/
theorem gaussianTail_sub_eq (hT : 0 < T /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) :
    gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2)
      = 12 * T^2 * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 := by
  rw [gaussianTail_eq hT hb, integral_Ioi_exp_neg_sq_div_div_sq hT hb]
  field_simp [hb.ne']
  ring

/-- The Gaussian tail two-term asymptotic expansion with quartic remainder, in exact
big-`O` form: as `b → ∞`,
`G_T(b) - (2T/b) exp(-b²/(4T)) (1 - 2T/b²) = O((2T/b) exp(-b²/(4T)) · b⁻⁴)`.

In fact the difference is *nonnegative* and equal to `12 T² ∫_b^∞ exp(-d²/(4T))/d⁴ dd`
(`gaussianTail_sub_eq`); the bound then follows from `∫ φ/d⁴ ≤ G_T(b)/b⁴` and the Mills
bound `gaussianTail_le`. -/
theorem gaussianTail_asymptotic (T : ℝ /- [definition] -/ ) (hT : 0 < T /- [standing] -/ ) :
    (fun b => gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2))
      =O[Filter.atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ)) := by
  rw [isBigO_iff]
  refine ⟨12 * T^2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with b hb
  have hb0 : (0:ℝ) < b := one_pos.trans_le hb
  have hrp : b^(-4:ℝ) = (b^4)⁻¹ := by
    rw [← Real.rpow_natCast b 4, ← Real.rpow_neg hb0.le]
    norm_cast
  rw [gaussianTail_sub_eq hT hb0]
  have hI4nn : 0 ≤ ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 :=
    setIntegral_nonneg measurableSet_Ioi fun d hd =>
      div_nonneg (Real.exp_nonneg _) (pow_nonneg (hb0.trans hd).le _)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 12 * T^2) hI4nn)]
  have hG0 : (0:ℝ) < (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ) := by positivity
  rw [Real.norm_of_nonneg hG0.le, hrp]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 12 * T^2)
  have hI4le : ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 ≤ gaussianTail T b / b^4 := by
    have hle : ∀ d ∈ Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 ≤ Real.exp (-d^2/(4*T)) / b^4 := by
      intro d hd
      have hd0 : (0:ℝ) < d := hb0.trans hd
      exact (div_le_div_iff_of_pos_left (Real.exp_pos _) (by positivity) (by positivity)).2
        (pow_le_pow_left₀ hb0.le hd.le 4)
    have hg4 : IntegrableOn (fun d => Real.exp (-d^2/(4*T)) / b^4) (Set.Ioi b) := by
      have hfun : (fun d : ℝ => Real.exp (-d^2/(4*T)) / b^4)
          = fun d => Real.exp (-d^2/(4*T)) * (b^4)⁻¹ := funext fun d => div_eq_mul_inv _ _
      rw [hfun]
      exact Integrable.mul_const (integrableOn_exp_neg_sq_div_Ioi hT b) _
    calc ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4
        ≤ ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / b^4 :=
          setIntegral_mono_on (integrableOn_exp_neg_sq_div_div_pow hT hb0 4)
            hg4 measurableSet_Ioi hle
      _ = (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T))) / b^4 := by
          simp only [div_eq_mul_inv, MeasureTheory.integral_mul_const]
      _ = gaussianTail T b / b^4 := rfl
  calc ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4
      ≤ gaussianTail T b / b^4 := hI4le
    _ ≤ ((2*T/b) * Real.exp (-b^2/(4*T))) / b^4 :=
        (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < b^4)).2 (gaussianTail_le hT hb0)
    _ = (2*T/b) * Real.exp (-b^2/(4*T)) * (b^4)⁻¹ := by ring

/-- The Mills-ratio asymptotic equivalence: `G_T(b) ~ (2T/b) exp(-b²/(4T))` as `b → ∞`. -/
theorem gaussianTail_isEquivalent (T : ℝ /- [definition] -/ ) (hT : 0 < T /- [standing] -/ ) :
    gaussianTail T ~[Filter.atTop] fun b => (2*T/b) * Real.exp (-b^2/(4*T)) := by
  have hGn : ∀ᶠ b in atTop, (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) b ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with b hb
    have hb0 : (0:ℝ) < b := one_pos.trans_le hb
    show (2*T/b) * Real.exp (-b^2/(4*T)) ≠ 0
    positivity
  have hmul : (fun b => (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) := by
    apply (isLittleO_iff_tendsto' ?_).2 ?_
    · exact hGn.mono fun b hb' h => by rw [h]; ring
    · have hratio : (fun b => ((2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ))
          / ((2*T/b) * Real.exp (-b^2/(4*T)))) =ᶠ[atTop] fun b => b^(-4:ℝ) := by
        filter_upwards [hGn] with b hb'
        exact mul_div_cancel_left₀ _ hb'
      exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 4)).congr' hratio.symm
  have hΔ : (fun b => gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) :=
    (gaussianTail_asymptotic T hT).trans_isLittleO hmul
  have hrest : (fun b => ((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) := by
    apply (isLittleO_iff_tendsto' ?_).2 ?_
    · exact hGn.mono fun b hb' h => by rw [h]; ring
    · have hratio : (fun b => (((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2))
          / ((2*T/b) * Real.exp (-b^2/(4*T)))) =ᶠ[atTop] fun b => 2*T * b^(-2:ℝ) := by
        filter_upwards [hGn, eventually_ge_atTop 1] with b hb' hb1
        have hb0 : (0:ℝ) < b := one_pos.trans_le hb1
        rw [mul_div_cancel_left₀ _ hb']
        have hrp2 : b^(-2:ℝ) = (b^2)⁻¹ := by
          rw [← Real.rpow_natCast b 2, ← Real.rpow_neg hb0.le]
          norm_cast
        rw [hrp2, div_eq_mul_inv]
      have htr : Tendsto (fun b : ℝ => 2*T * b^(-2:ℝ)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).const_mul (2*T)
        rwa [mul_zero] at h
      exact htr.congr' hratio.symm
  show (gaussianTail T - fun b => (2*T/b) * Real.exp (-b^2/(4*T)))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T)))
  exact (hΔ.sub hrest).congr
    (fun b => by
      show gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2)
          - ((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2)
        = gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T))
      ring)
    (fun _ => rfl)

end source4

noncomputable section source5
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-
! # The Schläfli integral for `K_{1/3}` and its large-`z` bound

The modified Bessel function of the second kind with index `1/3` has the Schläfli
integral representation

  `K_{1/3}(z) = ∫₀^∞ e^{-z cosh t} cosh(t/3) dt     (z > 0)`,

absolutely convergent for `z > 0`.  This file defines that integral (`schlaefliK13`),
proves positivity, and establishes the large-`z` Laplace-localization bound

  `schlaefliK13 z ≤ C · z^{-1/2} · e^{-z}     (z ≥ 2/3)`,

via the global pointwise domination

  `e^{-z cosh t} cosh(t/3) ≤ e^{-z} · e^{1/(9z)} · e^{-(z/4) t²}`

obtained from `cosh t ≥ 1 + t²/2` (power series), `cosh(t/3) ≤ e^{|t|/3}`, and the
AM–GM inequality `|t|/3 ≤ (z/4) t² + 1/(9z)`.  The dominating Gaussian integrates to
`2 √π · z^{-1/2}`, and the `e^{1/(9z)}` factor is bounded by `e^{1/6}` for `z ≥ 2/3`.
(The bound is stated for `z ≥ 2/3` rather than `z ≥ 1` so that the corollary for the
Airy prefactor applies already at `x = 1`, where `ζ = (2/3) x^{3/2} = 2/3`.)

## Main results

The Bessel equation and Airy–Bessel identity are proved below.
-/

open MeasureTheory Set Filter
open scoped Topology

/-- `cosh t ≥ 1 + t²/2` for all real `t`: the even power series has nonnegative terms. -/
theorem one_add_sq_div_two_le_cosh (t : ℝ /- [definition] -/ ) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq_tsum]
  have hs : Summable (fun n : ℕ => t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) :=
    (Real.hasSum_cosh t).summable
  calc 1 + t ^ 2 / 2 = ∑ n ∈ ({0, 1} : Finset ℕ), t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
        rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
        norm_num
    _ ≤ ∑' n : ℕ, t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) :=
        hs.sum_le_tsum _ (fun n _ => by rw [pow_mul]; positivity)

/-- `cosh t ≤ e^{|t|}` for all real `t`. -/
theorem cosh_le_exp_abs (t : ℝ /- [definition] -/ ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.2 (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.2 (neg_le_abs t)
  linarith [h1, h2]

/-- The Schläfli integral for the modified Bessel function `K_{1/3}`:
`K_{1/3}(z) = ∫₀^∞ e^{-z cosh t} cosh(t/3) dt`.  (Junk value `0` for `z ≤ 0`, where the
integral diverges.) -/
noncomputable def schlaefliK13 (z : ℝ /- [definition] -/ ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)

/-- Pointwise domination of the Schläfli integrand by a Gaussian, valid for all `t : ℝ`
and `0 < z`. -/
theorem schlaefliK13_integrand_le {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) (t : ℝ /- [definition] -/ ) :
    0 ≤ Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)
    ∧ Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)
      ≤ Real.exp (-z + 1/(9*z)) * Real.exp (-(z/4) * t^2) := by
  have hzp : z ≠ 0 := hz.ne'
  have hcosh := one_add_sq_div_two_le_cosh t
  have hAMGM : |t| / 3 ≤ z * t ^ 2 / 4 + 1 / (9 * z) := by
    have h0 := sq_nonneg (3 * z * |t| - 2)
    have h1 : 12 * z * |t| ≤ 9 * z ^ 2 * t ^ 2 + 4 := by
      have e : (3 * z * |t| - 2) ^ 2 = 9 * z ^ 2 * |t| ^ 2 - 12 * z * |t| + 4 := by ring
      rw [e, sq_abs] at h0
      linarith
    calc |t| / 3 = (12 * z * |t|) / (36 * z) := by field_simp; ring
      _ ≤ (9 * z ^ 2 * t ^ 2 + 4) / (36 * z) := by gcongr
      _ = z * t ^ 2 / 4 + 1 / (9 * z) := by field_simp; ring
  have h1 : Real.exp (-z * Real.cosh t) ≤ Real.exp (-z * (1 + t^2/2)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hcosh (neg_nonpos.2 hz.le))
  have h2 : Real.cosh (t/3) ≤ Real.exp (|t|/3) := by
    calc Real.cosh (t/3) ≤ Real.exp |t/3| := cosh_le_exp_abs (t/3)
      _ = Real.exp (|t|/3) := by
          rw [abs_div, show |(3:ℝ)| = 3 from by norm_num]
  refine ⟨mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le, ?_⟩
  calc Real.exp (-z * Real.cosh t) * Real.cosh (t/3)
      ≤ Real.exp (-z * (1 + t^2/2)) * Real.exp (|t|/3) :=
        mul_le_mul h1 h2 (Real.cosh_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-z * (1 + t^2/2) + |t|/3) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-z + 1/(9*z) - (z/4) * t^2) := Real.exp_le_exp.2 (by linarith [hAMGM])
    _ = Real.exp (-z + 1/(9*z)) * Real.exp (-(z/4) * t^2) := by
        rw [show (-z + 1/(9*z) - (z/4) * t^2) = (-z + 1/(9*z)) + (-(z/4) * t^2) from by ring,
          Real.exp_add]

/-- The dominating Gaussian is integrable for `0 < z`. -/
theorem integrable_schlaefliK13_dom {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    Integrable fun t : ℝ => Real.exp (-z + 1/(9*z)) * Real.exp (-(z/4) * t^2) :=
  (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < z/4)).const_mul _

/-- The Schläfli integrand is integrable for `0 < z`. -/
theorem integrable_schlaefliK13_integrand {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    Integrable fun t : ℝ => Real.exp (-z * Real.cosh t) * Real.cosh (t / 3) := by
  refine (integrable_schlaefliK13_dom hz).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    have h := schlaefliK13_integrand_le hz t
    rw [Real.norm_of_nonneg h.1]
    exact h.2

/-- The Schläfli integrand is integrable on `Ioi 0` for `0 < z`. -/
theorem integrableOn_schlaefliK13_integrand {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    IntegrableOn (fun t => Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)) (Set.Ioi 0) :=
  (integrable_schlaefliK13_integrand hz).integrableOn

/-- The Schläfli integral is strictly positive for `0 < z`. -/
theorem schlaefliK13_pos {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) : 0 < schlaefliK13 z := by
  unfold schlaefliK13
  have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)) :=
    MeasureTheory.ae_mono Measure.restrict_le_self
      (Filter.Eventually.of_forall fun t => (schlaefliK13_integrand_le hz t).1)
  rw [setIntegral_pos_iff_support_of_nonneg_ae h0 (integrableOn_schlaefliK13_integrand hz)]
  have hsupp : Function.support (fun t => Real.exp (-z * Real.cosh t) * Real.cosh (t/3))
      = Set.univ :=
    Set.eq_univ_of_forall fun t => (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).ne'
  rw [hsupp, Set.univ_inter, Real.volume_Ioi]
  simp

/-- **Headline bound** (Laplace localization): `schlaefliK13 z ≤ C · z^{-1/2} · e^{-z}` for
`z ≥ 2/3`, with the explicit constant `C = 2 √π e^{1/6}`. -/
theorem schlaefliK13_le : ∃ C : ℝ, ∀ z : ℝ, 2/3 ≤ z →
    schlaefliK13 z ≤ C * z^(-1/2:ℝ) * Real.exp (-z) := by
  refine ⟨2 * Real.sqrt Real.pi * Real.exp (1/6), fun z hz => ?_⟩
  have hz0 : (0:ℝ) < z := by linarith
  have hzp : z ≠ 0 := hz0.ne'
  have hval : Real.sqrt (Real.pi / (z/4)) = 2 * Real.sqrt Real.pi * z^(-1/2:ℝ) := by
    have e1 : Real.pi / (z/4) = (4 * Real.pi) * z⁻¹ := by field_simp
    have e2 : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [show (4:ℝ) * Real.pi = 2^2 * Real.pi from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have e3 : Real.sqrt (z⁻¹) = z^(-1/2:ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hz0.le]
      norm_num
    rw [e1, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * Real.pi), e2, e3]
  have hE : Real.exp (1/(9*z)) ≤ Real.exp (1/6) :=
    Real.exp_le_exp.2 (one_div_le_one_div_of_le (by norm_num) (by linarith : (6:ℝ) ≤ 9 * z))
  calc schlaefliK13 z
      ≤ ∫ t in Set.Ioi 0, Real.exp (-z + 1/(9*z)) * Real.exp (-(z/4) * t^2) := by
        apply setIntegral_mono_on (integrableOn_schlaefliK13_integrand hz0)
          (integrable_schlaefliK13_dom hz0).integrableOn measurableSet_Ioi
        intro t _
        exact (schlaefliK13_integrand_le hz0 t).2
    _ ≤ ∫ t : ℝ, Real.exp (-z + 1/(9*z)) * Real.exp (-(z/4) * t^2) :=
        setIntegral_le_integral (integrable_schlaefliK13_dom hz0)
          (Filter.Eventually.of_forall fun t => by positivity)
    _ = Real.exp (-z + 1/(9*z)) * Real.sqrt (Real.pi / (z/4)) := by
        rw [MeasureTheory.integral_const_mul, integral_gaussian]
    _ = Real.exp (-z) * Real.exp (1/(9*z)) * (2 * Real.sqrt Real.pi * z^(-1/2:ℝ)) := by
        rw [hval, Real.exp_add]
    _ ≤ 2 * Real.sqrt Real.pi * Real.exp (1/6) * z^(-1/2:ℝ) * Real.exp (-z) := by
        rw [show Real.exp (-z) * Real.exp (1/(9*z)) * (2 * Real.sqrt Real.pi * z^(-1/2:ℝ))
            = 2 * Real.sqrt Real.pi * z^(-1/2:ℝ) * (Real.exp (-z) * Real.exp (1/(9*z)))
            from by ring]
        rw [show 2 * Real.sqrt Real.pi * Real.exp (1/6) * z^(-1/2:ℝ) * Real.exp (-z)
            = 2 * Real.sqrt Real.pi * z^(-1/2:ℝ) * (Real.exp (-z) * Real.exp (1/6))
            from by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hE

/-- Exponential decay bound for the modified Bessel expression representing positive Airy values. -/
theorem airyK13_schlaefli_le : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    (1/Real.pi) * Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
      ≤ C * x^(-1/4:ℝ) * Real.exp (-(2/3 * x^(3/2:ℝ))) := by
  obtain ⟨C₀, hC₀⟩ := schlaefliK13_le
  refine ⟨C₀ * Real.pi⁻¹ * 3^(-1/2:ℝ) * (2/3)^(-1/2:ℝ), fun x hx => ?_⟩
  have hx0 : (0:ℝ) < x := by linarith
  have hz : 2/3 ≤ (2/3) * x^(3/2:ℝ) := by
    have h1 : (1:ℝ) ≤ x^(3/2:ℝ) := by
      calc (1:ℝ) = (1:ℝ)^(3/2:ℝ) := (Real.one_rpow _).symm
        _ ≤ x^(3/2:ℝ) := Real.rpow_le_rpow zero_le_one hx (by norm_num)
    linarith
  have hK := hC₀ _ hz
  have hsqrt : Real.sqrt (x/3) = x^(1/2:ℝ) * 3^(-1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow, show x/3 = x * 3⁻¹ from by ring,
      Real.mul_rpow hx0.le (by norm_num), ← Real.rpow_neg_one,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hzpow : ((2/3) * x^(3/2:ℝ))^(-1/2:ℝ) = (2/3)^(-1/2:ℝ) * x^(-3/4:ℝ) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
    norm_num
  calc (1/Real.pi) * Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
      ≤ (1/Real.pi) * Real.sqrt (x/3)
          * (C₀ * ((2/3)*x^(3/2:ℝ))^(-1/2:ℝ) * Real.exp (-((2/3)*x^(3/2:ℝ)))) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = C₀ * Real.pi⁻¹ * 3^(-1/2:ℝ) * (2/3)^(-1/2:ℝ) * x^(-1/4:ℝ)
          * Real.exp (-((2/3)*x^(3/2:ℝ))) := by
        rw [hsqrt, hzpow, one_div,
          show x^(-1/4:ℝ) = x^(1/2:ℝ) * x^(-3/4:ℝ) from by
            rw [← Real.rpow_add hx0]; congr 1; norm_num]
        ring

end source5

noncomputable section source6
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # The Airy–Bessel identity

For positive x, the Airy function equals `(1/π) √(x/3) K_{1/3}((2/3) x^{3/2})`.
The Schläfli integral satisfies the Bessel equation; the change of variables
gives the Airy equation, and the values and slopes at zero identify the solutions.
The identity also gives positivity and exponential upper bounds. -/

open MeasureTheory Set Filter
open scoped Topology

/-- The first `s`-integral piece of the Schläfli integral after the substitution
`s = (z/2) e^t`: `J₁(z) = ∫_{z/2}^∞ e^{-s - z²/(4s)} s^{-2/3} ds`. -/
noncomputable def schlaefliJ1 (z : ℝ /- [definition] -/ ) : ℝ :=
  ∫ s in Set.Ioi (z/2), Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ)

/-- The second `s`-integral piece: `J₂(z) = ∫_{z/2}^∞ e^{-s - z²/(4s)} s^{-4/3} ds`. -/
noncomputable def schlaefliJ2 (z : ℝ /- [definition] -/ ) : ℝ :=
  ∫ s in Set.Ioi (z/2), Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)

/-- The Schläfli integral in the `s = (z/2) e^t` parametrization (the image-substitution
form of `integral_image_eq_integral_abs_deriv_smul`). -/
theorem schlaefliK13_eq_s_form {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    schlaefliK13 z = ∫ s in Set.Ioi (z/2),
      Real.exp (-s - z^2/(4*s)) * ((2*s/z)^(1/3:ℝ) + (z/(2*s))^(1/3:ℝ)) / (2*s) := by
  have hzp : z ≠ 0 := hz.ne'
  -- the substitution map f(t) = (z/2) e^t and its calculus
  set f : ℝ → ℝ := fun t => (z/2) * Real.exp t with hf
  have hf' : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f t) (Set.Ioi 0) t :=
    fun t _ => ((Real.hasDerivAt_exp t).const_mul (z/2)).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    have hmono : StrictMono f := fun a b hab =>
      mul_lt_mul_of_pos_left (Real.exp_strictMono hab) (by linarith)
    exact hmono.injective.injOn
  have himg : f '' Set.Ioi 0 = Set.Ioi (z/2) := by
    ext s
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : (1:ℝ) < Real.exp t := by
        rw [← Real.exp_zero]; exact Real.exp_strictMono ht
      have := mul_lt_mul_of_pos_left h1 (by linarith : (0:ℝ) < z/2)
      simpa using this
    · intro hs
      have hs0 : (0:ℝ) < s := by linarith
      have h1 : (1:ℝ) < s / (z/2) := by
        rw [one_lt_div (by linarith : (0:ℝ) < z/2)]; exact hs
      refine ⟨Real.log (s / (z/2)), Real.log_pos h1, ?_⟩
      rw [hf]
      show (z/2) * Real.exp (Real.log (s / (z/2))) = s
      rw [Real.exp_log (by positivity)]
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ s (by positivity : (z/2 : ℝ) ≠ 0)
  -- unfold and rewrite by the image lemma
  unfold schlaefliK13
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  have hfpos : (0:ℝ) < f t := by positivity
  -- goal: F t = |f t| • H (f t); we compute the right-hand side
  symm
  dsimp only
  rw [abs_of_nonneg hfpos.le, smul_eq_mul]
  -- the pieces of the pointwise identity
  have h2sz : 2 * ((z/2) * Real.exp t) / z = Real.exp t := by
    field_simp
  have hz2s : z / (2 * ((z/2) * Real.exp t)) = Real.exp (-t) := by
    rw [Real.exp_neg]; field_simp
  have hexp : Real.exp (-((z/2) * Real.exp t) - z^2/(4 * ((z/2) * Real.exp t)))
      = Real.exp (-z * Real.cosh t) := by
    congr 1
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  have e1 : (Real.exp t)^(1/3:ℝ) = Real.exp (t/3) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp,
      show t * (1/3 : ℝ) = t/3 from by ring]
  have e2 : (Real.exp (-t))^(1/3:ℝ) = Real.exp (-(t/3)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      show -t * (1/3 : ℝ) = -(t/3) from by ring]
  have hcosh : ((Real.exp t)^(1/3:ℝ) + (Real.exp (-t))^(1/3:ℝ)) / 2 = Real.cosh (t/3) := by
    rw [Real.cosh_eq, e1, e2]
  -- the cancellation f(t) · (B/(2 f(t))) = B/2
  have hcancel : (z/2) * Real.exp t
        * (Real.exp (-((z/2) * Real.exp t) - z^2/(4 * ((z/2) * Real.exp t)))
          * ((2 * ((z/2) * Real.exp t) / z)^(1/3:ℝ) + (z / (2 * ((z/2) * Real.exp t)))^(1/3:ℝ))
          / (2 * ((z/2) * Real.exp t)))
      = Real.exp (-((z/2) * Real.exp t) - z^2/(4 * ((z/2) * Real.exp t)))
        * ((2 * ((z/2) * Real.exp t) / z)^(1/3:ℝ) + (z / (2 * ((z/2) * Real.exp t)))^(1/3:ℝ))
        / 2 := by
    field_simp
  rw [hcancel, hexp, h2sz, hz2s, e1, e2, mul_div_assoc, ← Real.cosh_eq]
/-- The `s`-kernel is continuous on `Ioi a` for `a > 0`. -/
theorem continuousOn_schlaefliJ_kernel {a z : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) (p : ℝ /- [definition] -/ ) :
    ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^p) (Set.Ioi a) := by
  intro s hs
  have hs' : a < s := hs
  have hsne : s ≠ 0 := by linarith
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul ?_ (Real.continuousAt_rpow_const s p (Or.inl hsne))
  apply Real.continuous_exp.continuousAt.comp
  apply ContinuousAt.sub (ContinuousAt.neg continuousAt_id)
  exact ContinuousAt.div₀ continuousAt_const (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hsne)

/-- The two `s`-kernels are integrable on `Ioi (z/2)` for `0 < z` and nonpositive `p`. -/
theorem integrableOn_schlaefliJ_kernel {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) {p : ℝ /- [definition] -/ } (hp : p ≤ 0 /- [standing] -/ ) :
    IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^p) (Set.Ioi (z/2)) := by
  have hza : (0:ℝ) < z/2 := by linarith
  apply Integrable.mono' (((integrableOn_exp_neg_Ioi (z/2)).const_mul ((z/2)^p))) ?_ ?_
  · exact (continuousOn_schlaefliJ_kernel hza p).aestronglyMeasurable measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := by have hs' : z/2 < s := hs; linarith
    have h1 : Real.exp (-s - z^2/(4*s)) ≤ Real.exp (-s) := by
      apply Real.exp_le_exp.2
      have hnn : (0:ℝ) ≤ z^2/(4*s) := by positivity
      linarith
    have h2 : s^p ≤ (z/2)^p := Real.rpow_le_rpow_of_nonpos hza (le_of_lt hs) hp
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-s - z^2/(4*s)) * s^p)]
    calc Real.exp (-s - z^2/(4*s)) * s^p ≤ Real.exp (-s) * s^p :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0.le _)
      _ ≤ Real.exp (-s) * (z/2)^p := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (z/2)^p * Real.exp (-s) := mul_comm _ _

/-- The pointwise split of the `s`-integrand into the two `J`-pieces with prefactors. -/
theorem schlaefli_sIntegrand_split {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) {s : ℝ /- [definition] -/ } (hs : s ∈ Set.Ioi (z/2)  /- [standing] -/ ) :
    Real.exp (-s - z^2/(4*s)) * ((2*s/z)^(1/3:ℝ) + (z/(2*s))^(1/3:ℝ)) / (2*s)
      = ((2/z)^(1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
        + ((2/z)^(-1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) := by
  have hs0 : (0:ℝ) < s := by have hs' : z/2 < s := hs; linarith
  have hp1 : (2*s/z)^(1/3:ℝ) = (2/z)^(1/3:ℝ) * s^(1/3:ℝ) := by
    rw [show 2*s/z = (2/z)*s from by ring, Real.mul_rpow (by positivity) hs0.le]
  have hp2 : (z/(2*s))^(1/3:ℝ) = (z/2)^(1/3:ℝ) * s^(-1/3:ℝ) := by
    rw [show z/(2*s) = (z/2) * s⁻¹ from by field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hs0.le,
      ← Real.rpow_neg hs0.le, neg_div]
  have hpref : (2/z)^(-1/3:ℝ) = (z/2)^(1/3:ℝ) := by
    rw [neg_div, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2/z),
      show (2/z)^(1/3:ℝ) = ((z/2)⁻¹)^(1/3:ℝ) from by rw [inv_div],
      Real.inv_rpow (by positivity : (0:ℝ) ≤ z/2), inv_inv]
  have hpow1 : s^(1/3:ℝ) / s = s^(-2/3:ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hs0]; norm_num
  have hpow2 : s^(-1/3:ℝ) / s = s^(-4/3:ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hs0]; norm_num
  rw [hp1, hp2, hpref]
  -- now pure algebra with the two power-conversion facts
  have key1 : Real.exp (-s - z^2/(4*s)) * ((2/z)^(1/3:ℝ) * s^(1/3:ℝ)) / (2*s)
      = ((2/z)^(1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ)) := by
    rw [← hpow1]; field_simp
  have key2 : Real.exp (-s - z^2/(4*s)) * ((z/2)^(1/3:ℝ) * s^(-1/3:ℝ)) / (2*s)
      = ((z/2)^(1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) := by
    rw [← hpow2]; field_simp
  rw [mul_add, add_div, key1, key2]

/-- The J-decomposition of the Schläfli integral:
`K(z) = ((2/z)^{1/3} J₁(z) + (2/z)^{-1/3} J₂(z))/2` for `0 < z`. -/
theorem schlaefliK13_eq_J12 {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    schlaefliK13 z = ((2/z)^(1/3:ℝ) * schlaefliJ1 z + (2/z)^(-1/3:ℝ) * schlaefliJ2 z)/2 := by
  have hz2 : (0:ℝ) < z/2 := by linarith
  have hi1 : IntegrableOn (fun s => ((2/z)^(1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ)))
      (Set.Ioi (z/2)) :=
    (integrableOn_schlaefliJ_kernel hz (by norm_num : (-2/3:ℝ) ≤ 0)).const_mul _
  have hi2 : IntegrableOn (fun s => ((2/z)^(-1/3:ℝ)/2) * (Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)))
      (Set.Ioi (z/2)) :=
    (integrableOn_schlaefliJ_kernel hz (by norm_num : (-4/3:ℝ) ≤ 0)).const_mul _
  rw [schlaefliK13_eq_s_form hz]
  rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => schlaefli_sIntegrand_split hz hs]
  rw [integral_add hi1 hi2]
  unfold schlaefliJ1 schlaefliJ2
  rw [integral_const_mul, integral_const_mul]
  ring

/-! ## The Bessel equation for the Schläfli `K_{1/3}` -/

/-- The `cosh`-power dominator for Schläfli parametric differentiation: for `0 < a` and
any `k : ℕ`, `t ↦ (cosh t)^k · e^{-a cosh t} · cosh (t/3)` is integrable on `ℝ` (the factor
`e^{-a cosh t}` decays like `e^{-(a/2) t²}`, beating any power of `cosh`). -/
theorem integrable_schlaefli_dom {a : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) (k : ℕ /- [definition] -/ ) :
    Integrable fun t : ℝ =>
      (Real.cosh t)^k * (Real.exp (-a * Real.cosh t) * Real.cosh (t / 3)) := by
  have ha4 : (0:ℝ) < a / 4 := by positivity
  have hbound : ∀ t : ℝ,
      (Real.cosh t)^k * (Real.exp (-a * Real.cosh t) * Real.cosh (t / 3))
        ≤ Real.exp (-a + ((k : ℝ) + 1/3)^2 / a) * Real.exp (-(a/4) * t^2) := by
    intro t
    have hcosh1 : (Real.cosh t)^k ≤ Real.exp ((k : ℝ) * |t|) :=
      (pow_le_pow_left₀ (Real.cosh_pos t).le (cosh_le_exp_abs t) k).trans
        (le_of_eq (Real.exp_nat_mul |t| k).symm)
    have hE : Real.exp (-a * Real.cosh t) ≤ Real.exp (-a) * Real.exp (-(a/2) * t^2) := by
      have h1 := mul_le_mul_of_nonneg_left (one_add_sq_div_two_le_cosh t) ha.le
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [h1])
    have hcosh3 : Real.cosh (t/3) ≤ Real.exp (|t|/3) :=
      (cosh_le_exp_abs (t/3)).trans_eq (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)])
    have hAMGM : ((k : ℝ) + 1/3) * |t| ≤ (a/4) * t^2 + ((k : ℝ) + 1/3)^2 / a := by
      set c : ℝ := (k : ℝ) + 1/3 with hc
      have h0 : (0:ℝ) ≤ (a * |t| / 2 - c)^2 := sq_nonneg _
      have habs : |t|^2 = t^2 := sq_abs t
      have e : (a * |t| / 2 - c)^2 = a^2 * |t|^2 / 4 - a * c * |t| + c^2 := by ring
      rw [e, habs] at h0
      have h2 : a * (c * |t|) ≤ a * ((a/4) * t^2 + c^2 / a) := by
        rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ ha.ne']
        nlinarith [h0, ha]
      exact le_of_mul_le_mul_left h2 ha
    have hprod := mul_le_mul hcosh1 (mul_le_mul hE hcosh3 (Real.cosh_pos _).le (by positivity))
      (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le) (Real.exp_pos _).le
    have hexp1 : Real.exp ((k : ℝ) * |t|)
        * ((Real.exp (-a) * Real.exp (-(a/2) * t^2)) * Real.exp (|t|/3))
        = Real.exp (-a + ((k : ℝ) + 1/3) * |t| - (a/2) * t^2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hexp2 : Real.exp (-a + ((k : ℝ) + 1/3)^2 / a - (a/4) * t^2)
        = Real.exp (-a + ((k : ℝ) + 1/3)^2 / a) * Real.exp (-(a/4) * t^2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (Real.cosh t)^k * (Real.exp (-a * Real.cosh t) * Real.cosh (t / 3))
        ≤ Real.exp ((k : ℝ) * |t|)
            * ((Real.exp (-a) * Real.exp (-(a/2) * t^2)) * Real.exp (|t|/3)) := hprod
      _ = Real.exp (-a + ((k : ℝ) + 1/3) * |t| - (a/2) * t^2) := hexp1
      _ ≤ Real.exp (-a + ((k : ℝ) + 1/3)^2 / a - (a/4) * t^2) :=
          Real.exp_le_exp.2 (by linarith [hAMGM])
      _ = Real.exp (-a + ((k : ℝ) + 1/3)^2 / a) * Real.exp (-(a/4) * t^2) := hexp2
  exact ((integrable_exp_neg_mul_sq ha4).const_mul _).mono'
    ((by fun_prop : Continuous fun t : ℝ =>
      (Real.cosh t)^k * (Real.exp (-a * Real.cosh t) * Real.cosh (t / 3))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Real.cosh_pos _).le _)
        (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le))]
      exact hbound t)

/-- First parametric derivative of the Schläfli integral: for `0 < z`,
`K'(z) = ∫₀^∞ (-cosh t) · e^{-z cosh t} · cosh(t/3) dt`, and this integrand is integrable. -/
theorem hasDerivAt_schlaefliK13 {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    IntegrableOn (fun t => -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      (Set.Ioi 0)
    ∧ HasDerivAt schlaefliK13
      (∫ t in Set.Ioi 0, -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      z := by
  have hz2 : (0:ℝ) < z/2 := by linarith
  have hball : Metric.ball z (z/2) ∈ 𝓝 z := Metric.ball_mem_nhds z hz2
  have hmeas : ∀ᶠ z' in 𝓝 z, AEStronglyMeasurable
      (fun t => Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))
      (volume.restrict (Set.Ioi 0)) :=
    Filter.Eventually.of_forall fun z' =>
      (by fun_prop : Continuous fun t : ℝ =>
        Real.exp (-z' * Real.cosh t) * Real.cosh (t/3)).aestronglyMeasurable
  have hFint : Integrable (fun t => Real.exp (-z * Real.cosh t) * Real.cosh (t/3))
      (volume.restrict (Set.Ioi 0)) := integrableOn_schlaefliK13_integrand hz
  have hF'meas : AEStronglyMeasurable
      (fun t => -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ =>
      -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ∀ z' ∈ Metric.ball z (z/2),
      ‖-(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))‖
        ≤ Real.cosh t * (Real.exp (-(z/2) * Real.cosh t) * Real.cosh (t/3)) := by
    refine Filter.Eventually.of_forall fun t z' hz' => ?_
    have hz'2 : z/2 ≤ z' := by
      rw [Metric.mem_ball, Real.dist_eq] at hz'
      linarith [abs_lt.1 hz']
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.cosh_pos t).le, abs_of_nonneg (Real.cosh_pos _).le]
    apply mul_le_mul_of_nonneg_left _ (Real.cosh_pos t).le
    apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hz'2)
      (Real.cosh_pos t).le)
  have hboundint : Integrable
      (fun t => Real.cosh t * (Real.exp (-(z/2) * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) := by
    have h : IntegrableOn
        (fun t => Real.cosh t * (Real.exp (-(z/2) * Real.cosh t) * Real.cosh (t/3)))
        (Set.Ioi 0) := by
      simpa only [pow_one] using (integrable_schlaefli_dom hz2 1).integrableOn
    exact h
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ∀ z' ∈ Metric.ball z (z/2),
      HasDerivAt (fun z' => Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))
        (-(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))) z' := by
    refine Filter.Eventually.of_forall fun t z' _ => ?_
    have h1 : HasDerivAt (fun z' => -z' * Real.cosh t) (-Real.cosh t) z' := by
      have h := (hasDerivAt_id' z').neg.mul_const (Real.cosh t)
      rwa [neg_one_mul] at h
    have h2 := h1.exp.mul_const (Real.cosh (t/3))
    convert! h2 using 1
    ring
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeas hFint
    hF'meas hbound hboundint hdiff
  exact ⟨hint, hder⟩

/-- Second parametric derivative of the Schläfli integral: for `0 < z`,
`K''(z) = ∫₀^∞ (cosh t)² · e^{-z cosh t} · cosh (t/3) dt` (integrable), the derivative of
the first-derivative integral. -/
theorem hasDerivAt_schlaefliK13_two {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    IntegrableOn (fun t => (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      (Set.Ioi 0)
    ∧ HasDerivAt (fun z' => ∫ t in Set.Ioi 0,
        -(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3)))
      (∫ t in Set.Ioi 0, (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      z := by
  have hz2 : (0:ℝ) < z/2 := by linarith
  have hball : Metric.ball z (z/2) ∈ 𝓝 z := Metric.ball_mem_nhds z hz2
  have hmeas : ∀ᶠ z' in 𝓝 z, AEStronglyMeasurable
      (fun t => -(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) :=
    Filter.Eventually.of_forall fun z' =>
      (by fun_prop : Continuous fun t : ℝ =>
        -(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))).aestronglyMeasurable
  have hFint : Integrable
      (fun t => -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) := (hasDerivAt_schlaefliK13 hz).1
  have hF'meas : AEStronglyMeasurable
      (fun t => (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ =>
      (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ∀ z' ∈ Metric.ball z (z/2),
      ‖(Real.cosh t)^2 * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))‖
        ≤ (Real.cosh t)^2 * (Real.exp (-(z/2) * Real.cosh t) * Real.cosh (t/3)) := by
    refine Filter.Eventually.of_forall fun t z' hz' => ?_
    have hz'2 : z/2 ≤ z' := by
      rw [Metric.mem_ball, Real.dist_eq] at hz'
      linarith [abs_lt.1 hz']
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (Real.cosh_pos _).le _)
      (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le))]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.cosh_pos t).le 2)
    apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hz'2)
      (Real.cosh_pos t).le)
  have hboundint : Integrable
      (fun t => (Real.cosh t)^2 * (Real.exp (-(z/2) * Real.cosh t) * Real.cosh (t/3)))
      (volume.restrict (Set.Ioi 0)) := (integrable_schlaefli_dom hz2 2).integrableOn
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ∀ z' ∈ Metric.ball z (z/2),
      HasDerivAt (fun z' => -(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3)))
        ((Real.cosh t)^2 * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))) z' := by
    refine Filter.Eventually.of_forall fun t z' _ => ?_
    have h1 : HasDerivAt (fun z' => Real.exp (-z' * Real.cosh t) * Real.cosh (t/3))
        (Real.exp (-z' * Real.cosh t) * (-Real.cosh t) * Real.cosh (t/3)) z' := by
      have h := (hasDerivAt_id' z').neg.mul_const (Real.cosh t)
      rw [neg_one_mul] at h
      exact h.exp.mul_const (Real.cosh (t/3))
    have h2 := h1.const_mul (-(Real.cosh t))
    convert! h2 using 1
    ring
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeas hFint
    hF'meas hbound hboundint hdiff
  exact ⟨hint, hder⟩

/-- The derivative of `schlaefliK13` itself, as an integral, for `0 < z`. -/
theorem hasDerivAt_deriv_schlaefliK13 {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    HasDerivAt (deriv schlaefliK13)
      (∫ t in Set.Ioi 0, (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      z := by
  obtain ⟨-, hder⟩ := hasDerivAt_schlaefliK13_two hz
  have heq : (fun z' => ∫ t in Set.Ioi 0,
        -(Real.cosh t) * (Real.exp (-z' * Real.cosh t) * Real.cosh (t/3)))
      =ᶠ[𝓝 z] deriv schlaefliK13 := by
    filter_upwards [Ioi_mem_nhds hz] with z' hz'
    exact ((hasDerivAt_schlaefliK13 hz').2).deriv.symm
  exact (Filter.EventuallyEq.hasDerivAt_iff heq).mp hder

/-- The antiderivative on the `t`-axis certifying the modified Bessel equation for the
Schläfli `K_{1/3}`: its `t`-derivative is the combination integrand `schlaefliK13Comb`
(the `sinh · sinh` cross terms cancel between `E' · M` and `E · M'`). -/
noncomputable def schlaefliK13Antideriv (z t : ℝ /- [definition] -/ ) : ℝ :=
  -(Real.exp (-z * Real.cosh t)
    * (z * Real.sinh t * Real.cosh (t/3) + (1/3) * Real.sinh (t/3)))

/-- The combination integrand `e^{-z cosh t} · (z² sinh²t - z cosh t - 1/9) · cosh(t/3)`. -/
noncomputable def schlaefliK13Comb (z t : ℝ /- [definition] -/ ) : ℝ :=
  Real.exp (-z * Real.cosh t)
    * ((z^2 * (Real.sinh t)^2 - z * Real.cosh t - 1/9) * Real.cosh (t/3))

theorem hasDerivAt_schlaefliK13Antideriv {z : ℝ /- [definition] -/ } (t : ℝ /- [definition] -/ ) :
    HasDerivAt (schlaefliK13Antideriv z) (schlaefliK13Comb z t) t := by
  unfold schlaefliK13Antideriv schlaefliK13Comb
  have hc3 : HasDerivAt (fun t => Real.cosh (t/3)) (Real.sinh (t/3) * (1/3)) t :=
    ((hasDerivAt_id' t).div_const (3:ℝ)).cosh
  have hs3 : HasDerivAt (fun t => Real.sinh (t/3)) (Real.cosh (t/3) * (1/3)) t :=
    ((hasDerivAt_id' t).div_const (3:ℝ)).sinh
  have hE : HasDerivAt (fun t => Real.exp (-z * Real.cosh t))
      (Real.exp (-z * Real.cosh t) * (-z * Real.sinh t)) t :=
    ((Real.hasDerivAt_cosh t).const_mul (-z)).exp
  have hM1 : HasDerivAt (fun t => (z * Real.sinh t) * Real.cosh (t/3))
      (z * Real.cosh t * Real.cosh (t/3) + z * Real.sinh t * (Real.sinh (t/3) * (1/3))) t :=
    ((Real.hasDerivAt_sinh t).const_mul z).mul hc3
  have hM2 : HasDerivAt (fun t => (1/3) * Real.sinh (t/3))
      ((1/3) * (Real.cosh (t/3) * (1/3))) t :=
    hs3.const_mul (1/3)
  have hM : HasDerivAt (fun t => (z * Real.sinh t) * Real.cosh (t/3) + (1/3) * Real.sinh (t/3))
      (z * Real.cosh t * Real.cosh (t/3) + z * Real.sinh t * (Real.sinh (t/3) * (1/3))
        + (1/3) * (Real.cosh (t/3) * (1/3))) t :=
    hM1.add hM2
  have hfull : HasDerivAt (fun t => -(Real.exp (-z * Real.cosh t)
        * ((z * Real.sinh t) * Real.cosh (t/3) + (1/3) * Real.sinh (t/3))))
      (-(Real.exp (-z * Real.cosh t) * (-z * Real.sinh t)
          * ((z * Real.sinh t) * Real.cosh (t/3) + (1/3) * Real.sinh (t/3))
        + Real.exp (-z * Real.cosh t)
          * (z * Real.cosh t * Real.cosh (t/3) + z * Real.sinh t * (Real.sinh (t/3) * (1/3))
            + (1/3) * (Real.cosh (t/3) * (1/3))))) t :=
    (hE.mul hM).neg
  convert! hfull using 1
  ring

theorem schlaefliK13Antideriv_zero {z : ℝ /- [definition] -/ } : schlaefliK13Antideriv z 0 = 0 := by
  simp [schlaefliK13Antideriv]

theorem tendsto_schlaefliK13Antideriv_atTop {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    Tendsto (schlaefliK13Antideriv z) atTop (𝓝 0) := by
  have hz4 : (0:ℝ) < z/4 := by linarith
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hsinh : ∀ u : ℝ, |Real.sinh u| ≤ Real.cosh u := fun u => by
    have h2 : |Real.exp u - Real.exp (-u)| ≤ Real.exp u + Real.exp (-u) := by
      have h := norm_add_le (Real.exp u) (-Real.exp (-u))
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_pos (Real.exp_pos u), abs_of_pos (Real.exp_pos (-u))] at h
      rwa [sub_eq_add_neg]
    rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hbound : ∀ t : ℝ, |schlaefliK13Antideriv z t|
      ≤ (z + 1/3) * Real.exp (-z + (16/(9*z))) * Real.exp (-(z/4) * t^2) := by
    intro t
    have hM : |z * Real.sinh t * Real.cosh (t/3) + (1/3) * Real.sinh (t/3)|
        ≤ (z + 1/3) * Real.exp ((4/3) * |t|) := by
      calc |z * Real.sinh t * Real.cosh (t/3) + (1/3) * Real.sinh (t/3)|
          ≤ |z * Real.sinh t * Real.cosh (t/3)| + |(1/3) * Real.sinh (t/3)| := by
            have h := norm_add_le (z * Real.sinh t * Real.cosh (t/3))
              ((1/3) * Real.sinh (t/3))
            rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
        _ = z * |Real.sinh t| * Real.cosh (t/3) + (1/3) * |Real.sinh (t/3)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz,
              abs_of_nonneg (Real.cosh_pos _).le,
              abs_of_pos (show (0:ℝ) < 1/3 by norm_num)]
        _ ≤ z * Real.cosh t * Real.cosh (t/3) + (1/3) * Real.cosh (t/3) :=
            add_le_add
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsinh t) hz.le)
                (Real.cosh_pos _).le)
              (mul_le_mul_of_nonneg_left (hsinh (t/3)) (by norm_num : (0:ℝ) ≤ 1/3))
        _ = (z * Real.cosh t + 1/3) * Real.cosh (t/3) := by ring
        _ ≤ (z * Real.exp |t| + 1/3) * Real.exp (|t|/3) := by
            have hc3 : Real.cosh (t/3) ≤ Real.exp (|t|/3) :=
              (cosh_le_exp_abs (t/3)).trans_eq
                (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)])
            have hle1 : z * Real.cosh t + 1/3 ≤ z * Real.exp |t| + 1/3 :=
              add_le_add (mul_le_mul_of_nonneg_left (cosh_le_exp_abs t) hz.le) le_rfl
            have hb : (0:ℝ) ≤ z * Real.exp |t| + 1/3 :=
              add_nonneg (mul_nonneg hz.le (Real.exp_pos _).le) (by norm_num)
            exact mul_le_mul hle1 hc3 (Real.cosh_pos _).le hb
        _ ≤ (z + 1/3) * Real.exp ((4/3) * |t|) := by
            have h1 : (1:ℝ) ≤ Real.exp |t| := by
              rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (abs_nonneg _)
            calc (z * Real.exp |t| + 1/3) * Real.exp (|t|/3)
                = z * (Real.exp |t| * Real.exp (|t|/3)) + (1/3) * Real.exp (|t|/3) := by ring
              _ ≤ z * (Real.exp |t| * Real.exp (|t|/3))
                  + (1/3) * (Real.exp |t| * Real.exp (|t|/3)) := by
                  have hE3 : Real.exp (|t|/3)
                      ≤ Real.exp |t| * Real.exp (|t|/3) := by
                    calc Real.exp (|t|/3) = 1 * Real.exp (|t|/3) := (one_mul _).symm
                      _ ≤ Real.exp |t| * Real.exp (|t|/3) :=
                          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
                  exact add_le_add le_rfl
                    (mul_le_mul_of_nonneg_left hE3 (by norm_num : (0:ℝ) ≤ 1/3))
              _ = (z + 1/3) * Real.exp ((4/3) * |t|) := by
                  have e : Real.exp |t| * Real.exp (|t|/3) = Real.exp ((4/3) * |t|) := by
                    rw [← Real.exp_add]; congr 1; ring
                  rw [e]; ring
    have hE : Real.exp (-z * Real.cosh t) ≤ Real.exp (-z) * Real.exp (-(z/2) * t^2) := by
      have h1 := mul_le_mul_of_nonneg_left (one_add_sq_div_two_le_cosh t) hz.le
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [h1])
    have hAMGM : (4/3) * |t| ≤ (z/4) * t^2 + 16/(9*z) := by
      have h0 : (0:ℝ) ≤ (z * |t| / 2 - 4/3)^2 := sq_nonneg _
      have habs : |t|^2 = t^2 := sq_abs t
      have e : (z * |t| / 2 - 4/3)^2 = z^2 * |t|^2 / 4 - z * (4/3) * |t| + (4/3)^2 := by ring
      rw [e, habs] at h0
      have h2 : z * ((4/3) * |t|) ≤ z * ((z/4) * t^2 + (4/3)^2 / z) := by
        rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hz.ne']
        nlinarith [h0, hz]
      have h3 := le_of_mul_le_mul_left h2 hz
      have h4 : (4/3:ℝ)^2 / z = 16/(9*z) := by field_simp; norm_num
      rwa [h4] at h3
    calc |schlaefliK13Antideriv z t|
        = Real.exp (-z * Real.cosh t)
            * |z * Real.sinh t * Real.cosh (t/3) + (1/3) * Real.sinh (t/3)| := by
          rw [schlaefliK13Antideriv, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-z * Real.cosh t) * ((z + 1/3) * Real.exp ((4/3) * |t|)) :=
          mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
      _ ≤ (Real.exp (-z) * Real.exp (-(z/2) * t^2)) * ((z + 1/3) * Real.exp ((4/3) * |t|)) :=
          mul_le_mul_of_nonneg_right hE
            (mul_nonneg (by linarith [hz]) (Real.exp_pos _).le)
      _ = (z + 1/3) * Real.exp (-z)
            * (Real.exp ((4/3) * |t|) * Real.exp (-(z/2) * t^2)) := by ring
      _ ≤ (z + 1/3) * Real.exp (-z) * (Real.exp (16/(9*z)) * Real.exp (-(z/4) * t^2)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by linarith [hz]) (Real.exp_pos _).le)
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.2 (by linarith [hAMGM])
      _ = (z + 1/3) * (Real.exp (-z) * Real.exp (16/(9*z))) * Real.exp (-(z/4) * t^2) := by
          ring
      _ = (z + 1/3) * Real.exp (-z + (16/(9*z))) * Real.exp (-(z/4) * t^2) := by
          rw [← Real.exp_add]
  apply squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _)
    (Eventually.of_forall hbound)
  have harg : Tendsto (fun t : ℝ => -(z/4) * t^2) atTop atBot := by
    have hp : Tendsto (fun t : ℝ => (z/4) * t^2) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hz4).mpr (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
    have h := tendsto_neg_atTop_atBot.comp hp
    rw [show (fun t : ℝ => -(z/4) * t^2) = Neg.neg ∘ (fun t => (z/4) * t^2) from
      funext fun t => by simp only [Function.comp_apply, neg_mul]]
    exact h
  have hexp := Real.tendsto_exp_atBot.comp harg
  have hfin := hexp.const_mul ((z + 1/3) * Real.exp (-z + (16/(9*z))))
  rwa [mul_zero] at hfin

/-- The integral of the combination integrand over `Ioi 0` vanishes: it is the
`t`-derivative of `schlaefliK13Antideriv`, which vanishes at `0` and at `+∞`. -/
theorem integral_schlaefliK13Comb {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    ∫ t in Set.Ioi 0, schlaefliK13Comb z t = 0 := by
  have hcont : ContinuousWithinAt (schlaefliK13Antideriv z) (Set.Ici 0) 0 :=
    (by unfold schlaefliK13Antideriv; fun_prop :
      Continuous (schlaefliK13Antideriv z)).continuousWithinAt
  obtain ⟨hI1, -⟩ := hasDerivAt_schlaefliK13 hz
  obtain ⟨hI2, -⟩ := hasDerivAt_schlaefliK13_two hz
  have hI0 := integrableOn_schlaefliK13_integrand hz
  have heq : schlaefliK13Comb z = fun t =>
      z^2 * ((Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      + z * (-(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
      - (z^2 + 1/9) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)) :=
    funext fun t => by
      unfold schlaefliK13Comb
      rw [Real.cosh_sq']
      ring
  have hint : IntegrableOn (schlaefliK13Comb z) (Set.Ioi 0) := by
    rw [heq]
    exact ((hI2.const_mul _).add (hI1.const_mul _)).sub (hI0.const_mul _)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t _ => hasDerivAt_schlaefliK13Antideriv t) hint
    (tendsto_schlaefliK13Antideriv_atTop hz)
  rwa [schlaefliK13Antideriv_zero, sub_zero] at hftc

/-- **The modified Bessel equation** for the Schläfli `K_{1/3}`: for `0 < z`,
`z² K''(z) + z K'(z) - (z² + 1/9) K(z) = 0`. -/
theorem schlaefliK13_bessel_eq {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    z^2 * iteratedDeriv 2 schlaefliK13 z + z * deriv schlaefliK13 z
      - (z^2 + 1/9) * schlaefliK13 z = 0 := by
  obtain ⟨hI1, hd1⟩ := hasDerivAt_schlaefliK13 hz
  obtain ⟨hI2, -⟩ := hasDerivAt_schlaefliK13_two hz
  have hd2 := hasDerivAt_deriv_schlaefliK13 hz
  have hI0 := integrableOn_schlaefliK13_integrand hz
  have hiter : iteratedDeriv 2 schlaefliK13 z = deriv (deriv schlaefliK13) z := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter, hd2.deriv, hd1.deriv,
    show schlaefliK13 z = ∫ t in Set.Ioi 0, Real.exp (-z * Real.cosh t) * Real.cosh (t/3)
      from rfl]
  calc z^2 * (∫ t in Set.Ioi 0,
          (Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
        + z * (∫ t in Set.Ioi 0,
          -(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
        - (z^2 + 1/9) * (∫ t in Set.Ioi 0,
          Real.exp (-z * Real.cosh t) * Real.cosh (t/3))
      = ∫ t in Set.Ioi 0,
          (z^2 * ((Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
          + z * (-(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
          - (z^2 + 1/9) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3))) := by
        have hAB : IntegrableOn (fun t =>
            z^2 * ((Real.cosh t)^2 * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3)))
            + z * (-(Real.cosh t) * (Real.exp (-z * Real.cosh t) * Real.cosh (t/3))))
            (Set.Ioi 0) :=
          (hI2.const_mul _).add (hI1.const_mul _)
        rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
          ← integral_add (hI2.const_mul _) (hI1.const_mul _),
          ← integral_sub hAB (hI0.const_mul _)]
    _ = ∫ t in Set.Ioi 0, schlaefliK13Comb z t :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => by
          unfold schlaefliK13Comb
          rw [Real.cosh_sq']
          ring
    _ = 0 := integral_schlaefliK13Comb hz

/-! ## The change of variables `y(x) = √(x/3) K((2/3) x^{3/2})` -/

/-- The change-of-variables function `y(x) = √(x/3) · K((2/3) x^{3/2})` (DLMF 9.6.1,
up to the factor `1/π`). -/
noncomputable def airyBesselY (x : ℝ /- [definition] -/ ) : ℝ :=
  Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ))

/-- The first derivative of `airyBesselY` on `(0, ∞)`, as a function:
`y'(x) = (√3)⁻¹ ((1/2) x^{-1/2} K(g(x)) + x K'(g(x)))` with `g(x) = (2/3) x^{3/2}`. -/
noncomputable def airyBesselY1 (x : ℝ /- [definition] -/ ) : ℝ :=
  (Real.sqrt 3)⁻¹ * ((1/2) * x^(-1/2:ℝ) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
    + x * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)))

/-- `√(x/3) = (√3)⁻¹ x^{1/2}` for `0 ≤ x`. -/
theorem sqrt_div_three {x : ℝ /- [definition] -/ } (hx : 0 ≤ x /- [standing] -/ ) :
    Real.sqrt (x/3) = (Real.sqrt 3)⁻¹ * x^(1/2:ℝ) := by
  rw [Real.sqrt_div hx, Real.sqrt_eq_rpow, div_eq_mul_inv,
    mul_comm (x^(1/2:ℝ)) (Real.sqrt 3)⁻¹]

theorem hasDerivAt_rpow_half {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    HasDerivAt (fun x => x^(1/2:ℝ)) ((1/2) * x^(-1/2:ℝ)) x := by
  convert! Real.hasDerivAt_rpow_const (p := (1/2:ℝ)) (Or.inl hx.ne') using 1
  rw [show (1/2:ℝ) - 1 = -1/2 by norm_num]

theorem hasDerivAt_rpow_neg_half {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    HasDerivAt (fun x => x^(-1/2:ℝ)) ((-1/2) * x^(-3/2:ℝ)) x := by
  convert! Real.hasDerivAt_rpow_const (p := (-1/2:ℝ)) (Or.inl hx.ne') using 1
  rw [show (-1/2:ℝ) - 1 = -3/2 by norm_num]

/-- `g(x) = (2/3) x^{3/2}` has derivative `x^{1/2}` for `0 < x`. -/
theorem hasDerivAt_g {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    HasDerivAt (fun x => (2/3) * x^(3/2:ℝ)) (x^(1/2:ℝ)) x := by
  convert! (Real.hasDerivAt_rpow_const (p := (3/2:ℝ)) (Or.inl hx.ne')).const_mul (2/3)
    using 1
  rw [show (2/3:ℝ) * ((3/2) * x^((3/2:ℝ) - 1)) = x^((3/2:ℝ) - 1) from by ring,
    show (3/2:ℝ) - 1 = (1/2:ℝ) from by norm_num]

/-- First derivative of the change-of-variables function: for `0 < x`,
`y'(x) = airyBesselY1 x` (product + chain rule; `K'` enters via
`hasDerivAt_schlaefliK13`). -/
theorem hasDerivAt_airyBesselY {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    HasDerivAt airyBesselY (airyBesselY1 x) x := by
  have hg_pos : (0:ℝ) < (2/3) * x^(3/2:ℝ) := by positivity
  have hKd : HasDerivAt schlaefliK13 (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      ((2/3) * x^(3/2:ℝ)) := by
    have h0 := (hasDerivAt_schlaefliK13 hg_pos).2
    rw [h0.deriv]
    exact h0
  have hKg : HasDerivAt (fun x => schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ)) x := by
    have h := hKd.comp x (hasDerivAt_g hx)
    exact h
  have hhalf : x^(1/2:ℝ) * x^(1/2:ℝ) = x := by
    rw [← Real.rpow_add hx, show (1/2:ℝ) + 1/2 = 1 from by norm_num, Real.rpow_one]
  have heq : airyBesselY =ᶠ[𝓝 x]
      fun x => (Real.sqrt 3)⁻¹ * (x^(1/2:ℝ) * schlaefliK13 ((2/3) * x^(3/2:ℝ))) := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx'
    rw [show airyBesselY x'
        = Real.sqrt (x'/3) * schlaefliK13 ((2/3) * x'^(3/2:ℝ)) from rfl,
      sqrt_div_three hx'.le]
    ring
  rw [Filter.EventuallyEq.hasDerivAt_iff heq]
  convert! ((hasDerivAt_rpow_half hx).mul hKg).const_mul (Real.sqrt 3)⁻¹ using 1
  unfold airyBesselY1
  rw [show x^(1/2:ℝ) * (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ))
      = (x^(1/2:ℝ) * x^(1/2:ℝ)) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) from by ring,
    hhalf]

/-- Second derivative of the change-of-variables function: for `0 < x`,
`(y')'(x) = x · y(x)` — the Airy equation, via the Bessel equation for `K`. -/
theorem hasDerivAt_airyBesselY1 {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    HasDerivAt airyBesselY1 (x * airyBesselY x) x := by
  have hg_pos : (0:ℝ) < (2/3) * x^(3/2:ℝ) := by positivity
  have hKd : HasDerivAt schlaefliK13 (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      ((2/3) * x^(3/2:ℝ)) := by
    have h0 := (hasDerivAt_schlaefliK13 hg_pos).2
    rw [h0.deriv]
    exact h0
  have hKg : HasDerivAt (fun x => schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ)) x := by
    have h := hKd.comp x (hasDerivAt_g hx)
    exact h
  have hK2d : HasDerivAt (deriv schlaefliK13)
      (iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))) ((2/3) * x^(3/2:ℝ)) := by
    have h := hasDerivAt_deriv_schlaefliK13 hg_pos
    have hiter : iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))
        = deriv (deriv schlaefliK13) ((2/3) * x^(3/2:ℝ)) := by
      have e1 : iteratedDeriv (1 + 1) schlaefliK13 = deriv (iteratedDeriv 1 schlaefliK13) :=
        iteratedDeriv_succ
      rw [iteratedDeriv_one] at e1
      exact congrFun e1 _
    rw [hiter, h.deriv]
    exact h
  have hK2g : HasDerivAt (fun x => deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      (iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ)) x := by
    have h := hK2d.comp x (hasDerivAt_g hx)
    exact h
  have hA := ((hasDerivAt_rpow_neg_half hx).const_mul (1/2)).mul hKg
  have hB := (hasDerivAt_id' x).mul hK2g
  have hsum := (hA.add hB).const_mul (Real.sqrt 3)⁻¹
  -- power identities for `x > 0`
  have hhalf : x^(1/2:ℝ) * x^(1/2:ℝ) = x := by
    rw [← Real.rpow_add hx, show (1/2:ℝ) + 1/2 = 1 from by norm_num, Real.rpow_one]
  have hinv : x^(-1/2:ℝ) * x^(1/2:ℝ) = 1 := by
    rw [← Real.rpow_add hx, show (-1/2:ℝ) + 1/2 = 0 from by norm_num, Real.rpow_zero]
  have h32 : x * x^(1/2:ℝ) = x^(3/2:ℝ) := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx, show (1:ℝ) + 1/2 = 3/2 from by norm_num]
  have h3 : (x^(3/2:ℝ)) * (x^(3/2:ℝ)) = x^(3:ℝ) := by
    rw [← Real.rpow_add hx, show (3/2:ℝ) + 3/2 = (3:ℝ) from by norm_num]
  have hgx2 : ((2/3) * x^(3/2:ℝ))^2 = (4/9) * x^(3:ℝ) := by
    rw [pow_two, show ((2/3) * x^(3/2:ℝ)) * ((2/3) * x^(3/2:ℝ))
        = (2/3) * (2/3) * (x^(3/2:ℝ) * x^(3/2:ℝ)) from by ring, h3,
      show (2/3:ℝ) * (2/3) = 4/9 from by norm_num]
  have hdiv : x^(3/2:ℝ) / x^(3:ℝ) = x^(-3/2:ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_add hx,
      show (3/2:ℝ) + -(3:ℝ) = -3/2 from by norm_num]
  have hne32 : x^(3/2:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hgx_ne : (2/3) * x^(3/2:ℝ) ≠ 0 := hg_pos.ne'
  have hBessel := schlaefliK13_bessel_eq hg_pos
  have hratio : x^(3/2:ℝ) / ((2/3) * x^(3/2:ℝ)) = 3/2 := by
    field_simp
    try ring
  have hkey : x^(3/2:ℝ) * (((2/3) * x^(3/2:ℝ))^2 + 1/9) / ((2/3) * x^(3/2:ℝ))^2
      = x^(3/2:ℝ) + (1/4) * x^(-3/2:ℝ) := by
    rw [hgx2, div_eq_iff (ne_of_gt (by positivity : (0:ℝ) < (4/9:ℝ) * x^(3:ℝ)))]
    have hn32 : x^(-3/2:ℝ) * x^(3:ℝ) = x^(3/2:ℝ) := by
      rw [← Real.rpow_add hx, show (-3/2:ℝ) + 3 = 3/2 from by norm_num]
    rw [show (x^(3/2:ℝ) + (1/4) * x^(-3/2:ℝ)) * ((4/9:ℝ) * x^(3:ℝ))
        = x^(3/2:ℝ) * ((4/9:ℝ) * x^(3:ℝ)) + (1/4) * (4/9) * (x^(-3/2:ℝ) * x^(3:ℝ))
        from by ring, hn32]
    ring
  -- the Bessel equation solved for `x^{3/2} K''(g(x))`
  have hK2eq : x^(3/2:ℝ) * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))
      = (x^(3/2:ℝ) + (1/4) * x^(-3/2:ℝ)) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
        - (3/2) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
    have h2 : ((2/3) * x^(3/2:ℝ))^2 * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))
        = (((2/3) * x^(3/2:ℝ))^2 + 1/9) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
          - (2/3) * x^(3/2:ℝ) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
      linarith [hBessel]
    calc x^(3/2:ℝ) * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))
        = (x^(3/2:ℝ) / ((2/3) * x^(3/2:ℝ))^2)
            * (((2/3) * x^(3/2:ℝ))^2
              * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))) := by
          field_simp
          try ring
      _ = (x^(3/2:ℝ) / ((2/3) * x^(3/2:ℝ))^2)
            * ((((2/3) * x^(3/2:ℝ))^2 + 1/9) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
              - (2/3) * x^(3/2:ℝ) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ))) := by
          rw [h2]
      _ = (x^(3/2:ℝ) * (((2/3) * x^(3/2:ℝ))^2 + 1/9) / ((2/3) * x^(3/2:ℝ))^2)
            * schlaefliK13 ((2/3) * x^(3/2:ℝ))
            - (x^(3/2:ℝ) / ((2/3) * x^(3/2:ℝ)))
              * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
          field_simp
          try ring
      _ = (x^(3/2:ℝ) + (1/4) * x^(-3/2:ℝ)) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
            - (3/2) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
          rw [hkey, hratio]
  -- final assembly: `show` unfolds `airyBesselY1`, then `convert` exposes the value
  show HasDerivAt (fun x => (Real.sqrt 3)⁻¹ * ((1/2) * x^(-1/2:ℝ)
      * schlaefliK13 ((2/3) * x^(3/2:ℝ))
      + x * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)))) (x * airyBesselY x) x
  convert! hsum using 1
  rw [show airyBesselY x = Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ)) from rfl,
    sqrt_div_three hx.le]
  have hn1 : (1/2) * x^(-1/2:ℝ) * (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ))
      = (1/2) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
    rw [show (1/2) * x^(-1/2:ℝ) * (deriv schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ))
        = (1/2) * (x^(-1/2:ℝ) * x^(1/2:ℝ)) * deriv schlaefliK13 ((2/3) * x^(3/2:ℝ))
        from by ring, hinv]
    ring
  have hn2 : x * (iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ))
      = x^(3/2:ℝ) * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
    rw [show x * (iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ)) * x^(1/2:ℝ))
        = (x * x^(1/2:ℝ)) * iteratedDeriv 2 schlaefliK13 ((2/3) * x^(3/2:ℝ))
        from by ring, h32]
  have hn3 : x * ((Real.sqrt 3)⁻¹ * x^(1/2:ℝ) * schlaefliK13 ((2/3) * x^(3/2:ℝ)))
      = (Real.sqrt 3)⁻¹ * x^(3/2:ℝ) * schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
    rw [show x * ((Real.sqrt 3)⁻¹ * x^(1/2:ℝ) * schlaefliK13 ((2/3) * x^(3/2:ℝ)))
        = (Real.sqrt 3)⁻¹ * (x * x^(1/2:ℝ)) * schlaefliK13 ((2/3) * x^(3/2:ℝ))
        from by ring, h32]
  rw [hn1, hn2, hn3, hK2eq]
  ring

/-- **The Airy equation** for the change-of-variables function: for `0 < x`,
`iteratedDeriv 2 airyBesselY x = x * airyBesselY x`. -/
theorem iteratedDeriv_two_airyBesselY {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    iteratedDeriv 2 airyBesselY x = x * airyBesselY x := by
  have h1 : deriv airyBesselY =ᶠ[𝓝 x] airyBesselY1 := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx'
    exact (hasDerivAt_airyBesselY hx').deriv
  have h2 : iteratedDeriv 2 airyBesselY x = deriv airyBesselY1 x := by
    have e1 : iteratedDeriv (1 + 1) airyBesselY = deriv (iteratedDeriv 1 airyBesselY) :=
      iteratedDeriv_succ
    rw [iteratedDeriv_one] at e1
    have e2 : iteratedDeriv 2 airyBesselY x = deriv (deriv airyBesselY) x := congrFun e1 x
    rw [e2, h1.deriv_eq]
  rw [h2, (hasDerivAt_airyBesselY1 hx).deriv]

/-! ## Matching constants at the origin via Γ-reflection -/

/-- Euler's reflection formula at `s = 1/3`: `Γ(1/3) Γ(2/3) = 2π/√3`. -/
theorem real_Gamma_one_third_mul_Gamma_two_thirds :
    Real.Gamma (1/3) * Real.Gamma (2/3) = 2 * Real.pi / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/3)
  rw [show (1:ℝ) - 1/3 = 2/3 from by norm_num,
    show Real.pi * (1/3) = Real.pi / 3 from by ring, Real.sin_pi_div_three] at h
  rw [h, div_div_eq_mul_div, mul_comm Real.pi 2]

/-- The value constant `y₀ = Γ(1/3) 3^{-1/6}/2` equals `π · Ai(0)`. -/
theorem airyBesselY0_eq :
    Real.Gamma (1/3) * 3^(-1/6:ℝ) / 2 = Real.pi * airyAiReal 0 := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  rw [airyAiReal_zero, ← mul_div_assoc Real.pi _ _]
  -- goal: Γ(1/3) * 3^(-1/6) / 2 = π * 3^(-2/3) / Γ(2/3)
  rw [div_eq_div_iff (by norm_num : (2:ℝ) ≠ 0)
    (Real.Gamma_pos_of_pos (show (0:ℝ) < 2/3 by norm_num)).ne']
  -- goal: Γ(1/3) * 3^(-1/6) * Γ(2/3) = π * 3^(-2/3) * 2
  rw [show Real.Gamma (1/3) * 3^(-1/6:ℝ) * Real.Gamma (2/3)
      = (Real.Gamma (1/3) * Real.Gamma (2/3)) * 3^(-1/6:ℝ) from by ring,
    real_Gamma_one_third_mul_Gamma_two_thirds]
  -- goal: (2π/√3) * 3^(-1/6) = π * 3^(-2/3) * 2
  have hmerge : (3:ℝ)^(-(1/2:ℝ)) * 3^(-1/6:ℝ) = 3^(-2/3:ℝ) := by
    rw [← Real.rpow_add h3pos]
    congr 1
    norm_num
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg h3pos.le]
  -- goal: 2 * π * 3^(-(1/2)) * 3^(-1/6) = π * 3^(-2/3) * 2
  rw [show 2 * Real.pi * (3:ℝ)^(-(1/2:ℝ)) * 3^(-1/6:ℝ)
      = 2 * Real.pi * ((3:ℝ)^(-(1/2:ℝ)) * 3^(-1/6:ℝ)) from by ring, hmerge]
  ring

/-- The slope constant `y₁ = -3^{1/6} Γ(2/3)/2` equals `π · Ai'(0)`. -/
theorem airyBesselY1_eq :
    -(3^(1/6:ℝ)) * Real.Gamma (2/3) / 2 = Real.pi * deriv airyAiReal 0 := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have h43 : (3:ℝ)^(-4/3:ℝ) * 3 = 3^(-1/3:ℝ) := by
    rw [show (3:ℝ)^(-4/3:ℝ) * 3 = (3:ℝ)^(-4/3:ℝ) * (3:ℝ)^(1:ℝ) from by rw [Real.rpow_one],
      ← Real.rpow_add h3pos]
    congr 1
    norm_num
  suffices h : (3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2
      = Real.pi * (3^(-1/3:ℝ) / Real.Gamma (1/3)) by
    rw [deriv_airyAiReal_zero, real_Gamma_four_thirds, div_div_eq_mul_div, h43,
      neg_mul, neg_div, mul_neg]
    exact congrArg Neg.neg h
  · rw [← mul_div_assoc Real.pi _ _]
    rw [div_eq_div_iff (by norm_num : (2:ℝ) ≠ 0)
      (Real.Gamma_pos_of_pos (show (0:ℝ) < 1/3 by norm_num)).ne']
    -- goal: 3^(1/6) * Γ(2/3) * Γ(1/3) = π * 3^(-1/3) * 2
    rw [show (3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) * Real.Gamma (1/3)
        = 3^(1/6:ℝ) * (Real.Gamma (1/3) * Real.Gamma (2/3)) from by ring,
      real_Gamma_one_third_mul_Gamma_two_thirds]
    -- goal: 3^(1/6) * (2π/√3) = π * 3^(-1/3) * 2
    have hmerge : (3:ℝ)^(1/6:ℝ) * 3^(-(1/2:ℝ)) = 3^(-1/3:ℝ) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      norm_num
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv (2 * Real.pi) ((3:ℝ)^(1/2:ℝ)),
      ← Real.rpow_neg h3pos.le]
    -- goal: 3^(1/6) * (2 * π * 3^(-(1/2))) = π * 3^(-1/3) * 2
    rw [show (3:ℝ)^(1/6:ℝ) * (2 * Real.pi * 3^(-(1/2:ℝ)))
        = 2 * Real.pi * ((3:ℝ)^(1/6:ℝ) * 3^(-(1/2:ℝ))) from by ring, hmerge]
    ring

end source6

noncomputable section source7
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

open MeasureTheory Set Filter
open scoped Topology
open Asymptotics

/-! # Small-`z` asymptotics of the Schläfli `s`-integrals

Small-argument asymptotics of the Schläfli integral.

* `schlaefliJ2_const`: the Hadamard finite-part evaluation
  `∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)`;
* `schlaefliJ2_sub_tendsto`: `J₂(z) - 3 (z/2)^{-1/3} → -3 Γ(2/3)` as `z → 0⁺`;
* `schlaefliJ1_isBigO`: `J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = O(z^{4/3})` as `z → 0⁺`.
-/

/-! ## Power integrals on half-lines and finite intervals -/

/-- For `0 < a` and `p < -1`, the power `s ↦ s^p` is integrable on `(a, ∞)` and
`∫_{a}^{∞} s^p ds = -a^{p+1}/(p+1)` (FTC with antiderivative `s^{p+1}/(p+1)`, which
vanishes at `+∞`). -/
theorem integrableOn_and_integral_rpow_Ioi {a : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) {p : ℝ /- [definition] -/ }
    (hp : p < -1 /- [standing] -/ ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioi a)
      ∧ ∫ s in Set.Ioi a, s^(p:ℝ) = - a^(p+1:ℝ)/(p+1) := by
  have hp1 : p + 1 < 0 := by linarith
  have hp1ne : (p + 1 : ℝ) ≠ 0 := ne_of_lt hp1
  have hderiv : ∀ s ∈ Set.Ioi a,
      HasDerivAt (fun s : ℝ => s^(p+1:ℝ)/(p+1)) (s^(p:ℝ)) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (ha.trans hs)
    have h := (Real.hasDerivAt_rpow_const (p := p+1) (Or.inl hs0)).div_const (p+1)
    convert! h using 1
    rw [show p + 1 - 1 = p by ring]
    field_simp
  have hT : Tendsto (fun s : ℝ => s^(p+1:ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (show (0:ℝ) < -(p+1) by linarith)
    simpa only [neg_neg] using h
  have hT2 : Tendsto (fun s : ℝ => s^(p+1:ℝ)/(p+1)) atTop (𝓝 0) := by
    have h := hT.div_const (p+1)
    rwa [zero_div] at h
  have hcont : ContinuousWithinAt (fun s : ℝ => s^(p+1:ℝ)/(p+1)) (Set.Ici a) a :=
    ((Real.continuousAt_rpow_const a (p+1) (Or.inl ha.ne')).div_const _).continuousWithinAt
  have hpos : ∀ s ∈ Set.Ioi a, 0 ≤ s^(p:ℝ) :=
    fun s hs => Real.rpow_nonneg (ha.trans hs).le _
  have hint : IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hT2
  refine ⟨hint, ?_⟩
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hT2
  rw [hftc, zero_sub, neg_div]

/-- For `0 < a ≤ b` and `p ≠ -1`, `∫_{(a,b)} s^p ds = (b^{p+1} - a^{p+1})/(p+1)`. -/
theorem integral_Ioo_rpow {a b : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) (hab : a ≤ b /- [standing] -/ ) {p : ℝ /- [definition] -/ }
    (hp : p ≠ -1 /- [standing] -/ ) :
    ∫ s in Set.Ioo a b, s^(p:ℝ) = (b^(p+1:ℝ) - a^(p+1:ℝ))/(p+1) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  exact integral_rpow (Or.inr ⟨hp, h0⟩)

/-- For `0 ≤ a` and `-1 < p`, the power `s ↦ s^p` is integrable on `(0, a]` with
`∫_{(0,a]} s^p ds = a^{p+1}/(p+1)`. -/
theorem integrableOn_and_integral_Ioc_zero_rpow {a : ℝ /- [definition] -/ } (ha : 0 ≤ a /- [standing] -/ ) {p : ℝ /- [definition] -/ }
    (hp : -1 < p /- [standing] -/ ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioc 0 a)
      ∧ ∫ s in Set.Ioc 0 a, s^(p:ℝ) = a^(p+1:ℝ)/(p+1) := by
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hp
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hI, ?_⟩
  rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hp),
    Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < p + 1)), sub_zero]

/-! ## The antiderivative for the Hadamard finite-part constant -/

/-- The antiderivative for the Hadamard finite-part computation of
`∫₀^∞ (e^{-s} - 1) s^{-4/3} ds`: on `(0, ∞)`, `A(s) = -3 (s^{-1/3} (e^{-s} - 1))`
differentiates to `s^{-4/3} (e^{-s} - 1) + 3 s^{-1/3} e^{-s}`. -/
noncomputable def schlaefliJ2ConstAntideriv (s : ℝ /- [definition] -/ ) : ℝ :=
  -3 * (s^(-1/3:ℝ) * (Real.exp (-s) - 1))

/-- The product-rule derivative of `schlaefliJ2ConstAntideriv`. -/
theorem hasDerivAt_schlaefliJ2ConstAntideriv {s : ℝ /- [definition] -/ } (hs : 0 < s /- [standing] -/ ) :
    HasDerivAt schlaefliJ2ConstAntideriv
      (s^(-4/3:ℝ) * (Real.exp (-s) - 1) + 3 * s^(-1/3:ℝ) * Real.exp (-s)) s := by
  have h1 : HasDerivAt (fun s : ℝ => s^(-1/3:ℝ)) ((-1/3) * s^(-4/3:ℝ)) s := by
    convert! Real.hasDerivAt_rpow_const (Or.inl hs.ne') using 1
    norm_num
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s) - 1) (-Real.exp (-s)) s := by
    convert! ((hasDerivAt_id' s).neg.exp.sub_const 1) using 1
    simp only [Pi.neg_apply]
    ring
  have h3 := (h1.mul h2).const_mul (-3)
  convert! h3 using 1
  ring

/-- `schlaefliJ2ConstAntideriv` vanishes at `0`. -/
theorem schlaefliJ2ConstAntideriv_zero : schlaefliJ2ConstAntideriv 0 = 0 := by
  simp [schlaefliJ2ConstAntideriv]

/-- `schlaefliJ2ConstAntideriv` is continuous at `0` from the right (squeeze against
`3 s^{2/3}`, using `|e^{-s} - 1| = 1 - e^{-s} ≤ s` for `s ≥ 0`). -/
theorem continuousWithinAt_schlaefliJ2ConstAntideriv_zero :
    ContinuousWithinAt schlaefliJ2ConstAntideriv (Set.Ici 0) 0 := by
  have hlim : Tendsto schlaefliJ2ConstAntideriv (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun s : ℝ => 3 * s^(2/3:ℝ))
      (Eventually.of_forall fun s => abs_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : 0 ≤ s := hs
      rcases hs0.eq_or_lt with rfl | hspos
      · show |(schlaefliJ2ConstAntideriv) 0| ≤ 3 * (0:ℝ)^(2/3:ℝ)
        rw [schlaefliJ2ConstAntideriv_zero, abs_zero]; positivity
      · have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hspos.le)
        have hle : 1 - Real.exp (-s) ≤ s := by
          have h := Real.add_one_le_exp (-s)
          linarith
        calc |schlaefliJ2ConstAntideriv s|
            = 3 * s^(-1/3:ℝ) * |Real.exp (-s) - 1| := by
              unfold schlaefliJ2ConstAntideriv
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hspos.le _),
                abs_of_pos (by norm_num : (0:ℝ) < 3), mul_assoc]
          _ = 3 * s^(-1/3:ℝ) * (1 - Real.exp (-s)) := by
              rw [abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
          _ ≤ 3 * s^(-1/3:ℝ) * s := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 3 * s^(2/3:ℝ) := by
              have key : s^(-1/3:ℝ) * s^(1:ℝ) = s^(2/3:ℝ) := by
                rw [← Real.rpow_add hspos, show (-1/3:ℝ) + 1 = 2/3 by norm_num]
              rw [Real.rpow_one] at key
              rw [mul_assoc, key]
    · have hc : ContinuousAt (fun s : ℝ => 3 * s^(2/3:ℝ)) 0 :=
        (Real.continuousAt_rpow_const 0 (2/3:ℝ) (Or.inr (by norm_num))).const_mul 3
      have hv : 3 * (0:ℝ)^(2/3:ℝ) = 0 := by
        rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), mul_zero]
      have h0 : Tendsto (fun s : ℝ => 3 * s^(2/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
        have ht := hc.tendsto
        rwa [hv] at ht
      exact h0.mono_left nhdsWithin_le_nhds
  simpa only [ContinuousWithinAt, schlaefliJ2ConstAntideriv_zero] using hlim

/-- `schlaefliJ2ConstAntideriv s → 0` as `s → ∞` (squeeze against `3 s^{-1/3}`). -/
theorem tendsto_schlaefliJ2ConstAntideriv_atTop :
    Tendsto schlaefliJ2ConstAntideriv Filter.atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (g := fun s : ℝ => 3 * s^(-1/3:ℝ))
    (Eventually.of_forall fun s => abs_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with s hs
    have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
    have hle : 1 - Real.exp (-s) ≤ 1 := by linarith [Real.exp_pos (-s)]
    calc |schlaefliJ2ConstAntideriv s|
        = 3 * s^(-1/3:ℝ) * |Real.exp (-s) - 1| := by
          unfold schlaefliJ2ConstAntideriv
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hs _),
            abs_of_pos (by norm_num : (0:ℝ) < 3), mul_assoc]
      _ = 3 * s^(-1/3:ℝ) * (1 - Real.exp (-s)) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      _ ≤ 3 * s^(-1/3:ℝ) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 3 * s^(-1/3:ℝ) := mul_one _
  · have h := tendsto_rpow_neg_atTop (show (0:ℝ) < 1/3 by norm_num)
    have h2 := h.const_mul 3
    rw [mul_zero, show -(1/3:ℝ) = (-1/3:ℝ) by norm_num] at h2
    exact h2

/-- The first summand `s ↦ s^{-4/3} (e^{-s} - 1)` of the derivative of
`schlaefliJ2ConstAntideriv` is integrable on `(0, ∞)`: it is `O(s^{-1/3})` near `0`
(since `|e^{-s} - 1| ≤ s`) and `O(s^{-4/3})` near `∞`. -/
theorem integrableOn_rpow_mul_exp_neg_sub_one :
    IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)) (Set.Ioi 0) := by
    intro s hs
    exact ((Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs))).mul
      ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub_const
        1)).continuousWithinAt
  have hIoc : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      (Set.Ioc 0 1) := by
    apply Integrable.mono' (integrableOn_and_integral_Ioc_zero_rpow zero_le_one
      (show (-1:ℝ) < -1/3 by norm_num)).1 ?_ ?_
    · exact (hcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 < s := hs.1
      have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)
      have hle : 1 - Real.exp (-s) ≤ s := by
        have h := Real.add_one_le_exp (-s)
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      calc s^(-4/3:ℝ) * (1 - Real.exp (-s)) ≤ s^(-4/3:ℝ) * s :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs0.le _)
        _ = s^(-1/3:ℝ) := by
          have key : s^(-4/3:ℝ) * s^(1:ℝ) = s^(-1/3:ℝ) := by
            rw [← Real.rpow_add hs0, show (-4/3:ℝ) + 1 = -1/3 by norm_num]
          rwa [Real.rpow_one] at key
  have hIoi : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      (Set.Ioi 1) := by
    apply Integrable.mono' (integrableOn_and_integral_rpow_Ioi one_pos
      (show (-4/3:ℝ) < -1 by norm_num)).1 ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := zero_lt_one.trans hs
      have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      have hle : 1 - Real.exp (-s) ≤ 1 := by linarith [Real.exp_pos (-s)]
      calc s^(-4/3:ℝ) * (1 - Real.exp (-s)) ≤ s^(-4/3:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs0.le _)
        _ = s^(-4/3:ℝ) := mul_one _
  have h := hIoc.union hIoi
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

/-- The second summand `s ↦ 3 s^{-1/3} e^{-s}` of the derivative of
`schlaefliJ2ConstAntideriv` is integrable on `(0, ∞)` (`O(s^{-1/3})` near `0`,
exponentially decaying near `∞`). -/
theorem integrableOn_rpow_mul_exp_neg :
    IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) := by
    intro s hs
    exact (((Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs))).const_mul 3).mul
      (Real.continuous_exp.continuousAt.comp continuousAt_id.neg)).continuousWithinAt
  have hIoc : IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s))
      (Set.Ioc 0 1) := by
    apply Integrable.mono' ((integrableOn_and_integral_Ioc_zero_rpow zero_le_one
      (show (-1:ℝ) < -1/3 by norm_num)).1.const_mul 3) ?_ ?_
    · exact (hcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 < s := hs.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0:ℝ) < 3)]
      calc 3 * s^(-1/3:ℝ) * Real.exp (-s) ≤ 3 * s^(-1/3:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le))
            (by positivity)
        _ = 3 * s^(-1/3:ℝ) := mul_one _
  have hIoi : IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s))
      (Set.Ioi 1) := by
    apply Integrable.mono' ((integrableOn_exp_neg_Ioi 1).const_mul 3) ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := zero_lt_one.trans hs
      have hs1 : 1 ≤ s := hs.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0:ℝ) < 3)]
      have hpow : s^(-1/3:ℝ) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-1/3:ℝ) ≤ 0 by norm_num)
        rwa [Real.rpow_zero] at h
      calc 3 * s^(-1/3:ℝ) * Real.exp (-s) ≤ 3 * 1 * Real.exp (-s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
            (Real.exp_pos _).le
        _ = 3 * Real.exp (-s) := by ring
  have h := hIoc.union hIoi
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

/-- The Hadamard finite-part constant: `∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)`.
Proof: FTC on `(0, ∞)` applied to `A(s) = -3 s^{-1/3} (e^{-s} - 1)` gives
`∫ A' = 0`, i.e. `∫ s^{-4/3} (e^{-s} - 1) = -3 ∫ s^{-1/3} e^{-s} = -3 Γ(2/3)`. -/
theorem schlaefliJ2_const :
    ∫ s in Set.Ioi (0:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ) = -3 * Real.Gamma (2/3) := by
  have hint : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)
      + 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_sub_one.add integrableOn_rpow_mul_exp_neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_schlaefliJ2ConstAntideriv_zero
    (fun s hs => hasDerivAt_schlaefliJ2ConstAntideriv hs)
    hint tendsto_schlaefliJ2ConstAntideriv_atTop
  rw [schlaefliJ2ConstAntideriv_zero, sub_zero] at hftc
  rw [integral_add integrableOn_rpow_mul_exp_neg_sub_one integrableOn_rpow_mul_exp_neg]
    at hftc
  have hG : Real.Gamma (2/3) = ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-1/3:ℝ) := by
    have h := Real.Gamma_eq_integral (show (0:ℝ) < 2/3 by norm_num)
    rwa [show (2/3:ℝ) - 1 = -1/3 by norm_num] at h
  have h2val : (∫ s in Set.Ioi 0, 3 * s^(-1/3:ℝ) * Real.exp (-s)) = 3 * Real.Gamma (2/3) := by
    have hcongr : (∫ s in Set.Ioi 0, 3 * s^(-1/3:ℝ) * Real.exp (-s))
        = 3 * ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-1/3:ℝ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      ring
    rw [hcongr, ← hG]
  have hmain : (∫ s in Set.Ioi 0, s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      = -3 * Real.Gamma (2/3) := by linarith [hftc, h2val]
  rw [← hmain]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  ring


/-! ## Small-`z` asymptotics of `J₂` -/

/-- The limiting centered integrand `k(s) = (e^{-s} - 1) s^{-4/3}` is integrable on
`(0, ∞)` (repackaging of `integrableOn_rpow_mul_exp_neg_sub_one`). -/
theorem integrableOn_exp_sub_one_mul_rpow :
    IntegrableOn (fun s : ℝ => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_sub_one.congr_fun (fun _ _ => mul_comm _ _)
    measurableSet_Ioi

/-- For `0 < z`, the centered `J₂` integral:
`J₂(z) - 3 (z/2)^{-1/3} = ∫_{z/2}^∞ (e^{-s - z²/(4s)} - 1) s^{-4/3} ds`
(the constant `3 (z/2)^{-1/3}` is the bare power integral `∫_{z/2}^∞ s^{-4/3} ds`). -/
theorem schlaefliJ2_sub_eq_integral {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ)
      = ∫ s in Set.Ioi (z/2), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI2 : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi (z/2)) :=
    (integrableOn_and_integral_rpow_Ioi hza (by norm_num)).1
  have hval : ∫ s in Set.Ioi (z/2), s^(-4/3:ℝ) = 3 * (z/2)^(-1/3:ℝ) := by
    have h := (integrableOn_and_integral_rpow_Ioi hza (show (-4/3:ℝ) < -1 by norm_num)).2
    rw [show (-4/3:ℝ) + 1 = -1/3 by norm_num] at h
    rw [h, div_eq_iff (by norm_num : (-1/3:ℝ) ≠ 0)]
    ring
  unfold schlaefliJ2
  rw [← hval, ← integral_sub hI1 hI2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  ring

/-- The centered `J₂` integrand is integrable on `(z/2, ∞)` for `0 < z`. -/
theorem integrableOn_centeredJ2 {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    IntegrableOn (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := by
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI2 : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi (z/2)) :=
    (integrableOn_and_integral_rpow_Ioi (by linarith) (by norm_num)).1
  have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) - (fun s => s^(-4/3:ℝ)) := by
    funext s
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact hI1.sub hI2

/-- For `0 < z ≤ 1`, the centered `J₂` integral splits at `s = 1`. -/
theorem centeredJ2_split {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) (hz1 : z ≤ 1 /- [standing] -/ ) :
    (∫ s in Set.Ioi (z/2), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (∫ s in Set.Ioc (z/2) 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        + ∫ s in Set.Ioi 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ) := by
  have hz2 : z/2 ≤ 1 := by linarith
  have hI := integrableOn_centeredJ2 hz
  rw [← Ioc_union_Ioi_eq_Ioi hz2]
  exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hz2))

/-- Powers `s ↦ s^p` are integrable on `(a, b)` when `0 < a ≤ b` (any `p`). -/
theorem integrableOn_Ioo_rpow_of_pos {a : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hab : a ≤ b /- [standing] -/ )
    (p : ℝ /- [definition] -/ ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioo a b) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hI).mono_set
    Ioo_subset_Ioc_self

/-- Dominated convergence of the centered `J₂` integral on `(1, ∞)` as `z → 0⁺`
(dominator `s^{-4/3}`). -/
theorem tendsto_centeredJ2_Ioi_one :
    Tendsto (fun z => ∫ s in Set.Ioi (1:ℝ), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun s : ℝ => s^(-4/3:ℝ)) ?_ ?_
    ((integrableOn_and_integral_rpow_Ioi one_pos (by norm_num)).1) ?_
  · filter_upwards with z
    have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
        (Set.Ioi 1) := continuousOn_schlaefliJ_kernel one_pos _
    have h2 : ContinuousOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi 1) := by
      intro s hs
      exact (Real.continuousAt_rpow_const s _
        (Or.inl (ne_of_gt (zero_lt_one.trans hs)))).continuousWithinAt
    have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        = fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ) - s^(-4/3:ℝ) :=
      funext fun s => by ring
    have hc : ContinuousOn (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        (Set.Ioi 1) := by
      rw [heq]
      exact h1.sub h2
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := zero_lt_one.trans hs
    have hnn : (0:ℝ) ≤ z^2/(4*s) :=
      div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
    have hexp1 : Real.exp (-s - z^2/(4*s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub,
      abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    have hle : 1 - Real.exp (-s - z^2/(4*s)) ≤ 1 := by
        linarith [Real.exp_pos (-s - z^2/(4*s))]
    calc (1 - Real.exp (-s - z^2/(4*s))) * s^(-4/3:ℝ) ≤ 1 * s^(-4/3:ℝ) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs0.le _)
      _ = s^(-4/3:ℝ) := one_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := zero_lt_one.trans hs
    have hc : ContinuousAt (fun z : ℝ => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ)) 0 := by
      fun_prop
    have h0 : Tendsto (fun z : ℝ => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        (𝓝 (0:ℝ)) (𝓝 ((Real.exp (-s - (0:ℝ)^2/(4*s)) - 1) * s^(-4/3:ℝ))) := hc.tendsto
    have hv : (Real.exp (-s - (0:ℝ)^2/(4*s)) - 1) * s^(-4/3:ℝ)
        = (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
      rw [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_zero]
    rw [hv] at h0
    exact h0.mono_left nhdsWithin_le_nhds

/-- The `k`-integral over `(z/2, 1)` tends to the `k`-integral over `(0, 1)` as `z → 0⁺`
(dominated convergence with dominator `|k|`). -/
theorem tendsto_airyAsympK_Ioo :
    Tendsto (fun z => ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
  have hkI : IntegrableOn (fun s : ℝ => (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (Set.Ioo 0 1) :=
    integrableOn_exp_sub_one_mul_rpow.mono_set Ioo_subset_Ioi_self
  have hmeas : AEStronglyMeasurable (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (volume.restrict (Set.Ioo 0 1)) := by
    have hcont : ContinuousOn (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioi 0) := by
      intro s hs
      exact (((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub
        continuousAt_const).mul
        (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs)))).continuousWithinAt
    exact (hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
  have hdct : Tendsto (fun z => ∫ s in Set.Ioo 0 1,
        (Set.Ioi (z/2)).indicator (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => |(Real.exp (-s) - 1) * s^(-4/3:ℝ)|) ?_ ?_ hkI.abs ?_
    · filter_upwards with z
      exact hmeas.indicator measurableSet_Ioi
    · filter_upwards with z
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun s _ => ?_
      calc ‖(Set.Ioi (z/2)).indicator (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s‖
          ≤ ‖(Real.exp (-s) - 1) * s^(-4/3:ℝ)‖ := norm_indicator_le_norm_self _ _
        _ = |(Real.exp (-s) - 1) * s^(-4/3:ℝ)| := Real.norm_eq_abs _
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
      have hz2 : Tendsto (fun z : ℝ => z/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hc : ContinuousAt (fun z : ℝ => z / 2) 0 := continuousAt_id.div_const 2
        have h0 : Tendsto (fun z : ℝ => z / 2) (𝓝 (0:ℝ)) (𝓝 0) := by
          have ht := hc.tendsto
          rwa [zero_div] at ht
        exact h0.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ z in 𝓝[>] (0:ℝ), z/2 < s := hz2.eventually (Iio_mem_nhds hs.1)
      have heq : (fun z => (Set.Ioi (z/2)).indicator
            (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) := by
        filter_upwards [hev] with z hz2s
        exact Set.indicator_of_mem hz2s _
      exact heq.tendsto
  refine Tendsto.congr' ?_ hdct
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
  have hzpos : (0:ℝ) < z := hz
  have hz2 : (0:ℝ) ≤ z/2 := by linarith
  rw [setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioo 0 1 ∩ Set.Ioi (z/2) = Set.Ioo (z/2) 1 := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [hset]

/-- The pointwise bound for the difference integrand: for `0 < z` and `z/2 < s`,
`|(e^{-s-z²/(4s)} - e^{-s}) s^{-4/3}| ≤ (z²/4) s^{-7/3}` (from `1 - e^{-u} ≤ u`). -/
theorem abs_centeredJ2_diff_le {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) {s : ℝ /- [definition] -/ } (hs : z/2 < s /- [standing] -/ ) :
    |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| ≤ (z^2/4) * s^(-7/3:ℝ) := by
  have hs0 : 0 < s := by linarith [hz]
  have hnn : (0:ℝ) ≤ z^2/(4*s) := div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
  have hrewrite : Real.exp (-s - z^2/(4*s)) - Real.exp (-s)
      = Real.exp (-s) * (Real.exp (-(z^2/(4*s))) - 1) := by
    rw [show -s - z^2/(4*s) = -s + -(z^2/(4*s)) by ring, Real.exp_add]
    ring
  have hexp1 : Real.exp (-(z^2/(4*s))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnn)
  have hle : 1 - Real.exp (-(z^2/(4*s))) ≤ z^2/(4*s) := by
    have h := Real.add_one_le_exp (-(z^2/(4*s)))
    linarith
  rw [hrewrite, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub,
    abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
  calc Real.exp (-s) * (1 - Real.exp (-(z^2/(4*s)))) * s^(-4/3:ℝ)
      ≤ 1 * (z^2/(4*s)) * s^(-4/3:ℝ) := by
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0.le _)
        exact mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)) hle
          (sub_nonneg.mpr hexp1) zero_le_one
    _ = (z^2/4) * s^(-7/3:ℝ) := by
        have key : s^(-1:ℝ) * s^(-4/3:ℝ) = s^(-7/3:ℝ) := by
          rw [← Real.rpow_add hs0, show (-1:ℝ) + -4/3 = -7/3 by norm_num]
        have h2 : z^2/(4*s) = (z^2/4) * s^(-1:ℝ) := by
          have hsne : s ≠ 0 := hs0.ne'
          rw [Real.rpow_neg_one]
          field_simp
        rw [h2]
        calc 1 * ((z^2/4) * s^(-1:ℝ)) * s^(-4/3:ℝ)
            = (z^2/4) * (s^(-1:ℝ) * s^(-4/3:ℝ)) := by ring
          _ = (z^2/4) * s^(-7/3:ℝ) := by rw [key]

/-- Continuity of the difference integrand on `(a, ∞)` for `0 < a`. -/
theorem continuousOn_centeredJ2_diff {z a : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) :
    ContinuousOn (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      (Set.Ioi a) := by
  have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) (Set.Ioi a) :=
    continuousOn_schlaefliJ_kernel ha _
  have h2 : ContinuousOn (fun s : ℝ => Real.exp (-s) * s^(-4/3:ℝ)) (Set.Ioi a) := by
    intro s hs
    exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
      (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt (ha.trans hs))))).continuousWithinAt
  have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      = fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ) - Real.exp (-s) * s^(-4/3:ℝ) :=
    funext fun s => by ring
  rw [heq]
  exact h1.sub h2

/-- The difference integrand on `(z/2, 1)` tends to `0` as `z → 0⁺`: its absolute value is
bounded by `(z²/4) ∫_{z/2}^1 s^{-7/3} ds = (3/16) z² ((z/2)^{-4/3} - 1) ≤ C z^{2/3}`. -/
theorem tendsto_centeredJ2_diff_Ioo :
    Tendsto (fun z => ∫ s in Set.Ioo (z/2) 1,
      (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (g := fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ))
    (Eventually.of_forall fun z => abs_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
    have hzpos : (0:ℝ) < z := hz
    have hz2 : (0:ℝ) < z/2 := by linarith
    have hz2le : z/2 ≤ 1 := by linarith
    have hg : IntegrableOn (fun s : ℝ => (z^2/4) * s^(-7/3:ℝ)) (Set.Ioo (z/2) 1) :=
      (integrableOn_Ioo_rpow_of_pos hz2 hz2le _).const_mul _
    have hf : IntegrableOn
        (fun s => |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|)
        (Set.Ioo (z/2) 1) := by
      apply hg.mono' ?_ ?_
      · exact ((continuousOn_centeredJ2_diff hz2).mono
          Ioo_subset_Ioi_self).abs.aestronglyMeasurable measurableSet_Ioo
      · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_centeredJ2_diff_le hz hs.1
    have hval : ∫ s in Set.Ioo (z/2) 1, s^(-7/3:ℝ) = (3/4) * ((z/2)^(-4/3:ℝ) - 1) := by
      rw [integral_Ioo_rpow hz2 hz2le (by norm_num : (-7/3:ℝ) ≠ -1), Real.one_rpow,
        show (-7/3:ℝ) + 1 = -4/3 by norm_num]
      field_simp
      ring
    have h1 : |∫ s in Set.Ioo (z/2) 1,
        (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
        ≤ ∫ s in Set.Ioo (z/2) 1,
            |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := by
      calc |∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
          = ‖∫ s in Set.Ioo (z/2) 1,
              (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Set.Ioo (z/2) 1,
              ‖(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ s in Set.Ioo (z/2) 1,
              |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro s _
            exact Real.norm_eq_abs _
    calc |∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
        ≤ ∫ s in Set.Ioo (z/2) 1,
            |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := h1
      _ ≤ ∫ s in Set.Ioo (z/2) 1, (z^2/4) * s^(-7/3:ℝ) :=
          setIntegral_mono_on hf hg measurableSet_Ioo
            (fun s hs => abs_centeredJ2_diff_le hz hs.1)
      _ = (z^2/4) * ((3/4) * ((z/2)^(-4/3:ℝ) - 1)) := by
          rw [integral_const_mul, hval]
      _ ≤ (z^2/4) * ((3/4) * (z/2)^(-4/3:ℝ)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by norm_num)
      _ = (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ) := by
          have hz2pow : (z/2)^(-4/3:ℝ) = (2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ) := by
            have h2p : (0:ℝ) < (2:ℝ)^(-4/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
            rw [Real.div_rpow hz.le (by norm_num : (0:ℝ) ≤ 2), div_eq_iff h2p.ne']
            calc z^(-4/3:ℝ) = 1 * z^(-4/3:ℝ) := (one_mul _).symm
              _ = (2:ℝ)^((4/3:ℝ) + (-4/3:ℝ)) * z^(-4/3:ℝ) := by
                  rw [show (4/3:ℝ) + -4/3 = 0 by norm_num, Real.rpow_zero]
              _ = (2:ℝ)^(4/3:ℝ) * (2:ℝ)^(-4/3:ℝ) * z^(-4/3:ℝ) := by
                  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
              _ = (2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ) * (2:ℝ)^(-4/3:ℝ) := by ring
          have hzpow : z^2 * z^(-4/3:ℝ) = z^(2/3:ℝ) := by
            rw [← Real.rpow_natCast z 2, ← Real.rpow_add hz]
            norm_num
          rw [hz2pow]
          calc (z^2/4) * ((3/4) * ((2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ)))
              = (3/16) * (2:ℝ)^(4/3:ℝ) * (z^2 * z^(-4/3:ℝ)) := by ring
            _ = (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ) := by rw [hzpow]
  · have hc : ContinuousAt (fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ)) 0 :=
      (Real.continuousAt_rpow_const 0 (2/3:ℝ) (Or.inr (by norm_num))).const_mul _
    have hv : (3/16) * (2:ℝ)^(4/3:ℝ) * (0:ℝ)^(2/3:ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), mul_zero]
    have h0 : Tendsto (fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
      have ht := hc.tendsto
      rwa [hv] at ht
    exact h0.mono_left nhdsWithin_le_nhds

/-- Decomposition of the centered `J₂` integral on `(z/2, 1]` into the difference part and
the limiting part, for `0 < z ≤ 1`. -/
theorem centeredJ2_Ioc_eq_add {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) (hz1 : z ≤ 1 /- [standing] -/ ) :
    (∫ s in Set.Ioc (z/2) 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
        + ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
  have hz2 : (0:ℝ) < z/2 := by linarith
  have hz2le : z/2 ≤ 1 := by linarith
  have hg : IntegrableOn (fun s : ℝ => (z^2/4) * s^(-7/3:ℝ)) (Set.Ioo (z/2) 1) :=
    (integrableOn_Ioo_rpow_of_pos hz2 hz2le _).const_mul _
  have hhI : IntegrableOn
      (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      (Set.Ioo (z/2) 1) := by
    apply hg.mono' ?_ ?_
    · exact ((continuousOn_centeredJ2_diff hz2).mono
        Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
      rw [Real.norm_eq_abs]
      exact abs_centeredJ2_diff_le hz hs.1
  have hkI : IntegrableOn (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioo (z/2) 1) :=
    integrableOn_exp_sub_one_mul_rpow.mono_set
      (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hz2.le))
  rw [integral_Ioc_eq_integral_Ioo, ← integral_add hhI hkI]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s _
  ring

/-- `J₂(z) = 3 (z/2)^{-1/3} - 3 Γ(2/3) + o(1)` as `z → 0⁺`: the centered integral tends to
`∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)` (`schlaefliJ2_const`) by dominated convergence
on `(1, ∞)` and on `(0, 1)`, and the `z²/(4s)`-perturbation contributes `O(z^{2/3})`. -/
theorem schlaefliJ2_sub_tendsto :
    Tendsto (fun z => schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (-3 * Real.Gamma (2/3))) := by
  have heq : (fun z => (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        + ((∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
          + ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ)))
      =ᶠ[𝓝[>] (0:ℝ)] fun z => schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
    rw [schlaefliJ2_sub_eq_integral hz, centeredJ2_split hz hz1.le,
      centeredJ2_Ioc_eq_add hz hz1.le]
    ring
  refine Tendsto.congr' heq ?_
  have hsum := tendsto_centeredJ2_Ioi_one.add
    (tendsto_centeredJ2_diff_Ioo.add tendsto_airyAsympK_Ioo)
  have hval : (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      + (0 + ∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      = -3 * Real.Gamma (2/3) := by
    have hsplit : (∫ s in Set.Ioi 0, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
        = (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
          + ∫ s in Set.Ici 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
      have hdisj : Disjoint (Set.Ioo (0:ℝ) 1) (Set.Ici 1) := by
        rw [Set.disjoint_left]
        rintro s ⟨-, h1⟩ h2
        exact absurd h2 (not_le.mpr h1)
      rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
      exact setIntegral_union hdisj measurableSet_Ici
        (integrableOn_exp_sub_one_mul_rpow.mono_set Ioo_subset_Ioi_self)
        (integrableOn_exp_sub_one_mul_rpow.mono_set
          (by intro s hs; exact Set.mem_Ioi.mpr (zero_lt_one.trans_le (Set.mem_Ici.mp hs))))
    rw [schlaefliJ2_const, integral_Ici_eq_integral_Ioi] at hsplit
    linarith [hsplit]
  rwa [hval] at hsum


/-! ## Small-`z` asymptotics of `J₁` -/

/-- Powers `s ↦ s^p` are integrable on `(a, b]` when `0 < a ≤ b` (any `p`). -/
theorem integrableOn_Ioc_rpow_of_pos {a : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) {b : ℝ /- [definition] -/ } (hab : a ≤ b /- [standing] -/ )
    (p : ℝ /- [definition] -/ ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioc a b) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hI

/-- For `0 < s` and any `p`, `|(e^{-s} - 1) s^p| ≤ s^{p+1}` (from `1 - e^{-s} ≤ s`). -/
theorem abs_exp_sub_one_mul_rpow_le {p : ℝ /- [definition] -/ } {s : ℝ /- [definition] -/ } (hs : 0 < s /- [standing] -/ ) :
    |(Real.exp (-s) - 1) * s^(p:ℝ)| ≤ s^(p + 1:ℝ) := by
  have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  have hle : 1 - Real.exp (-s) ≤ s := by
    have h := Real.add_one_le_exp (-s)
    linarith
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
  calc (1 - Real.exp (-s)) * s^(p:ℝ) ≤ s * s^(p:ℝ) :=
      mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs.le _)
    _ = s^(p + 1:ℝ) := by
      have key : s^(1:ℝ) * s^(p:ℝ) = s^(p + 1:ℝ) := by
        rw [← Real.rpow_add hs, show (1:ℝ) + p = p + 1 by ring]
      rwa [Real.rpow_one] at key

/-- The `J₁` decomposition: for `0 < z`,
`J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = R₂(z) - R₁(z)` with
`R₂(z) = ∫_{z/2}^∞ (e^{-z²/(4s)} - 1) e^{-s} s^{-2/3} ds` and
`R₁(z) = ∫_0^{z/2} (e^{-s} - 1) s^{-2/3} ds`. -/
theorem schlaefliJ1_decomp {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ)
      = (∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        - ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hG0 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x^(-2/3:ℝ)) (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (show (0:ℝ) < 1/3 by norm_num)
    rwa [show (1/3:ℝ) - 1 = -2/3 by norm_num] at h
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI1' : IntegrableOn (fun s => Real.exp (-s) * s^(-2/3:ℝ)) (Set.Ioi (z/2)) :=
    hG0.mono_set (Ioi_subset_Ioi hza.le)
  have hR2I : IntegrableOn
      (fun s => (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
      (Set.Ioi (z/2)) := by
    have heq : (fun s => (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        = (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
          - (fun s => Real.exp (-s) * s^(-2/3:ℝ)) := by
      funext s
      simp only [Pi.sub_apply]
      rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
      ring
    rw [heq]
    exact hI1.sub hI1'
  have hJ : schlaefliJ1 z = (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      + ∫ s in Set.Ioi (z/2),
          (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)) := by
    unfold schlaefliJ1
    rw [← integral_add hI1' hR2I]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only
    rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
    ring
  have hG : Real.Gamma (1/3) = (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      + ∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-2/3:ℝ) := by
    have hGe : Real.Gamma (1/3) = ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-2/3:ℝ) := by
      have h := Real.Gamma_eq_integral (show (0:ℝ) < 1/3 by norm_num)
      rwa [show (1/3:ℝ) - 1 = -2/3 by norm_num] at h
    rw [hGe, ← Ioc_union_Ioi_eq_Ioi hza.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hG0.mono_set (fun s hs => hs.1)) hI1'
  have hIoc : (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      = 3 * (z/2)^(1/3:ℝ) + ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
    have hpow : ∫ s in Set.Ioc 0 (z/2), s^(-2/3:ℝ) = 3 * (z/2)^(1/3:ℝ) := by
      have h := (integrableOn_and_integral_Ioc_zero_rpow hza.le
        (show (-1:ℝ) < -2/3 by norm_num)).2
      rw [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
      rw [h, div_eq_iff (by norm_num : (1/3:ℝ) ≠ 0)]
      ring
    have hIp : IntegrableOn (fun s : ℝ => s^(-2/3:ℝ)) (Set.Ioc 0 (z/2)) :=
      (integrableOn_and_integral_Ioc_zero_rpow hza.le (by norm_num)).1
    have hIe : IntegrableOn (fun s => (Real.exp (-s) - 1) * s^(-2/3:ℝ))
        (Set.Ioc 0 (z/2)) := by
      have hG0' := hG0.mono_set (fun s (hs : s ∈ Set.Ioc 0 (z/2)) => hs.1)
      have heq : (fun s => (Real.exp (-s) - 1) * s^(-2/3:ℝ))
          = (fun s => Real.exp (-s) * s^(-2/3:ℝ)) - (fun s => s^(-2/3:ℝ)) := by
        funext s
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      exact hG0'.sub hIp
    have hsplit : (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
        = (∫ s in Set.Ioc 0 (z/2), s^(-2/3:ℝ))
          + ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
      rw [← integral_add hIp hIe]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      ring
    rw [hsplit, hpow]
  rw [hJ, hG, hIoc]
  ring

/-- The `R₁` bound: for `0 < z`,
`|∫_0^{z/2} (e^{-s} - 1) s^{-2/3} ds| ≤ ∫_0^{z/2} s^{1/3} ds = (3/4) (z/2)^{4/3}`. -/
theorem abs_schlaefliJ1_R1_le {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) :
    |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)| ≤ (3/4) * (z/2)^(4/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hg : IntegrableOn (fun s : ℝ => s^(1/3:ℝ)) (Set.Ioc 0 (z/2)) :=
    (integrableOn_and_integral_Ioc_zero_rpow hza.le (by norm_num)).1
  have hval : ∫ s in Set.Ioc 0 (z/2), s^(1/3:ℝ) = (3/4) * (z/2)^(4/3:ℝ) := by
    have h := (integrableOn_and_integral_Ioc_zero_rpow hza.le
      (show (-1:ℝ) < 1/3 by norm_num)).2
    rw [show (1/3:ℝ) + 1 = 4/3 by norm_num] at h
    rw [h, div_eq_iff (by norm_num : (4/3:ℝ) ≠ 0)]
    ring
  have hf : IntegrableOn (fun s => |(Real.exp (-s) - 1) * s^(-2/3:ℝ)|)
      (Set.Ioc 0 (z/2)) := by
    apply Integrable.mono' hg ?_ ?_
    · have hcont : ContinuousOn (fun s => |(Real.exp (-s) - 1) * s^(-2/3:ℝ)|)
        (Set.Ioi 0) := by
        intro s hs
        exact ((((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub
          continuousAt_const).mul
          (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs)))).abs).continuousWithinAt
      exact (hcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      rw [Real.norm_eq_abs, abs_abs]
      have h := abs_exp_sub_one_mul_rpow_le (p := -2/3) hs.1
      rwa [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
  calc |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ ∫ s in Set.Ioc 0 (z/2), |(Real.exp (-s) - 1) * s^(-2/3:ℝ)| := by
        calc |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
            = ‖∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ∫ s in Set.Ioc 0 (z/2), ‖(Real.exp (-s) - 1) * s^(-2/3:ℝ)‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ s in Set.Ioc 0 (z/2), |(Real.exp (-s) - 1) * s^(-2/3:ℝ)| := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro s _
              exact Real.norm_eq_abs _
    _ ≤ ∫ s in Set.Ioc 0 (z/2), s^(1/3:ℝ) := by
        apply setIntegral_mono_on hf hg measurableSet_Ioc
        intro s hs
        have h := abs_exp_sub_one_mul_rpow_le (p := -2/3) hs.1
        rwa [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
    _ = (3/4) * (z/2)^(4/3:ℝ) := hval

/-- The `R₂` bound, first form: for `0 < z ≤ 1`,
`|R₂(z)| ≤ (z²/4)((3/2)(z/2)^{-2/3} + 1)`. -/
theorem abs_schlaefliJ1_R2_le_aux {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) (hz1 : z ≤ 1 /- [standing] -/ ) :
    |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hzle : z/2 ≤ 1 := by linarith
  have hdom : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi (z/2)) := by
    have h1 : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioc (z/2) 1) := by
      apply Integrable.mono' (integrableOn_Ioc_rpow_of_pos hza hzle (-5/3)) ?_ ?_
      · have hcont : ContinuousOn (fun s => Real.exp (-s) * s^(-5/3:ℝ))
          (Set.Ioi (z/2)) := by
          intro s hs
          exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
            (Real.continuousAt_rpow_const s _
              (Or.inl (ne_of_gt (hza.trans hs))))).continuousWithinAt
        exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
        have hs0 : 0 < s := hza.trans hs.1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
        calc Real.exp (-s) * s^(-5/3:ℝ) ≤ 1 * s^(-5/3:ℝ) :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)) (Real.rpow_nonneg hs0.le _)
          _ = s^(-5/3:ℝ) := one_mul _
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi 1) := by
      apply Integrable.mono' (integrableOn_exp_neg_Ioi 1) ?_ ?_
      · have hcont : ContinuousOn (fun s => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi 1) := by
          intro s hs
          exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
            (Real.continuousAt_rpow_const s _
              (Or.inl (ne_of_gt (zero_lt_one.trans hs))))).continuousWithinAt
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
        have hs1 : 1 ≤ s := hs.le
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hs).le _)]
        have hpow : s^(-5/3:ℝ) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-5/3:ℝ) ≤ 0 by norm_num)
          rwa [Real.rpow_zero] at h
        calc Real.exp (-s) * s^(-5/3:ℝ) ≤ Real.exp (-s) * 1 :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
          _ = Real.exp (-s) := mul_one _
    have h := h1.union h2
    rwa [Ioc_union_Ioi_eq_Ioi hzle] at h
  have hpt : ∀ s ∈ Set.Ioi (z/2),
      |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        ≤ (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
    intro s hs
    have hs0 : 0 < s := hza.trans hs
    have hnn : (0:ℝ) ≤ z^2/(4*s) := div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
    have hexp1 : Real.exp (-z^2/(4*s)) ≤ 1 := by
      rw [neg_div]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnn)
    have hle : 1 - Real.exp (-z^2/(4*s)) ≤ z^2/(4*s) := by
      rw [neg_div]
      have h := Real.add_one_le_exp (-(z^2/(4*s)))
      linarith
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub, abs_mul,
      abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    calc (1 - Real.exp (-z^2/(4*s))) * (Real.exp (-s) * s^(-2/3:ℝ))
        ≤ (z^2/(4*s)) * (Real.exp (-s) * s^(-2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right hle
          (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _))
      _ = (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
        have key : s^(-1:ℝ) * s^(-2/3:ℝ) = s^(-5/3:ℝ) := by
          rw [← Real.rpow_add hs0, show (-1:ℝ) + -2/3 = -5/3 by norm_num]
        have h2 : z^2/(4*s) = (z^2/4) * s^(-1:ℝ) := by
          have hsne : s ≠ 0 := hs0.ne'
          rw [Real.rpow_neg_one]
          field_simp
        rw [h2]
        calc (z^2/4 * s^(-1:ℝ)) * (Real.exp (-s) * s^(-2/3:ℝ))
            = (z^2/4) * (Real.exp (-s) * (s^(-1:ℝ) * s^(-2/3:ℝ))) := by ring
          _ = (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by rw [key]
  have hfabs : IntegrableOn
      (fun s => |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|)
      (Set.Ioi (z/2)) := by
    apply Integrable.mono' (hdom.const_mul (z^2/4)) ?_ ?_
    · have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
          (Set.Ioi (z/2)) := continuousOn_schlaefliJ_kernel hza _
      have h2 : ContinuousOn (fun s => Real.exp (-s) * s^(-2/3:ℝ)) (Set.Ioi (z/2)) := by
        intro s hs
        exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
          (Real.continuousAt_rpow_const s _
            (Or.inl (ne_of_gt (hza.trans hs))))).continuousWithinAt
      have heq : (fun s => |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|)
          = fun s => |Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ)
              - Real.exp (-s) * s^(-2/3:ℝ)| := by
        funext s
        congr 1
        rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
        ring
      have hcont : ContinuousOn
          (fun s => |Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ) - Real.exp (-s) * s^(-2/3:ℝ)|)
          (Set.Ioi (z/2)) := (h1.sub h2).abs
      rw [heq]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      rw [Real.norm_eq_abs, abs_abs]
      exact hpt s hs
  have hnorm : |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ ∫ s in Set.Ioi (z/2), (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
    calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        ≤ ∫ s in Set.Ioi (z/2),
            |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))| := by
          calc |∫ s in Set.Ioi (z/2),
                (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
              = ‖∫ s in Set.Ioi (z/2),
                  (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))‖ :=
                (Real.norm_eq_abs _).symm
            _ ≤ ∫ s in Set.Ioi (z/2),
                  ‖(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ s in Set.Ioi (z/2),
                  |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))| := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro s _
                exact Real.norm_eq_abs _
      _ ≤ ∫ s in Set.Ioi (z/2), (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) :=
          setIntegral_mono_on hfabs (hdom.const_mul (z^2/4)) measurableSet_Ioi hpt
  rw [integral_const_mul] at hnorm
  have hint : (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ))
      ≤ (3/2) * (z/2)^(-2/3:ℝ) + 1 := by
    have hsplit : (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ))
        = (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
          + ∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ) := by
      rw [← Ioc_union_Ioi_eq_Ioi hzle]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hdom.mono_set Ioc_subset_Ioi_self) (hdom.mono_set (Ioi_subset_Ioi hzle))
    have h1le : (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
        ≤ (3/2) * ((z/2)^(-2/3:ℝ) - 1) := by
      calc (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
          ≤ ∫ s in Set.Ioc (z/2) 1, s^(-5/3:ℝ) := by
            apply setIntegral_mono_on (hdom.mono_set Ioc_subset_Ioi_self)
              (integrableOn_Ioc_rpow_of_pos hza hzle _) measurableSet_Ioc
            intro s hs
            have hs0 : 0 < s := hza.trans hs.1
            calc Real.exp (-s) * s^(-5/3:ℝ) ≤ 1 * s^(-5/3:ℝ) :=
                mul_le_mul_of_nonneg_right
                  (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le))
                  (Real.rpow_nonneg hs0.le _)
              _ = s^(-5/3:ℝ) := one_mul _
        _ = (3/2) * ((z/2)^(-2/3:ℝ) - 1) := by
            rw [integral_Ioc_eq_integral_Ioo,
              integral_Ioo_rpow hza hzle (by norm_num : (-5/3:ℝ) ≠ -1), Real.one_rpow,
              show (-5/3:ℝ) + 1 = -2/3 by norm_num, div_eq_iff (by norm_num : (-2/3:ℝ) ≠ 0)]
            ring
    have h2le : (∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ)) ≤ 1 := by
      calc (∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ))
          ≤ ∫ s in Set.Ioi 1, Real.exp (-s) := by
            apply setIntegral_mono_on (hdom.mono_set (Ioi_subset_Ioi hzle))
              (integrableOn_exp_neg_Ioi 1) measurableSet_Ioi
            intro s hs
            have hs1 : 1 ≤ s := hs.le
            have hpow : s^(-5/3:ℝ) ≤ 1 := by
              have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-5/3:ℝ) ≤ 0 by norm_num)
              rwa [Real.rpow_zero] at h
            calc Real.exp (-s) * s^(-5/3:ℝ) ≤ Real.exp (-s) * 1 :=
                mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
              _ = Real.exp (-s) := mul_one _
        _ = Real.exp (-1) := integral_exp_neg_Ioi 1
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    rw [hsplit]
    linarith [h1le, h2le]
  calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ) := hnorm
    _ ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hint (by positivity)

/-- The `R₂` bound, final form: for `0 < z ≤ 1`, `|R₂(z)| ≤ z^{4/3}`. -/
theorem abs_schlaefliJ1_R2_le {z : ℝ /- [definition] -/ } (hz : 0 < z /- [standing] -/ ) (hz1 : z ≤ 1 /- [standing] -/ ) :
    |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ z^(4/3:ℝ) := by
  have haux := abs_schlaefliJ1_R2_le_aux hz hz1
  have h2pow2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two (show (2/3:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hzpow4 : z^2 ≤ z^(4/3:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hz hz1
      (show (4/3:ℝ) ≤ ((2:ℕ):ℝ) by norm_num)
    rwa [Real.rpow_natCast] at h
  have hz2pow : (z/2)^(-2/3:ℝ) = (2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ) := by
    have h2p : (0:ℝ) < (2:ℝ)^(-2/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.div_rpow hz.le (by norm_num : (0:ℝ) ≤ 2), div_eq_iff h2p.ne']
    calc z^(-2/3:ℝ) = 1 * z^(-2/3:ℝ) := (one_mul _).symm
      _ = (2:ℝ)^((2/3:ℝ) + (-2/3:ℝ)) * z^(-2/3:ℝ) := by
          rw [show (2/3:ℝ) + -2/3 = 0 by norm_num, Real.rpow_zero]
      _ = (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-2/3:ℝ) * z^(-2/3:ℝ) := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      _ = (2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ) * (2:ℝ)^(-2/3:ℝ) := by ring
  have hzpow : z^2 * z^(-2/3:ℝ) = z^(4/3:ℝ) := by
    rw [← Real.rpow_natCast z 2, ← Real.rpow_add hz]
    norm_num
  calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) := haux
    _ = (3/8) * (2:ℝ)^(2/3:ℝ) * z^(4/3:ℝ) + z^2/4 := by
        rw [hz2pow]
        calc (z^2/4) * ((3/2) * ((2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ)) + 1)
            = (3/8) * (2:ℝ)^(2/3:ℝ) * (z^2 * z^(-2/3:ℝ)) + z^2/4 := by ring
          _ = (3/8) * (2:ℝ)^(2/3:ℝ) * z^(4/3:ℝ) + z^2/4 := by rw [hzpow]
    _ ≤ (3/8) * 2 * z^(4/3:ℝ) + z^(4/3:ℝ)/4 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2pow2 (by norm_num)) (Real.rpow_nonneg hz.le _)
        · calc z^2/4 = z^2 * (1/4) := by ring
            _ ≤ z^(4/3:ℝ) * (1/4) := mul_le_mul_of_nonneg_right hzpow4 (by norm_num)
            _ = z^(4/3:ℝ)/4 := by ring
    _ = z^(4/3:ℝ) := by ring

/-- `J₁(z) = Γ(1/3) - 3 (z/2)^{1/3} + O(z^{4/3})` as `z → 0⁺`:
`J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = R₂(z) - R₁(z)` with
`|R₂(z)| ≤ z^{4/3}` and `|R₁(z)| ≤ (3/4) (z/2)^{4/3} ≤ (3/4) z^{4/3}` on `(0, 1]`. -/
theorem schlaefliJ1_isBigO :
    (fun z => schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ))
      =O[𝓝[>] (0:ℝ)] fun z => z^(4/3:ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨7/4, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
  have hzpos : (0:ℝ) < z := hz
  have hz1le : z ≤ 1 := hz1.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hzpos.le _)]
  rw [schlaefliJ1_decomp hzpos]
  have hR1 : |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ (3/4) * (z/2)^(4/3:ℝ) := abs_schlaefliJ1_R1_le hzpos
  have hR2 : |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ z^(4/3:ℝ) := abs_schlaefliJ1_R2_le hzpos hz1le
  have h14 : (z/2)^(4/3:ℝ) ≤ z^(4/3:ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  calc |(∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        - ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        + |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)| := abs_sub _ _
    _ ≤ z^(4/3:ℝ) + (3/4) * (z/2)^(4/3:ℝ) := add_le_add hR2 hR1
    _ ≤ z^(4/3:ℝ) + (3/4) * z^(4/3:ℝ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left h14 (show (0:ℝ) ≤ 3/4 by norm_num)) _
    _ = 7/4 * z^(4/3:ℝ) := by ring


end source7

noncomputable section source8
/- Developed by the author. -/
open Complex

open MeasureTheory Set Filter
open scoped Topology

/-!
# Abstract uniqueness for the Airy ODE on the half-line

Uniqueness for the Airy differential equation.

Proof: Grönwall (`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`) applied to
the pair `u = (W, W')`.  The work is to show, from the ODE and the slope hypothesis:
`W'(0) = 0`, right-continuity of `W'` at `0` (via `W'(a) → L` and `L = 0` by the mean
value theorem), `W'(h) = ∫₀ʰ t W(t) dt`, and the slope limit of `u` at `0`.
-/

section AiryODEUniqueness

variable {W : ℝ → ℝ /- [definition] -/ } (hW0 : W 0 = 0 /- [standing] -/ ) (hcont : ContinuousOn W (Set.Ici 0)  /- [standing] -/ )
  (hdiff : ∀ x ∈ Set.Ioi 0, DifferentiableAt ℝ W x /- [standing] -/ )
  (hW'' : ∀ x ∈ Set.Ioi 0, HasDerivAt (deriv W) (x * W x) x /- [standing] -/ )
  (hslopes : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 0) )
  {M : ℝ /- [definition] -/ } (hM : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖W t‖ ≤ M /- [standing] -/ )

include hcont hW'' in
/-- FTC on `[a, b]`, `0 < a ≤ b`: `∫ t in a..b, t W t = W'(b) − W'(a)`. -/
theorem airyODE_ftc {a b : ℝ /- [definition] -/ } (ha : 0 < a /- [standing] -/ ) (hab : a ≤ b /- [standing] -/ ) :
    ∫ t in a..b, t * W t = deriv W b - deriv W a := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (deriv W) (x * W x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hW'' x (Set.mem_Ioi.mpr (ha.trans_le hx.1))
  have hint : IntervalIntegrable (fun t => t * W t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_id.mul (hcont.mono (fun x hx => ha.le.trans hx.1))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

include hcont hM in
/-- `∫ t in a..b, t W t → ∫ t in 0..b, t W t` as `a → 0⁺` (for `0 < b ≤ 1`). -/
theorem airyODE_int_lim {b : ℝ /- [definition] -/ } (hb : 0 < b /- [standing] -/ ) (hb1 : b ≤ 1 /- [standing] -/ ) :
    Tendsto (fun a => ∫ t in a..b, t * W t) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in 0..b, t * W t)) := by
  have hint : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 →
      IntervalIntegrable (fun t => t * W t) volume c d := by
    intro c d hc hcd hd
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hcd]
    exact continuousOn_id.mul (hcont.mono (fun x hx => hc.trans hx.1))
  have hsmall : Tendsto (fun a => ∫ t in 0..a, t * W t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun a : ℝ => M * a) (Eventually.of_forall fun a => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)]
        with a ha ha1
      have hbound : ‖∫ t in 0..a, t * W t‖ ≤ M * |a - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le ha.le] at ht
        have htM : ‖W t‖ ≤ M := hM t ⟨ht.1.le, ht.2.trans ha1.le⟩
        calc ‖t * W t‖ = |t| * ‖W t‖ := by
              rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          _ ≤ 1 * M := mul_le_mul (by rw [abs_of_pos ht.1]; exact ht.2.trans ha1.le) htM
              (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      rw [sub_zero, abs_of_pos ha] at hbound
      exact hbound
    · have hM' : Tendsto (fun a : ℝ => M * a) (𝓝 (0:ℝ)) (𝓝 (M * 0)) :=
        (continuousAt_id.const_mul M).tendsto
      rw [mul_zero] at hM'
      exact hM'.mono_left nhdsWithin_le_nhds
  have hsplit : (fun a => ∫ t in a..b, t * W t) =ᶠ[𝓝[>] (0:ℝ)]
      fun a => (∫ t in 0..b, t * W t) - ∫ t in 0..a, t * W t := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)] with a ha hab2
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hint (le_refl 0) ha.le (hab2.le.trans hb1)) (hint ha.le hab2.le hb1)
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have hmain : Tendsto (fun a => (∫ t in 0..b, t * W t) - ∫ t in 0..a, t * W t)
      (𝓝[>] (0:ℝ)) (𝓝 ((∫ t in 0..b, t * W t) - 0)) := tendsto_const_nhds.sub hsmall
  rw [sub_zero] at hmain
  exact Tendsto.congr' hsplit.symm hmain

include hcont hW'' hM in
/-- `deriv W a → L := deriv W 1 − ∫₀¹ t W t` along `𝓝[>] 0`. -/
theorem airyODE_deriv_lim :
    Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 1 - ∫ t in 0..1, t * W t)) := by
  have heq : deriv W =ᶠ[𝓝[>] (0:ℝ)] fun a => deriv W 1 - ∫ t in a..1, t * W t := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with a ha ha1
    have h := airyODE_ftc hcont hW'' ha ha1.le
    rw [h]; ring
  have hlim := airyODE_int_lim hcont hM one_pos (le_refl 1)
  have hmain : Tendsto (fun a => deriv W 1 - ∫ t in a..1, t * W t) (𝓝[>] (0:ℝ))
      (𝓝 (deriv W 1 - ∫ t in 0..1, t * W t)) := tendsto_const_nhds.sub hlim
  exact Tendsto.congr' heq.symm hmain

include hcont hdiff hW'' hslopes hM in
/-- The limit `L` vanishes: `deriv W a → 0` along `𝓝[>] 0` (mean value theorem on `W`
composed with the deriv-limit). -/
theorem airyODE_deriv_lim_zero :
    Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hderWL := airyODE_deriv_lim hcont hW'' hM
  set L := deriv W 1 - ∫ t in 0..1, t * W t with hLdef
  have hMVT : ∀ h : ℝ, ∃ ξ : ℝ, 0 < h →
      (ξ ∈ Set.Ioo 0 h ∧ deriv W ξ = (W h - W 0) / (h - 0)) := by
    intro h
    by_cases hh : 0 < h
    · obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope W hh
        (hcont.mono Set.Icc_subset_Ici_self)
        (fun x hx => (hdiff x (Set.Ioo_subset_Ioi_self hx)).differentiableWithinAt)
      exact ⟨ξ, fun _ => ⟨hξmem, hξeq⟩⟩
    · exact ⟨0, fun h0 => absurd h0 hh⟩
  choose ξ hξ using hMVT
  have hξT0 : Tendsto ξ (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (g := fun h : ℝ => h)
    · filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.1.le
    · filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.2.le
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hξTI : Tendsto ξ (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hξT0, by filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.1⟩
  have hcomp : Tendsto (fun h => deriv W (ξ h)) (𝓝[>] (0:ℝ)) (𝓝 L) := hderWL.comp hξTI
  have heq : (fun h => deriv W (ξ h)) =ᶠ[𝓝[>] (0:ℝ)] fun h => (W h - W 0) / h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [(hξ h hh).2, sub_zero]
  have hcomp' : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 L) :=
    Tendsto.congr' heq hcomp
  have hL : L = 0 := tendsto_nhds_unique hcomp' hslopes
  rwa [hL] at hderWL

include hcont hdiff hW'' hslopes hM in
/-- `W'(0) = 0`. -/
theorem airyODE_deriv_zero : deriv W 0 = 0 := by
  have hderW0 := airyODE_deriv_lim_zero hcont hdiff hW'' hslopes hM
  by_cases h0d : DifferentiableAt ℝ W 0
  · have hs := h0d.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hs
    have hs' : Tendsto (slope W 0) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) := by
      apply hs.mono_left
      apply nhdsWithin_mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx
    have heq2 : slope W 0 =ᶠ[𝓝[>] (0:ℝ)] fun h => (W h - W 0) / h := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      show (h - 0)⁻¹ • (W h -ᵥ W 0) = (W h - W 0) / h
      rw [sub_zero, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
    have hs'' : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) :=
      Tendsto.congr' heq2 hs'
    exact tendsto_nhds_unique hs'' hslopes
  · exact deriv_zero_of_not_differentiableAt h0d

include hW0 hcont hdiff hW'' hslopes in
/-- **Uniqueness for the Airy equation on the half-line** (step 6): a solution `W` of
`W'' = x W` on `(0, ∞)`, continuous on `[0, ∞)`, with `W(0) = 0` and vanishing right
slope at `0`, is identically zero on `(0, ∞)`. -/
theorem airy_ode_uniqueness {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) : W x = 0 := by
  -- the uniform bound of `‖W‖` on `[0, 1]`
  have hWcont01 : ContinuousOn (fun t => ‖W t‖) (Set.Icc 0 1) :=
    (hcont.mono Set.Icc_subset_Ici_self).norm
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hWcont01
  have hM : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖W t‖ ≤ ‖W x₀‖ := by
    intro t ht
    exact Filter.eventually_principal.mp hmax t ht
  have hderW0lim := airyODE_deriv_lim_zero hcont hdiff hW'' hslopes hM
  have hdW0 : deriv W 0 = 0 := airyODE_deriv_zero hcont hdiff hW'' hslopes hM
  -- value of `deriv W` on `(0, 1]`
  have hD : ∀ h ∈ Set.Ioc (0:ℝ) 1, deriv W h = ∫ t in 0..h, t * W t := by
    intro h hh
    have h1 : Tendsto (fun a => ∫ t in a..h, t * W t) (𝓝[>] (0:ℝ))
        (𝓝 (∫ t in 0..h, t * W t)) := airyODE_int_lim hcont hM hh.1 hh.2
    have heq : (fun a => ∫ t in a..h, t * W t) =ᶠ[𝓝[>] (0:ℝ)]
        fun a => deriv W h - deriv W a := by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hh.1)] with a ha hah
      exact airyODE_ftc hcont hW'' ha hah.le
    have h2 : Tendsto (fun a => deriv W h - deriv W a) (𝓝[>] (0:ℝ))
        (𝓝 (deriv W h - 0)) := tendsto_const_nhds.sub hderW0lim
    have h1' := Tendsto.congr' heq h1
    have huniq := tendsto_nhds_unique h1' h2
    linarith [huniq]
  -- the quadratic bound on `deriv W`
  have hE : ∀ h ∈ Set.Ioc (0:ℝ) 1, ‖deriv W h‖ ≤ h^2 * ‖W x₀‖ := by
    intro h hh
    rw [hD h hh]
    have hbound : ‖∫ t in 0..h, t * W t‖ ≤ (h * ‖W x₀‖) * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hh.1.le] at ht
      have htM : ‖W t‖ ≤ ‖W x₀‖ := hM t ⟨ht.1.le, ht.2.trans hh.2⟩
      calc ‖t * W t‖ = |t| * ‖W t‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ h * ‖W x₀‖ := mul_le_mul (by rw [abs_of_pos ht.1]; exact ht.2) htM (norm_nonneg _) hh.1.le
    rw [sub_zero, abs_of_pos hh.1] at hbound
    calc ‖∫ t in 0..h, t * W t‖ ≤ h * ‖W x₀‖ * h := hbound
      _ = h^2 * ‖W x₀‖ := by ring
  -- right-continuity of `deriv W` at `0`
  have hderWcont0 : ContinuousWithinAt (deriv W) (Set.Ici 0) 0 := by
    have hIci : Set.Ici (0:ℝ) = insert 0 (Set.Ioi 0) := by
      ext x
      simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
      constructor
      · intro h; rcases h.eq_or_lt with rfl | h
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | h)
        · exact le_refl 0
        · exact h.le
    have hpure : Tendsto (deriv W) (pure (0:ℝ)) (𝓝 (deriv W 0)) := tendsto_pure_nhds _ _
    have hderW0lim' : Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) := by
      simpa only [hdW0] using hderW0lim
    show Tendsto (deriv W) (𝓝[Set.Ici 0] 0) (𝓝 (deriv W 0))
    rw [hIci, nhdsWithin_insert, tendsto_sup]
    exact ⟨hpure, hderW0lim'⟩
  -- the pair `u = (W, W')`
  set u : ℝ → ℝ × ℝ := fun x => (W x, deriv W x) with hu
  have hucont : ContinuousOn u (Set.Ici 0) := by
    apply ContinuousOn.prodMk hcont
    intro t ht
    have ht0 : 0 ≤ t := ht
    rcases ht0.eq_or_lt with rfl | htpos
    · exact hderWcont0
    · exact (hW'' t (Set.mem_Ioi.mpr htpos)).continuousAt.continuousWithinAt
  -- the slope limit of `u` at `0`
  have hstep8 : HasDerivWithinAt u (0, 0) (Set.Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : Set.Ici (0:ℝ) \ {0} = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        exact lt_of_le_of_ne h0 (Ne.symm h1)
      · intro h
        exact ⟨h.le, ne_of_gt h⟩
    rw [hset, nhds_prod_eq]
    have hslope : slope u 0 =ᶠ[𝓝[>] (0:ℝ)] fun h => (h⁻¹ * W h, h⁻¹ * deriv W h) := by
      apply Eventually.of_forall
      intro h
      show (h - 0)⁻¹ • (u h -ᵥ u 0) = _
      rw [sub_zero, vsub_eq_sub, hu]
      show h⁻¹ • ((W h, deriv W h) - (W 0, deriv W 0)) = _
      rw [hW0, hdW0, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.smul_def,
        smul_eq_mul, smul_eq_mul]
    have hcoord1 : Tendsto (fun h : ℝ => h⁻¹ * W h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have heq : (fun h : ℝ => h⁻¹ * W h) = fun h => (W h - W 0) / h := by
        funext h
        rw [hW0, sub_zero, div_eq_inv_mul]
      rw [heq]
      exact hslopes
    have hcoord2 : Tendsto (fun h : ℝ => h⁻¹ * deriv W h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero' (g := fun h : ℝ => ‖W x₀‖ * h)
        (Eventually.of_forall fun h => norm_nonneg _)
      · filter_upwards [self_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)]
          with h hh hh1
        have hb := hE h ⟨hh, hh1.le⟩
        calc ‖h⁻¹ * deriv W h‖ = h⁻¹ * ‖deriv W h‖ := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hh), Real.norm_eq_abs]
          _ ≤ h⁻¹ * (h^2 * ‖W x₀‖) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hh))
          _ = ‖W x₀‖ * h := by
              rw [pow_two, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh),
                one_mul, mul_comm]
      · have hM' : Tendsto (fun h : ℝ => ‖W x₀‖ * h) (𝓝 (0:ℝ)) (𝓝 (‖W x₀‖ * 0)) :=
          (continuousAt_id.const_mul _).tendsto
        rw [mul_zero] at hM'
        exact hM'.mono_left nhdsWithin_le_nhds
    exact Tendsto.congr' hslope.symm (hcoord1.prodMk hcoord2)
  -- the Grönwall norm bound
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) x,
      ‖(deriv W t, t * W t)‖ ≤ (1 + x) * ‖(W t, deriv W t)‖ := by
    intro t ht
    have hnn : (0:ℝ) ≤ max |W t| |deriv W t| := le_trans (abs_nonneg _) (le_max_left _ _)
    have hx1 : (1:ℝ) ≤ 1 + x := le_add_of_nonneg_right hx.le
    show max ‖deriv W t‖ ‖t * W t‖ ≤ (1 + x) * max ‖W t‖ ‖deriv W t‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
    apply max_le
    · calc |deriv W t| ≤ max |W t| |deriv W t| := le_max_right _ _
        _ ≤ (1 + x) * max |W t| |deriv W t| := le_mul_of_one_le_left hnn hx1
    · calc t * |W t| ≤ x * |W t| := mul_le_mul_of_nonneg_right ht.2.le (abs_nonneg _)
        _ ≤ (1 + x) * |W t| :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (abs_nonneg _)
        _ ≤ (1 + x) * max |W t| |deriv W t| :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (zero_le_one.trans hx1)
  have hG : ∀ t ∈ Set.Icc (0:ℝ) x, u t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f' := fun x => (deriv W x, x * W x)) (K := 1 + x)
      (hucont.mono Set.Icc_subset_Ici_self)
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      rcases ht0.eq_or_lt with rfl | htpos
      · show HasDerivWithinAt u (deriv W 0, 0 * W 0) (Set.Ici 0) 0
        rw [hdW0, zero_mul]
        exact hstep8
      · exact ((hdiff t (Set.mem_Ioi.mpr htpos)).hasDerivAt.prodMk
          (hW'' t (Set.mem_Ioi.mpr htpos))).hasDerivWithinAt
    · show u 0 = 0
      rw [hu]
      show ((W 0, deriv W 0) : ℝ × ℝ) = 0
      rw [hW0, hdW0]
      exact Prod.ext rfl rfl
    · intro t ht
      exact hbound t ht
  have hWx : (u x).1 = ((0, 0) : ℝ × ℝ).1 := congrArg Prod.fst (hG x (Set.right_mem_Icc.mpr hx.le))
  exact hWx

end AiryODEUniqueness

end source8

noncomputable section source9
/- Developed by the author. -/
open Complex

open MeasureTheory Set Filter
open scoped Topology
open Asymptotics

/-! # Matching the Airy–Bessel solution at zero

The small-argument asymptotics determine its value and slope at zero.
Gamma reflection identifies these with `π Ai(0)` and `π Ai'(0)`.
Uniqueness of the Airy equation gives the Airy–Bessel identity. -/

section AiryMatching

theorem rpow_three_inv : (3:ℝ)^(-1/3:ℝ) = ((3:ℝ)^(1/3:ℝ))⁻¹ := by
  rw [show (-1/3:ℝ) = -(1/3:ℝ) by norm_num, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]

/-- `(gx/2)^{1/3} = 3^{-1/3} · x^{1/2}` for `0 < x`, `g x = (2/3) x^{3/2}`. -/
theorem airyG_half_rpow_pos {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ) = (3:ℝ)^(-1/3:ℝ) * x^(1/2:ℝ) := by
  have hXnn : (0:ℝ) ≤ x^(3/2:ℝ) := Real.rpow_nonneg hx.le _
  have h1 : (2/3) * x^(3/2:ℝ)/2 = (3:ℝ)⁻¹ * x^(3/2:ℝ) := by ring
  rw [h1, Real.mul_rpow (inv_nonneg.mpr (by norm_num : (0:ℝ) ≤ 3)) hXnn,
    Real.inv_rpow (by norm_num : (0:ℝ) ≤ 3), ← Real.rpow_mul hx.le,
    show (3/2:ℝ) * (1/3) = 1/2 by norm_num, rpow_three_inv]

/-- `(gx/2)^{-1/3} = 3^{1/3} · x^{-1/2}` for `0 < x`. -/
theorem airyG_half_rpow_neg {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ) = (3:ℝ)^(1/3:ℝ) * x^(-1/2:ℝ) := by
  have hpos : (0:ℝ) < (2/3) * x^(3/2:ℝ)/2 := by positivity
  rw [show (-1/3:ℝ) = -(1/3:ℝ) by norm_num, Real.rpow_neg hpos.le,
    airyG_half_rpow_pos hx, mul_inv, rpow_three_inv, inv_inv,
    show x^(-1/2:ℝ) = (x^(1/2:ℝ))⁻¹ by
      rw [show (-1/2:ℝ) = -(1/2:ℝ) by norm_num, Real.rpow_neg hx.le]]

/-- `√(x/3) = 3^{-(1/2)} · x^{1/2}` for `0 < x`. -/
theorem sqrt_div_three_rpow {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    Real.sqrt (x/3) = (3:ℝ)^(-(1/2:ℝ)) * x^(1/2:ℝ) := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  rw [Real.sqrt_div hx.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, div_eq_mul_inv,
    ← Real.rpow_neg h3pos.le]
  ring

/-- `√(x/3) · (2/(gx))^{1/3} = 3^{-1/6}` for `0 < x`. -/
theorem coeffJ1 {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    Real.sqrt (x/3) * (2/((2/3) * x^(3/2:ℝ)))^(1/3:ℝ) = (3:ℝ)^(-1/6:ℝ) := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have hX : (0:ℝ) < x^(3/2:ℝ) := Real.rpow_pos_of_pos hx _
  have hx2 : (0:ℝ) < x^(1/2:ℝ) := Real.rpow_pos_of_pos hx _
  have h2z : 2/((2/3) * x^(3/2:ℝ)) = 3 * (x^(3/2:ℝ))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc, show (2:ℝ) * (2/3)⁻¹ = 3 by norm_num]
  rw [h2z, sqrt_div_three_rpow hx, Real.mul_rpow h3pos.le (inv_nonneg.mpr hX.le),
    Real.inv_rpow hX.le, ← Real.rpow_mul hx.le,
    show (3/2:ℝ) * (1/3) = 1/2 by norm_num]
  -- goal: 3^{-(1/2)} * x^{1/2} * (3^{1/3} * (x^{1/2})⁻¹) = 3^{-1/6}
  rw [show (3:ℝ)^(-1/6:ℝ) = (3:ℝ)^(-(1/2:ℝ)) * (3:ℝ)^(1/3:ℝ) by
    rw [← Real.rpow_add h3pos]; congr 1; norm_num]
  rw [show (3:ℝ)^(-(1/2:ℝ)) * x^(1/2:ℝ) * ((3:ℝ)^(1/3:ℝ) * (x^(1/2:ℝ))⁻¹)
      = ((3:ℝ)^(-(1/2:ℝ)) * (3:ℝ)^(1/3:ℝ)) * (x^(1/2:ℝ) * (x^(1/2:ℝ))⁻¹) from by ring,
    mul_inv_cancel₀ hx2.ne', mul_one]

/-- `√(x/3) · (2/(gx))^{-1/3} = 3^{-5/6} · x` for `0 < x`. -/
theorem coeffJ2 {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    Real.sqrt (x/3) * (2/((2/3) * x^(3/2:ℝ)))^(-1/3:ℝ) = (3:ℝ)^(-5/6:ℝ) * x := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have hX : (0:ℝ) < x^(3/2:ℝ) := Real.rpow_pos_of_pos hx _
  have h2z : 2/((2/3) * x^(3/2:ℝ)) = 3 * (x^(3/2:ℝ))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc, show (2:ℝ) * (2/3)⁻¹ = 3 by norm_num]
  rw [h2z, sqrt_div_three_rpow hx,
    show (-1/3:ℝ) = -(1/3:ℝ) by norm_num,
    Real.rpow_neg (mul_nonneg h3pos.le (inv_nonneg.mpr hX.le)),
    Real.mul_rpow h3pos.le (inv_nonneg.mpr hX.le),
    Real.inv_rpow hX.le, ← Real.rpow_mul hx.le,
    show (3/2:ℝ) * (1/3) = 1/2 by norm_num, mul_inv, inv_inv]
  -- goal: 3^{-(1/2)} * x^{1/2} * ((3^{1/3})⁻¹ * x^{1/2}) = 3^{-5/6} * x
  rw [show ((3:ℝ)^(1/3:ℝ))⁻¹ = (3:ℝ)^(-(1/3:ℝ)) from (Real.rpow_neg h3pos.le (1/3)).symm]
  rw [show (3:ℝ)^(-5/6:ℝ) = (3:ℝ)^(-(1/2:ℝ)) * (3:ℝ)^(-(1/3:ℝ)) by
    rw [← Real.rpow_add h3pos]; congr 1; norm_num]
  rw [show (3:ℝ)^(-(1/2:ℝ)) * x^(1/2:ℝ) * ((3:ℝ)^(-(1/3:ℝ)) * x^(1/2:ℝ))
      = ((3:ℝ)^(-(1/2:ℝ)) * (3:ℝ)^(-(1/3:ℝ))) * (x^(1/2:ℝ) * x^(1/2:ℝ)) from by ring,
    ← Real.rpow_add hx, show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one]

/-- `g x = (2/3) x^{3/2} → 0⁺` as `x → 0⁺`. -/
theorem tendsto_airyG :
    Tendsto (fun x : ℝ => (2/3) * x^(3/2:ℝ)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  have h0 : Tendsto (fun x : ℝ => (2/3) * x^(3/2:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => (2/3) * x^(3/2:ℝ)) 0 :=
      (Real.continuousAt_rpow_const 0 (3/2:ℝ) (Or.inr (by norm_num))).const_mul (2/3)
    have hv : (2/3) * (0:ℝ)^(3/2:ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0), mul_zero]
    have ht := hc.tendsto
    rw [hv] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxp : (0:ℝ) < x := hx
  exact Set.mem_Ioi.mpr (by positivity)

/-- `J₁ z → Γ(1/3)` as `z → 0⁺` (consequence of `schlaefliJ1_isBigO`). -/
theorem schlaefliJ1_tendsto :
    Tendsto schlaefliJ1 (𝓝[>] (0:ℝ)) (𝓝 (Real.Gamma (1/3))) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp schlaefliJ1_isBigO
  have hpow : Tendsto (fun z : ℝ => (z/2)^(1/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun z : ℝ => (z/2)^(1/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => t^(1/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
        have h := (Real.continuousAt_rpow_const 0 (1/3:ℝ) (Or.inr (by norm_num))).tendsto
        rwa [Real.zero_rpow (by norm_num : (1/3:ℝ) ≠ 0)] at h
      have h2 : Tendsto (fun z : ℝ => z/2) (𝓝 (0:ℝ)) (𝓝 0) := by
        have h := ((continuousAt_id (x := (0:ℝ))).div_const 2).tendsto
        simpa using h
      exact h1.comp h2
    exact hc.mono_left nhdsWithin_le_nhds
  have hC0 : Tendsto (fun z : ℝ => C * z^(4/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℝ => z^(4/3:ℝ)) 0 :=
      Real.continuousAt_rpow_const 0 (4/3:ℝ) (Or.inr (by norm_num))
    have h0 : (0:ℝ)^(4/3:ℝ) = 0 := Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0)
    have ht := (hc.const_mul C).tendsto
    rw [h0, mul_zero] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun z => schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun z => C * z^(4/3:ℝ))
      (Eventually.of_forall fun z => norm_nonneg _)
    · filter_upwards [hC, self_mem_nhdsWithin] with z hz hz0
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hz0.le _)] at hz
      exact hz
    · exact hC0
  have h2 : Tendsto (fun z => (schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ))
      - 3 * (z/2)^(1/3:ℝ) + Real.Gamma (1/3)) (𝓝[>] (0:ℝ))
      (𝓝 (0 - 3 * 0 + Real.Gamma (1/3))) :=
    (h1.sub (hpow.const_mul 3)).add tendsto_const_nhds
  have heq : (fun z => (schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ))
      - 3 * (z/2)^(1/3:ℝ) + Real.Gamma (1/3)) = schlaefliJ1 := by
    funext z; ring
  rw [heq] at h2
  simpa using h2

/-- `x · x^{-1/2} = x^{1/2}` for `0 < x`. -/
theorem mul_rpow_neg_half {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    x * x^(-1/2:ℝ) = x^(1/2:ℝ) := by
  nth_rewrite 1 [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  congr 1
  norm_num

/-- The `J₁`-`J₂` decomposition of `airyBesselY` with explicit coefficients. -/
theorem airyBesselY_eq_J12 {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    airyBesselY x = ((3:ℝ)^(-1/6:ℝ)/2) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
      + ((3:ℝ)^(-5/6:ℝ)/2) * x * schlaefliJ2 ((2/3) * x^(3/2:ℝ)) := by
  have hz : (0:ℝ) < (2/3) * x^(3/2:ℝ) := by positivity
  unfold airyBesselY
  rw [schlaefliK13_eq_J12 hz, mul_div,
    show Real.sqrt (x/3) * ((2/((2/3) * x^(3/2:ℝ)))^(1/3:ℝ) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
        + (2/((2/3) * x^(3/2:ℝ)))^(-1/3:ℝ) * schlaefliJ2 ((2/3) * x^(3/2:ℝ)))
      = (Real.sqrt (x/3) * (2/((2/3) * x^(3/2:ℝ)))^(1/3:ℝ)) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
        + (Real.sqrt (x/3) * (2/((2/3) * x^(3/2:ℝ)))^(-1/3:ℝ)) * schlaefliJ2 ((2/3) * x^(3/2:ℝ))
      from by ring,
    coeffJ1 hx, coeffJ2 hx]
  ring

/-- First matching datum: `y(x) → y₀ = Γ(1/3) 3^{-1/6}/2` as `x → 0⁺`. -/
theorem airyBesselY_tendsto_zero_right :
    Tendsto airyBesselY (𝓝[>] (0:ℝ)) (𝓝 (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2)) := by
  have hJ1 : Tendsto (fun x : ℝ => schlaefliJ1 ((2/3) * x^(3/2:ℝ))) (𝓝[>] (0:ℝ))
      (𝓝 (Real.Gamma (1/3))) := schlaefliJ1_tendsto.comp tendsto_airyG
  have hJ2sub : Tendsto (fun x : ℝ => schlaefliJ2 ((2/3) * x^(3/2:ℝ))
        - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (-3 * Real.Gamma (2/3))) := schlaefliJ2_sub_tendsto.comp tendsto_airyG
  have hxpow : ∀ x : ℝ, 0 < x → x * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ)
      = (3:ℝ)^(1/3:ℝ) * x^(1/2:ℝ) := by
    intro x hx
    rw [airyG_half_rpow_neg hx, mul_comm ((3:ℝ)^(1/3:ℝ)) (x^(-1/2:ℝ)), ← mul_assoc,
      mul_rpow_neg_half hx, mul_comm]
  -- second part `x · J₂(gx) → 0`
  have hpart2 : Tendsto (fun x : ℝ => x * schlaefliJ2 ((2/3) * x^(3/2:ℝ))) (𝓝[>] (0:ℝ))
      (𝓝 0) := by
    have heq : (fun x : ℝ => x * schlaefliJ2 ((2/3) * x^(3/2:ℝ))) =ᶠ[𝓝[>] (0:ℝ)]
        fun x => 3 * (x * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))
          + x * (schlaefliJ2 ((2/3) * x^(3/2:ℝ))
            - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      ring
    have hA : Tendsto (fun x : ℝ => 3 * (x * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ)))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have heq2 : (fun x : ℝ => 3 * (x * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))) =ᶠ[𝓝[>] (0:ℝ)]
          fun x => 3 * ((3:ℝ)^(1/3:ℝ) * x^(1/2:ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [hxpow x hx]
      have h0 : Tendsto (fun x : ℝ => (3:ℝ)^(1/3:ℝ) * x^(1/2:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hc : ContinuousAt (fun x : ℝ => x^(1/2:ℝ)) 0 :=
          Real.continuousAt_rpow_const 0 (1/2:ℝ) (Or.inr (by norm_num))
        have hv : (0:ℝ)^(1/2:ℝ) = 0 := Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0)
        have ht := (hc.const_mul ((3:ℝ)^(1/3:ℝ))).tendsto
        rw [hv, mul_zero] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      have h30 := h0.const_mul 3
      rw [mul_zero] at h30
      exact Tendsto.congr' heq2.symm h30
    have hB : Tendsto (fun x : ℝ => x * (schlaefliJ2 ((2/3) * x^(3/2:ℝ))
          - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))) (𝓝[>] (0:ℝ))
        (𝓝 (0 * (-3 * Real.Gamma (2/3)))) := by
      have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      exact hid.mul hJ2sub
    rw [zero_mul] at hB
    have hAB := hA.add hB
    rw [zero_add] at hAB
    exact Tendsto.congr' heq.symm hAB
  -- assemble
  have heq : airyBesselY =ᶠ[𝓝[>] (0:ℝ)]
      fun x => ((3:ℝ)^(-1/6:ℝ)/2) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
        + ((3:ℝ)^(-5/6:ℝ)/2) * (x * schlaefliJ2 ((2/3) * x^(3/2:ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [airyBesselY_eq_J12 hx]
    ring
  have hmain : Tendsto (fun x => ((3:ℝ)^(-1/6:ℝ)/2) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
        + ((3:ℝ)^(-5/6:ℝ)/2) * (x * schlaefliJ2 ((2/3) * x^(3/2:ℝ)))) (𝓝[>] (0:ℝ))
      (𝓝 (((3:ℝ)^(-1/6:ℝ)/2) * Real.Gamma (1/3) + ((3:ℝ)^(-5/6:ℝ)/2) * 0)) :=
    (hJ1.const_mul _).add (hpart2.const_mul _)
  rw [mul_zero, add_zero] at hmain
  have hcongr : Tendsto (fun x => ((3:ℝ)^(-1/6:ℝ)/2) * schlaefliJ1 ((2/3) * x^(3/2:ℝ))
        + ((3:ℝ)^(-5/6:ℝ)/2) * (x * schlaefliJ2 ((2/3) * x^(3/2:ℝ)))) (𝓝[>] (0:ℝ))
      (𝓝 (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2)) := by
    convert! hmain using 2
    ring
  exact Tendsto.congr' heq.symm hcongr

/-- Second matching datum: `(y(x) − y₀)/x → y₁ = −3^{1/6} Γ(2/3)/2` as `x → 0⁺`. -/
theorem airyBesselY_slope_tendsto :
    Tendsto (fun x => (airyBesselY x - Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2) / x)
      (𝓝[>] (0:ℝ)) (𝓝 (-(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2)) := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp schlaefliJ1_isBigO
  -- the three-piece decomposition
  have hdecomp : (fun x => (airyBesselY x - Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2) / x)
      =ᶠ[𝓝[>] (0:ℝ)] fun x =>
        ((3:ℝ)^(-1/6:ℝ)/2) * (schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
            + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
        + ((3:ℝ)^(-5/6:ℝ)/2) * (schlaefliJ2 ((2/3) * x^(3/2:ℝ))
            - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))
        + (((3:ℝ)^(-1/6:ℝ)/2) * (-3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
            + ((3:ℝ)^(-5/6:ℝ)/2) * (3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : (0:ℝ) < x := hx
    rw [airyBesselY_eq_J12 hx]
    field_simp [hxp.ne']
    ring
  -- piece T1 → 0 (the isBigO remainder, with `(gx)^{4/3}/x = (2/3)^{4/3} · x`)
  have hT1 : Tendsto (fun x => ((3:ℝ)^(-1/6:ℝ)/2)
        * (schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
            + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hCg : ∀ᶠ x in 𝓝[>] (0:ℝ),
        ‖schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
            + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)‖
          ≤ C * ‖((2/3) * x^(3/2:ℝ))^(4/3:ℝ)‖ := tendsto_airyG.eventually hC
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (g := fun x : ℝ => ((3:ℝ)^(-1/6:ℝ)/2) * C * ((2/3) * x^(3/2:ℝ))^(4/3:ℝ) / x)
      (Eventually.of_forall fun x => norm_nonneg _)
    · filter_upwards [hCg, self_mem_nhdsWithin] with x hx hx0
      have hxp : (0:ℝ) < x := hx0
      have hnorm : ‖((2/3) * x^(3/2:ℝ))^(4/3:ℝ)‖ = ((2/3) * x^(3/2:ℝ))^(4/3:ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      rw [hnorm] at hx
      calc ‖((3:ℝ)^(-1/6:ℝ)/2) * (schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
              + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x‖
          = ((3:ℝ)^(-1/6:ℝ)/2) * ‖schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
              + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)‖ / x := by
            rw [norm_div, norm_mul, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0:ℝ) < (3:ℝ)^(-1/6:ℝ)/2),
              Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxp]
        _ ≤ ((3:ℝ)^(-1/6:ℝ)/2) * C * ((2/3) * x^(3/2:ℝ))^(4/3:ℝ) / x := by
            have h1 : (0:ℝ) ≤ (3:ℝ)^(-1/6:ℝ)/2 := by positivity
            have h2 : (0:ℝ) ≤ x⁻¹ := inv_nonneg.mpr hxp.le
            calc ((3:ℝ)^(-1/6:ℝ)/2) * ‖schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
                    + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)‖ / x
                = ((3:ℝ)^(-1/6:ℝ)/2) * ‖schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
                    + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)‖ * x⁻¹ := by rw [div_eq_mul_inv]
              _ ≤ ((3:ℝ)^(-1/6:ℝ)/2) * (C * ((2/3) * x^(3/2:ℝ))^(4/3:ℝ)) * x⁻¹ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx h1) h2
              _ = ((3:ℝ)^(-1/6:ℝ)/2) * C * ((2/3) * x^(3/2:ℝ))^(4/3:ℝ) / x := by
                  rw [div_eq_mul_inv]; ring
    · have heq : (fun x : ℝ => ((3:ℝ)^(-1/6:ℝ)/2) * C * ((2/3) * x^(3/2:ℝ))^(4/3:ℝ) / x)
          =ᶠ[𝓝[>] (0:ℝ)] fun x => (((3:ℝ)^(-1/6:ℝ)/2) * C * (2/3)^(4/3:ℝ)) * x := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hxp : (0:ℝ) < x := hx
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2/3) (Real.rpow_nonneg hxp.le _),
          ← Real.rpow_mul hxp.le, show (3/2:ℝ) * (4/3) = 1 + 1 by norm_num,
          Real.rpow_add hxp, Real.rpow_one]
        field_simp
      have h0 : Tendsto (fun x : ℝ => (((3:ℝ)^(-1/6:ℝ)/2) * C * (2/3)^(4/3:ℝ)) * x)
          (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have ht : Tendsto (fun x : ℝ => (((3:ℝ)^(-1/6:ℝ)/2) * C * (2/3)^(4/3:ℝ)) * x)
            (𝓝 (0:ℝ)) (𝓝 ((((3:ℝ)^(-1/6:ℝ)/2) * C * (2/3)^(4/3:ℝ)) * 0)) :=
          (continuousAt_id.const_mul (((3:ℝ)^(-1/6:ℝ)/2) * C * (2/3)^(4/3:ℝ))).tendsto
        rw [mul_zero] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      exact Tendsto.congr' heq.symm h0
  -- piece T2 → y₁
  have hT2 : Tendsto (fun x => ((3:ℝ)^(-5/6:ℝ)/2) * (schlaefliJ2 ((2/3) * x^(3/2:ℝ))
        - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))) (𝓝[>] (0:ℝ))
      (𝓝 (-(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2)) := by
    have hcomp : Tendsto (fun x : ℝ => schlaefliJ2 ((2/3) * x^(3/2:ℝ))
          - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ)) (𝓝[>] (0:ℝ))
        (𝓝 (-3 * Real.Gamma (2/3))) := schlaefliJ2_sub_tendsto.comp tendsto_airyG
    have h := hcomp.const_mul ((3:ℝ)^(-5/6:ℝ)/2)
    rw [show ((3:ℝ)^(-5/6:ℝ)/2) * (-3 * Real.Gamma (2/3))
        = -(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2 by
      rw [show (3:ℝ)^(1/6:ℝ) = (3:ℝ)^(-5/6:ℝ) * (3:ℝ)^(1:ℝ) by
        rw [← Real.rpow_add h3pos]; congr 1; norm_num]
      rw [Real.rpow_one]
      ring] at h
    exact h
  -- piece T3 = 0 identically on `(0, ∞)`
  have hT3 : (fun x => (((3:ℝ)^(-1/6:ℝ)/2) * (-3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
        + ((3:ℝ)^(-5/6:ℝ)/2) * (3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))))
      =ᶠ[𝓝[>] (0:ℝ)] fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : (0:ℝ) < x := hx
    rw [airyG_half_rpow_pos hx, airyG_half_rpow_neg hx]
    have hxp12 : x^(1/2:ℝ) / x = x^(-1/2:ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx]
      congr 1
      norm_num
    have hc1 : (3:ℝ)^(-1/6:ℝ) * (3:ℝ)^(-1/3:ℝ) = (3:ℝ)^(-(1/2:ℝ)) := by
      rw [← Real.rpow_add h3pos]; congr 1; norm_num
    have hc2 : (3:ℝ)^(-5/6:ℝ) * (3:ℝ)^(1/3:ℝ) = (3:ℝ)^(-(1/2:ℝ)) := by
      rw [← Real.rpow_add h3pos]; congr 1; norm_num
    have hc3 : 3 * (3:ℝ)^(-(1/2:ℝ)) = (3:ℝ)^(1/2:ℝ) := by
      nth_rewrite 1 [show (3:ℝ) = (3:ℝ)^(1:ℝ) from (Real.rpow_one 3).symm]
      rw [← Real.rpow_add h3pos]; congr 1; norm_num
    rw [show (3:ℝ)^(-1/6:ℝ)/2 * (-3 * ((3:ℝ)^(-1/3:ℝ) * x^(1/2:ℝ))) / x
        = -((3 * ((3:ℝ)^(-1/6:ℝ) * (3:ℝ)^(-1/3:ℝ)))/2) * (x^(1/2:ℝ) / x) from by ring]
    rw [show (3:ℝ)^(-5/6:ℝ)/2 * (3 * ((3:ℝ)^(1/3:ℝ) * x^(-1/2:ℝ)))
        = ((3 * ((3:ℝ)^(-5/6:ℝ) * (3:ℝ)^(1/3:ℝ)))/2) * x^(-1/2:ℝ) from by ring]
    rw [hc1, hc2, hxp12, hc3]
    ring
  -- assemble
  have hsum : Tendsto (fun x =>
        ((3:ℝ)^(-1/6:ℝ)/2) * (schlaefliJ1 ((2/3) * x^(3/2:ℝ)) - Real.Gamma (1/3)
            + 3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
        + ((3:ℝ)^(-5/6:ℝ)/2) * (schlaefliJ2 ((2/3) * x^(3/2:ℝ))
            - 3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))
        + (((3:ℝ)^(-1/6:ℝ)/2) * (-3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
            + ((3:ℝ)^(-5/6:ℝ)/2) * (3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))))
      (𝓝[>] (0:ℝ)) (𝓝 (0 + (-(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2) + 0)) := by
    have hT3' : Tendsto (fun x =>
          (((3:ℝ)^(-1/6:ℝ)/2) * (-3 * ((2/3) * x^(3/2:ℝ)/2)^(1/3:ℝ)) / x
            + ((3:ℝ)^(-5/6:ℝ)/2) * (3 * ((2/3) * x^(3/2:ℝ)/2)^(-1/3:ℝ))))
        (𝓝[>] (0:ℝ)) (𝓝 0) := Tendsto.congr' hT3.symm tendsto_const_nhds
    exact (hT1.add hT2).add hT3'
  rw [zero_add, add_zero] at hsum
  exact Tendsto.congr' hdecomp.symm hsum

end AiryMatching



/-! ## Final assembly: the Airy–Bessel identity (DLMF 9.6.1)

`airyBesselY_eq_pi_airyAiReal`: `airyBesselY x = π · airyAiReal x` for `0 < x`, i.e.
`Ai(x) = (1/π) √(x/3) K_{1/3}((2/3) x^{3/2})` (`airyAiReal_eq_airyBesselY_div_pi`).

`W := yExt − π Ai` (with `yExt` the extension of `airyBesselY` by `y₀` at `0`)
satisfies every hypothesis of `airy_ode_uniqueness`, hence vanishes on `(0, ∞)`.
-/

section AiryIdentity

/-- `Ai`'s derivative also solves `Ai'' = x Ai` in `HasDerivAt` form. -/
theorem hasDerivAt_deriv_airyAiReal' (x : ℝ /- [definition] -/ ) :
    HasDerivAt (deriv airyAiReal) (x * airyAiReal x) x := by
  convert! hasDerivAt_deriv_airyAiReal x using 1
  have h := complex_iteratedDeriv_two_airyAi (x : ℂ)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [h, Complex.mul_re]
  simp [airyAiReal]

/-- The extension of `airyBesselY` by the limit value `y₀` at `x = 0`. -/
noncomputable def airyBesselYExt (x : ℝ /- [definition] -/ ) : ℝ :=
  if x = 0 then Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2 else airyBesselY x

theorem airyBesselYExt_eq {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    airyBesselYExt x = airyBesselY x := by
  unfold airyBesselYExt
  rw [if_neg hx.ne']

/-- The function `W := yExt − π · Ai` of the uniqueness argument. -/
noncomputable def airyIdentityW (x : ℝ /- [definition] -/ ) : ℝ :=
  airyBesselYExt x - Real.pi * airyAiReal x

theorem hW0 : airyIdentityW 0 = 0 := by
  unfold airyIdentityW airyBesselYExt
  rw [if_pos rfl, airyBesselY0_eq, sub_self]

theorem hdiff : ∀ x ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ airyIdentityW x := by
  intro x hx
  have hyExt : airyBesselYExt =ᶠ[𝓝 x] airyBesselY := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx'
    exact airyBesselYExt_eq hx'
  have h1 : DifferentiableAt ℝ airyBesselYExt x :=
    (Filter.EventuallyEq.differentiableAt_iff hyExt).mpr
      (hasDerivAt_airyBesselY hx).differentiableAt
  have h2 : DifferentiableAt ℝ (fun x => Real.pi * airyAiReal x) x :=
    (hasDerivAt_airyAiReal x).differentiableAt.const_mul _
  exact h1.sub h2

theorem hcont : ContinuousOn airyIdentityW (Set.Ici 0) := by
  have hy : ContinuousOn airyBesselYExt (Set.Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    rcases ht0.eq_or_lt with rfl | htpos
    · -- right-continuity at `0`: `yExt → y₀` from the value limit
      have hIci : Set.Ici (0:ℝ) = insert 0 (Set.Ioi 0) := by
        ext x
        simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
        constructor
        · intro h; rcases h.eq_or_lt with rfl | h
          · exact Or.inl rfl
          · exact Or.inr h
        · rintro (rfl | h)
          · exact le_refl 0
          · exact h.le
      have hpure : Tendsto airyBesselYExt (pure (0:ℝ)) (𝓝 (airyBesselYExt 0)) :=
        tendsto_pure_nhds _ _
      have hright : Tendsto airyBesselYExt (𝓝[>] (0:ℝ)) (𝓝 (airyBesselYExt 0)) := by
        have hval : airyBesselYExt 0 = Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2 := by
          unfold airyBesselYExt
          rw [if_pos rfl]
        rw [hval]
        have heq : airyBesselYExt =ᶠ[𝓝[>] (0:ℝ)] airyBesselY := by
          filter_upwards [self_mem_nhdsWithin] with x hx
          exact airyBesselYExt_eq hx
        exact Tendsto.congr' heq.symm airyBesselY_tendsto_zero_right
      show Tendsto airyBesselYExt (𝓝[Set.Ici 0] 0) (𝓝 (airyBesselYExt 0))
      rw [hIci, nhdsWithin_insert, tendsto_sup]
      exact ⟨hpure, hright⟩
    · -- at `t > 0`: locally equal to `airyBesselY`, which is differentiable there
      have hyExt : airyBesselYExt =ᶠ[𝓝 t] airyBesselY := by
        filter_upwards [Ioi_mem_nhds htpos] with x' hx'
        exact airyBesselYExt_eq hx'
      have hcat : ContinuousAt airyBesselY t :=
        (hasDerivAt_airyBesselY htpos).continuousAt
      exact ((continuousAt_congr hyExt).mpr hcat).continuousWithinAt
  have hAi : ContinuousOn (fun x => Real.pi * airyAiReal x) (Set.Ici 0) := by
    intro t ht
    exact ((hasDerivAt_airyAiReal t).continuousAt.const_mul _).continuousWithinAt
  exact hy.sub hAi

theorem hW'' : ∀ x ∈ Set.Ioi (0:ℝ),
    HasDerivAt (deriv airyIdentityW) (x * airyIdentityW x) x := by
  intro x hx
  -- `deriv yExt =ᶠ airyBesselY1` near `x`
  have hyExt : airyBesselYExt =ᶠ[𝓝 x] airyBesselY := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx'
    exact airyBesselYExt_eq hx'
  have hderY : deriv airyBesselYExt =ᶠ[𝓝 x] airyBesselY1 := by
    filter_upwards [hyExt.deriv, Ioi_mem_nhds hx] with x' h1 hx'
    rw [h1]
    exact (hasDerivAt_airyBesselY hx').deriv
  have hY1 : HasDerivAt (deriv airyBesselYExt) (x * airyBesselY x) x :=
    (hderY.hasDerivAt_iff).mpr (hasDerivAt_airyBesselY1 hx)
  -- `deriv (π · Ai) = π · Ai'`
  have hderAi : deriv (fun x => Real.pi * airyAiReal x) = fun x => Real.pi * deriv airyAiReal x :=
    funext fun x => deriv_const_mul Real.pi (hasDerivAt_airyAiReal x).differentiableAt
  have hAi : HasDerivAt (deriv (fun x => Real.pi * airyAiReal x)) (Real.pi * (x * airyAiReal x)) x := by
    rw [hderAi]
    exact (hasDerivAt_deriv_airyAiReal' x).const_mul Real.pi
  -- `deriv W =ᶠ deriv yExt − deriv (π · Ai)` near `x`
  have hderW : deriv airyIdentityW =ᶠ[𝓝 x]
      fun y => deriv airyBesselYExt y - deriv (fun x => Real.pi * airyAiReal x) y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hyExt : airyBesselYExt =ᶠ[𝓝 y] airyBesselY := by
      filter_upwards [Ioi_mem_nhds hy] with x' hx'
      exact airyBesselYExt_eq hx'
    have hd1 : DifferentiableAt ℝ airyBesselYExt y :=
      (Filter.EventuallyEq.differentiableAt_iff hyExt).mpr
        (hasDerivAt_airyBesselY hy).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun x => Real.pi * airyAiReal x) y :=
      (hasDerivAt_airyAiReal y).differentiableAt.const_mul _
    exact deriv_sub hd1 hd2
  have hsub : HasDerivAt (fun y => deriv airyBesselYExt y
        - deriv (fun x => Real.pi * airyAiReal x) y)
      (x * airyBesselY x - Real.pi * (x * airyAiReal x)) x := hY1.sub hAi
  have hmain : HasDerivAt (deriv airyIdentityW)
      (x * airyBesselY x - Real.pi * (x * airyAiReal x)) x :=
    (hderW.hasDerivAt_iff).mpr hsub
  convert! hmain using 1
  rw [airyIdentityW, airyBesselYExt_eq hx]
  ring

theorem hslopes : Tendsto (fun h => (airyIdentityW h - airyIdentityW 0) / h)
    (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hAi0 : HasDerivAt airyAiReal (deriv airyAiReal 0) 0 := by
    convert! hasDerivAt_airyAiReal 0 using 1
    exact (hasDerivAt_airyAiReal 0).deriv
  have hslopeAi : Tendsto (fun h => (airyAiReal h - airyAiReal 0) / h) (𝓝[>] (0:ℝ))
      (𝓝 (deriv airyAiReal 0)) := by
    rw [hasDerivAt_iff_tendsto_slope] at hAi0
    have hsub : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := by
      apply nhdsWithin_mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx
    have hs' := hAi0.mono_left hsub
    have heq : slope airyAiReal 0 =ᶠ[𝓝[>] (0:ℝ)] fun h => (airyAiReal h - airyAiReal 0) / h := by
      filter_upwards with h
      show (h - 0)⁻¹ • (airyAiReal h -ᵥ airyAiReal 0) = (airyAiReal h - airyAiReal 0) / h
      rw [sub_zero, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
    exact Tendsto.congr' heq hs'
  -- decompose `(W h − W 0)/h`
  have hdecomp : (fun h => (airyIdentityW h - airyIdentityW 0) / h) =ᶠ[𝓝[>] (0:ℝ)]
      fun h => (airyBesselY h - Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2) / h
        - Real.pi * ((airyAiReal h - airyAiReal 0) / h)
        + (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2 - Real.pi * airyAiReal 0) / h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hW0, sub_zero, airyIdentityW, airyBesselYExt_eq hh]
    ring
  have hconst : (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2 - Real.pi * airyAiReal 0) = 0 :=
    sub_eq_zero.mpr airyBesselY0_eq
  have h1 := airyBesselY_slope_tendsto
  have h2 : Tendsto (fun h => Real.pi * ((airyAiReal h - airyAiReal 0) / h)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.pi * deriv airyAiReal 0)) := hslopeAi.const_mul _
  have h3 : Tendsto (fun h => (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2
        - Real.pi * airyAiReal 0) / h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    rw [hconst]
    simp
  have hsum : Tendsto (fun h => (airyBesselY h - Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2) / h
        - Real.pi * ((airyAiReal h - airyAiReal 0) / h)
        + (Real.Gamma (1/3) * (3:ℝ)^(-1/6:ℝ) / 2 - Real.pi * airyAiReal 0) / h)
      (𝓝[>] (0:ℝ))
      (𝓝 ( (-(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2) - Real.pi * deriv airyAiReal 0 + 0)) :=
    (h1.sub h2).add h3
  rw [add_zero, show (-(3:ℝ)^(1/6:ℝ) * Real.Gamma (2/3) / 2)
        - Real.pi * deriv airyAiReal 0 = 0 from sub_eq_zero.mpr airyBesselY1_eq] at hsum
  exact Tendsto.congr' hdecomp.symm hsum

/-- **The Airy–Bessel identity (DLMF 9.6.1)**: `√(x/3) · K_{1/3}((2/3) x^{3/2}) = π · Ai(x)`
for `0 < x`. -/
theorem airyBesselY_eq_pi_airyAiReal {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    airyBesselY x = Real.pi * airyAiReal x := by
  have h := airy_ode_uniqueness hW0 hcont hdiff hW'' hslopes hx
  rw [airyIdentityW, airyBesselYExt_eq hx, sub_eq_zero] at h
  exact h

/-- The DLMF 9.6.1 form: `Ai(x) = (1/π) √(x/3) K_{1/3}((2/3) x^{3/2})` for `0 < x`. -/
theorem airyAiReal_eq_airyBesselY_div_pi {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) :
    airyAiReal x = airyBesselY x / Real.pi := by
  rw [airyBesselY_eq_pi_airyAiReal hx]
  field_simp [Real.pi_ne_zero]

end AiryIdentity


/-! ## Payoffs of the identity

Positivity of `airyAiReal` on `[0, ∞)` (`airyBesselY_pos`, `airyAiReal_pos`,
`airyAiReal_pos_of_nonneg`) and the Airy upper bound
`Ai(x) ≤ C x^{-1/4} e^{-(2/3) x^{3/2}}` for `x ≥ 1` (`airyAiReal_le`), by transfer
through the identity.
-/

section AiryPayoffs

/-- Positivity of the Airy–Bessel function on `(0, ∞)`. -/
theorem airyBesselY_pos {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) : 0 < airyBesselY x := by
  unfold airyBesselY
  have h1 : 0 < Real.sqrt (x/3) := Real.sqrt_pos_of_pos (by linarith)
  have h2 : 0 < schlaefliK13 ((2/3) * x^(3/2:ℝ)) := schlaefliK13_pos (by positivity)
  exact mul_pos h1 h2

/-- Positivity of the real Airy function `Ai` on `(0, ∞)`. -/
theorem airyAiReal_pos {x : ℝ /- [definition] -/ } (hx : 0 < x /- [standing] -/ ) : 0 < airyAiReal x := by
  rw [airyAiReal_eq_airyBesselY_div_pi hx]
  exact div_pos (airyBesselY_pos hx) Real.pi_pos

/-- Positivity of the real Airy function `Ai` on `[0, ∞)`. -/
theorem airyAiReal_pos_of_nonneg {x : ℝ /- [definition] -/ } (hx : 0 ≤ x /- [standing] -/ ) : 0 < airyAiReal x := by
  rcases hx.eq_or_lt with rfl | h
  · exact airyAiReal_zero_pos
  · exact airyAiReal_pos h

/-- The Airy upper bound: for `x ≥ 1`, `Ai(x) ≤ C x^{-1/4} e^{-(2/3) x^{3/2}}`
(with the explicit constant `C = 2 √π e^{1/6} · π⁻¹ · 3^{-1/2} · (2/3)^{-1/2}` of
`airyK13_schlaefli_le`, transferred through the identity). -/
theorem airyAiReal_le : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    airyAiReal x ≤ C * x^(-1/4:ℝ) * Real.exp (-(2/3 * x^(3/2:ℝ))) := by
  obtain ⟨C, hC⟩ := airyK13_schlaefli_le
  refine ⟨C, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [airyAiReal_eq_airyBesselY_div_pi hx0]
  unfold airyBesselY
  have hrewrite : Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ)) / Real.pi
      = (1/Real.pi) * Real.sqrt (x/3) * schlaefliK13 ((2/3) * x^(3/2:ℝ)) := by
    rw [div_eq_mul_inv, one_div]
    ring
  rw [hrewrite]
  exact hC x hx

end AiryPayoffs

end source9

noncomputable section source10
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

open MeasureTheory Set Filter
open scoped Topology

/-
## Main statement

* `airyAiReal_laplace_half`: `∃ C, ∀ β ≥ 1,
  ∫ u in Ioi 0, exp (2βu) * (airyAiReal u)^2 ≤ C * exp ((2/3) β³)`.

## See also
-/

/-- The exact algebraic identity `2βv² - (4/3)v³ = (2/3)β³ - (2/3)(v-β)²(β+2v)`
(pure `ring`; written in the `+ -` form to match `Real.exp_add` output). -/
theorem airyLaplace_exp_identity (v β : ℝ /- [definition] -/ ) :
    2*β*v^2 + -(4/3)*v^3 = (2/3)*β^3 + -(2/3)*(v-β)^2*(β+2*v) := by ring

/-- The weight bound: for `0 ≤ v`, `2v (1+v²)^{-1/2} ≤ 2` (i.e. `v ≤ √(1+v²)`). -/
theorem airyLaplace_weight_le {v : ℝ /- [definition] -/ } (hv : 0 ≤ v /- [standing] -/ ) :
    2 * v * (Real.sqrt (1 + v^2))⁻¹ ≤ 2 := by
  have hs : v ≤ Real.sqrt (1 + v^2) := by
    calc v = Real.sqrt (v^2) := (Real.sqrt_sq hv).symm
      _ ≤ Real.sqrt (1 + v^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg v])
  have hpos : 0 < Real.sqrt (1 + v^2) := Real.sqrt_pos_of_pos (by positivity)
  calc 2 * v * (Real.sqrt (1 + v^2))⁻¹
      ≤ 2 * Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (by positivity)
    _ = 2 := by
        rw [show 2 * Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹
            = 2 * (Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹) from by ring,
          mul_inv_cancel₀ hpos.ne', mul_one]

/-- The squared Airy bound in the `v`-variable: some `0 ≤ C₂` with
`Ai(v²)² ≤ C₂ (1+v²)^{-1/2} e^{-(4/3) v³}` for all `0 ≤ v`. The large-`v` branch squares
`airyAiReal_le` (and `(v²)^{-1/4} = v^{-1/2}`, `(v²)^{3/2} = v³`,
`v^{-1} ≤ 2 (1+v²)^{-1/2}` for `v ≥ 1`); the small-`v` branch uses the maximum of the
continuous `Ai` on the compact interval `[0, 1]`. -/
theorem airyAiReal_sq_le :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ v : ℝ, 0 ≤ v →
      (airyAiReal (v^2))^2 ≤ C₂ * (Real.sqrt (1 + v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hcont : ContinuousOn airyAiReal (Set.Icc 0 1) := fun x _ =>
    (hasDerivAt_airyAiReal x).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hMnn : (0:ℝ) ≤ (airyAiReal x₀)^2 := sq_nonneg _
  refine ⟨2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2,
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg C₁))
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le) hMnn), fun v hv => ?_⟩
  have hsq : 0 ≤ airyAiReal (v^2) := (airyAiReal_pos_of_nonneg (sq_nonneg v)).le
  by_cases hv1 : 1 ≤ v
  · -- branch `1 ≤ v`: square `airyAiReal_le`
    have hv0 : 0 < v := by linarith
    have hv2 : 1 ≤ v^2 := by nlinarith [hv1, sq_nonneg v]
    have e1 : (v^2)^(-1/4:ℝ) = v^(-1/2:ℝ) := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
      norm_num
    have e2 : (v^2)^(3/2:ℝ) = v^3 := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
      norm_num [Real.rpow_natCast]
    have h1 : airyAiReal (v^2) ≤ C₁ * v^(-1/2:ℝ) * Real.exp (-(2/3) * v^3) := by
      have hAi := hC₁ (v^2) hv2
      rwa [e1, e2, show -(2/3 * v^3) = -(2/3) * v^3 from by ring] at hAi
    have hsquare : (airyAiReal (v^2))^2
        ≤ C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := by
      have hsqle := pow_le_pow_left₀ hsq h1 2
      have h1e : (v^(-1/2:ℝ))^2 = v^(-1:ℝ) := by
        rw [← Real.rpow_natCast (v^(-1/2:ℝ)) 2, ← Real.rpow_mul hv0.le]
        norm_num
      have h2e : (Real.exp (-(2/3) * v^3))^2 = Real.exp (-(4/3) * v^3) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      calc (airyAiReal (v^2))^2 ≤ (C₁ * v^(-1/2:ℝ) * Real.exp (-(2/3) * v^3))^2 := hsqle
        _ = C₁^2 * (v^(-1/2:ℝ))^2 * (Real.exp (-(2/3) * v^3))^2 := by ring
        _ = C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := by rw [h1e, h2e]
    have hw : v^(-1:ℝ) ≤ 2 * (Real.sqrt (1 + v^2))⁻¹ := by
      have h2v : Real.sqrt (1 + v^2) ≤ 2 * v := by
        have hle : 1 + v^2 ≤ (2*v)^2 := by nlinarith [hv1, sq_nonneg v]
        calc Real.sqrt (1 + v^2) ≤ Real.sqrt ((2*v)^2) := Real.sqrt_le_sqrt hle
          _ = 2 * v := Real.sqrt_sq (by linarith)
      have hpos : (0:ℝ) < Real.sqrt (1 + v^2) := Real.sqrt_pos_of_pos (by positivity)
      calc v^(-1:ℝ) = v⁻¹ := Real.rpow_neg_one v
        _ = (Real.sqrt (1 + v^2))⁻¹ * (Real.sqrt (1 + v^2) * v⁻¹) := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
        _ ≤ (Real.sqrt (1 + v^2))⁻¹ * (2 * v * v⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h2v (by positivity)) (by positivity)
        _ = 2 * (Real.sqrt (1 + v^2))⁻¹ := by
            rw [show (2:ℝ) * v * v⁻¹ = 2 * (v * v⁻¹) from by ring,
              mul_inv_cancel₀ hv0.ne', mul_one, mul_comm]
    calc (airyAiReal (v^2))^2 ≤ C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := hsquare
      _ ≤ (2*C₁^2) * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3) := by
          have he : (2:ℝ)*C₁^2 * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3)
              = C₁^2 * (2 * (Real.sqrt (1+v^2))⁻¹) * Real.exp (-(4/3) * v^3) := by ring
          rw [he]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hw (sq_nonneg C₁)) (Real.exp_pos _).le
      _ ≤ (2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3) := by
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le) hMnn)
  · -- branch `0 ≤ v ≤ 1`: the compact-interval maximum
    have hv1' : v ≤ 1 := le_of_not_ge hv1
    have hv2mem : v^2 ∈ Set.Icc (0:ℝ) 1 := ⟨sq_nonneg v, by nlinarith [hv, hv1']⟩
    have hM : airyAiReal (v^2) ≤ airyAiReal x₀ := hmax hv2mem
    have hsqM : (airyAiReal (v^2))^2 ≤ (airyAiReal x₀)^2 := pow_le_pow_left₀ hsq hM 2
    have hfac : 1 ≤ Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹
        * Real.exp (-(4/3)*v^3) := by
      have h1 : (Real.sqrt 2)⁻¹ ≤ (Real.sqrt (1+v^2))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (Real.sqrt_pos_of_pos (by positivity : (0:ℝ) < 1 + v^2))
          (Real.sqrt_le_sqrt (by nlinarith [hv1', sq_nonneg v]))
      have h2 : Real.exp (-(4/3)) ≤ Real.exp (-(4/3)*v^3) := by
        apply Real.exp_le_exp.2
        have hv3 : v^3 ≤ 1 := by
          calc v^3 = v * v^2 := by ring
            _ ≤ 1 * v^2 := mul_le_mul_of_nonneg_right hv1' (sq_nonneg v)
            _ = v^2 := one_mul _
            _ ≤ 1 := by nlinarith [hv, hv1']
        nlinarith [hv3]
      have hfac0 : (1:ℝ)
          = Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3)) := by
        have he : Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3))
            = (Real.sqrt 2 * (Real.sqrt 2)⁻¹) * (Real.exp (4/3) * Real.exp (-(4/3))) := by
          ring
        rw [he, mul_inv_cancel₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)).ne',
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      calc (1:ℝ) = Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3)) :=
          hfac0
        _ ≤ Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
              (Real.exp_pos _).le (by positivity)
    calc (airyAiReal (v^2))^2 ≤ (airyAiReal x₀)^2 := hsqM
      _ ≤ (Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
          calc (airyAiReal x₀)^2 = (airyAiReal x₀)^2 * 1 := by rw [mul_one]
            _ ≤ (airyAiReal x₀)^2
                  * (Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹
                    * Real.exp (-(4/3)*v^3)) :=
                mul_le_mul_of_nonneg_left hfac hMnn
            _ = (Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
                  * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by ring
      _ ≤ (2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg C₁))

/-- The substitution `u = v²` for the Laplace integral:
`∫₀^∞ e^{2βu} Ai(u)² du = ∫₀^∞ 2v e^{2βv²} Ai(v²)² dv`. -/
theorem airyLaplace_sq_subst (β : ℝ /- [definition] -/ ) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      = ∫ v in Set.Ioi (0:ℝ), 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2) := by
  set f : ℝ → ℝ := fun v => v^2 with hf
  have hf' : ∀ v ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (2*v) (Set.Ioi 0) v := by
    intro v _
    have h : HasDerivAt (fun x : ℝ => x^2) (2*v) v := by
      convert! hasDerivAt_pow 2 v using 1
      norm_num [pow_one]
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    have hmono : StrictMonoOn f (Set.Ioi 0) := by
      intro a ha b hb hab
      exact pow_lt_pow_left₀ hab (le_of_lt ha) (by norm_num : (2:ℕ) ≠ 0)
    exact hmono.injOn
  have himg : f '' Set.Ioi 0 = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact pow_pos hv 2
    · intro hu
      exact ⟨Real.sqrt u, Real.sqrt_pos_of_pos hu, Real.sq_sqrt (le_of_lt hu)⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj, himg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv0 : (0:ℝ) < v := hv
  dsimp only [f]
  rw [abs_of_pos (by positivity : (0:ℝ) < 2*v), smul_eq_mul]

/-- An exponential-cubic bound for the exponentially weighted Airy-square integral over the positive ray. -/
theorem airyAiReal_laplace_half : ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β →
    ∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ C * Real.exp ((2/3)*β^3) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := airyAiReal_sq_le
  refine ⟨2 * C₂ * Real.sqrt (3 * Real.pi / 2), fun β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  rw [airyLaplace_sq_subst β]
  have hgauss : Integrable (fun v : ℝ => Real.exp (-(2/3) * (v-β)^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2/3)).comp_sub_right β
  have h3 : ∀ v : ℝ, 0 ≤ v →
      Real.exp (-(2/3)*(v-β)^2*(β+2*v)) ≤ Real.exp (-(2/3)*(v-β)^2) := by
    intro v hv
    apply Real.exp_le_exp.2
    have hX : (0:ℝ) ≤ (2/3)*(v-β)^2 := by positivity
    have h1 : (1:ℝ) ≤ β + 2*v := by linarith
    have hle : (2/3)*(v-β)^2 ≤ (2/3)*(v-β)^2*(β+2*v) := by
      calc (2/3)*(v-β)^2 = (2/3)*(v-β)^2 * 1 := by rw [mul_one]
        _ ≤ (2/3)*(v-β)^2*(β+2*v) := mul_le_mul_of_nonneg_left h1 hX
    linarith
  have h2 : ∀ v : ℝ, 0 ≤ v → 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
      ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by
    intro v hv
    calc 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
        ≤ 2*v * (Real.exp (2*β*v^2)
            * (C₂ * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hC₂ v hv) (Real.exp_pos _).le) (by linarith)
      _ = C₂ * (2*v*(Real.sqrt (1+v^2))⁻¹)
            * (Real.exp (2*β*v^2) * Real.exp (-(4/3)*v^3)) := by ring
      _ ≤ C₂ * 2 * (Real.exp (2*β*v^2) * Real.exp (-(4/3)*v^3)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (airyLaplace_weight_le hv) hC₂0) (by positivity)
      _ = 2*C₂ * Real.exp (2*β*v^2 + -(4/3)*v^3) := by
          rw [← Real.exp_add]; ring
      _ = 2*C₂ * (Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v))) := by
          rw [← Real.exp_add, airyLaplace_exp_identity v β]
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by ring
  have hdom2 : IntegrableOn (fun v => 2*C₂ * Real.exp ((2/3)*β^3)
      * Real.exp (-(2/3)*(v-β)^2*(β+2*v))) (Set.Ioi 0) := by
    apply Integrable.mono' ((hgauss.integrableOn).const_mul (2*C₂ * Real.exp ((2/3)*β^3)))
      ?_ ?_
    · exact ((by fun_prop : Continuous fun v : ℝ =>
        Real.exp (-(2/3)*(v-β)^2*(β+2*v))).const_mul _).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_
      have hnn : (0:ℝ) ≤ 2*C₂ * Real.exp ((2/3)*β^3)
          * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (h3 v (le_of_lt hv))
        (mul_nonneg (mul_nonneg (by norm_num) hC₂0) (Real.exp_pos _).le)
  have hint1 : IntegrableOn (fun v => 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2))
      (Set.Ioi 0) := by
    apply Integrable.mono' hdom2 ?_ ?_
    · have hAi0 : Continuous airyAiReal :=
        continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
      have hAi : Continuous fun v : ℝ => airyAiReal (v^2) := hAi0.comp (continuous_pow 2)
      have hcont : Continuous fun v : ℝ =>
          2*v * Real.exp (2*β*v^2) * (airyAiReal (v^2))^2 :=
        ((by fun_prop : Continuous fun v : ℝ => 2*v * Real.exp (2*β*v^2))).mul (hAi.pow 2)
      have heq : (fun v : ℝ => 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2))
          = fun v => 2*v * Real.exp (2*β*v^2) * (airyAiReal (v^2))^2 :=
        funext fun v => by ring
      rw [heq]
      exact hcont.aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_
      have hv0 : (0:ℝ) < v := hv
      have hnn : (0:ℝ) ≤ 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2) :=
        mul_nonneg (by linarith [hv0]) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact h2 v (le_of_lt hv)
  calc ∫ v in Set.Ioi 0, 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
      ≤ ∫ v in Set.Ioi 0, 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2) := by
        apply setIntegral_mono_on hint1 ((hgauss.integrableOn).const_mul _)
          measurableSet_Ioi
        intro v hv
        calc 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
            ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) :=
              h2 v (le_of_lt hv)
          _ ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2) :=
              mul_le_mul_of_nonneg_left (h3 v (le_of_lt hv))
                (mul_nonneg (mul_nonneg (by norm_num) hC₂0) (Real.exp_pos _).le)
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * ∫ v in Set.Ioi 0, Real.exp (-(2/3)*(v-β)^2) := by
          rw [integral_const_mul]
      _ ≤ 2*C₂ * Real.exp ((2/3)*β^3) * ∫ v : ℝ, Real.exp (-(2/3)*(v-β)^2) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply setIntegral_le_integral hgauss
          exact Filter.Eventually.of_forall fun v => (Real.exp_pos _).le
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * ∫ x : ℝ, Real.exp (-(2/3)*x^2) := by
          congr 1
          exact integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(2/3) * x^2)) β
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * Real.sqrt (3*Real.pi/2) := by
          congr 1
          have hval : (∫ x : ℝ, Real.exp (-(2/3) * x^2)) = Real.sqrt (3*Real.pi/2) := by
            have h := integral_gaussian (2/3)
            rwa [show (Real.pi / (2/3)) = 3*Real.pi/2 by ring] at h
          exact hval
      _ = (2 * C₂ * Real.sqrt (3*Real.pi/2)) * Real.exp ((2/3)*β^3) := by ring

end source10

noncomputable section source11
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

open MeasureTheory Set Filter
open scoped Topology

/-
Boundedness of `Ai` on `ℝ₋` by energy monotonicity, and the full Laplace bound on `ℝ`
by combining the negative half (the exponential weight is integrable against the uniform
bound) with the positive half `airyAiReal_laplace_half`.

## Main statements
-/

/-- The energy `F u = Ai(u)^2 + Ai'(u)^2 / (-u)`, whose derivative is `Ai'(u)^2 / u^2`. -/
noncomputable def airyEnergyFull (u : ℝ /- [definition] -/ ) : ℝ :=
  (airyAiReal u)^2 + (deriv airyAiReal u)^2 * (-u)⁻¹

/-- For `u < 0`, `F'(u) = (Ai'(u))^2 / u^2`: the quotient-rule term `2 Ai' Ai'' (-u)`
uses the ODE `Ai'' = u·Ai` and cancels `d/du [Ai^2] = 2 Ai Ai'`. -/
theorem hasDerivAt_airyEnergyFull (u : ℝ /- [definition] -/ ) (hu : u < 0 /- [standing] -/ ) :
    HasDerivAt airyEnergyFull ((deriv airyAiReal u)^2 / u^2) u := by
  have hu0 : u ≠ 0 := hu.ne
  have hu0' : (-u) ≠ 0 := neg_ne_zero.mpr hu0
  have hODE : deriv (deriv airyAiReal) u = u * airyAiReal u := by
    have h := iteratedDeriv_two_airyAiReal u
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  have hA : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
    rw [deriv_airyAiReal]
    exact hasDerivAt_airyAiReal u
  have hB : HasDerivAt (deriv airyAiReal) (u * airyAiReal u) u := by
    have h := hasDerivAt_deriv_airyAiReal u
    have hval : (deriv (deriv complex_airyAi) (u : ℂ)).re = u * airyAiReal u :=
      ((hasDerivAt_deriv_airyAiReal u).deriv).symm.trans hODE
    rwa [hval] at h
  have h1 : HasDerivAt (fun u : ℝ => (airyAiReal u)^2)
      (2 * airyAiReal u * deriv airyAiReal u) u := by
    have h := hA.fun_mul hA
    have e1 : (fun u : ℝ => (airyAiReal u)^2) = fun u => airyAiReal u * airyAiReal u :=
      funext fun u => pow_two _
    have e2 : 2 * airyAiReal u * deriv airyAiReal u
        = deriv airyAiReal u * airyAiReal u + airyAiReal u * deriv airyAiReal u := by
      ring
    rwa [e1, e2]
  have hg : HasDerivAt (fun u : ℝ => (deriv airyAiReal u)^2)
      (2 * u * airyAiReal u * deriv airyAiReal u) u := by
    have h := hB.fun_mul hB
    have e1 : (fun u : ℝ => (deriv airyAiReal u)^2)
        = fun u => deriv airyAiReal u * deriv airyAiReal u :=
      funext fun u => pow_two _
    have e2 : 2 * u * airyAiReal u * deriv airyAiReal u
        = (u * airyAiReal u) * deriv airyAiReal u
          + deriv airyAiReal u * (u * airyAiReal u) := by
      ring
    rwa [e1, e2]
  have hinv : HasDerivAt (fun u : ℝ => (-u)⁻¹) (1 / u^2) u := by
    have hn : HasDerivAt (fun x : ℝ => -x) (-1) u := hasDerivAt_neg' u
    have h := hn.fun_inv hu0'
    have e2 : (1:ℝ) / u^2 = -(-1) / (-u)^2 := by rw [neg_neg, neg_sq]
    rwa [e2]
  have h2 : HasDerivAt (fun u : ℝ => (deriv airyAiReal u)^2 * (-u)⁻¹)
      ((deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u) u := by
    have h := hg.fun_mul hinv
    have e2 : (deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u
        = (2 * u * airyAiReal u * deriv airyAiReal u) * (-u)⁻¹
          + (deriv airyAiReal u)^2 * (1 / u^2) := by
      field_simp
      ring
    rwa [e2]
  have h := h1.fun_add h2
  have e2 : (deriv airyAiReal u)^2 / u^2
      = 2 * airyAiReal u * deriv airyAiReal u
        + ((deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u) := by
    ring
  rwa [e2]

/-- The energy is monotone on `(-∞, -1]`: it is continuous there, differentiable on the
interior `(-∞, -1)`, and its derivative `(Ai')^2 / u^2` is nonnegative. -/
theorem airyEnergy_monotoneOn : MonotoneOn airyEnergyFull (Set.Iic (-1)) := by
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  have hAic' : Continuous (deriv airyAiReal) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_deriv_airyAiReal x).continuousAt
  have hFcont : ContinuousOn airyEnergyFull (Set.Iic (-1)) := by
    have h1c : ContinuousOn (fun u : ℝ => (airyAiReal u)^2) (Set.Iic (-1)) :=
      (hAic.pow 2).continuousOn
    have h2c : ContinuousOn (fun u : ℝ => (deriv airyAiReal u)^2 * (-u)⁻¹)
        (Set.Iic (-1)) := by
      apply ContinuousOn.mul (hAic'.pow 2).continuousOn
      apply ContinuousOn.inv₀ (continuous_id.neg).continuousOn
      intro x hx
      exact neg_ne_zero.mpr (ne_of_lt (lt_of_le_of_lt (mem_Iic.mp hx) (by norm_num)))
    exact h1c.add h2c
  have hdifF : DifferentiableOn ℝ airyEnergyFull (interior (Set.Iic (-1))) := by
    rw [interior_Iic]
    intro x hx
    exact (hasDerivAt_airyEnergyFull x
      (lt_trans (mem_Iio.mp hx) (by norm_num : (-1:ℝ) < 0))).differentiableAt
      |>.differentiableWithinAt
  have hderF : ∀ x ∈ interior (Set.Iic (-1)), 0 ≤ deriv airyEnergyFull x := by
    rw [interior_Iic]
    intro x hx
    have hx0 : x < 0 := lt_trans (mem_Iio.mp hx) (by norm_num : (-1:ℝ) < 0)
    rw [(hasDerivAt_airyEnergyFull x hx0).deriv]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact monotoneOn_of_deriv_nonneg (convex_Iic (-1)) hFcont hdifF hderF

/-- **Negative-half Airy bound**: `Ai` is uniformly bounded on `(-∞, 0]`.
For `u ≤ -1`, `(Ai u)^2 ≤ F u ≤ F (-1)` by energy monotonicity; on `[-1, 0]` the
continuous `|Ai|` attains a maximum. -/
theorem airyAiReal_abs_le_nonpos : ∃ C : ℝ, ∀ u : ℝ, u ≤ 0 → |airyAiReal u| ≤ C := by
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  have hEn : ∀ u : ℝ, u ≤ -1 → |airyAiReal u| ≤ Real.sqrt (airyEnergyFull (-1)) := by
    intro u hu
    have hu0 : u ≤ 0 := by linarith
    have hnn : 0 ≤ (deriv airyAiReal u)^2 * (-u)⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (neg_nonneg.mpr hu0))
    have hsle : (airyAiReal u)^2 ≤ airyEnergyFull u := le_add_of_nonneg_right hnn
    have hmono : airyEnergyFull u ≤ airyEnergyFull (-1) :=
      airyEnergy_monotoneOn (mem_Iic.mpr hu) (mem_Iic.mpr le_rfl) hu
    calc |airyAiReal u| = Real.sqrt ((airyAiReal u)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (airyEnergyFull u) := Real.sqrt_le_sqrt hsle
      _ ≤ Real.sqrt (airyEnergyFull (-1)) := Real.sqrt_le_sqrt hmono
  have hcontabs : ContinuousOn (fun u => |airyAiReal u|) (Set.Icc (-1) 0) :=
    hAic.abs.continuousOn
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1:ℝ) ≤ 0)) hcontabs
  refine ⟨Real.sqrt (airyEnergyFull (-1)) + |airyAiReal x₀|, fun u hu => ?_⟩
  by_cases hu1 : u ≤ -1
  · exact (hEn u hu1).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have humem : u ∈ Set.Icc (-1) 0 := ⟨le_of_not_ge hu1, hu⟩
    exact (hmax humem).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

/-- An exponential-cubic bound for the exponentially weighted Airy-square integral over the real line. -/
theorem airyAiReal_laplace : ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β →
    ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C * Real.exp ((2/3)*β^3) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  obtain ⟨Cp, hCp⟩ := airyAiReal_laplace_half
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  refine ⟨Cp + C₀^2 / 2, fun β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hgexp : Continuous fun u : ℝ => Real.exp (2*β*u) := by fun_prop
  have hgcont : Continuous (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2) :=
    hgexp.mul (hAic.pow 2)
  -- negative half: pointwise domination by `C₀^2 e^{2βu}`
  have hbound : ∀ u : ℝ, u ≤ 0 →
      Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C₀^2 * Real.exp (2*β*u) := by
    intro u hu
    have hsq : (airyAiReal u)^2 ≤ C₀^2 := by
      rw [← sq_abs (airyAiReal u)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₀ u hu) 2
    calc Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ Real.exp (2*β*u) * C₀^2 :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = C₀^2 * Real.exp (2*β*u) := by ring
  have hgIic : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Iic 0) volume := by
    apply Integrable.mono'
      ((integrableOn_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0).const_mul (C₀^2))
      hgcont.aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Iic fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hbound u (mem_Iic.mp hu)
  -- positive tail `u > 9β²`: domination by `C₁^2 e^{-(2/3)u}` via `airyAiReal_le`
  have htail : ∀ u : ℝ, u ∈ Set.Ioi (9*β^2) →
      Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C₁^2 * Real.exp (-(2/3)*u) := by
    intro u hu
    have hu9 : 9*β^2 < u := mem_Ioi.mp hu
    have hβ2 : 1 ≤ β^2 := by nlinarith [hβ]
    have hu1 : 1 ≤ u := by nlinarith [hu9, hβ2]
    have hu0 : 0 < u := by linarith [hu1]
    have hsq : (airyAiReal u)^2
        ≤ (C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))))^2 :=
      pow_le_pow_left₀ (airyAiReal_pos_of_nonneg hu0.le).le (hC₁ u hu1) 2
    have h1e : (u^(-1/4:ℝ))^2 = u^(-1/2:ℝ) := by
      rw [← Real.rpow_natCast (u^(-1/4:ℝ)) 2, ← Real.rpow_mul hu0.le]
      norm_num
    have h2e : (Real.exp (-(2/3 * u^(3/2:ℝ))))^2
        = Real.exp (-(4/3) * u^(3/2:ℝ)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hsq2 : (airyAiReal u)^2
        ≤ C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ)) := by
      calc (airyAiReal u)^2
          ≤ (C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))))^2 := hsq
        _ = C₁^2 * (u^(-1/4:ℝ))^2 * (Real.exp (-(2/3 * u^(3/2:ℝ))))^2 := by ring
        _ = C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ)) := by rw [h1e, h2e]
    have hsqrt : ((3*β)^2)^(1/2:ℝ) = 3*β := by
      rw [← Real.rpow_natCast (3*β) 2, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 3*β),
        show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, Real.rpow_one]
    have hU : (3*β)^2 ≤ u := by nlinarith [hu9]
    have h12 : 3*β ≤ u^(1/2:ℝ) := by
      rw [← hsqrt]
      exact Real.rpow_le_rpow (sq_nonneg _) hU (by norm_num : (0:ℝ) ≤ 1/2)
    have hr32 : u^(3/2:ℝ) = u * u^(1/2:ℝ) := by
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hu0, Real.rpow_one]
    have h32 : 3*β*u ≤ u^(3/2:ℝ) := by
      have h' := mul_le_mul_of_nonneg_left h12 hu0.le
      rw [hr32]
      linarith [h']
    have h1le : u ≤ 3*β*u := by
      have h' := mul_le_mul_of_nonneg_right hβ hu0.le
      nlinarith [h']
    have hfin : 2*β*u + -(4/3)*u^(3/2:ℝ) ≤ -(2/3)*u := by nlinarith [h32, h1le]
    calc Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ Real.exp (2*β*u) * (C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ))) :=
          mul_le_mul_of_nonneg_left hsq2 (Real.exp_pos _).le
      _ ≤ Real.exp (2*β*u) * (C₁^2 * 1 * Real.exp (-(4/3) * u^(3/2:ℝ))) := by
          apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num : (-1/2 : ℝ) ≤ 0))
            (sq_nonneg C₁)
      _ = C₁^2 * (Real.exp (2*β*u) * Real.exp (-(4/3) * u^(3/2:ℝ))) := by ring
      _ = C₁^2 * Real.exp (2*β*u + -(4/3) * u^(3/2:ℝ)) := by rw [← Real.exp_add]
      _ ≤ C₁^2 * Real.exp (-(2/3)*u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hfin) (sq_nonneg C₁)
  have hgIoiU : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioi (9*β^2)) volume := by
    apply Integrable.mono'
      ((integrableOn_exp_mul_Ioi (show (-(2/3):ℝ) < 0 by norm_num) (9*β^2)).const_mul
        (C₁^2))
      hgcont.aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact htail u hu
  have hgIoc : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioc 0 (9*β^2)) volume :=
    hgcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hgIoi : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioi 0) volume := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 9*β^2 by positivity)]
    exact hgIoc.union hgIoiU
  -- split `∫_ℝ` at `0`
  have hsplit : ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2
      = (∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2)
        + (∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2) := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0:ℝ)),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hgIic hgIoi]
  -- negative-half estimate
  have h1 : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) :=
    setIntegral_mono_on hgIic
      ((integrableOn_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0).const_mul (C₀^2))
      measurableSet_Iic fun u hu => hbound u (mem_Iic.mp hu)
  have hexp0 : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) = 1 / (2*β) := by
    have h := integral_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0
    rwa [mul_zero, Real.exp_zero] at h
  have h2 : ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) = C₀^2 / (2*β) := by
    rw [integral_const_mul, hexp0]
    ring
  have h3 : C₀^2 / (2*β) ≤ C₀^2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg C₀) (by norm_num : (0:ℝ) < 2)
      (by linarith : (2:ℝ) ≤ 2*β)
  have h4 : C₀^2 / 2 ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hneg : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) :=
    calc ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) := h1
      _ = C₀^2 / (2*β) := h2
      _ ≤ C₀^2 / 2 := h3
      _ ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) := h4
  calc ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2
      = (∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2)
        + (∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2) := hsplit
    _ ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) + Cp * Real.exp ((2/3)*β^3) :=
        add_le_add hneg (hCp β hβ)
    _ = (Cp + C₀^2 / 2) * Real.exp ((2/3)*β^3) := by ring

end source11

noncomputable section source12
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # Hilbert–Schmidt operators: the sum-of-squares enorm

For a continuous linear map `T : E →L[𝕜] F` between inner product spaces over an `RCLike`
field `𝕜`, and a Hilbert basis `b : HilbertBasis ι 𝕜 E` of the domain, we define the
Hilbert–Schmidt sum of squares

  `HS²(T, b) := ∑' i, ‖T (b i)‖ₑ ^ 2`,

and prove that it is **independent of the basis** (`sumSq_independent`).
This is the enorm side of the design prescribed in the review of mathlib PR #41477: the
Hilbert–Schmidt norm is defined on plain continuous linear maps (an `ℝ≥0∞`-valued enorm),
without a separate type and without a `NormedAddCommGroup` structure (which exists only in
finite dimension).

## Proof outline for basis independence

With `c` any Hilbert basis of `F`, two applications of Parseval
(`norm_sq_eq_tsum_norm_inner`, proved from
`HilbertBasis.tsum_inner_mul_inner`) plus Tonelli for the double sum of nonnegative reals
(`ENNReal.tsum_comm`) give

  `∑ᵢ ‖T bᵢ‖² = ∑ᵢ∑ⱼ |⟪cⱼ, T bᵢ⟫|² = ∑ᵢ∑ⱼ |⟪T† cⱼ, bᵢ⟫|² = ∑ⱼ ‖T† cⱼ‖²`

(`sumSq_eq_sumSq_adjoint`), and the right-hand side does not involve `b`.

## Main definitions

* `canonicalIndex`, `canonicalBasis`: a Hilbert basis of an
  arbitrary inner product space over an `RCLike` field, chosen via `Classical.choice`
  applied to `exists_hilbertBasis`.  Note that no separability hypothesis is needed on the
  pin: `exists_hilbertBasis` builds a basis indexed by a subset of the space.
* `sumSq T b`: the basis-relative sum of squares `∑' i, ‖T (b i)‖ₑ ^ 2`.
* `hsENorm T`: `(∑' i, ‖T (canonicalBasis i)‖ₑ ^ 2) ^ (1/2 : ℝ)`.
* `IsHilbertSchmidt T`: `hsENorm T ≠ ⊤`.
* `rankOne 𝕜 v a`: the rank-one operator `x ↦ ⟪v, x⟫ • a`.

## Main results

* `norm_sq_eq_tsum_norm_inner`: Parseval in norm form,
  `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²` (also in `ℝ≥0∞`: `enorm_sq_eq_tsum`).
* `sumSq_eq_sumSq_adjoint`: the adjoint flip identity.
* `sumSq_independent`, `hsENorm_eq_tsum_basis`:
  basis independence.
* `isHilbertSchmidt_rankOne`: rank-one operators are Hilbert–Schmidt.

## TODO

* `IsHilbertSchmidt ⇒ IsCompactOperator` (truncate onto finite basis subsets and estimate
  the operator norm of the tail by the tail sum of squares).
* The eventual type-synonym packaging `HilbertSchmidt 𝕜 E F` (mathlib PR #41477 design).
-/

open scoped ENNReal InnerProduct InnerProductSpace

/-- The squared enorm is `ENNReal.ofReal` of the squared norm. -/
theorem enorm_sq_eq_ofReal {G : Type* /- [definition] -/ } [NormedAddCommGroup G /- [standing] -/ ] (v : G /- [definition] -/ ) :
    ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  simp


variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ]
variable {E : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ]

/-- The inner-product summand identity behind Parseval:
`⟪x, b i⟫ * ⟪b i, x⟫ = (‖⟪b i, x⟫‖ ^ 2 : 𝕜)`. -/
theorem inner_mul_inner_eq_norm_sq {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x : E /- [definition] -/ ) (i : ι /- [definition] -/ ) :
    ⟪x, b i⟫_𝕜 * ⟪b i, x⟫_𝕜 = ((‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm x (b i), RCLike.conj_mul]
  push_cast
  ring

/-- Parseval's identity in norm form: `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`. -/
theorem norm_sq_eq_tsum_norm_inner {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x : E /- [definition] -/ ) :
    ‖x‖ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
  have hsum : Summable fun i => ((‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) :=
    (HilbertBasis.summable_inner_mul_inner b x x).congr (inner_mul_inner_eq_norm_sq b x)
  have h := HilbertBasis.tsum_inner_mul_inner b x x
  rw [tsum_congr (inner_mul_inner_eq_norm_sq b x), ← RCLike.ofReal_tsum] at h
  have h' := congrArg RCLike.re h
  rw [RCLike.ofReal_re, inner_self_eq_norm_sq] at h'
  exact h'.symm

/-- The squared norms of the inner products against a Hilbert basis are summable. -/
theorem summable_norm_inner_sq {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x : E /- [definition] -/ ) :
    Summable fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2 :=
  (RCLike.summable_ofReal 𝕜).1
    ((HilbertBasis.summable_inner_mul_inner b x x).congr (inner_mul_inner_eq_norm_sq b x))

/-- Parseval's identity in `ℝ≥0∞`: `∑' i, ‖⟪b i, x⟫‖ₑ² = ‖x‖ₑ²`. -/
theorem enorm_sq_eq_tsum {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x : E /- [definition] -/ ) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  calc ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2
      = ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_𝕜‖ ^ 2) := tsum_congr fun i => enorm_sq_eq_ofReal _
    _ = ENNReal.ofReal (∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (summable_norm_inner_sq b x)).symm
    _ = ENNReal.ofReal (‖x‖ ^ 2) := by rw [norm_sq_eq_tsum_norm_inner b x]
    _ = ‖x‖ₑ ^ 2 := (enorm_sq_eq_ofReal x).symm



variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ]
variable {E F : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ]
  [NormedAddCommGroup F /- [standing] -/ ] [InnerProductSpace 𝕜 F /- [standing] -/ ]

/-- The Hilbert–Schmidt sum of squares of `T` relative to a Hilbert basis `b` of the
domain. -/
noncomputable def sumSq {ι : Type* /- [definition] -/ } (T : E →L[𝕜] F /- [definition] -/ ) (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

/-- The flip identity: the Hilbert–Schmidt sum of squares of `T` relative to a Hilbert basis
`b` of the domain equals that of the adjoint `T†` relative to any Hilbert basis `c` of the
codomain. -/
theorem sumSq_eq_sumSq_adjoint [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] {ι ι' : Type* /- [definition] -/ }
    (T : E →L[𝕜] F /- [definition] -/ ) (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (c : HilbertBasis ι' 𝕜 F /- [definition] -/ ) :
    sumSq T b = sumSq (T†) c := by
  have hadj : ∀ (j : ι') (i : ι), ‖⟪c j, T (b i)⟫_𝕜‖ ^ 2 = ‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2 := by
    intro j i
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm ((T†) (c j)) (b i),
      RCLike.norm_conj]
  calc ∑' i, ‖T (b i)‖ₑ ^ 2
      = ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) := tsum_congr fun i => enorm_sq_eq_ofReal _
    _ = ∑' i, ENNReal.ofReal (∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun i => by rw [norm_sq_eq_tsum_norm_inner c (T (b i))]
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun i => ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          (summable_norm_inner_sq c (T (b i)))
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun j => tsum_congr fun i => by rw [hadj j i]
    _ = ∑' j, ENNReal.ofReal (∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun j => (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (summable_norm_inner_sq b ((T†) (c j)))).symm
    _ = ∑' j, ENNReal.ofReal (‖(T†) (c j)‖ ^ 2) :=
        tsum_congr fun j => by rw [← norm_sq_eq_tsum_norm_inner b ((T†) (c j))]
    _ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := tsum_congr fun j => (enorm_sq_eq_ofReal _).symm

/-- The index type of the canonical Hilbert basis of `E` (chosen via `Classical.choice`). -/
noncomputable def canonicalIndex (𝕜 : Type* /- [definition] -/ ) [RCLike 𝕜 /- [standing] -/ ] (E : Type* /- [definition] -/ ) [NormedAddCommGroup E /- [standing] -/ ]
    [InnerProductSpace 𝕜 E /- [standing] -/ ] [CompleteSpace E /- [standing] -/ ] :=
  Classical.choose (exists_hilbertBasis (𝕜 := 𝕜) (E := E))

/-- The canonical Hilbert basis of an inner product space `E` over an `RCLike` field `𝕜`. -/
noncomputable def canonicalBasis (𝕜 : Type* /- [definition] -/ ) [RCLike 𝕜 /- [standing] -/ ] (E : Type* /- [definition] -/ ) [NormedAddCommGroup E /- [standing] -/ ]
    [InnerProductSpace 𝕜 E /- [standing] -/ ] [CompleteSpace E /- [standing] -/ ] : HilbertBasis (canonicalIndex 𝕜 E) 𝕜 E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := 𝕜) (E := E)))

/-- Basis independence of the Hilbert–Schmidt sum of squares. -/
theorem sumSq_independent [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] {ι ι' : Type* /- [definition] -/ }
    (T : E →L[𝕜] F /- [definition] -/ ) (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (b' : HilbertBasis ι' 𝕜 E /- [definition] -/ ) :
    sumSq T b = sumSq T b' := by
  rw [sumSq_eq_sumSq_adjoint T b (canonicalBasis 𝕜 F),
    sumSq_eq_sumSq_adjoint T b' (canonicalBasis 𝕜 F)]

/-- The Hilbert–Schmidt enorm of a continuous linear map between Hilbert spaces: the square
root of the sum of squared norms on a Hilbert basis.  By `hsENorm_eq_tsum_basis`, any
Hilbert basis gives the same value. -/
noncomputable def hsENorm [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] (T : E →L[𝕜] F /- [definition] -/ ) : ℝ≥0∞ :=
  (sumSq T (canonicalBasis 𝕜 E)) ^ (1/2 : ℝ)

/-- The Hilbert–Schmidt enorm computed on an arbitrary Hilbert basis. -/
theorem hsENorm_eq_tsum_basis [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] {ι : Type* /- [definition] -/ }
    (T : E →L[𝕜] F /- [definition] -/ ) (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    hsENorm T = (∑' i, ‖T (b i)‖ₑ ^ 2) ^ (1/2 : ℝ) :=
  congrArg (· ^ (1/2 : ℝ)) (sumSq_independent T (canonicalBasis 𝕜 E) b)

/-- A continuous linear map between Hilbert spaces is Hilbert–Schmidt if its Hilbert–Schmidt
enorm is finite. -/
noncomputable def IsHilbertSchmidt [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] (T : E →L[𝕜] F /- [definition] -/ ) : Prop :=
  hsENorm T ≠ ⊤

/-- The rank-one continuous linear map `x ↦ ⟪v, x⟫ • a`. -/
noncomputable def rankOne (𝕜 : Type* /- [definition] -/ ) [RCLike 𝕜 /- [standing] -/ ] {E F : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ]
    [NormedAddCommGroup F /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ] [InnerProductSpace 𝕜 F /- [standing] -/ ] (v : E /- [definition] -/ ) (a : F /- [definition] -/ ) :
    E →L[𝕜] F :=
  (innerSL 𝕜 v).smulRight a

@[simp]
theorem rankOne_apply (𝕜 : Type* /- [definition] -/ ) [RCLike 𝕜 /- [standing] -/ ] {E F : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ]
    [NormedAddCommGroup F /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ] [InnerProductSpace 𝕜 F /- [standing] -/ ] (v : E /- [definition] -/ ) (a : F /- [definition] -/ )
    (x : E /- [definition] -/ ) :
    rankOne 𝕜 v a x = ⟪v, x⟫_𝕜 • a := rfl

/-- The Hilbert–Schmidt sum of squares of the rank-one operator `x ↦ ⟪v, x⟫ • a` is
`‖v‖ₑ² * ‖a‖ₑ²`. -/
theorem sumSq_rankOne {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (v : E /- [definition] -/ ) (a : F /- [definition] -/ ) :
    sumSq (rankOne 𝕜 v a) b = ‖v‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := by
  calc ∑' i, ‖rankOne 𝕜 v a (b i)‖ₑ ^ 2
      = ∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := tsum_congr fun i => by
        rw [rankOne_apply, enorm_smul, mul_pow, ← inner_conj_symm v (b i), RCLike.enorm_conj]
    _ = (∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2) * ‖a‖ₑ ^ 2 := ENNReal.tsum_mul_right
    _ = ‖v‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := by rw [enorm_sq_eq_tsum b v]

/-- Rank-one operators are Hilbert–Schmidt. -/
theorem isHilbertSchmidt_rankOne [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] (v : E /- [definition] -/ ) (a : F /- [definition] -/ ) :
    IsHilbertSchmidt (rankOne 𝕜 v a) := by
  unfold IsHilbertSchmidt hsENorm
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  rw [sumSq_rankOne]
  refine ENNReal.mul_ne_top ?_ ?_
  · rw [enorm_sq_eq_ofReal v]
    exact ENNReal.ofReal_ne_top
  · rw [enorm_sq_eq_ofReal a]
    exact ENNReal.ofReal_ne_top


end source12

noncomputable section source13
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # Kernel operators on `L²` are Hilbert–Schmidt

For a scalar kernel `K : X × X → 𝕜` (with `𝕜` an `RCLike` field) which is square-integrable
for the product measure (`MemLp K 2 (μ.prod μ)`), the integral operator

  `T_K f x = ∫ y, K (x, y) * f y ∂μ`,     `kernelOperator hK : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ`,

is Hilbert–Schmidt, and its Hilbert–Schmidt sum of squares equals the squared `L²`-norm of
the kernel.

## Main results

* `eLpNorm_kernelOperator_le`: the `L²`-to-`L²` bound
  `eLpNorm (T_K f) ≤ eLpNorm K * eLpNorm f` (Cauchy–Schwarz/Hölder on each slice).
* `sumSq_kernelOperator_le`: the general bound
  `sumSq (T_K) b ≤ (eLpNorm K 2 (μ.prod μ))²` for *every* Hilbert basis `b` of `L²(μ)`
  (no countability assumptions), hence `IsHilbertSchmidt (T_K)` and
  `hsENorm (T_K) ≤ eLpNorm K 2 (μ.prod μ)`; also the operator norm bound
  `enorm_kernelOperator_le`.
* `sumSq_kernelOperator_eq`: the norm **equality** for a *countable* Hilbert
  basis of `L²(μ)`, via Parseval inside the integral and Tonelli;
  `hsENorm_kernelOperator`: `hsENorm (T_K) = eLpNorm K 2 (μ.prod μ)`.

## Proof notes

The operator is defined pointwise and packaged with `LinearMap.mkContinuous`. The
sum-of-squares computation goes through the slices `K (x, ·)`: for a.e. `x` the slice is in
`L²(μ)` (Tonelli + `ae_lt_top'`), and `T_K f x = ⟪slice_x, f⟫_𝕜` a.e., so
`‖T_K bᵢ‖² = ∫ ‖⟪slice_x, bᵢ⟫_𝕜‖² dx`; the sum over `i` then uses Bessel's inequality (for
`≤`) or Parseval (for `=`, where the `∑ᵢ`-`∫` swap is `lintegral_tsum`, which requires
countability — a non-separable generalization would need monotone convergence over a
non-countable directed set, which is false in general measure spaces).

## TODO

* The bilinear-form evaluation `⟪T_K f, g⟫_𝕜 = ∫ p, conj (K p) * conj (f p.2) * g p.1`
  (the PR-42003 `mercerForm` pattern) for trace computations.
-/

open MeasureTheory Filter Complex
open scoped ENNReal InnerProduct InnerProductSpace
open scoped Classical


/-- For an a.e.-strongly-measurable `f`, `(eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`. -/
theorem eLpNorm_two_sq_eq_lintegral {α E : Type* /- [definition] -/ } [MeasurableSpace α /- [standing] -/ ] [NormedAddCommGroup E /- [standing] -/ ]
    {μ : Measure α /- [definition] -/ } {f : α → E /- [definition] -/ } (hf : AEStronglyMeasurable f μ /- [standing] -/ ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  simp_rw [show ∀ x : α, ‖f x‖ₑ ^ (2:ℝ) = ‖f x‖ₑ ^ 2 from fun x => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]]
  rw [← ENNReal.rpow_natCast _ (2 : ℕ), show ((2 : ℕ) : ℝ) = 2 by norm_num,
    ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]



variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ] [BorelSpace 𝕜 /- [standing] -/ ]
variable {X : Type* /- [definition] -/ } [MeasurableSpace X /- [standing] -/ ] {μ : Measure X /- [definition] -/ } [SFinite μ /- [standing] -/ ]

/-- `X ^ (2 : ℝ) = X ^ 2` for `X : ℝ≥0∞`. -/
theorem enorm_rpow_two (X : ℝ≥0∞ /- [definition] -/ ) : X ^ (2 : ℝ) = X ^ 2 := by
  rw [← ENNReal.rpow_natCast]
  norm_num

/-- `(X ^ (1/2 : ℝ)) ^ 2 = X` for `X : ℝ≥0∞`. -/
theorem rpow_half_sq (X : ℝ≥0∞ /- [definition] -/ ) : (X ^ (1/2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, ← ENNReal.rpow_mul,
    show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- `(X ^ 2) ^ (1/2 : ℝ) = X` for `X : ℝ≥0∞`. -/
theorem rpow_half_sq' (X : ℝ≥0∞ /- [definition] -/ ) : (X ^ 2) ^ (1/2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the slice `K (x, ·)` of a product-`L²` kernel is a.e.-strongly-measurable
with finite second moment. -/
theorem slice_measurable_finite_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) μ
      ∧ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) < ⊤ := by
  have hmeas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) μ :=
    AEStronglyMeasurable.prodMk_left hK.aestronglyMeasurable
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  have hfin : ∀ᵐ x ∂μ, (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) < ⊤ := by
    apply ae_lt_top' hKnorm.lintegral_prod_right'
    rw [(MeasureTheory.lintegral_prod _ hKnorm).symm,
      ← eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable, pow_two]
    exact ENNReal.mul_ne_top hK.eLpNorm_ne_top hK.eLpNorm_ne_top
  filter_upwards [hmeas, hfin] with x h1 h2
  exact ⟨h1, h2⟩

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the conjugated slice `star ∘ K (x, ·)` is in `L²(μ)`. -/
theorem memLp_conj_slice_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    ∀ᵐ x ∂μ, MemLp (fun y => star (K (x, y))) 2 μ := by
  filter_upwards [slice_measurable_finite_ae hK] with x hx
  have hstar := continuous_star.comp_aestronglyMeasurable hx.1
  have hnorm : eLpNorm (fun y => star (K (x, y))) 2 μ = eLpNorm (fun y => K (x, y)) 2 μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hstar,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hx.1]
    congr 1
    apply lintegral_congr
    intro y
    simp
  change eLpNorm (fun y => star (K (x, y))) 2 μ < ⊤
  rw [hnorm]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hx.1).2 ?_
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  simp_rw [enorm_rpow_two]
  exact hx.2

/-- The conjugated slice of the kernel at `x`, as an element of `Lp 𝕜 2 μ`
(junk value `0` when the slice is not in `L²`). -/
noncomputable def sliceLp (μ : Measure X /- [definition] -/ ) (K : X × X → 𝕜 /- [definition] -/ ) (x : X /- [definition] -/ ) : Lp 𝕜 2 μ :=
  if h : MemLp (fun y => star (K (x, y))) 2 μ then MemLp.toLp (fun y => star (K (x, y))) h else 0

omit [BorelSpace 𝕜] [SFinite μ] in
/-- The slice at `x` is the `toLp` of the conjugated slice of `K` when that is in `L²`. -/
theorem sliceLp_eq_toLp {K : X × X → 𝕜 /- [definition] -/ } {x : X /- [definition] -/ }
    (hx : MemLp (fun y => star (K (x, y))) 2 μ /- [standing] -/ ) :
    sliceLp μ K x = MemLp.toLp (fun y => star (K (x, y))) hx := by
  unfold sliceLp
  exact dif_pos hx

omit [BorelSpace 𝕜] [SFinite μ] in
/-- The slice as a function is a.e. the conjugated slice of `K` at `x` when that is in
`L²`. -/
theorem sliceLp_apply_ae {K : X × X → 𝕜 /- [definition] -/ } {x : X /- [definition] -/ }
    (hx : MemLp (fun y => star (K (x, y))) 2 μ /- [standing] -/ ) :
    ∀ᵐ y ∂μ, (sliceLp μ K x) y = star (K (x, y)) := by
  rw [sliceLp_eq_toLp hx]
  exact MemLp.coeFn_toLp hx

omit [BorelSpace 𝕜] in
/-- The `L²`-norm of the slice: `‖sliceLp μ K x‖ₑ ^ 2 = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2` for a.e. `x`. -/
theorem enorm_sliceLp_sq {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    ∀ᵐ x ∂μ, ‖sliceLp μ K x‖ₑ ^ 2 = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  have h0 : ‖sliceLp μ K x‖ₑ ^ 2 = (eLpNorm (sliceLp μ K x) 2 μ) ^ 2 := by rw [Lp.enorm_def]
  rw [h0, eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
  apply lintegral_congr_ae
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [hy]
  simp

/-- The pointwise kernel integral `x ↦ ∫ y, K (x, y) * f y ∂μ`. -/
noncomputable def kernelIntegralFun (K : X × X → 𝕜 /- [definition] -/ ) (f : Lp 𝕜 2 μ /- [definition] -/ ) : X → 𝕜 :=
  fun x => ∫ y, K (x, y) * f y ∂μ

omit [BorelSpace 𝕜] in
/-- The pointwise kernel integral is a.e.-strongly-measurable. -/
theorem kernelIntegralFun_aestronglyMeasurable {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    AEStronglyMeasurable (kernelIntegralFun K f) μ :=
  (hK.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).comp_snd)).integral_prod_right'

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the integrand `K (x, ·) * f` of the kernel integral is integrable. -/
theorem integrable_kernelFun_slice_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) μ := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  have h := MeasureTheory.L2.integrable_inner (𝕜 := 𝕜) (sliceLp μ K x) f
  apply h.congr
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [RCLike.inner_apply', hy]
  simp

omit [BorelSpace 𝕜] in
/-- Pointwise bound for the kernel integral:
`‖T f x‖ₑ ^ 2 ≤ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2) * (eLpNorm f 2 μ) ^ 2` for a.e. `x`. -/
theorem kernelIntegralFun_enorm_sq_le {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    ∀ᵐ x ∂μ, ‖kernelIntegralFun K f x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
  filter_upwards [slice_measurable_finite_ae hK] with x hx
  have hnorm : AEMeasurable (fun y => ‖K (x, y)‖ₑ) μ := hx.1.enorm
  have hnormf : AEMeasurable (fun y => ‖f y‖ₑ) μ := (Lp.aestronglyMeasurable f).enorm
  have hstep : ‖kernelIntegralFun K f x‖ₑ ≤ ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ :=
    (enorm_integral_le_lintegral_enorm _).trans_eq
      (lintegral_congr fun y => enorm_mul _ _)
  have hholder : ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ
      ≤ (∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hnorm hnormf
  calc ‖kernelIntegralFun K f x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]
    _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        congr 1 <;> · apply lintegral_congr; intro y; rw [enorm_rpow_two]
    _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
        rw [eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable f)]

omit [BorelSpace 𝕜] in
/-- The `L²`-bound for the kernel integral:
`eLpNorm (T f) ≤ eLpNorm K * eLpNorm f`. -/
theorem eLpNorm_kernelIntegral_le {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    eLpNorm (kernelIntegralFun K f) 2 μ ≤ eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ := by
  have hmeas := kernelIntegralFun_aestronglyMeasurable hK f
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ) (μ.prod μ) := hK.aestronglyMeasurable.enorm
  have hmain : (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ)
      ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2) ^ (1/2 : ℝ) := by
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    calc (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ)
        ≤ ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [kernelIntegralFun_enorm_sq_le hK f] with x hx
          rwa [enorm_rpow_two]
      _ = (∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
          rw [lintegral_mul_const'' _ ((hKnorm.pow_const (2:ℕ)).lintegral_prod_right')]
      _ = (∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ)) * (eLpNorm f 2 μ) ^ 2 := by
          rw [MeasureTheory.lintegral_prod _ ((hKnorm.pow_const (2:ℕ)))]
      _ = (eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2 := by
          rw [eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  calc eLpNorm (kernelIntegralFun K f) 2 μ
      = (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) :=
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas
    _ ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2) ^ (1/2 : ℝ) := hmain
    _ = (eLpNorm K 2 (μ.prod μ)) * (eLpNorm f 2 μ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), rpow_half_sq',
          rpow_half_sq']

omit [BorelSpace 𝕜] in
/-- The pointwise kernel integral is in `L²(μ)`. -/
theorem memLp_kernelIntegral {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    MemLp (kernelIntegralFun K f) 2 μ := by
  exact (eLpNorm_kernelIntegral_le hK f).trans_lt
    (ENNReal.mul_lt_top hK.eLpNorm_lt_top (Lp.eLpNorm_lt_top f))

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the pointwise kernel integral equals the inner product against the slice. -/
theorem kernelIntegralFun_eq_inner_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    ∀ᵐ x ∂μ, kernelIntegralFun K f x = ⟪sliceLp μ K x, f⟫_𝕜 := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [RCLike.inner_apply', hy]
  simp

omit [BorelSpace 𝕜] in
/-- The kernel integral is additive in `f` (a.e.). -/
theorem kernelIntegralFun_add_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f g : Lp 𝕜 2 μ /- [definition] -/ ) :
    (fun x => ∫ y, K (x, y) * (f + g) y ∂μ) =ᵐ[μ]
      fun x => (∫ y, K (x, y) * f y ∂μ) + (∫ y, K (x, y) * g y ∂μ) := by
  filter_upwards [integrable_kernelFun_slice_ae hK f, integrable_kernelFun_slice_ae hK g]
    with x hxf hxg
  have h : (∫ y, K (x, y) * (f + g) y ∂μ) = ∫ y, K (x, y) * f y + K (x, y) * g y ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply]
    ring
  rw [h, integral_add hxf hxg]

omit [BorelSpace 𝕜] in
/-- The kernel integral is homogeneous in `f` (a.e.). -/
theorem kernelIntegralFun_smul_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) (c : 𝕜 /- [definition] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    (fun x => ∫ y, K (x, y) * (c • f) y ∂μ) =ᵐ[μ] fun x => c * (∫ y, K (x, y) * f y ∂μ) := by
  filter_upwards [integrable_kernelFun_slice_ae hK f] with x hxf
  have h : (∫ y, K (x, y) * (c • f) y ∂μ) = ∫ y, c * (K (x, y) * f y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, MeasureTheory.integral_const_mul]

/-- The kernel integral operator as a continuous linear map on `L²(μ)`. -/
noncomputable def kernelOperator {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => MemLp.toLp _ (memLp_kernelIntegral hK f)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_kernelIntegral hK (f + g)),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK f),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK g),
          Lp.coeFn_add (MemLp.toLp _ (memLp_kernelIntegral hK f))
            (MemLp.toLp _ (memLp_kernelIntegral hK g)),
          kernelIntegralFun_add_ae hK f g] with x hfg hf' hg' hadd hsplit
        rw [hfg, hadd, Pi.add_apply, hf', hg']
        exact hsplit
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_kernelIntegral hK (c • f)),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK f),
          Lp.coeFn_smul c (MemLp.toLp _ (memLp_kernelIntegral hK f)),
          kernelIntegralFun_smul_ae hK c f] with x hcf hf' hsmul hsplit
        rw [hcf, RingHom.id_apply, hsmul, Pi.smul_apply, hf', smul_eq_mul]
        exact hsplit }
    ((eLpNorm K 2 (μ.prod μ)).toReal)
    (fun f => by
      have hb := eLpNorm_kernelIntegral_le hK f
      have hfin : eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ ≠ ⊤ :=
        ENNReal.mul_ne_top hK.eLpNorm_ne_top (Lp.eLpNorm_ne_top f)
      calc ‖MemLp.toLp _ (memLp_kernelIntegral hK f)‖
          = (eLpNorm (kernelIntegralFun K f) 2 μ).toReal := by
            rw [Lp.norm_def]
            congr 1
            exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)
        _ ≤ (eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ).toReal :=
            ENNReal.toReal_mono hfin hb
        _ = (eLpNorm K 2 (μ.prod μ)).toReal * (eLpNorm f 2 μ).toReal := ENNReal.toReal_mul
        _ = (eLpNorm K 2 (μ.prod μ)).toReal * ‖f‖ := by rw [Lp.norm_def])

omit [BorelSpace 𝕜] in
/-- The operator applied to `f` is a.e. the pointwise kernel integral. -/
theorem kernelOperator_apply_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    ∀ᵐ x ∂μ, (kernelOperator hK f) x = kernelIntegralFun K f x := by
  have h : kernelOperator hK f = MemLp.toLp _ (memLp_kernelIntegral hK f) := rfl
  rw [h]
  exact MemLp.coeFn_toLp _

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, `(T_K f) x = ⟪sliceLp μ K x, f⟫_𝕜`. -/
theorem kernelOperator_eval_inner_ae {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ )
    (f : Lp 𝕜 2 μ /- [definition] -/ ) :
    ∀ᵐ x ∂μ, (kernelOperator hK f) x = ⟪sliceLp μ K x, f⟫_𝕜 := by
  filter_upwards [kernelOperator_apply_ae hK f, kernelIntegralFun_eq_inner_ae hK f]
    with x h1 h2
  rw [h1, h2]

omit [BorelSpace 𝕜] in
/-- The operator norm of the kernel operator is bounded by the `L²`-norm of the kernel. -/
theorem enorm_kernelOperator_le {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    ‖kernelOperator hK‖ₑ ≤ eLpNorm K 2 (μ.prod μ) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro f
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (kernelOperator_apply_ae hK f)]
  exact eLpNorm_kernelIntegral_le hK f

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt sum of squares of the kernel operator is bounded by the squared
`L²`-norm of the kernel.  No countability assumption is needed: finite partial sums are
estimated by Bessel's inequality pointwise in `x`, and the bound is closed by Tonelli. -/
theorem sumSq_kernelOperator_le {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)  /- [definition] -/ ) :
    sumSq (kernelOperator hK) b ≤ (eLpNorm K 2 (μ.prod μ)) ^ 2 := by
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  rw [show (eLpNorm K 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) from
    eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  unfold sumSq
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  calc ∑ i ∈ s, ‖kernelOperator hK (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ x, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Lp.enorm_def, eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
    _ = ∫⁻ x, ∑ i ∈ s, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ := by
        rw [lintegral_finsetSum' s (fun i _ =>
          ((Lp.aestronglyMeasurable _).enorm).pow_const (2 : ℕ))]
    _ ≤ ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ := by
        apply lintegral_mono_ae
        have hb : ∀ i, i ∈ s → ∀ᵐ x ∂μ, (kernelOperator hK (b i)) x = ⟪sliceLp μ K x, b i⟫_𝕜 :=
          fun i _ => kernelOperator_eval_inner_ae hK (b i)
        filter_upwards [ae_ball_iff (Finset.countable_toSet s) |>.2 hb, enorm_sliceLp_sq hK]
          with x hx hxn
        calc ∑ i ∈ s, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2
            = ∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hx i hi, ← inner_conj_symm (sliceLp μ K x) (b i), RCLike.enorm_conj]
          _ ≤ ‖sliceLp μ K x‖ₑ ^ 2 := by
              rw [show (∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2)
                  = ENNReal.ofReal (∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ ^ 2) from
                (Finset.sum_congr rfl fun i _ => enorm_sq_eq_ofReal _).trans
                  (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm,
                enorm_sq_eq_ofReal (sliceLp μ K x)]
              apply ENNReal.ofReal_le_ofReal
              exact (HilbertBasis.orthonormal b).sum_inner_products_le _
          _ = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ := hxn
    _ = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) := (MeasureTheory.lintegral_prod _ hKnorm).symm

omit [BorelSpace 𝕜] in
/-- The kernel operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_kernelOperator {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    IsHilbertSchmidt (kernelOperator hK) := by
  unfold IsHilbertSchmidt hsENorm
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  refine ne_of_lt ((sumSq_kernelOperator_le hK (canonicalBasis 𝕜 (Lp 𝕜 2 μ))).trans_lt ?_)
  exact ENNReal.pow_lt_top hK.eLpNorm_lt_top

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt enorm of the kernel operator is bounded by the `L²`-norm of the
kernel. -/
theorem hsENorm_kernelOperator_le {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) :
    hsENorm (kernelOperator hK) ≤ eLpNorm K 2 (μ.prod μ) := by
  unfold hsENorm
  calc (sumSq (kernelOperator hK) (canonicalBasis 𝕜 (Lp 𝕜 2 μ))) ^ (1/2 : ℝ)
      ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_kernelOperator_le hK _) (by norm_num)
    _ = eLpNorm K 2 (μ.prod μ) := rpow_half_sq' _

omit [BorelSpace 𝕜] in
/-- The headline equality: on a *countable* Hilbert basis of `L²(μ)`, the Hilbert–Schmidt sum
of squares of the kernel operator equals the squared `L²`-norm of the kernel. -/
theorem sumSq_kernelOperator_eq {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    [Countable ι /- [standing] -/ ] (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)  /- [definition] -/ ) :
    sumSq (kernelOperator hK) b = (eLpNorm K 2 (μ.prod μ)) ^ 2 := by
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  rw [show (eLpNorm K 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) from
    eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  calc sumSq (kernelOperator hK) b
      = ∑' i, ∫⁻ x, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ :=
        tsum_congr fun i => by
          rw [Lp.enorm_def, eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
    _ = ∑' i, ∫⁻ x, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2 ∂μ :=
        tsum_congr fun i =>
          lintegral_congr_ae ((kernelOperator_eval_inner_ae hK (b i)).mono fun x hx => by
            dsimp only
            rw [hx])
    _ = ∫⁻ x, ∑' i, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2 ∂μ := by
        symm
        apply lintegral_tsum
        intro i
        exact (((Lp.aestronglyMeasurable _).enorm).pow_const (2 : ℕ)).congr
          ((kernelOperator_eval_inner_ae hK (b i)).mono fun x hx => by
            dsimp only
            rw [hx])
    _ = ∫⁻ x, ‖sliceLp μ K x‖ₑ ^ 2 ∂μ := by
        apply lintegral_congr
        intro x
        rw [show (∑' i, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2)
            = ∑' i, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2 from
          tsum_congr fun i => by
            rw [← inner_conj_symm (sliceLp μ K x) (b i), RCLike.enorm_conj]]
        exact enorm_sq_eq_tsum b (sliceLp μ K x)
    _ = ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ := lintegral_congr_ae (enorm_sliceLp_sq hK)
    _ = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) := (MeasureTheory.lintegral_prod _ hKnorm).symm

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt enorm of the kernel operator equals the `L²`-norm of the kernel
(on a countable Hilbert basis). -/
theorem hsENorm_kernelOperator {K : X × X → 𝕜 /- [definition] -/ } (hK : MemLp K 2 (μ.prod μ)  /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    [Countable ι /- [standing] -/ ] (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)  /- [definition] -/ ) :
    hsENorm (kernelOperator hK) = eLpNorm K 2 (μ.prod μ) := by
  rw [hsENorm_eq_tsum_basis (kernelOperator hK) b]
  show (sumSq (kernelOperator hK) b) ^ (1/2 : ℝ) = eLpNorm K 2 (μ.prod μ)
  rw [sumSq_kernelOperator_eq hK b, rpow_half_sq']


end source13

noncomputable section source14
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # Trace-class operators via Hilbert–Schmidt factorization

Using the basis-independent Hilbert–Schmidt enorm `sumSq` / `hsENorm`,
this section defines trace-class operators on a Hilbert space `E` over an
`RCLike` field `𝕜`.

## Main definitions

* `IsTraceClass T`: `T : E →L[𝕜] E` factors as `T = A ∘L B` with `A`, `B`
  Hilbert–Schmidt.  (On Hilbert spaces this is equivalent to the singular-value definition
  `∑' n, sₙ(T) < ⊤`; the factorization form is what the Fredholm-determinant layer needs.)
* `trace T`: the sum of the diagonal matrix elements `⟪bᵢ, T bᵢ⟫` in the
  canonical Hilbert basis (junk value from `tsum` when the series is not summable).
* `basisTruncation T b s`: the finite-rank truncation
  `x ↦ ∑ i ∈ s, ⟪b i, x⟫ • T (b i)` of `T` onto the basis vectors indexed by `s : Finset ι`.

## Main results

* `sumSq_comp_le`, `sumSq_comp_le_right`: composition with a
  bounded operator on either side multiplies the sum of squares by at most the squared
  operator enorm — the Hilbert–Schmidt class is a two-sided ideal
  (`IsHilbertSchmidt.comp_left`, `IsHilbertSchmidt.comp_right`).
* `enorm_sq_apply_le_sumSq_mul`, `opENorm_le_sumSq_rpow_half`:
  the operator enorm is bounded by the Hilbert–Schmidt enorm.
* `IsHilbertSchmidt.isCompactOperator`: Hilbert–Schmidt operators are
  compact, by finite-rank truncation with the tail vanishing
  (`ENNReal.tendsto_tsum_compl_atTop_zero`) and `isCompactOperator_of_tendsto`.
* `summable_norm_inner_diagonal`: the diagonal series of a trace-class
  operator is absolutely summable (via AM–GM, no separability hypothesis).
* `tsum_inner_comp_eq`: the trace-swap engine
  `∑' i, ⟪b i, A (B (b i))⟫ = ∑' j, ⟪c j, B (A (c j))⟫` (Parseval + an absolutely
  convergent interchange).
* `trace_eq_tsum_inner`: basis independence of the trace on trace-class
  operators; `trace_comp_comm`: `trace (A ∘L B) = trace (B ∘L A)`.
* `IsTraceClass.isHilbertSchmidt`: trace class implies Hilbert–Schmidt.
  (The converse is false in infinite dimension: the identity on `ℓ²` is not Hilbert–Schmidt,
  and e.g. the diagonal operator `(1/n)` on `ℓ²(ℕ)` is Hilbert–Schmidt but not trace class.)

## TODO

* The 2-regularized Fredholm determinant `det₂(1 - K)` for Hilbert–Schmidt `K`,
  and its evaluation on the Airy-kernel operator.
-/

open Filter
open scoped Topology ENNReal InnerProduct InnerProductSpace
open scoped Classical


variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ]

section Composition

variable {E F G : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ]
  [NormedAddCommGroup F /- [standing] -/ ] [InnerProductSpace 𝕜 F /- [standing] -/ ] [NormedAddCommGroup G /- [standing] -/ ] [InnerProductSpace 𝕜 G /- [standing] -/ ]

/-- Composing on the left by a bounded operator: `sumSq (S ∘L T) b ≤ ‖S‖ₑ² * sumSq T b`. -/
theorem sumSq_comp_le (S : F →L[𝕜] G /- [definition] -/ ) (T : E →L[𝕜] F /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    sumSq (S ∘L T) b ≤ ‖S‖ₑ ^ 2 * sumSq T b := by
  unfold sumSq
  calc ∑' i, ‖(S ∘L T) (b i)‖ₑ ^ 2
      ≤ ∑' i, (‖S‖ₑ * ‖T (b i)‖ₑ) ^ 2 := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [ContinuousLinearMap.comp_apply]
        exact pow_le_pow_left' (ContinuousLinearMap.le_opENorm S (T (b i))) 2
    _ = ∑' i, ‖S‖ₑ ^ 2 * ‖T (b i)‖ₑ ^ 2 := tsum_congr fun i => mul_pow _ _ _
    _ = ‖S‖ₑ ^ 2 * ∑' i, ‖T (b i)‖ₑ ^ 2 := ENNReal.tsum_mul_left

/-- The adjoint is an isometry: `‖T†‖ₑ = ‖T‖ₑ`. -/
theorem enorm_adjoint [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] (T : E →L[𝕜] F /- [definition] -/ ) :
    ‖T†‖ₑ = ‖T‖ₑ :=
  (ContinuousLinearMap.adjoint).enorm_map T

/-- Composing on the right by a bounded operator: `sumSq (S ∘L T) b ≤ ‖T‖ₑ² * sumSq S c`,
via two adjoint flips. -/
theorem sumSq_comp_le_right [CompleteSpace E /- [standing] -/ ] [CompleteSpace F /- [standing] -/ ] [CompleteSpace G /- [standing] -/ ]
    (S : F →L[𝕜] G /- [definition] -/ ) (T : E →L[𝕜] F /- [definition] -/ ) {ι ι' : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (c : HilbertBasis ι' 𝕜 F /- [definition] -/ ) :
    sumSq (S ∘L T) b ≤ ‖T‖ₑ ^ 2 * sumSq S c := by
  calc sumSq (S ∘L T) b
      = sumSq ((S ∘L T)†) (canonicalBasis 𝕜 G) := sumSq_eq_sumSq_adjoint _ b _
    _ = sumSq ((T†) ∘L (S†)) (canonicalBasis 𝕜 G) := by
        rw [ContinuousLinearMap.adjoint_comp]
    _ ≤ ‖T†‖ₑ ^ 2 * sumSq (S†) (canonicalBasis 𝕜 G) := sumSq_comp_le _ _ _
    _ = ‖T‖ₑ ^ 2 * sumSq (S†) (canonicalBasis 𝕜 G) := by rw [enorm_adjoint]
    _ = ‖T‖ₑ ^ 2 * sumSq S c := by
        rw [← sumSq_eq_sumSq_adjoint S c (canonicalBasis 𝕜 G)]

end Composition

variable {E : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ] [CompleteSpace E /- [standing] -/ ]

/-- If `T` is Hilbert–Schmidt, its sum of squares on the canonical basis is finite. -/
theorem IsHilbertSchmidt.sumSq_ne_top {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ ) :
    sumSq T (canonicalBasis 𝕜 E) ≠ ⊤ := by
  intro h
  apply hT
  show (sumSq T (canonicalBasis 𝕜 E)) ^ (1/2 : ℝ) = ⊤
  rw [h]
  exact ENNReal.top_rpow_of_pos (by norm_num)

/-- If `T` is Hilbert–Schmidt, its sum of squares on any Hilbert basis is finite. -/
theorem IsHilbertSchmidt.sumSq_ne_top_basis {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ )
    {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : sumSq T b ≠ ⊤ := by
  rw [sumSq_independent T b (canonicalBasis 𝕜 E)]
  exact hT.sumSq_ne_top

/-- Finiteness of the canonical-basis sum of squares suffices for Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_sumSq_ne_top (T : E →L[𝕜] E /- [definition] -/ )
    (h : sumSq T (canonicalBasis 𝕜 E) ≠ ⊤ /- [standing] -/ ) : IsHilbertSchmidt T :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) h

/-- The adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ ) :
    IsHilbertSchmidt (T†) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  rw [sumSq_eq_sumSq_adjoint (T†) (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E),
    ContinuousLinearMap.adjoint_adjoint]
  exact hT.sumSq_ne_top

/-- The Hilbert–Schmidt class is closed under left composition by bounded operators. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ )
    (S : E →L[𝕜] E /- [definition] -/ ) : IsHilbertSchmidt (S ∘L T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  exact ne_of_lt ((sumSq_comp_le S T (canonicalBasis 𝕜 E)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 enorm_ne_top))
      (lt_top_iff_ne_top.2 hT.sumSq_ne_top)))

/-- The Hilbert–Schmidt class is closed under right composition by bounded operators. -/
theorem IsHilbertSchmidt.comp_right {S : E →L[𝕜] E /- [definition] -/ } (hS : IsHilbertSchmidt S /- [standing] -/ )
    (T : E →L[𝕜] E /- [definition] -/ ) : IsHilbertSchmidt (S ∘L T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  exact ne_of_lt ((sumSq_comp_le_right S T (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 enorm_ne_top))
      (lt_top_iff_ne_top.2 hS.sumSq_ne_top)))

/-- The squared enorm of `T x` is bounded by the sum of squares times `‖x‖ₑ²`
(Parseval on `T x` plus pointwise Cauchy–Schwarz, via the adjoint). -/
theorem enorm_sq_apply_le_sumSq_mul (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (x : E /- [definition] -/ ) : ‖T x‖ₑ ^ 2 ≤ sumSq T b * ‖x‖ₑ ^ 2 := by
  calc ‖T x‖ₑ ^ 2
      = ∑' i, ‖⟪b i, T x⟫_𝕜‖ₑ ^ 2 := (enorm_sq_eq_tsum b (T x)).symm
    _ = ∑' i, ‖⟪(T†) (b i), x⟫_𝕜‖ₑ ^ 2 := tsum_congr fun i => by
        rw [← ContinuousLinearMap.adjoint_inner_left]
    _ ≤ ∑' i, (‖(T†) (b i)‖ₑ * ‖x‖ₑ) ^ 2 := ENNReal.tsum_le_tsum fun i =>
        pow_le_pow_left' (by simpa only [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] using ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)) 2
    _ = ∑' i, ‖(T†) (b i)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := tsum_congr fun i => mul_pow _ _ _
    _ = sumSq (T†) b * ‖x‖ₑ ^ 2 := ENNReal.tsum_mul_right
    _ = sumSq T b * ‖x‖ₑ ^ 2 := by
        rw [sumSq_eq_sumSq_adjoint T b b]

/-- The operator enorm is bounded by the Hilbert–Schmidt sum of squares' square root. -/
theorem opENorm_le_sumSq_rpow_half (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    ‖T‖ₑ ≤ (sumSq T b) ^ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro x
  have h := ENNReal.rpow_le_rpow (enorm_sq_apply_le_sumSq_mul T b x) (by norm_num : (0:ℝ) ≤ 1/2)
  rw [rpow_half_sq', ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    rpow_half_sq'] at h
  exact h

/-- An operator is *trace class* if it factors as a composition of two Hilbert–Schmidt
operators. -/
noncomputable def IsTraceClass (T : E →L[𝕜] E /- [definition] -/ ) : Prop :=
  ∃ A B : E →L[𝕜] E, IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A ∘L B

/-- Trace-class operators are Hilbert–Schmidt (Hilbert–Schmidt is a left ideal).  The
converse fails in infinite dimension. -/
theorem IsTraceClass.isHilbertSchmidt {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) :
    IsHilbertSchmidt T := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact hB.comp_left A

/-- The squared norms of the basis images of a Hilbert–Schmidt operator are summable. -/
theorem summable_norm_sq_apply_basis {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : Summable fun i => ‖T (b i)‖ ^ 2 := by
  have h := ENNReal.summable_toReal (hT.sumSq_ne_top_basis b)
  exact h.congr fun i => by rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The diagonal series of a trace-class operator is absolutely summable. -/
theorem summable_norm_inner_diagonal {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : Summable fun i => ‖⟪b i, T (b i)⟫_𝕜‖ := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  have hAm := summable_norm_sq_apply_basis hA.adjoint b
  have hBm := summable_norm_sq_apply_basis hB b
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
    ((hAm.add hBm).div_const 2)
  rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  calc ‖⟪(A†) (b i), B (b i)⟫_𝕜‖ ≤ ‖(A†) (b i)‖ * ‖B (b i)‖ := norm_inner_le_norm _ _
    _ ≤ (‖(A†) (b i)‖ ^ 2 + ‖B (b i)‖ ^ 2) / 2 := by
        have h := two_mul_le_add_pow_two ‖(A†) (b i)‖ ‖B (b i)‖
        linarith

/-- The diagonal series of a trace-class operator is summable. -/
theorem summable_inner_diagonal {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : Summable fun i => ⟪b i, T (b i)⟫_𝕜 :=
  (summable_norm_inner_diagonal hT b).of_norm

/-- Squared inner products `⟪A† bᵢ, cⱼ⟫` over the product of two basis index sets are
summable (Parseval in `j`, then the Hilbert–Schmidt sum in `i`). -/
theorem summable_norm_sq_inner_adjoint_fst {A : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    {ι ι' : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (c : HilbertBasis ι' 𝕜 E /- [definition] -/ ) :
    Summable fun p : ι × ι' => ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ ^ 2 := by
  have hfin : (∑' p : ι × ι', ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ₑ ^ 2) ≠ ⊤ := by
    have step : ∀ i, (∑' j, ‖⟪(A†) (b i), c j⟫_𝕜‖ₑ ^ 2) = ‖(A†) (b i)‖ₑ ^ 2 := fun i => by
      rw [tsum_congr fun j => show ‖⟪(A†) (b i), c j⟫_𝕜‖ₑ ^ 2 = ‖⟪c j, (A†) (b i)⟫_𝕜‖ₑ ^ 2 by
        rw [← inner_conj_symm, RCLike.enorm_conj]]
      exact enorm_sq_eq_tsum c ((A†) (b i))
    have htot : (∑' p : ι × ι', ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ₑ ^ 2)
        = ∑' i, ‖(A†) (b i)‖ₑ ^ 2 := by
      rw [ENNReal.tsum_prod']
      exact tsum_congr step
    rw [htot]
    exact hA.adjoint.sumSq_ne_top_basis b
  exact (ENNReal.summable_toReal hfin).congr fun p => by
    rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Squared inner products `⟪cⱼ, B bᵢ⟫` over the product of two basis index sets are
summable (Parseval in `j`, then the Hilbert–Schmidt sum in `i`). -/
theorem summable_norm_sq_inner_snd {B : E →L[𝕜] E /- [definition] -/ } (hB : IsHilbertSchmidt B /- [standing] -/ ) {ι ι' : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (c : HilbertBasis ι' 𝕜 E /- [definition] -/ ) :
    Summable fun p : ι × ι' => ‖⟪c p.2, B (b p.1)⟫_𝕜‖ ^ 2 := by
  have hfin : (∑' p : ι × ι', ‖⟪c p.2, B (b p.1)⟫_𝕜‖ₑ ^ 2) ≠ ⊤ := by
    have step : ∀ i, (∑' j, ‖⟪c j, B (b i)⟫_𝕜‖ₑ ^ 2) = ‖B (b i)‖ₑ ^ 2 := fun i =>
      enorm_sq_eq_tsum c (B (b i))
    have htot : (∑' p : ι × ι', ‖⟪c p.2, B (b p.1)⟫_𝕜‖ₑ ^ 2) = ∑' i, ‖B (b i)‖ₑ ^ 2 := by
      rw [ENNReal.tsum_prod']
      exact tsum_congr step
    rw [htot]
    exact hB.sumSq_ne_top_basis b
  exact (ENNReal.summable_toReal hfin).congr fun p => by
    rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Absolute summability of the double Parseval expansion of `A ∘L B`, justifying the
index swap in `tsum_inner_comp_eq`. -/
theorem summable_uncurry_inner_mul_inner {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) {ι ι' : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (c : HilbertBasis ι' 𝕜 E /- [definition] -/ ) :
    Summable (Function.uncurry fun i j => ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜) := by
  apply Summable.of_norm
  have h1 := summable_norm_sq_inner_adjoint_fst hA b c
  have h2 := summable_norm_sq_inner_snd hB b c
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    ((h1.add h2).div_const 2)
  show ‖⟪(A†) (b p.1), c p.2⟫_𝕜 * ⟪c p.2, B (b p.1)⟫_𝕜‖ ≤ _
  rw [norm_mul]
  have h := two_mul_le_add_pow_two ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ ‖⟪c p.2, B (b p.1)⟫_𝕜‖
  linarith

/-- The trace-swap identity for a product of two Hilbert–Schmidt operators, computed on
two arbitrary Hilbert bases. -/
theorem tsum_inner_comp_eq {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ ) (hB : IsHilbertSchmidt B /- [standing] -/ )
    {ι ι' : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (c : HilbertBasis ι' 𝕜 E /- [definition] -/ ) :
    ∑' i, ⟪b i, (A ∘L B) (b i)⟫_𝕜 = ∑' j, ⟪c j, (B ∘L A) (c j)⟫_𝕜 := by
  have hsum := summable_uncurry_inner_mul_inner hA hB b c
  calc ∑' i, ⟪b i, (A ∘L B) (b i)⟫_𝕜
      = ∑' i, ⟪(A†) (b i), B (b i)⟫_𝕜 := tsum_congr fun i => by
        rw [ContinuousLinearMap.comp_apply]
        exact (ContinuousLinearMap.adjoint_inner_left A (B (b i)) (b i)).symm
    _ = ∑' i, ∑' j, ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜 :=
        tsum_congr fun i => (HilbertBasis.tsum_inner_mul_inner c ((A†) (b i)) (B (b i))).symm
    _ = ∑' j, ∑' i, ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜 := (Summable.tsum_comm hsum).symm
    _ = ∑' j, ∑' i, ⟪(B†) (c j), b i⟫_𝕜 * ⟪b i, A (c j)⟫_𝕜 := tsum_congr fun j =>
        tsum_congr fun i => by
          rw [ContinuousLinearMap.adjoint_inner_left A (c j) (b i),
            ← ContinuousLinearMap.adjoint_inner_left B (b i) (c j), mul_comm]
    _ = ∑' j, ⟪(B†) (c j), A (c j)⟫_𝕜 :=
        tsum_congr fun j => HilbertBasis.tsum_inner_mul_inner b ((B†) (c j)) (A (c j))
    _ = ∑' j, ⟪c j, (B ∘L A) (c j)⟫_𝕜 := tsum_congr fun j =>
        ContinuousLinearMap.adjoint_inner_left B (A (c j)) (c j)

/-- The trace of an operator on a Hilbert space: the sum of the diagonal matrix elements
in the canonical Hilbert basis.  For trace-class operators this is basis-independent
(`trace_eq_tsum_inner`) and cyclic (`trace_comp_comm`). -/
noncomputable def trace (T : E →L[𝕜] E /- [definition] -/ ) : 𝕜 :=
  ∑' i, ⟪canonicalBasis 𝕜 E i, T (canonicalBasis 𝕜 E i)⟫_𝕜

/-- The trace of a trace-class operator can be computed in any Hilbert basis. -/
theorem trace_eq_tsum_inner {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) : trace T = ∑' i, ⟪b i, T (b i)⟫_𝕜 := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  unfold trace
  rw [tsum_inner_comp_eq hA hB (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)]
  exact (tsum_inner_comp_eq hA hB b (canonicalBasis 𝕜 E)).symm

/-- The trace is cyclic on Hilbert–Schmidt factors. -/
theorem trace_comp_comm {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ ) (hB : IsHilbertSchmidt B /- [standing] -/ ) :
    trace (A ∘L B) = trace (B ∘L A) :=
  tsum_inner_comp_eq hA hB (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)

/-- The truncation of `T` onto the span of the basis vectors indexed by `s`. -/
noncomputable def basisTruncation (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ ) : E →L[𝕜] E :=
  ∑ i ∈ s, rankOne 𝕜 (b i) (T (b i))

omit [CompleteSpace E] in
/-- The truncation evaluated at a basis vector. -/
theorem basisTruncation_apply_basis (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ ) (j : ι /- [definition] -/ ) :
    basisTruncation T b s (b j) = if j ∈ s then T (b j) else 0 := by
  classical
  simp only [basisTruncation, sum_apply, rankOne_apply]
  rw [show (∑ i ∈ s, ⟪b i, b j⟫_𝕜 • T (b i)) = ∑ i ∈ s, if i = j then T (b i) else 0 from
    Finset.sum_congr rfl fun i _ => by
      by_cases hij : i = j
      · rcases hij with rfl
        have h1 : ⟪b i, b i⟫_𝕜 = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; norm_num
        rw [h1, one_smul, if_pos rfl]
      · rw [b.orthonormal.2 hij, zero_smul, if_neg hij]]
  exact Finset.sum_ite_eq' s j _

omit [CompleteSpace E] in
/-- The `sumSq` of `T` minus its truncation is the tail of the sum-of-squares series. -/
theorem sumSq_sub_basisTruncation (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ ) :
    sumSq (T - basisTruncation T b s) b = ∑' j, if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2 := by
  classical
  unfold sumSq
  apply tsum_congr
  intro j
  rw [sub_apply, basisTruncation_apply_basis]
  by_cases hj : j ∈ s
  · rw [if_pos hj, if_pos hj, sub_self]
    simp
  · rw [if_neg hj, if_neg hj, sub_zero]

/-- The tail of the sum-of-squares series of a Hilbert–Schmidt operator vanishes along
the directed set of finite subsets. -/
theorem tendsto_sumSq_tail (T : E →L[𝕜] E /- [definition] -/ ) (hT : IsHilbertSchmidt T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    Tendsto (fun s : Finset ι => ∑' j, if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2) atTop (𝓝 0) := by
  classical
  have hfin : (∑' j, ‖T (b j)‖ₑ ^ 2) ≠ ⊤ := hT.sumSq_ne_top_basis b
  have h := ENNReal.tendsto_tsum_compl_atTop_zero hfin
  apply h.congr
  intro s
  have hsub : Function.support (fun j => if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2)
      ⊆ {x : ι | x ∉ s} := by
    intro j hj hjs
    exact hj (if_pos hjs)
  rw [← tsum_subtype_eq_of_support_subset hsub]
  apply tsum_congr
  rintro ⟨j, hj⟩
  rw [if_neg hj]

/-- The square root of the truncated tail tends to zero. -/
theorem tendsto_sumSq_tail_rpow (T : E →L[𝕜] E /- [definition] -/ ) (hT : IsHilbertSchmidt T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    Tendsto (fun s : Finset ι => (sumSq (T - basisTruncation T b s) b) ^ (1/2 : ℝ)) atTop
      (𝓝 0) := by
  classical
  have hanti : Antitone (fun s : Finset ι => (sumSq (T - basisTruncation T b s) b) ^ (1/2 : ℝ)) := by
    intro s s' hss'
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    rw [sumSq_sub_basisTruncation, sumSq_sub_basisTruncation]
    apply ENNReal.tsum_le_tsum
    intro j
    by_cases hj : j ∈ s'
    · rw [if_pos hj]
      exact zero_le
    · rw [if_neg hj, if_neg fun h => hj (Finset.mem_of_subset hss' h)]
  refine (ENNReal.tendsto_atTop_zero_iff_le_of_antitone hanti).2 fun ε hε => ?_
  rcases eq_top_or_lt_top ε with rfl | hεtop
  · exact ⟨∅, le_top⟩
  · have htail := tendsto_sumSq_tail T hT b
    have hpos : (0 : ℝ≥0∞) < ε ^ 2 := pos_iff_ne_zero.2 (pow_ne_zero 2 (ne_of_gt hε))
    rcases (htail.eventually (Iio_mem_nhds hpos)).exists with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [sumSq_sub_basisTruncation]
    exact (ENNReal.rpow_le_rpow hs.le (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (rpow_half_sq' ε)

/-- The truncations converge to `T` in operator norm. -/
theorem tendsto_basisTruncation (T : E →L[𝕜] E /- [definition] -/ ) (hT : IsHilbertSchmidt T /- [standing] -/ ) {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) :
    Tendsto (fun s : Finset ι => basisTruncation T b s) atTop (𝓝 T) := by
  have htail := tendsto_sumSq_tail_rpow T hT b
  have hen : Tendsto (fun s : Finset ι => ‖T - basisTruncation T b s‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun s => zero_le) (fun s => opENorm_le_sumSq_rpow_half _ _)
  have hreal : Tendsto (fun s : Finset ι => ‖T - basisTruncation T b s‖) atTop (𝓝 0) := by
    have hc := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hen
    rw [ENNReal.toReal_zero] at hc
    exact hc.congr fun s => by simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hreal

omit [CompleteSpace E] in
/-- Rank-one operators `x ↦ ⟪v, x⟫ • a` are compact: they factor through the locally
compact scalar field. -/
theorem isCompactOperator_inner_smul (v a : E /- [definition] -/ ) :
    IsCompactOperator (fun x => ⟪v, x⟫_𝕜 • a) := by
  have h1 : IsCompactOperator ⇑((ContinuousLinearMap.id 𝕜 𝕜).smulRight a) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have h2 := h1.comp_clm (innerSL 𝕜 v)
  have heq : ⇑((ContinuousLinearMap.id 𝕜 𝕜).smulRight a) ∘ ⇑(innerSL 𝕜 v)
      = fun x => ⟪v, x⟫_𝕜 • a := funext fun _ => rfl
  rwa [heq] at h2

omit [CompleteSpace E] in
/-- Finite-rank truncations of `T` are compact operators. -/
theorem isCompactOperator_basisTruncation (T : E →L[𝕜] E /- [definition] -/ ) {ι : Type* /- [definition] -/ } (b : HilbertBasis ι 𝕜 E /- [definition] -/ )
    (s : Finset ι /- [definition] -/ ) : IsCompactOperator ⇑(basisTruncation T b s) := by
  classical
  have heq : ∀ s : Finset ι,
      ⇑(basisTruncation T b s) = fun x => ∑ i ∈ s, ⟪b i, x⟫_𝕜 • T (b i) :=
    fun s => funext fun x => by simp only [basisTruncation, sum_apply, rankOne_apply]
  rw [heq]
  induction s using Finset.induction with
  | empty =>
      rw [show (fun x => ∑ i ∈ (∅ : Finset ι), ⟪b i, x⟫_𝕜 • T (b i)) = (0 : E → E) from
        funext fun x => by simp]
      exact isCompactOperator_zero
  | insert a s ha ih =>
      rw [show (fun x => ∑ i ∈ insert a s, ⟪b i, x⟫_𝕜 • T (b i))
          = (fun x => ⟪b a, x⟫_𝕜 • T (b a)) + fun x => ∑ i ∈ s, ⟪b i, x⟫_𝕜 • T (b i) from
        funext fun x => by rw [Finset.sum_insert ha]; rfl]
      exact IsCompactOperator.add (isCompactOperator_inner_smul _ _) ih

/-- Hilbert–Schmidt operators are compact: their finite-rank truncations converge to them
in operator norm, and compact operators are closed under operator-norm limits. -/
theorem IsHilbertSchmidt.isCompactOperator {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ ) :
    IsCompactOperator T :=
  isCompactOperator_of_tendsto (tendsto_basisTruncation T hT (canonicalBasis 𝕜 E))
    (Eventually.of_forall fun s => isCompactOperator_basisTruncation T (canonicalBasis 𝕜 E) s)

/-- Trace-class operators are compact. -/
theorem IsTraceClass.isCompactOperator {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) :
    IsCompactOperator T :=
  hT.isHilbertSchmidt.isCompactOperator


end source14

noncomputable section source15
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # The 2-regularized Fredholm determinant for Hilbert–Schmidt operators

For a Hilbert–Schmidt operator `K : E →L[𝕜] E` on a Hilbert space over `𝕜 = ℝ` or `ℂ`
(`RCLike 𝕜`), the powers `K ^ m` are trace class for `m ≥ 2`, so the
Plemelj-type trace series

  `∑_{m=2}^∞ (−1)^{m+1} z^m · tr(K^m) / m`

is well-defined term by term, and the **2-regularized Fredholm determinant** is

  `det₂(1 + zK) := exp (∑_{m ≥ 2} (−1)^{m+1} z^m tr(K^m) / m)`.

## What is proved here

* `IsTraceClass.comp_right`, `IsTraceClass.comp_left`: the
  trace class is a two-sided ideal among bounded operators.
* `IsHilbertSchmidt.isTraceClass_pow`: for `2 ≤ m`, `K ^ m` is trace class
  when `K` is Hilbert–Schmidt (it factors as `K² ∘L K^{m-2}`).
* `hsENorm_comp_le`, `hsENorm_pow_le`,
  `hsNorm_pow_le`: submultiplicativity of the Hilbert–Schmidt norm,
  `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for `1 ≤ j`.
* `norm_trace_comp_le`: `‖tr (A ∘L B)‖ ≤ ‖A‖₂ ‖B‖₂` (Cauchy–Schwarz on the
  diagonal, through the adjoint factorization), and
  `norm_trace_pow_le`: `‖tr (K ^ m)‖ ≤ ‖K‖₂ ^ m` for `2 ≤ m`.
* `summable_norm_fredholmDetTwoTerm`: the series converges **absolutely**
  on the open disk `‖z‖ * ‖K‖₂ < 1`, and
  `inv_hsNorm_le_radius`: the associated formal power series has radius of
  convergence at least `(‖K‖₂)⁻¹` (with `(0)⁻¹ = ⊤`, so the radius is infinite when
  `K = 0`).
* `fredholmDetTwo`: the definition `det₂ K z = exp (series-sum)`.
* `differentiableOn_fredholmDetTwo`: `z ↦ det₂ K z` is differentiable on the
  open ball `Metric.eball 0 (‖K‖₂)⁻¹`; `fredholmDetTwo_zero`: the value at
  `z = 0` is `1`; `hasFDerivAt_fredholmDetTwo_zero` and
  `deriv_fredholmDetTwo_zero`: the derivative at `z = 0` is `0` (the
  coefficient of `z¹` vanishes — this is exactly the 2-regularization).
* `differentiable_fredholmDetTwo_of_hsNorm_eq_zero`: in the degenerate case
  `‖K‖₂ = 0` (i.e. `K = 0`), `det₂ K` is the constant function `1`, hence differentiable
  everywhere.

## What is NOT proved here (scope note)

The Plemelj trace series has radius of convergence `1 / spr(K)` in general (`spr` the
spectral radius), so `det₂(1 + zK)` *as defined by this series* is genuinely analytic only
on a disk: for `K = diag(1, 1/2, 1/3, …)` on `ℓ²(ℕ)` (Hilbert–Schmidt), `tr(K^m) = ζ(m) → 1`
and the series has radius exactly `1`. The classical fact that `det₂` extends to an *entire*
function for Hilbert–Schmidt `K` requires a different global definition (the Hadamard
product over eigenvalues `(1 + zλ_j) e^{−zλ_j}`, or equivalently the Plemelj–Smithies
exterior-power series, which has `1/n!` factors and converges everywhere) plus the equality
with the trace series on the disk. That entire extension is future work; nothing in this
file claims it.

## TODO

* The entire extension of `det₂` via the Hadamard product or the Plemelj–Smithies series.
* `det₂(1 + zK) = det((1 + zK) ∘ exp(−zK))` for trace-class `K`.
* Multiplicative properties: `det₂((1 + zA)(1 + zB)) = det₂(1 + zA) det₂(1 + zB)
  exp(z² tr(AB))`-type identities, as needed by the Airy-kernel application.
-/

open Filter
open scoped ENNReal NNReal InnerProduct InnerProductSpace


variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ]
variable {E : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ] [CompleteSpace E /- [standing] -/ ]

section TraceClassIdeal

/-- The trace class is a right ideal: a trace-class operator composed on the right with a
bounded operator is trace class. -/
theorem IsTraceClass.comp_right {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) (S : E →L[𝕜] E /- [definition] -/ ) :
    IsTraceClass (T ∘L S) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact ⟨A, B ∘L S, hA, hB.comp_right S, ContinuousLinearMap.comp_assoc A B S⟩

/-- The trace class is a left ideal: a trace-class operator composed on the left with a
bounded operator is trace class. -/
theorem IsTraceClass.comp_left {T : E →L[𝕜] E /- [definition] -/ } (hT : IsTraceClass T /- [standing] -/ ) (S : E →L[𝕜] E /- [definition] -/ ) :
    IsTraceClass (S ∘L T) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact ⟨S ∘L A, B, hA.comp_left S, hB, (ContinuousLinearMap.comp_assoc S A B).symm⟩

omit [CompleteSpace E] in
/-- For `1 ≤ m`, the `m`-th power splits as `K ^ m = K ∘L K ^ (m - 1)`. -/
theorem pow_eq_comp_one_sub (K : E →L[𝕜] E /- [definition] -/ ) {m : ℕ /- [definition] -/ } (hm : 1 ≤ m /- [standing] -/ ) :
    K ^ m = K ∘L K ^ (m - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
  rfl

/-- Powers of exponent at least `2` of a Hilbert–Schmidt operator are trace class:
`K ^ m = (K ∘L K) ∘L K ^ (m - 2)` factors through the trace-class `K ^ 2`. -/
theorem IsHilbertSchmidt.isTraceClass_pow {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {m : ℕ /- [definition] -/ }
    (hm : 2 ≤ m /- [standing] -/ ) : IsTraceClass (K ^ m) := by
  have h2 : IsTraceClass (K ^ 2) := by
    rw [pow_two]
    exact ⟨K, K, hK, hK, rfl⟩
  rw [show m = 2 + (m - 2) from (Nat.add_sub_cancel' hm).symm, pow_add]
  exact h2.comp_right _

end TraceClassIdeal

section HSNorm

/-- The real-valued Hilbert–Schmidt norm `‖T‖₂`: the `toReal` of the `ℝ≥0∞`-valued
Hilbert–Schmidt enorm.  It is finite (i.e. the enorm is not `⊤`) exactly when `T` is
Hilbert–Schmidt. -/
noncomputable def hsNorm (T : E →L[𝕜] E /- [definition] -/ ) : ℝ := (hsENorm T).toReal

/-- The Hilbert–Schmidt norm is nonnegative. -/
theorem hsNorm_nonneg (T : E →L[𝕜] E /- [definition] -/ ) : 0 ≤ hsNorm T := ENNReal.toReal_nonneg

/-- The Hilbert–Schmidt enorm of the adjoint equals that of the operator. -/
theorem hsENorm_adjoint (T : E →L[𝕜] E /- [definition] -/ ) : hsENorm (T†) = hsENorm T := by
  unfold hsENorm
  rw [sumSq_eq_sumSq_adjoint (T†) (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E),
    ContinuousLinearMap.adjoint_adjoint]

/-- The real Hilbert–Schmidt norm of the adjoint equals that of the operator. -/
theorem hsNorm_adjoint (T : E →L[𝕜] E /- [definition] -/ ) : hsNorm (T†) = hsNorm T := by
  unfold hsNorm
  rw [hsENorm_adjoint]

/-- The Hilbert–Schmidt enorm is submultiplicative: `‖S ∘L T‖₂ ≤ ‖S‖₂ * ‖T‖₂`. -/
theorem hsENorm_comp_le (S T : E →L[𝕜] E /- [definition] -/ ) : hsENorm (S ∘L T) ≤ hsENorm S * hsENorm T := by
  unfold hsENorm
  calc (sumSq (S ∘L T) (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ)
      ≤ (‖S‖ₑ ^ 2 * sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_comp_le S T (canonicalBasis 𝕜 E))
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = ‖S‖ₑ * (sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq']
    _ ≤ (sumSq S (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) *
          (sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_left (opENorm_le_sumSq_rpow_half S (canonicalBasis 𝕜 E)) _

/-- `(x ^ n).toReal = (x.toReal) ^ n` for `x : ℝ≥0∞`. -/
theorem toReal_pow (x : ℝ≥0∞ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) : (x ^ n).toReal = x.toReal ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ENNReal.toReal_mul, ih, pow_succ]

omit [CompleteSpace E] in
/-- For `1 ≤ j`, `K ^ (j + 1) = K ^ j ∘L K` (the monoid multiplication on `E →L[𝕜] E` is
composition). -/
theorem pow_succ_eq_comp (K : E →L[𝕜] E /- [definition] -/ ) (j : ℕ /- [definition] -/ ) : K ^ (j + 1) = (K ^ j) ∘L K := by
  conv_lhs => rw [pow_succ]
  rfl

/-- Powers have submultiplicative Hilbert–Schmidt enorm: `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for
`1 ≤ j`. -/
theorem hsENorm_pow_le (K : E →L[𝕜] E /- [definition] -/ ) {j : ℕ /- [definition] -/ } (hj : 1 ≤ j /- [standing] -/ ) :
    hsENorm (K ^ j) ≤ hsENorm K ^ j := by
  induction j, hj using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ j hj ih =>
      rw [pow_succ_eq_comp K j]
      calc hsENorm ((K ^ j) ∘L K) ≤ hsENorm (K ^ j) * hsENorm K := hsENorm_comp_le _ _
        _ ≤ hsENorm K ^ j * hsENorm K := mul_le_mul_left ih _
        _ = hsENorm K ^ (j + 1) := by rw [pow_succ]

/-- The real-valued power bound: `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for `1 ≤ j` and Hilbert–Schmidt
`K`. -/
theorem hsNorm_pow_le {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {j : ℕ /- [definition] -/ } (hj : 1 ≤ j /- [standing] -/ ) :
    hsNorm (K ^ j) ≤ hsNorm K ^ j := by
  have htop : hsENorm K ^ j ≠ ⊤ :=
    lt_top_iff_ne_top.1 (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hK))
  have h := ENNReal.toReal_mono htop (hsENorm_pow_le K hj)
  rw [toReal_pow] at h
  exact h

/-- Powers of exponent at least `1` of a Hilbert–Schmidt operator are Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.pow {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {j : ℕ /- [definition] -/ }
    (hj : 1 ≤ j /- [standing] -/ ) : IsHilbertSchmidt (K ^ j) :=
  lt_top_iff_ne_top.1 (lt_of_le_of_lt (hsENorm_pow_le K hj)
    (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hK)))

end HSNorm

section TraceBound

/-- Squared Cauchy–Schwarz for `tsum`: for nonnegative real families with summable
squares, `(∑' i, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * (∑' i, b i ^ 2)`. -/
theorem tsum_mul_sq_le {ι : Type* /- [definition] -/ } {a b : ι → ℝ /- [definition] -/ }
    (ha : Summable fun i => a i ^ 2 /- [standing] -/ ) (hb : Summable fun i => b i ^ 2 /- [standing] -/ )
    (ha0 : ∀ i, 0 ≤ a i /- [standing] -/ ) (hb0 : ∀ i, 0 ≤ b i /- [standing] -/ ) :
    (∑' i, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * (∑' i, b i ^ 2) := by
  have hab : Summable fun i => a i * b i := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (hb0 i)) _
        ((ha.add hb).div_const 2)
    intro i
    have h := two_mul_le_add_pow_two (a i) (b i)
    calc a i * b i = 2 * a i * b i / 2 := by ring
      _ ≤ (a i ^ 2 + b i ^ 2) / 2 := by linarith
  have hX : (∑' i, a i * b i) ≤ Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) := by
    apply hab.tsum_le_of_sum_le
    intro s
    calc ∑ i ∈ s, a i * b i
        ≤ Real.sqrt ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2)) :=
          (Real.le_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (ha0 i) (hb0 i))
            (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
              (Finset.sum_nonneg fun i _ => sq_nonneg _))).2
            (Finset.sum_mul_sq_le_sq_mul_sq s a b)
      _ ≤ Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (ha.sum_le_tsum s fun i _ => sq_nonneg _)
            (hb.sum_le_tsum s fun i _ => sq_nonneg _)
            (Finset.sum_nonneg fun i _ => sq_nonneg _)
            (tsum_nonneg fun i => sq_nonneg _)
  calc (∑' i, a i * b i) ^ 2
      ≤ (Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun i => mul_nonneg (ha0 i) (hb0 i)) hX 2
    _ = (∑' i, a i ^ 2) * (∑' i, b i ^ 2) :=
        Real.sq_sqrt (mul_nonneg (tsum_nonneg fun i => sq_nonneg _)
          (tsum_nonneg fun i => sq_nonneg _))

/-- The trace of a product of two Hilbert–Schmidt operators is bounded by the product of
their Hilbert–Schmidt norms: `‖tr (A ∘L B)‖ ≤ ‖A‖₂ * ‖B‖₂`.  This is the Hilbert–Schmidt
factorization form of the trace-norm bound `‖T‖₁ ≤ ‖A‖₂ ‖B‖₂` for `T = A ∘L B`. -/
theorem norm_trace_comp_le {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) :
    ‖trace (A ∘L B)‖ ≤ hsNorm A * hsNorm B := by
  have hT : IsTraceClass (A ∘L B) := ⟨A, B, hA, hB, rfl⟩
  have hsum1 : Summable fun i =>
      ‖⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖ :=
    summable_norm_inner_diagonal hT _
  have hsumA : Summable fun i => ‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2 :=
    summable_norm_sq_apply_basis hA.adjoint _
  have hsumB : Summable fun i => ‖B (canonicalBasis 𝕜 E i)‖ ^ 2 :=
    summable_norm_sq_apply_basis hB _
  have hsum1' : Summable fun i =>
      ‖⟪(A†) (canonicalBasis 𝕜 E i), B (canonicalBasis 𝕜 E i)⟫_𝕜‖ :=
    hsum1.congr fun i => by
      rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  have hprod : Summable fun i =>
      ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖ := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
      ((hsumA.add hsumB).div_const 2)
    intro i
    have h := two_mul_le_add_pow_two ‖(A†) (canonicalBasis 𝕜 E i)‖ ‖B (canonicalBasis 𝕜 E i)‖
    calc ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖
        = 2 * ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖ / 2 := by ring
      _ ≤ (‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2 + ‖B (canonicalBasis 𝕜 E i)‖ ^ 2) / 2 := by
          linarith
  have heval : ∀ {T : E →L[𝕜] E}, IsHilbertSchmidt T →
      (∑' i, ‖T (canonicalBasis 𝕜 E i)‖ ^ 2) = hsNorm T ^ 2 := by
    intro T hT
    have h1 : ENNReal.ofReal (∑' i, ‖T (canonicalBasis 𝕜 E i)‖ ^ 2)
        = sumSq T (canonicalBasis 𝕜 E) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
        (summable_norm_sq_apply_basis hT _)]
      exact tsum_congr fun i => (enorm_sq_eq_ofReal _).symm
    have h2 : hsNorm T ^ 2 = (sumSq T (canonicalBasis 𝕜 E)).toReal := by
      unfold hsNorm hsENorm
      rw [← toReal_pow _ 2, rpow_half_sq]
    rw [← h1] at h2
    rw [h2, ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _)]
  have hsq : ‖trace (A ∘L B)‖ ^ 2 ≤ (hsNorm A * hsNorm B) ^ 2 := by
    calc ‖trace (A ∘L B)‖ ^ 2
        = ‖∑' i, ⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖ ^ 2 := rfl
      _ ≤ (∑' i, ‖⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm hsum1) 2
      _ = (∑' i, ‖⟪(A†) (canonicalBasis 𝕜 E i), B (canonicalBasis 𝕜 E i)⟫_𝕜‖) ^ 2 := by
            congr 1
            exact tsum_congr fun i => by
              rw [ContinuousLinearMap.comp_apply,
                ← ContinuousLinearMap.adjoint_inner_left]
      _ ≤ (∑' i, ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖) ^ 2 :=
          pow_le_pow_left₀ (tsum_nonneg fun i => norm_nonneg _)
            (hsum1'.tsum_le_tsum (fun i => norm_inner_le_norm _ _) hprod) 2
      _ ≤ (∑' i, ‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2) *
            (∑' i, ‖B (canonicalBasis 𝕜 E i)‖ ^ 2) :=
          tsum_mul_sq_le hsumA hsumB (fun i => norm_nonneg _) (fun i => norm_nonneg _)
      _ = hsNorm A ^ 2 * hsNorm B ^ 2 := by
            rw [heval hA.adjoint, heval hB, hsNorm_adjoint]
      _ = (hsNorm A * hsNorm B) ^ 2 := (mul_pow ..).symm
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))] at h

/-- The trace-of-power bound `‖tr (K ^ m)‖ ≤ ‖K‖₂ ^ m` for `2 ≤ m`, from
`K ^ m = K ∘L K ^ (m - 1)` and `norm_trace_comp_le`. -/
theorem norm_trace_pow_le {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {m : ℕ /- [definition] -/ } (hm : 2 ≤ m /- [standing] -/ ) :
    ‖trace (K ^ m)‖ ≤ hsNorm K ^ m := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hKj : IsHilbertSchmidt (K ^ (m - 1)) := hK.pow hm1
  calc ‖trace (K ^ m)‖ = ‖trace (K ∘L K ^ (m - 1))‖ := by rw [pow_eq_comp_one_sub K (by omega)]
    _ ≤ hsNorm K * hsNorm (K ^ (m - 1)) := norm_trace_comp_le hK hKj
    _ ≤ hsNorm K * hsNorm K ^ (m - 1) :=
        mul_le_mul_of_nonneg_left (hsNorm_pow_le hK hm1) (hsNorm_nonneg K)
    _ = hsNorm K ^ m := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]

end TraceBound

section Coefficient

/-- The coefficients of the Plemelj-type series of the 2-regularized determinant:
`cₘ = (−1)^{m+1} · tr(K ^ m) / m` for `m ≥ 2`, and `c₀ = c₁ = 0`.  The vanishing of the
first two coefficients is exactly the 2-regularization. -/
noncomputable def fredholmDetTwoCoeff (K : E →L[𝕜] E /- [definition] -/ ) (m : ℕ /- [definition] -/ ) : 𝕜 :=
  if 2 ≤ m then (-1 : 𝕜) ^ (m + 1) * trace (K ^ m) / m else 0

/-- The first coefficient vanishes. -/
theorem fredholmDetTwoCoeff_zero (K : E →L[𝕜] E /- [definition] -/ ) : fredholmDetTwoCoeff K 0 = 0 := by
  unfold fredholmDetTwoCoeff
  norm_num

/-- The second coefficient vanishes. -/
theorem fredholmDetTwoCoeff_one (K : E →L[𝕜] E /- [definition] -/ ) : fredholmDetTwoCoeff K 1 = 0 := by
  unfold fredholmDetTwoCoeff
  norm_num

/-- The coefficient bound `‖cₘ‖ ≤ ‖K‖₂ ^ m / m` for `2 ≤ m`. -/
theorem norm_fredholmDetTwoCoeff_le {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {m : ℕ /- [definition] -/ }
    (hm : 2 ≤ m /- [standing] -/ ) :
    ‖fredholmDetTwoCoeff K m‖ ≤ hsNorm K ^ m / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [fredholmDetTwoCoeff, if_pos hm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, RCLike.norm_natCast]
  exact (div_le_div_iff_of_pos_right hm0).2 (norm_trace_pow_le hK hm)

/-- Absolute convergence of the coefficient series weighted by `r ^ m` for real `r` with
`r * ‖K‖₂ < 1`: comparison with the geometric series of ratio `r * ‖K‖₂`. -/
theorem summable_norm_fredholmDetTwoCoeff_mul_pow {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ )
    {r : ℝ /- [definition] -/ } (hr0 : 0 ≤ r /- [standing] -/ ) (hr : r * hsNorm K < 1 /- [standing] -/ ) :
    Summable fun m => ‖fredholmDetTwoCoeff K m‖ * r ^ m := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) _
    (summable_geometric_of_lt_one (mul_nonneg hr0 (hsNorm_nonneg K)) hr)
  intro m
  by_cases hm : 2 ≤ m
  · calc ‖fredholmDetTwoCoeff K m‖ * r ^ m
        ≤ (hsNorm K ^ m / m) * r ^ m :=
          mul_le_mul_of_nonneg_right (norm_fredholmDetTwoCoeff_le hK hm) (pow_nonneg hr0 m)
      _ ≤ hsNorm K ^ m * r ^ m :=
          mul_le_mul_of_nonneg_right
            (div_le_self (pow_nonneg (hsNorm_nonneg _) _)
              (by exact_mod_cast (by omega : 1 ≤ m))) (pow_nonneg hr0 m)
      _ = (r * hsNorm K) ^ m := by
          rw [← mul_pow, mul_comm (hsNorm K) r]
  · rw [fredholmDetTwoCoeff, if_neg hm, norm_zero, zero_mul]
    exact pow_nonneg (mul_nonneg hr0 (hsNorm_nonneg K)) m

/-- Absolute convergence of the Plemelj series on the open disk `‖z‖ * ‖K‖₂ < 1`:
`∑' m, ‖cₘ z ^ m‖ < ∞`. -/
theorem summable_norm_fredholmDetTwoTerm {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) {z : 𝕜 /- [definition] -/ }
    (hz : ‖z‖ * hsNorm K < 1 /- [standing] -/ ) :
    Summable fun m => ‖fredholmDetTwoCoeff K m * z ^ m‖ := by
  have h := summable_norm_fredholmDetTwoCoeff_mul_pow hK (norm_nonneg z) hz
  apply h.congr
  intro m
  rw [norm_mul, norm_pow]

end Coefficient

section Series

/-- The Plemelj-type formal power series `∑ cₘ x ^ m` of the 2-regularized
log-determinant. -/
noncomputable def fredholmDetTwoSeries (K : E →L[𝕜] E /- [definition] -/ ) : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
  .ofScalars 𝕜 (fredholmDetTwoCoeff K)

/-- The radius of convergence of the Plemelj series is at least `(‖K‖₂)⁻¹` (read as `⊤`
when `‖K‖₂ = 0`). -/
theorem inv_hsNorm_le_radius {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) :
    (ENNReal.ofReal (hsNorm K))⁻¹ ≤ (fredholmDetTwoSeries K).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : (r : ℝ) * hsNorm K < 1 := by
    have h1 : (r : ℝ≥0∞) * ENNReal.ofReal (hsNorm K) < 1 := by
      have hr' : (r : ℝ≥0∞) < 1 / ENNReal.ofReal (hsNorm K) := by
        rw [one_div]
        exact hr
      exact (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.coe_ne_top)
        (Or.inl ENNReal.ofReal_ne_top)).1 hr'
    have h2 : (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    rw [h2, ← ENNReal.ofReal_mul (NNReal.coe_nonneg r)] at h1
    exact ENNReal.ofReal_lt_one.1 h1
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hs := summable_norm_fredholmDetTwoCoeff_mul_pow hK (NNReal.coe_nonneg r) hr1
  apply hs.congr
  intro m
  rw [fredholmDetTwoSeries, FormalMultilinearSeries.ofScalars_norm]

/-- The radius of convergence of the Plemelj series is positive. -/
theorem fredholmDetTwoSeries_radius_pos {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) :
    0 < (fredholmDetTwoSeries K).radius :=
  (ENNReal.inv_pos.2 ENNReal.ofReal_ne_top).trans_le (inv_hsNorm_le_radius hK)

end Series

section Determinant

/-- The 2-regularized Fredholm determinant of a Hilbert–Schmidt operator:

  `det₂(1 + zK) := exp (∑_{m ≥ 2} (−1)^{m+1} z^m tr(K^m) / m)`,

defined for all `z` as the exponential of the sum of the formal power series
`fredholmDetTwoSeries K` (the sum takes the junk value `0` outside the disk of
convergence, so `det₂ K z = 1` there by convention; the meaningful values are on the open
disk `‖z‖ * ‖K‖₂ < 1`, see `summable_norm_fredholmDetTwoTerm` and
`inv_hsNorm_le_radius`). -/
noncomputable def fredholmDetTwo (K : E →L[𝕜] E /- [definition] -/ ) (z : 𝕜 /- [definition] -/ ) : 𝕜 :=
  NormedSpace.exp ((fredholmDetTwoSeries K).sum z)

/-- The series representation: `det₂ K z = exp (∑' m, cₘ * z ^ m)`. -/
theorem fredholmDetTwo_eq_exp_tsum (K : E →L[𝕜] E /- [definition] -/ ) (z : 𝕜 /- [definition] -/ ) :
    fredholmDetTwo K z = NormedSpace.exp (∑' m, fredholmDetTwoCoeff K m * z ^ m) := by
  unfold fredholmDetTwo fredholmDetTwoSeries
  congr 1
  exact tsum_congr fun m => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- `det₂ K 0 = 1`. -/
@[simp]
theorem fredholmDetTwo_zero (K : E →L[𝕜] E /- [definition] -/ ) : fredholmDetTwo K 0 = 1 := by
  have h0 : (fredholmDetTwoSeries K).sum 0 = 0 := by
    have h := FormalMultilinearSeries.ofScalarsSum_zero (E := 𝕜) (c := fredholmDetTwoCoeff K)
    rw [fredholmDetTwoCoeff_zero K] at h
    rw [zero_smul] at h
    exact h
  rw [fredholmDetTwo, h0, NormedSpace.exp_zero]

/-- `det₂ K` has derivative `0` at `z = 0`: the coefficient of `z ^ 1` vanishes. -/
theorem hasFDerivAt_fredholmDetTwo_zero {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) :
    HasFDerivAt (fredholmDetTwo K) (0 : 𝕜 →L[𝕜] 𝕜) 0 := by
  have hp := ((fredholmDetTwoSeries K).hasFPowerSeriesOnBall
    (fredholmDetTwoSeries_radius_pos hK)).hasFPowerSeriesAt.hasFDerivAt
  have hL : continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (fredholmDetTwoSeries K 1) = 0 := by
    have h1 : fredholmDetTwoSeries K 1 = 0 := by
      show FormalMultilinearSeries.ofScalars 𝕜 (fredholmDetTwoCoeff K) 1 = 0
      exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero 𝕜
        (fredholmDetTwoCoeff_one K)
    rw [h1, map_zero]
  rw [hL] at hp
  have hcomp := (hasFDerivAt_exp (𝕂 := 𝕜)).comp 0 hp
  rw [ContinuousLinearMap.comp_zero] at hcomp
  exact hcomp

/-- The scalar derivative of `det₂ K` at `z = 0` is `0`. -/
theorem deriv_fredholmDetTwo_zero {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) :
    deriv (fredholmDetTwo K) 0 = 0 := by
  have h := (hasFDerivAt_fredholmDetTwo_zero hK).hasDerivAt
  rw [h.deriv]
  simp

/-- `z ↦ det₂ K z` is differentiable on the open ball of radius `(‖K‖₂)⁻¹` centered at
`0` (the whole space when `‖K‖₂ = 0`). -/
theorem differentiableOn_fredholmDetTwo {K : E →L[𝕜] E /- [definition] -/ } (hK : IsHilbertSchmidt K /- [standing] -/ ) :
    DifferentiableOn 𝕜 (fredholmDetTwo K)
      (Metric.eball 0 (ENNReal.ofReal (hsNorm K))⁻¹) := by
  have hp := ((fredholmDetTwoSeries K).hasFPowerSeriesOnBall
    (fredholmDetTwoSeries_radius_pos hK)).differentiableOn
  have hsub : Metric.eball (0 : 𝕜) (ENNReal.ofReal (hsNorm K))⁻¹ ⊆
      Metric.eball (0 : 𝕜) (fredholmDetTwoSeries K).radius :=
    Metric.eball_subset_eball (inv_hsNorm_le_radius hK)
  have hexp : Differentiable 𝕜 (NormedSpace.exp : 𝕜 → 𝕜) :=
    fun _ => hasFDerivAt_exp.differentiableAt
  exact hexp.comp_differentiableOn (hp.mono hsub)

/-- In the degenerate case `‖K‖₂ = 0` (equivalently `K = 0`), `det₂ K` is differentiable
everywhere: the ball is the whole space. -/
theorem differentiable_fredholmDetTwo_of_hsNorm_eq_zero {K : E →L[𝕜] E /- [definition] -/ }
    (hK : IsHilbertSchmidt K /- [standing] -/ ) (h0 : hsNorm K = 0 /- [standing] -/ ) :
    Differentiable 𝕜 (fredholmDetTwo K) := by
  rw [← differentiableOn_univ]
  have huniv : (Set.univ : Set 𝕜) = Metric.eball 0 (ENNReal.ofReal (hsNorm K))⁻¹ := by
    rw [h0, ENNReal.ofReal_zero, ENNReal.inv_zero]
    ext z
    simp
  rw [huniv]
  exact differentiableOn_fredholmDetTwo hK

end Determinant


end source15

noncomputable section source16
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # The 1-regularized Fredholm determinant for trace-class operators

For a trace-class operator `A : E →L[𝕜] E` on a Hilbert space over `𝕜 = ℝ` or `ℂ`
(`RCLike 𝕜`), the Plemelj trace series

  `− ∑_{m=1}^∞ z^m · tr(A^m) / m`

is absolutely convergent on the open disk `‖z‖ * ‖A‖₂ < 1` (the `m = 1` term is finite
since `A` is trace class; for `m ≥ 2`, `‖tr(A^m)‖ ≤ ‖A‖₂^m` by the Hilbert–Schmidt power bound), and the
**1-regularized Fredholm determinant** is

  `det₁(1 - zA) := exp (− ∑_{m ≥ 1} z^m tr(A^m) / m)`.

## What is proved here

* Trace linearity: `trace_add`, `trace_sub`, `trace_smul`, `trace_sum`
  (diagonal-tsum manipulations using `summable_inner_diagonal`).
* Closure/ideal lemmas: `IsHilbertSchmidt.neg`, `IsHilbertSchmidt.sub`,
  `IsHilbertSchmidt.isTraceClass_comp`, `hsNorm_comp_le`, `hsNorm_neg`.
* `plemeljSummable`: summability of the Plemelj series on the disk `‖z‖ * ‖A‖₂ < 1`,
  with the `z = 1` specializations `summable_trace_pow_div`,
  `summable_norm_trace_pow_div`, and the tail bounds
  `tsum_norm_trace_pow_div_tail_le`, `norm_tsum_trace_pow_div_tail_le`.
* `fredholmDetOne`: the definition; `fredholmDetOne_zero`: the value `1` at `z = 0`.
* `fredholmDetOne_eq_exp_neg_trace_mul_detTwo`: on `hsNorm A < 1`, the classical
  relation `det₁(1 - A) = exp(−tr A) · det₂(1 - A)` between the two regularizations
  (with `fredholmDetTwo (-A) 1 = det₂(1 - A)` in the `det₂(1 + zK)` convention of
  `FredholmTwo.lean`).
* `fredholmDetOne_one_sub_eq_sub_trace_add_remainder`: the first-order expansion
  `1 − det₁(1−A) = tr A + remainder` with the explicit bound
  `‖1 − det₁(1−A) − tr A‖ ≤ (‖tr A‖ + ‖A‖₂²)²/2 · e^{‖tr A‖ + ‖A‖₂²} + ‖A‖₂²`
  for `‖A‖₂ ≤ 1/2`.
* `trace_pow_comp_comm` and `fredholmDetOne_cyclic`: `tr((AB)^m) = tr((BA)^m)` for
  Hilbert–Schmidt `A, B` and every `m ≥ 1`, hence `det₁(1 − AB) = det₁(1 − BA)`
  (Simon's cyclicity; termwise equality of the series, so no disk hypothesis).
* `norm_trace_pow_div_tail_sub_le`: the `m ≥ 2` Plemelj tail (equivalently, by D2, the
  `det₂` exponent series) is Hilbert–Schmidt Lipschitz on the disk `‖A‖₂, ‖B‖₂ ≤ R < 1`,
  via the telescoping factorization `A^n − B^n = ∑_{i<n} A^i (A−B) B^{n−1−i}`;
  `norm_exp_neg_trace_pow_div_tail_sub_le` is the same estimate after `exp`.

## Scope note

As in `FredholmTwo.lean`, everything takes place on the disk of convergence of the
Plemelj trace series; the entire extension of `det₁` for trace-class `A` (via the
eigenvalue product `∏ (1 − zλ_j)` or the Plemelj–Smithies exterior-power series) is
future work and nothing here claims it.

`det₁` itself is NOT Hilbert–Schmidt Lipschitz: the `m = 1` term `tr A` is not
controlled by `‖A‖₂` (e.g. `X_N = N^{-1/2} diag(1, …, 1)` on `𝕜^N` has
`‖X_N‖₂ = 1` but `tr X_N = √N`), so a continuity statement for `det₁` needs the extra
`|tr A − tr B|` term or factorized (trace-norm) convergence.  The `m ≥ 2` tail —
which is what `det₂` sees — has no such obstruction.
-/

open Filter
open scoped ENNReal NNReal InnerProduct InnerProductSpace


variable {𝕜 : Type* /- [definition] -/ } [RCLike 𝕜 /- [standing] -/ ]
variable {E : Type* /- [definition] -/ } [NormedAddCommGroup E /- [standing] -/ ] [InnerProductSpace 𝕜 E /- [standing] -/ ] [CompleteSpace E /- [standing] -/ ]

section Helpers

/-- The trace is additive (given summability of the two diagonal series). -/
theorem trace_add_of_summable {S T : E →L[𝕜] E /- [definition] -/ }
    (hS : Summable fun i => ⟪canonicalBasis 𝕜 E i, S (canonicalBasis 𝕜 E i)⟫_𝕜 /- [standing] -/ )
    (hT : Summable fun i => ⟪canonicalBasis 𝕜 E i, T (canonicalBasis 𝕜 E i)⟫_𝕜 /- [standing] -/ ) :
    trace (S + T) = trace S + trace T := by
  unfold trace
  rw [← Summable.tsum_add hS hT]
  exact tsum_congr fun i => by rw [add_apply, inner_add_right]

/-- The trace is additive on trace-class operators. -/
theorem trace_add {S T : E →L[𝕜] E /- [definition] -/ } (hS : IsTraceClass S /- [standing] -/ ) (hT : IsTraceClass T /- [standing] -/ ) :
    trace (S + T) = trace S + trace T :=
  trace_add_of_summable (summable_inner_diagonal hS _) (summable_inner_diagonal hT _)

/-- The trace is subtractive on trace-class operators. -/
theorem trace_sub {S T : E →L[𝕜] E /- [definition] -/ } (hS : IsTraceClass S /- [standing] -/ ) (hT : IsTraceClass T /- [standing] -/ ) :
    trace (S - T) = trace S - trace T := by
  unfold trace
  rw [← Summable.tsum_sub (summable_inner_diagonal hS _) (summable_inner_diagonal hT _)]
  exact tsum_congr fun i => by rw [sub_apply, inner_sub_right]

/-- The trace is homogeneous. -/
theorem trace_smul (c : 𝕜 /- [definition] -/ ) (T : E →L[𝕜] E /- [definition] -/ ) : trace (c • T) = c * trace T := by
  unfold trace
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by rw [smul_apply, inner_smul_right]

/-- The trace of a finite sum of operators is the sum of the traces (given summability
of each diagonal series). -/
theorem trace_sum {ι : Type* /- [definition] -/ } (s : Finset ι /- [definition] -/ ) {T : ι → E →L[𝕜] E /- [definition] -/ }
    (hT : ∀ i ∈ s, Summable fun j => ⟪canonicalBasis 𝕜 E j, T i (canonicalBasis 𝕜 E j)⟫_𝕜 /- [standing] -/ ) :
    trace (∑ i ∈ s, T i) = ∑ i ∈ s, trace (T i) := by
  unfold trace
  have step : ∀ j, ⟪canonicalBasis 𝕜 E j, (∑ i ∈ s, T i) (canonicalBasis 𝕜 E j)⟫_𝕜
      = ∑ i ∈ s, ⟪canonicalBasis 𝕜 E j, T i (canonicalBasis 𝕜 E j)⟫_𝕜 := fun j => by
    rw [sum_apply, inner_sum]
  rw [tsum_congr step, Summable.tsum_finsetSum fun i hi => hT i hi]

omit [CompleteSpace E] in
/-- Powers of scalar multiples of an operator: `(c • A) ^ m = c ^ m • A ^ m`. -/
theorem smul_pow_clm (c : 𝕜 /- [definition] -/ ) (A : E →L[𝕜] E /- [definition] -/ ) (m : ℕ /- [definition] -/ ) : (c • A) ^ m = c ^ m • A ^ m :=
  smul_pow c A m

omit [CompleteSpace E] in
/-- Powers of the negative of an operator: `(-A) ^ m = (-1) ^ m • A ^ m`. -/
theorem neg_pow_clm (A : E →L[𝕜] E /- [definition] -/ ) (m : ℕ /- [definition] -/ ) : (-A) ^ m = (-1 : 𝕜) ^ m • A ^ m := by
  have h : -A = (-1 : 𝕜) • A := (neg_one_smul 𝕜 A).symm
  rw [h, smul_pow_clm]

/-- The Hilbert–Schmidt enorm is even: `‖−T‖₂,ₑ = ‖T‖₂,ₑ`. -/
theorem hsENorm_neg (T : E →L[𝕜] E /- [definition] -/ ) : hsENorm (-T) = hsENorm T := by
  unfold hsENorm
  congr 1
  unfold sumSq
  exact tsum_congr fun i => by rw [neg_apply, enorm_neg]

/-- The real Hilbert–Schmidt norm is even. -/
theorem hsNorm_neg (T : E →L[𝕜] E /- [definition] -/ ) : hsNorm (-T) = hsNorm T := by
  unfold hsNorm
  rw [hsENorm_neg]

/-- The Hilbert–Schmidt class is closed under negation. -/
theorem IsHilbertSchmidt.neg {T : E →L[𝕜] E /- [definition] -/ } (hT : IsHilbertSchmidt T /- [standing] -/ ) :
    IsHilbertSchmidt (-T) := by
  show hsENorm (-T) ≠ ⊤
  rwa [hsENorm_neg]

/-- A composition of two Hilbert–Schmidt operators is trace class. -/
theorem IsHilbertSchmidt.isTraceClass_comp {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) : IsTraceClass (A ∘L B) :=
  ⟨A, B, hA, hB, rfl⟩

/-- The real Hilbert–Schmidt norm is submultiplicative on Hilbert–Schmidt operators. -/
theorem hsNorm_comp_le {S T : E →L[𝕜] E /- [definition] -/ } (hS : IsHilbertSchmidt S /- [standing] -/ )
    (hT : IsHilbertSchmidt T /- [standing] -/ ) : hsNorm (S ∘L T) ≤ hsNorm S * hsNorm T := by
  unfold hsNorm
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hS hT) (hsENorm_comp_le S T)

/-- The Hilbert–Schmidt class is closed under subtraction. -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] E /- [definition] -/ } (hS : IsHilbertSchmidt S /- [standing] -/ )
    (hT : IsHilbertSchmidt T /- [standing] -/ ) : IsHilbertSchmidt (S - T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  have hle : sumSq (S - T) (canonicalBasis 𝕜 E) ≤
      4 * (sumSq S (canonicalBasis 𝕜 E) + sumSq T (canonicalBasis 𝕜 E)) := by
    calc sumSq (S - T) (canonicalBasis 𝕜 E)
        = ∑' i, ‖(S - T) (canonicalBasis 𝕜 E i)‖ₑ ^ 2 := rfl
      _ ≤ ∑' i, 4 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) := by
          apply ENNReal.tsum_le_tsum
          intro i
          rw [sub_apply]
          have h1 : ‖S (canonicalBasis 𝕜 E i) - T (canonicalBasis 𝕜 E i)‖ₑ
              ≤ ‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ := enorm_sub_le
          refine (pow_le_pow_left' h1 2).trans ?_
          have hsup : (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2
              ≤ ‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2 := by
            rcases le_total ‖S (canonicalBasis 𝕜 E i)‖ₑ ‖T (canonicalBasis 𝕜 E i)‖ₑ with h | h
            · rw [sup_eq_right.2 h]
              exact self_le_add_left (‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
                (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
            · rw [sup_eq_left.2 h]
              exact self_le_add_right (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
                (‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
          calc (‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2
              ≤ (2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ)) ^ 2 := by
                apply pow_le_pow_left'
                have hs1 : ‖S (canonicalBasis 𝕜 E i)‖ₑ ≤
                    ‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ := le_sup_left
                have hs2 : ‖T (canonicalBasis 𝕜 E i)‖ₑ ≤
                    ‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ := le_sup_right
                calc ‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ
                    ≤ (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) +
                        (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) :=
                      add_le_add hs1 hs2
                  _ = 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) :=
                      (two_mul _).symm
            _ = 2 ^ 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2 :=
                mul_pow _ _ _
            _ ≤ 2 ^ 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) :=
                mul_le_mul' le_rfl hsup
            _ = 4 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) := by
                rw [show (2 : ℝ≥0∞) ^ 2 = 4 from by norm_num]
      _ = 4 * (sumSq S (canonicalBasis 𝕜 E) + sumSq T (canonicalBasis 𝕜 E)) := by
          unfold sumSq
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  exact ne_of_lt (lt_of_le_of_lt hle
    (ENNReal.mul_lt_top (Ne.lt_top ENNReal.ofNat_ne_top)
      (ENNReal.add_lt_top.2 ⟨hS.sumSq_ne_top.lt_top, hT.sumSq_ne_top.lt_top⟩)))

/-- The trace is cyclic on powers of a product of two Hilbert–Schmidt operators:
`tr ((A ∘L B) ^ n) = tr ((B ∘L A) ^ n)` for `1 ≤ n`.  For `n = 1` this is
`trace_comp_comm`; in general one rewrites `(A∘LB)^n = A ∘L ((B∘LA)^{n−1} ∘L B)` and
cycles once. -/
theorem trace_pow_comp_comm {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) {n : ℕ /- [definition] -/ } (hn : 1 ≤ n /- [standing] -/ ) :
    trace ((A ∘L B) ^ n) = trace ((B ∘L A) ^ n) := by
  rcases hn.eq_or_lt with hn1 | hn2
  · rw [← hn1, pow_one, pow_one]
    exact trace_comp_comm hA hB
  · have hAB : IsHilbertSchmidt (A ∘L B) := hB.comp_left A
    have aux : ∀ k : ℕ, B ∘L (A ∘L B) ^ k = ((B ∘L A) ^ k) ∘L B := by
      intro k
      induction k with
      | zero =>
          rw [pow_zero, pow_zero]
          exact (mul_one B).trans (one_mul B).symm
      | succ k ih =>
          rw [pow_succ_eq_comp _ k, ← ContinuousLinearMap.comp_assoc, ih,
            ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc B A B,
            ← ContinuousLinearMap.comp_assoc, ← pow_succ_eq_comp _ k]
    have hYn : IsHilbertSchmidt (B ∘L (A ∘L B) ^ (n - 1)) :=
      (hAB.pow (by omega : 1 ≤ n - 1)).comp_left B
    calc trace ((A ∘L B) ^ n)
        = trace (A ∘L (B ∘L (A ∘L B) ^ (n - 1))) := by
          rw [pow_eq_comp_one_sub _ hn, ContinuousLinearMap.comp_assoc]
      _ = trace ((B ∘L (A ∘L B) ^ (n - 1)) ∘L A) := trace_comp_comm hA hYn
      _ = trace ((((B ∘L A) ^ (n - 1)) ∘L B) ∘L A) := by rw [aux (n - 1)]
      _ = trace (((B ∘L A) ^ (n - 1)) ∘L (B ∘L A)) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = trace ((B ∘L A) ^ n) := by
          rw [← pow_succ_eq_comp _ (n - 1), Nat.sub_add_cancel hn]

end Helpers

section Plemelj

/-- **D0.** The Plemelj trace series `∑_{m ≥ 1} z^m tr(A^m)/m` of a trace-class operator
is summable on the open disk `‖z‖ * ‖A‖₂ < 1`.  The `m = 1` term is a single finite
value; the `m ≥ 2` tail is dominated termwise by the geometric series of ratio
`‖z‖ * ‖A‖₂` via `norm_trace_pow_le`. -/
theorem plemeljSummable {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ ) {z : 𝕜 /- [definition] -/ }
    (hz : ‖z‖ * hsNorm A < 1 /- [standing] -/ ) :
    Summable fun m : ℕ => z ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have hr0 : 0 ≤ ‖z‖ * hsNorm A := mul_nonneg (norm_nonneg z) (hsNorm_nonneg A)
  have hgeo : Summable fun m : ℕ => (‖z‖ * hsNorm A) ^ m :=
    summable_geometric_of_lt_one hr0 hz
  have htail : Summable fun m : ℕ =>
      z ^ (m + 1 + 1) * trace (A ^ (m + 1 + 1)) / ((m + 1 + 1 : ℕ) : 𝕜) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      (hgeo.mul_left ((‖z‖ * hsNorm A) ^ 2))
    rw [norm_div, norm_mul, norm_pow, RCLike.norm_natCast]
    have hm1 : (1 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 + 1 by omega)
    calc ‖z‖ ^ (m + 1 + 1) * ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ)
        ≤ ‖z‖ ^ (m + 1 + 1) * hsNorm A ^ (m + 1 + 1) / ((m + 1 + 1 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 1 + 1 by omega))).2
            (mul_le_mul_of_nonneg_left (norm_trace_pow_le hA2 (show 2 ≤ m + 1 + 1 by omega))
              (pow_nonneg (norm_nonneg z) _))
      _ ≤ ‖z‖ ^ (m + 1 + 1) * hsNorm A ^ (m + 1 + 1) :=
          div_le_self (mul_nonneg (pow_nonneg (norm_nonneg z) _)
            (pow_nonneg (hsNorm_nonneg _) _)) hm1
      _ = (‖z‖ * hsNorm A) ^ 2 * (‖z‖ * hsNorm A) ^ m := by
          rw [← mul_pow, show m + 1 + 1 = 2 + m from by omega, pow_add]
  exact (summable_nat_add_iff 1).mp htail

/-- The `z = 1` Plemelj series of a trace-class operator is summable on `‖A‖₂ < 1`. -/
theorem summable_trace_pow_div {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) : Summable fun m : ℕ => trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
  have h := plemeljSummable hA (z := 1) (by rwa [norm_one, one_mul])
  exact h.congr fun m => by rw [one_pow, one_mul]

/-- The `z = 1` Plemelj series converges absolutely on `‖A‖₂ < 1`. -/
theorem summable_norm_trace_pow_div {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 1))‖ / ((m + 1 : ℕ) : ℝ) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have hgeo : Summable fun m : ℕ => hsNorm A ^ m :=
    summable_geometric_of_lt_one (hsNorm_nonneg A) hz
  have htail : Summable fun m : ℕ => ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ) := by
    refine Summable.of_nonneg_of_le
      (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
      (hgeo.mul_left (hsNorm A ^ 2))
    have hm1 : (1 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 + 1 by omega)
    calc ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 1 + 1) / ((m + 1 + 1 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 1 + 1 by omega))).2
            (norm_trace_pow_le hA2 (show 2 ≤ m + 1 + 1 by omega))
      _ ≤ hsNorm A ^ (m + 1 + 1) := div_le_self (pow_nonneg (hsNorm_nonneg _) _) hm1
      _ = hsNorm A ^ 2 * hsNorm A ^ m := by
          rw [show m + 1 + 1 = 2 + m from by omega, pow_add]
  exact (summable_nat_add_iff 1).mp htail

/-- The tail of the absolute `z = 1` Plemelj series is summable. -/
theorem summable_norm_trace_pow_div_tail {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
    ((summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left (hsNorm A ^ 2))
  calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
          (norm_trace_pow_le hA2 (show 2 ≤ m + 2 by omega))
    _ ≤ hsNorm A ^ (m + 2) :=
        div_le_self (pow_nonneg (hsNorm_nonneg _) _)
          (by exact_mod_cast (show 1 ≤ m + 2 by omega))
    _ = hsNorm A ^ 2 * hsNorm A ^ m := by
        rw [show m + 2 = 2 + m from by omega, pow_add]

/-- The tail of the `z = 1` Plemelj series (indices `m ≥ 2`) is summable. -/
theorem summable_trace_pow_div_tail {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) : Summable fun m : ℕ => trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  apply Summable.of_norm
  exact (summable_norm_trace_pow_div_tail hA hz).congr fun m => by
    rw [norm_div, RCLike.norm_natCast]

/-- The tail of the absolute `z = 1` Plemelj series:
`∑'_{m ≥ 2} ‖tr(A^m)‖/m ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem tsum_norm_trace_pow_div_tail_le {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have bound : ∀ m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
    intro m
    calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
            (norm_trace_pow_le hA2 (show 2 ≤ m + 2 by omega))
      _ ≤ hsNorm A ^ (m + 2) / 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (hsNorm_nonneg _) _) (by norm_num)
            (by exact_mod_cast (show 2 ≤ m + 2 by omega))
      _ = (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
          rw [show m + 2 = 2 + m from by omega, pow_add, div_mul_eq_mul_div]
  have h1 : Summable fun m : ℕ => (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
    (summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left _
  have h2 : Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
      bound h1
  calc ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ ∑' m : ℕ, (hsNorm A ^ 2 / 2) * hsNorm A ^ m := h2.tsum_le_tsum bound h1
    _ = (hsNorm A ^ 2 / 2) * ∑' m : ℕ, hsNorm A ^ m := by rw [← tsum_mul_left]
    _ = (hsNorm A ^ 2 / 2) * (1 - hsNorm A)⁻¹ := by
        rw [tsum_geometric_of_lt_one (hsNorm_nonneg A) hz]
    _ = hsNorm A ^ 2 / (2 * (1 - hsNorm A)) :=
        (div_eq_mul_inv _ _).symm.trans (div_div _ _ _)

/-- The tail bound simplifies to `‖A‖₂²` when `‖A‖₂ ≤ 1/2`. -/
theorem tsum_norm_trace_pow_div_tail_le_of_le_half {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) (h2 : hsNorm A ≤ 1 / 2 /- [standing] -/ ) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤ hsNorm A ^ 2 := by
  refine (tsum_norm_trace_pow_div_tail_le hA hz).trans ?_
  have h1 : (1 : ℝ) ≤ 2 * (1 - hsNorm A) := by linarith [hsNorm_nonneg A]
  exact div_le_self (pow_nonneg (hsNorm_nonneg _) _) h1

/-- The norm of the tail of the `z = 1` Plemelj series:
`‖∑'_{m ≥ 2} tr(A^m)/m‖ ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem norm_tsum_trace_pow_div_tail_le {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hsumnorm : Summable fun m : ℕ => ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    (summable_norm_trace_pow_div_tail hA hz).congr fun m => by
      rw [norm_div, RCLike.norm_natCast]
  calc ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := tsum_congr fun m => by
        rw [norm_div, RCLike.norm_natCast]
    _ ≤ hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := tsum_norm_trace_pow_div_tail_le hA hz

/-- The norm of the tail of the `z = 1` Plemelj series is at most `‖A‖₂²` when
`‖A‖₂ ≤ 1/2`. -/
theorem norm_tsum_trace_pow_div_tail_le_of_le_half {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) (h2 : hsNorm A ≤ 1 / 2 /- [standing] -/ ) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤ hsNorm A ^ 2 := by
  refine (norm_tsum_trace_pow_div_tail_le hA hz).trans ?_
  have h1 : (1 : ℝ) ≤ 2 * (1 - hsNorm A) := by linarith [hsNorm_nonneg A]
  exact div_le_self (pow_nonneg (hsNorm_nonneg _) _) h1

/-- Peeling the `m = 1` term off the `z = 1` Plemelj series:
`∑'_{m ≥ 1} tr(A^m)/m = tr A + ∑'_{m ≥ 2} tr(A^m)/m`. -/
theorem tsum_trace_pow_div_eq_trace_add_tail {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    ∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
      trace A + ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  have hsum := summable_trace_pow_div hA hz
  rw [hsum.tsum_eq_zero_add]
  have hg0 : trace (A ^ (0 + 1)) / ((0 + 1 : ℕ) : 𝕜) = trace A := by
    rw [show 0 + 1 = 1 from rfl, pow_one, Nat.cast_one, div_one]
  have htail : (∑' m : ℕ, trace (A ^ (m + 1 + 1)) / ((m + 1 + 1 : ℕ) : 𝕜)) =
      ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) :=
    tsum_congr fun m => by rw [show m + 1 + 1 = m + 2 from rfl]
  rw [hg0, htail]

end Plemelj

section ExpBounds

/-- The exponential series in `𝕜`: `NormedSpace.exp w = ∑' n, w ^ n / n !`. -/
theorem hasSum_pow_div_factorial (w : 𝕜 /- [definition] -/ ) :
    HasSum (fun n : ℕ => w ^ n / (n.factorial : 𝕜)) (NormedSpace.exp w) := by
  simpa only [NormedSpace.expSeries_apply_eq_div] using
    NormedSpace.expSeries_hasSum_exp (𝕂 := 𝕜) w

/-- The exponential series is summable. -/
theorem summable_pow_div_factorial (w : 𝕜 /- [definition] -/ ) : Summable fun n : ℕ => w ^ n / (n.factorial : 𝕜) :=
  (hasSum_pow_div_factorial w).summable

/-- The exponential series sums to `NormedSpace.exp w`. -/
theorem tsum_pow_div_factorial (w : 𝕜 /- [definition] -/ ) :
    ∑' n : ℕ, w ^ n / (n.factorial : 𝕜) = NormedSpace.exp w :=
  (hasSum_pow_div_factorial w).tsum_eq

/-- The real exponential series of a norm is summable. -/
theorem summable_norm_pow_div_factorial (w : 𝕜 /- [definition] -/ ) :
    Summable fun n : ℕ => ‖w‖ ^ n / (n.factorial : ℝ) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) ‖w‖
  refine h.congr fun n => ?_
  rw [smul_eq_mul, mul_comm, div_eq_mul_inv]

/-- The real exponential series of a norm sums to `Real.exp ‖w‖`. -/
theorem tsum_norm_pow_div_factorial (w : 𝕜 /- [definition] -/ ) :
    ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) = Real.exp ‖w‖ := by
  have h : HasSum (fun n : ℕ => ‖w‖ ^ n / (n.factorial : ℝ)) (NormedSpace.exp ‖w‖) := by
    simpa only [NormedSpace.expSeries_apply_eq_div] using
      NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (𝔸 := ℝ) ‖w‖
  rw [Real.exp_eq_exp_ℝ]
  exact h.tsum_eq

/-- `‖exp w‖ ≤ e^{‖w‖}` for `w : 𝕜`. -/
theorem norm_exp_le (w : 𝕜 /- [definition] -/ ) : ‖NormedSpace.exp w‖ ≤ Real.exp ‖w‖ := by
  have hnorm : ∀ n : ℕ, ‖w ^ n / (n.factorial : 𝕜)‖ = ‖w‖ ^ n / (n.factorial : ℝ) := fun n => by
    rw [norm_div, norm_pow, RCLike.norm_natCast]
  have hsum : Summable fun n : ℕ => ‖w ^ n / (n.factorial : 𝕜)‖ :=
    (summable_norm_pow_div_factorial w).congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w‖ = ‖∑' n : ℕ, w ^ n / (n.factorial : 𝕜)‖ := by rw [tsum_pow_div_factorial]
    _ ≤ ∑' n : ℕ, ‖w ^ n / (n.factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := tsum_congr hnorm
    _ = Real.exp ‖w‖ := tsum_norm_pow_div_factorial w

/-- First-order remainder for `exp` in `𝕜`: `‖exp w − 1‖ ≤ ‖w‖ · e^{‖w‖}`. -/
theorem norm_exp_sub_one_le (w : 𝕜 /- [definition] -/ ) :
    ‖NormedSpace.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hsplit : NormedSpace.exp w - 1 = ∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : 𝕜) := by
    rw [← tsum_pow_div_factorial w, (summable_pow_div_factorial w).tsum_eq_zero_add]
    have h0 : w ^ 0 / (Nat.factorial 0 : 𝕜) = 1 := by
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [h0, add_sub_cancel_left]
  have hnorm : ∀ n : ℕ, ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ = ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    fun n => by rw [norm_div, norm_pow, RCLike.norm_natCast]
  have bound : ∀ n : ℕ, ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) ≤ ‖w‖ ^ (n + 1) / (n.factorial : ℝ) := by
    intro n
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
  have hsum1 : Summable fun n : ℕ => ‖w‖ ^ (n + 1) / (n.factorial : ℝ) :=
    ((summable_norm_pow_div_factorial w).mul_left ‖w‖).congr fun n => by
      rw [pow_succ', mul_div_assoc]

  have hsum2 : Summable fun n : ℕ => ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)) bound hsum1
  have hsum0 : Summable fun n : ℕ => ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ :=
    hsum2.congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w - 1‖
      = ‖∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum0
    _ = ∑' n : ℕ, ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) := tsum_congr hnorm
    _ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 1) / (n.factorial : ℝ) := hsum2.tsum_le_tsum bound hsum1
    _ = ‖w‖ * ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by rw [pow_succ', mul_div_assoc]
    _ = ‖w‖ * Real.exp ‖w‖ := by rw [tsum_norm_pow_div_factorial]

/-- Second-order remainder for `exp` in `𝕜`: `‖exp w − 1 − w‖ ≤ ‖w‖²/2 · e^{‖w‖}`. -/
theorem norm_exp_sub_one_sub_le (w : 𝕜 /- [definition] -/ ) :
    ‖NormedSpace.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 / 2 * Real.exp ‖w‖ := by
  have hsplit : NormedSpace.exp w - 1 - w = ∑' n : ℕ, w ^ (n + 2) / ((n + 2).factorial : 𝕜) := by
    have h := (summable_pow_div_factorial w).sum_add_tsum_nat_add 2
    have hstart : ∑ i ∈ Finset.range 2, w ^ i / (i.factorial : 𝕜) = 1 + w := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
    rw [← tsum_pow_div_factorial w, ← h, hstart]
    ring
  have hnorm : ∀ n : ℕ, ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ = ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    fun n => by rw [norm_div, norm_pow, RCLike.norm_natCast]
  have hfact : ∀ n : ℕ, ‖w‖ ^ 2 / 2 * (‖w‖ ^ n / (n.factorial : ℝ)) =
      ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := by
    intro n
    rw [div_mul_eq_mul_div, ← mul_div_assoc, div_div, ← pow_add,
      show 2 + n = n + 2 from by omega, mul_comm ((n.factorial : ℝ)) 2]
  have bound : ∀ n : ℕ, ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := by
    intro n
    apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr (Nat.factorial_pos n)))
    have h : 2 * n.factorial ≤ (n + 2).factorial := by
      have e : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
      rw [e]
      have h2 : (2 : ℕ) ≤ (n + 2) * (n + 1) :=
        calc (2 : ℕ) = 2 * 1 := rfl
          _ ≤ (n + 2) * (n + 1) :=
            Nat.mul_le_mul (by omega : 2 ≤ n + 2) (by omega : 1 ≤ n + 1)
      exact mul_le_mul h2 le_rfl (Nat.zero_le _) (Nat.zero_le _)
    exact_mod_cast h
  have hsum2 : Summable fun n : ℕ => ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) :=
    ((summable_norm_pow_div_factorial w).mul_left (‖w‖ ^ 2 / 2)).congr hfact
  have hsum1 : Summable fun n : ℕ => ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)) bound hsum2
  have hsum0 : Summable fun n : ℕ => ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ :=
    hsum1.congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w - 1 - w‖
      = ‖∑' n : ℕ, w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum0
    _ = ∑' n : ℕ, ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) := tsum_congr hnorm
    _ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := hsum1.tsum_le_tsum bound hsum2
    _ = ‖w‖ ^ 2 / 2 * ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => (hfact n).symm
    _ = ‖w‖ ^ 2 / 2 * Real.exp ‖w‖ := by rw [tsum_norm_pow_div_factorial]

end ExpBounds

section Determinant

/-- The 1-regularized Fredholm determinant of a trace-class operator:

  `det₁(1 - zA) := exp (− ∑_{m ≥ 1} z^m tr(A^m)/m)`,

defined for all `z` as the exponential of the Plemelj-series sum (the sum takes the
junk value `0` when the series is not summable; the meaningful values are on the open
disk `‖z‖ * ‖A‖₂ < 1`, see `plemeljSummable`).  The trace-class proof argument is
present for API uniformity; the value does not depend on it. -/
noncomputable def fredholmDetOne (A : E →L[𝕜] E /- [definition] -/ ) (_hA : IsTraceClass A /- [standing] -/ ) (z : 𝕜 /- [definition] -/ ) : 𝕜 :=
  NormedSpace.exp (-∑' m : ℕ, z ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))

/-- `det₁(1 - 0·A) = 1`. -/
@[simp]
theorem fredholmDetOne_zero (A : E →L[𝕜] E /- [definition] -/ ) (hA : IsTraceClass A /- [standing] -/ ) :
    fredholmDetOne A hA 0 = 1 := by
  have h0 : (fun m : ℕ => (0 : 𝕜) ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))
      = fun _ => 0 := by
    ext m
    rw [zero_pow (show m + 1 ≠ 0 by omega), zero_mul, zero_div]
  unfold fredholmDetOne
  rw [h0, tsum_zero, neg_zero, NormedSpace.exp_zero]

/-- The `z = 1` specialization: `det₁(1 - A) = exp (− ∑'_{m ≥ 1} tr(A^m)/m)`. -/
theorem fredholmDetOne_one_eq_exp_neg_tsum (A : E →L[𝕜] E /- [definition] -/ ) (hA : IsTraceClass A /- [standing] -/ ) :
    fredholmDetOne A hA 1 =
      NormedSpace.exp (-∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) := by
  unfold fredholmDetOne
  congr 1
  congr 1
  exact tsum_congr fun m => by rw [one_pow, one_mul]

/-- **D2.** The classical relation between the two regularizations: on the disk
`‖A‖₂ < 1`,
`det₁(1 - A) = exp(−tr A) · det₂(1 - A)`.

Here `fredholmDetTwo (-A) 1` is `det₂(1 - A)` in the `det₂(1 + zK)` convention of
`FredholmTwo.lean`: the det₂ coefficient of `−A` at `m ≥ 2` is
`(−1)^{m+1} tr((−A)^m)/m = −tr(A^m)/m`, matching the det₁ tail, while the missing
`m = 1` term is exactly `exp (−tr A)`. -/
theorem fredholmDetOne_eq_exp_neg_trace_mul_detTwo {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    fredholmDetOne A hA 1 = NormedSpace.exp (-(trace A)) * fredholmDetTwo (-A) 1 := by
  set f : ℕ → 𝕜 := fun m => -trace (A ^ m) / (m : 𝕜) with hf
  have h1 : Summable fun m : ℕ => trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) :=
    summable_trace_pow_div hA hz
  have hf1 : Summable fun m : ℕ => f (m + 1) := by
    refine h1.neg.congr fun m => ?_
    show -(trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) =
      -trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)
    rw [neg_div]
  have hf0 : Summable f := (summable_nat_add_iff 1).mp hf1
  have hf2 : Summable fun m : ℕ => f (m + 2) := (summable_nat_add_iff 2).mpr hf0
  have hcoeff : ∀ m : ℕ, fredholmDetTwoCoeff (-A) m = if 2 ≤ m then f m else 0 := by
    intro m
    by_cases hm : 2 ≤ m
    · rw [fredholmDetTwoCoeff, if_pos hm, if_pos hm]
      show (-1 : 𝕜) ^ (m + 1) * trace ((-A) ^ m) / (m : 𝕜) = -trace (A ^ m) / (m : 𝕜)
      rw [neg_pow_clm, trace_smul]
      have hsign : (-1 : 𝕜) ^ (m + 1) * (-1 : 𝕜) ^ m = -1 := by
        rw [← pow_add, show m + 1 + m = 2 * m + 1 from by omega, pow_add, pow_one,
          pow_mul, show (-1 : 𝕜) ^ 2 = 1 from by ring, one_pow, one_mul]
      rw [← mul_assoc, hsign, neg_one_mul]
    · rw [fredholmDetTwoCoeff, if_neg hm, if_neg hm]
  have hge : Summable fun m : ℕ => if 2 ≤ m then f m else 0 := by
    apply (summable_nat_add_iff 2).mp
    exact hf2.congr fun m => (if_pos (show 2 ≤ m + 2 by omega)).symm
  have hsplit2 : (∑' m : ℕ, if 2 ≤ m then f m else 0) = ∑' m : ℕ, f (m + 2) := by
    have h := hge.sum_add_tsum_nat_add 2
    have hstart : ∑ i ∈ Finset.range 2, (if 2 ≤ i then f i else 0) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, if_neg (show ¬ 2 ≤ 1 by omega),
        if_neg (show ¬ 2 ≤ 0 by omega), add_zero]
    rw [← h, hstart, zero_add]
    exact tsum_congr fun m => if_pos (show 2 ≤ m + 2 by omega)
  have key : (∑' m : ℕ, f (m + 1)) =
      -∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
    rw [← tsum_neg]
    exact tsum_congr fun m => by
      show -trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
        -(trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))
      rw [neg_div]
  have he1 : -∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
      -trace A + ∑' m : ℕ, f (m + 2) := by
    have hpeel : (∑' m : ℕ, f (m + 1)) = f 1 + ∑' m : ℕ, f (m + 2) := hf1.tsum_eq_zero_add
    have hf1' : f 1 = -trace A := by
      show -trace (A ^ 1) / ((1 : ℕ) : 𝕜) = -trace A
      rw [pow_one, Nat.cast_one, div_one]
    rw [← key, hpeel, hf1']
  have he2 : (∑' m : ℕ, fredholmDetTwoCoeff (-A) m * (1 : 𝕜) ^ m) =
      ∑' m : ℕ, f (m + 2) := by
    rw [tsum_congr fun m => by rw [hcoeff m, one_pow, mul_one], hsplit2]
  rw [fredholmDetOne_one_eq_exp_neg_tsum, he1, NormedSpace.exp_add,
    fredholmDetTwo_eq_exp_tsum, he2]

/-- **Simon's cyclicity** for the 1-regularized determinant: for Hilbert–Schmidt
`A, B`, `det₁(1 − zAB) = det₁(1 − zBA)` for every `z`.  The Plemelj series agree
termwise by `trace_pow_comp_comm`, so the (possibly non-summable) `tsum`s agree; no
disk hypothesis is needed. -/
theorem fredholmDetOne_cyclic {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) (z : 𝕜 /- [definition] -/ ) :
    fredholmDetOne (A ∘L B) (IsHilbertSchmidt.isTraceClass_comp hA hB) z =
      fredholmDetOne (B ∘L A) (IsHilbertSchmidt.isTraceClass_comp hB hA) z := by
  unfold fredholmDetOne
  have htsum : (∑' m : ℕ, z ^ (m + 1) * trace ((A ∘L B) ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) =
      ∑' m : ℕ, z ^ (m + 1) * trace ((B ∘L A) ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) :=
    tsum_congr fun m => by rw [trace_pow_comp_comm hA hB (by omega : 1 ≤ m + 1)]
  rw [htsum]

/--
  `1 − det₁(1−A) = tr A + R(A)` with
  `‖R(A)‖ ≤ (‖tr A‖ + ‖A‖₂²)²/2 · e^{‖tr A‖ + ‖A‖₂²} + ‖A‖₂²`.

Indeed `1 − exp(−S) = S + O(‖S‖² e^{‖S‖})` for the Plemelj sum `S = tr A + T`, and the
tail satisfies `‖T‖ ≤ ‖A‖₂²` by `norm_tsum_trace_pow_div_tail_le_of_le_half`. 
-/
theorem norm_one_sub_fredholmDetOne_one_sub_trace_le {A : E →L[𝕜] E /- [definition] -/ } (hA : IsTraceClass A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) (h2 : hsNorm A ≤ 1 / 2 /- [standing] -/ ) :
    ‖1 - fredholmDetOne A hA 1 - trace A‖ ≤
      (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (‖trace A‖ + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by
  rw [fredholmDetOne_one_eq_exp_neg_tsum]
  have hsplit := tsum_trace_pow_div_eq_trace_add_tail hA hz
  set T : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hTdef
  set S : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) with hSdef
  have hSeq : S = trace A + T := hsplit
  have hnormT : ‖T‖ ≤ hsNorm A ^ 2 := norm_tsum_trace_pow_div_tail_le_of_le_half hA hz h2
  have hnormS : ‖S‖ ≤ ‖trace A‖ + hsNorm A ^ 2 := by
    calc ‖S‖ = ‖trace A + T‖ := by rw [hSeq]
      _ ≤ ‖trace A‖ + ‖T‖ := norm_add_le _ _
      _ ≤ ‖trace A‖ + hsNorm A ^ 2 := add_le_add le_rfl hnormT
  have hexp : 1 - NormedSpace.exp (-S) - trace A
      = T - (NormedSpace.exp (-S) - 1 - (-S)) := by
    rw [hSeq]; ring
  rw [hexp]
  calc ‖T - (NormedSpace.exp (-S) - 1 - (-S))‖
      ≤ ‖T‖ + ‖NormedSpace.exp (-S) - 1 - (-S)‖ := norm_sub_le _ _
    _ ≤ hsNorm A ^ 2 + (‖-S‖ ^ 2 / 2 * Real.exp ‖-S‖) :=
        add_le_add hnormT (norm_exp_sub_one_sub_le (-S))
    _ = hsNorm A ^ 2 + (‖S‖ ^ 2 / 2 * Real.exp ‖S‖) := by rw [norm_neg]
    _ ≤ hsNorm A ^ 2 + ((‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2
        * Real.exp (‖trace A‖ + hsNorm A ^ 2)) := by
        apply add_le_add le_rfl
        have hnnS : 0 ≤ ‖S‖ := norm_nonneg _
        have hnnX : 0 ≤ ‖trace A‖ + hsNorm A ^ 2 :=
          add_nonneg (norm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _)
        have hsq : ‖S‖ ^ 2 / 2 ≤ (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 := by
          have hpow := pow_le_pow_left₀ hnnS hnormS 2
          linarith
        exact mul_le_mul hsq (Real.exp_le_exp.mpr hnormS) (Real.exp_nonneg _)
          (div_nonneg (pow_nonneg hnnX _) two_pos.le)
    _ = (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (‖trace A‖ + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by ring

end Determinant

section LipschitzTail

omit [CompleteSpace E] in
/-- Left composition distributes over a finite sum of operators. -/
theorem comp_sum {ι : Type* /- [definition] -/ } (s : Finset ι /- [definition] -/ ) (T : ι → E →L[𝕜] E /- [definition] -/ ) (A : E →L[𝕜] E /- [definition] -/ ) :
    A ∘L (∑ i ∈ s, T i) = ∑ i ∈ s, A ∘L T i := by
  ext x
  rw [ContinuousLinearMap.comp_apply, sum_apply, map_sum, sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
/-- The telescoping factorization of a difference of powers in the composition monoid:
`A ^ n - B ^ n = ∑_{i < n} (A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))`. -/
theorem sub_pow_eq_sum_comp (A B : E →L[𝕜] E /- [definition] -/ ) (n : ℕ /- [definition] -/ ) :
    A ^ n - B ^ n = ∑ i ∈ Finset.range n, (A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sub_self, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      have key : A ^ (n + 1) - B ^ (n + 1) = A ∘L (A ^ n - B ^ n) + (A - B) ∘L B ^ n := by
        rw [pow_succ', pow_succ']
        show A * A ^ n - B * B ^ n = A * (A ^ n - B ^ n) + (A - B) * B ^ n
        noncomm_ring
      have hsplit : (∑ i ∈ Finset.range (n + 1),
            (A ^ i) ∘L ((A - B) ∘L B ^ (n + 1 - 1 - i)))
          = (∑ i ∈ Finset.range n, (A ^ (i + 1)) ∘L ((A - B) ∘L B ^ (n - 1 - i))) +
              (A - B) ∘L B ^ n := by
        rw [Finset.sum_range_succ']
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by
            rw [show n + 1 - 1 - (i + 1) = n - 1 - i from by omega]
      rw [key, ih, comp_sum, hsplit]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [← ContinuousLinearMap.comp_assoc,
          show A ∘L A ^ i = A ^ (i + 1) from (pow_succ' A i).symm]

/-- The trace-of-power-difference bound: for Hilbert–Schmidt `A, B` with
`‖A‖₂, ‖B‖₂ ≤ R` and `n ≥ 2`,
`‖tr (A ^ n) − tr (B ^ n)‖ ≤ n · R ^ (n−1) · ‖A − B‖₂`.

Via the noncommutative telescoping `A^n − B^n = ∑_{i<n} A^i (A−B) B^{n−1−i}`
(`sub_pow_eq_sum_comp`), `norm_trace_comp_le` on each summand, and `hsNorm_pow_le`. -/
theorem norm_trace_sub_pow_le {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) {R : ℝ /- [definition] -/ } (hRA : hsNorm A ≤ R /- [standing] -/ ) (hRB : hsNorm B ≤ R /- [standing] -/ ) {n : ℕ /- [definition] -/ }
    (hn : 2 ≤ n /- [standing] -/ ) :
    ‖trace (A ^ n) - trace (B ^ n)‖ ≤ (n : ℝ) * R ^ (n - 1) * hsNorm (A - B) := by
  have hAB : IsHilbertSchmidt (A - B) := hA.sub hB
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hTC : ∀ i ∈ Finset.range n, IsTraceClass ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, Nat.sub_zero]
      show IsTraceClass ((1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)))
      rw [show (1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)) = (A - B) ∘L B ^ (n - 1) from
        one_mul _]
      exact hAB.isTraceClass_comp (hB.pow (by omega : 1 ≤ n - 1))
    · exact ⟨A ^ i, (A - B) ∘L B ^ (n - 1 - i), hA.pow hi0, hAB.comp_right _, rfl⟩
  have hbound : ∀ i ∈ Finset.range n,
      ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ ≤ R ^ (n - 1) * hsNorm (A - B) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, Nat.sub_zero]
      show ‖trace ((1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)))‖ ≤ _
      rw [show (1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)) = (A - B) ∘L B ^ (n - 1) from
        one_mul _]
      calc ‖trace ((A - B) ∘L B ^ (n - 1))‖
          ≤ hsNorm (A - B) * hsNorm (B ^ (n - 1)) :=
            norm_trace_comp_le hAB (hB.pow (by omega : 1 ≤ n - 1))
        _ ≤ hsNorm (A - B) * hsNorm B ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (hsNorm_pow_le hB (by omega : 1 ≤ n - 1))
              (hsNorm_nonneg _)
        _ ≤ hsNorm (A - B) * R ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hsNorm_nonneg _) hRB _)
              (hsNorm_nonneg _)
        _ = R ^ (n - 1) * hsNorm (A - B) := mul_comm _ _
    · rcases eq_or_lt_of_le (show i ≤ n - 1 by omega) with hi1 | hi1
      · rw [hi1]
        have hb0 : (A - B) ∘L B ^ (n - 1 - (n - 1)) = A - B := by
          rw [show n - 1 - (n - 1) = 0 from by omega, pow_zero]
          show (A - B) ∘L (1 : E →L[𝕜] E) = A - B
          exact mul_one _
        rw [hb0]
        calc ‖trace ((A ^ (n - 1)) ∘L (A - B))‖
            ≤ hsNorm (A ^ (n - 1)) * hsNorm (A - B) :=
              norm_trace_comp_le (hA.pow (by omega : 1 ≤ n - 1)) hAB
          _ ≤ hsNorm A ^ (n - 1) * hsNorm (A - B) :=
              mul_le_mul_of_nonneg_right (hsNorm_pow_le hA (by omega : 1 ≤ n - 1))
                (hsNorm_nonneg _)
          _ ≤ R ^ (n - 1) * hsNorm (A - B) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hsNorm_nonneg _) hRA _)
                (hsNorm_nonneg _)
      · have hj : 1 ≤ n - 1 - i := by omega
        calc ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖
            ≤ hsNorm (A ^ i) * hsNorm ((A - B) ∘L B ^ (n - 1 - i)) :=
              norm_trace_comp_le (hA.pow hi0) (hAB.comp_right _)
          _ ≤ hsNorm A ^ i * (hsNorm (A - B) * hsNorm (B ^ (n - 1 - i))) :=
              mul_le_mul (hsNorm_pow_le hA hi0) (hsNorm_comp_le hAB (hB.pow hj))
                (hsNorm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _)
          _ ≤ hsNorm A ^ i * (hsNorm (A - B) * hsNorm B ^ (n - 1 - i)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hsNorm_pow_le hB hj) (hsNorm_nonneg _))
                (pow_nonneg (hsNorm_nonneg _) _)
          _ ≤ R ^ i * (hsNorm (A - B) * R ^ (n - 1 - i)) :=
              mul_le_mul (pow_le_pow_left₀ (hsNorm_nonneg _) hRA _)
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hsNorm_nonneg _) hRB _)
                  (hsNorm_nonneg _))
                (mul_nonneg (hsNorm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _))
                (pow_nonneg hR0 _)
          _ = R ^ (n - 1) * hsNorm (A - B) := by
              rw [mul_left_comm, ← pow_add, show i + (n - 1 - i) = n - 1 from by omega,
                mul_comm]
  have htr : trace (A ^ n) - trace (B ^ n) =
      ∑ i ∈ Finset.range n, trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))) := by
    rw [← trace_sub (hA.isTraceClass_pow hn) (hB.isTraceClass_pow hn),
      sub_pow_eq_sum_comp A B n,
      trace_sum _ fun i hi => summable_inner_diagonal (hTC i hi) _]
  calc ‖trace (A ^ n) - trace (B ^ n)‖
      = ‖∑ i ∈ Finset.range n, trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ := by rw [htr]
    _ ≤ ∑ i ∈ Finset.range n, ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, R ^ (n - 1) * hsNorm (A - B) := Finset.sum_le_sum hbound
    _ = (n : ℝ) * R ^ (n - 1) * hsNorm (A - B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]

/-- The tail of the absolute `z = 1` Plemelj series is summable for a Hilbert–Schmidt
operator (all powers `A ^ (m + 2)` are trace class by `IsHilbertSchmidt.isTraceClass_pow`,
so no trace-class hypothesis on `A` is needed). -/
theorem summable_norm_trace_pow_div_tail_of_hs {A : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := by
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
    ((summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left (hsNorm A ^ 2))
  calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
          (norm_trace_pow_le hA (show 2 ≤ m + 2 by omega))
    _ ≤ hsNorm A ^ (m + 2) :=
        div_le_self (pow_nonneg (hsNorm_nonneg _) _)
          (by exact_mod_cast (show 1 ≤ m + 2 by omega))
    _ = hsNorm A ^ 2 * hsNorm A ^ m := by
        rw [show m + 2 = 2 + m from by omega, pow_add]

/-- The tail of the `z = 1` Plemelj series (indices `m ≥ 2`) is summable for a
Hilbert–Schmidt operator. -/
theorem summable_trace_pow_div_tail_of_hs {A : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) : Summable fun m : ℕ => trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  apply Summable.of_norm
  exact (summable_norm_trace_pow_div_tail_of_hs hA hz).congr fun m => by
    rw [norm_div, RCLike.norm_natCast]

/-- The tail of the absolute `z = 1` Plemelj series of a Hilbert–Schmidt operator:
`∑'_{m ≥ 2} ‖tr(A^m)‖/m ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem tsum_norm_trace_pow_div_tail_le_of_hs {A : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have bound : ∀ m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
    intro m
    calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
            (norm_trace_pow_le hA (show 2 ≤ m + 2 by omega))
      _ ≤ hsNorm A ^ (m + 2) / 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (hsNorm_nonneg _) _) (by norm_num)
            (by exact_mod_cast (show 2 ≤ m + 2 by omega))
      _ = (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
          rw [show m + 2 = 2 + m from by omega, pow_add, div_mul_eq_mul_div]
  have h1 : Summable fun m : ℕ => (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
    (summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left _
  calc ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ ∑' m : ℕ, (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
        (summable_norm_trace_pow_div_tail_of_hs hA hz).tsum_le_tsum bound h1
    _ = (hsNorm A ^ 2 / 2) * ∑' m : ℕ, hsNorm A ^ m := by rw [← tsum_mul_left]
    _ = (hsNorm A ^ 2 / 2) * (1 - hsNorm A)⁻¹ := by
        rw [tsum_geometric_of_lt_one (hsNorm_nonneg A) hz]
    _ = hsNorm A ^ 2 / (2 * (1 - hsNorm A)) :=
        (div_eq_mul_inv _ _).symm.trans (div_div _ _ _)

/-- The norm of the tail of the `z = 1` Plemelj series of a Hilbert–Schmidt operator:
`‖∑'_{m ≥ 2} tr(A^m)/m‖ ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem norm_tsum_trace_pow_div_tail_le_of_hs {A : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hz : hsNorm A < 1 /- [standing] -/ ) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hsumnorm : Summable fun m : ℕ => ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    (summable_norm_trace_pow_div_tail_of_hs hA hz).congr fun m => by
      rw [norm_div, RCLike.norm_natCast]
  calc ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := tsum_congr fun m => by
        rw [norm_div, RCLike.norm_natCast]
    _ ≤ hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := tsum_norm_trace_pow_div_tail_le_of_hs hA hz

/-- **D5 (rescoped).**  The `m ≥ 2` Plemelj tail series — equivalently, by
`fredholmDetOne_eq_exp_neg_trace_mul_detTwo`, minus the `det₂` exponent series of `−A`
at `z = 1` — is Hilbert–Schmidt Lipschitz on the disk: for Hilbert–Schmidt `A, B` with
`‖A‖₂, ‖B‖₂ ≤ R < 1`, -/
theorem norm_trace_pow_div_tail_sub_le {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) {R : ℝ /- [definition] -/ } (hRA : hsNorm A ≤ R /- [standing] -/ ) (hRB : hsNorm B ≤ R /- [standing] -/ )
    (hR : R < 1 /- [standing] -/ ) :
    ‖(∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)) -
        ∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      R / (1 - R) * hsNorm (A - B) := by
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hA1 : hsNorm A < 1 := hRA.trans_lt hR
  have hB1 : hsNorm B < 1 := hRB.trans_lt hR
  have hsA := summable_trace_pow_div_tail_of_hs hA hA1
  have hsB := summable_trace_pow_div_tail_of_hs hB hB1
  have hgeo : Summable fun m : ℕ => R ^ (m + 1) * hsNorm (A - B) :=
    (((summable_geometric_of_lt_one hR0 hR).mul_left R).congr fun m =>
      (pow_succ' R m).symm).mul_right _
  have hbound : ∀ m : ℕ,
      ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) - trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
        ≤ R ^ (m + 1) * hsNorm (A - B) := by
    intro m
    rw [← sub_div, norm_div, RCLike.norm_natCast]
    have h := norm_trace_sub_pow_le hA hB hRA hRB (n := m + 2) (show 2 ≤ m + 2 by omega)
    have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc ‖trace (A ^ (m + 2)) - trace (B ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ ((m + 2 : ℕ) * R ^ (m + 1) * hsNorm (A - B)) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (by omega))).2 h
      _ = R ^ (m + 1) * hsNorm (A - B) := by
          rw [mul_assoc, mul_div_cancel_left₀ _ hm2]
  have hsumnorm : Summable fun m : ℕ =>
      ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) - trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound hgeo
  rw [← Summable.tsum_sub hsA hsB]
  calc ‖∑' m : ℕ, (trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) -
          trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜))‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) -
          trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' m : ℕ, R ^ (m + 1) * hsNorm (A - B) := hsumnorm.tsum_le_tsum hbound hgeo
    _ = hsNorm (A - B) * R * ∑' m : ℕ, R ^ m := by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => by rw [pow_succ']; ring
    _ = hsNorm (A - B) * R * (1 - R)⁻¹ := by
        rw [tsum_geometric_of_lt_one hR0 hR]
    _ = R / (1 - R) * hsNorm (A - B) := by rw [div_eq_mul_inv]; ring

/-- The exponential of the `m ≥ 2` Plemelj tail is Hilbert–Schmidt Lipschitz on the
disk: for Hilbert–Schmidt `A, B` with `‖A‖₂, ‖B‖₂ ≤ R < 1`, writing
`S̃(A) = ∑'_{m ≥ 2} tr(A^m)/m`, -/
theorem norm_exp_neg_trace_pow_div_tail_sub_le {A B : E →L[𝕜] E /- [definition] -/ } (hA : IsHilbertSchmidt A /- [standing] -/ )
    (hB : IsHilbertSchmidt B /- [standing] -/ ) {R : ℝ /- [definition] -/ } (hRA : hsNorm A ≤ R /- [standing] -/ ) (hRB : hsNorm B ≤ R /- [standing] -/ )
    (hR : R < 1 /- [standing] -/ ) :
    ‖NormedSpace.exp (-∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)) -
        NormedSpace.exp (-∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜))‖ ≤
      Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
        ((R / (1 - R) * hsNorm (A - B)) * Real.exp (R / (1 - R) * hsNorm (A - B))) := by
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hA1 : hsNorm A < 1 := hRA.trans_lt hR
  have hB1 : hsNorm B < 1 := hRB.trans_lt hR
  set SA : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hSA
  set SB : 𝕜 := ∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hSB
  have hSBA : ‖SA - SB‖ ≤ R / (1 - R) * hsNorm (A - B) :=
    norm_trace_pow_div_tail_sub_le hA hB hRA hRB hR
  have hSBn : ‖SB‖ ≤ hsNorm B ^ 2 / (2 * (1 - hsNorm B)) :=
    norm_tsum_trace_pow_div_tail_le_of_hs hB hB1
  have hD0 : 0 ≤ R / (1 - R) * hsNorm (A - B) :=
    mul_nonneg (div_nonneg hR0 (by linarith)) (hsNorm_nonneg _)
  have hfact : NormedSpace.exp (-SA) - NormedSpace.exp (-SB) =
      NormedSpace.exp (-SB) * (NormedSpace.exp (SB - SA) - 1) := by
    have h1 : NormedSpace.exp (-SB) * NormedSpace.exp (SB - SA) = NormedSpace.exp (-SA) := by
      rw [← NormedSpace.exp_add]
      congr 1
      ring
    rw [← h1]
    ring
  rw [hfact, norm_mul]
  have h2 := norm_exp_sub_one_le (SB - SA)
  rw [show ‖SB - SA‖ = ‖SA - SB‖ from norm_sub_rev _ _] at h2
  have h1 : ‖NormedSpace.exp (-SB)‖ ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) :=
    (norm_exp_le _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hSBn))
  calc ‖NormedSpace.exp (-SB)‖ * ‖NormedSpace.exp (SB - SA) - 1‖
      ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
          (‖SA - SB‖ * Real.exp ‖SA - SB‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
          ((R / (1 - R) * hsNorm (A - B)) * Real.exp (R / (1 - R) * hsNorm (A - B))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hSBA (Real.exp_le_exp.mpr hSBA) (Real.exp_nonneg _) hD0)
          (Real.exp_nonneg _)

end LipschitzTail


end source16

noncomputable section source17
/- Developed by the author. -/
open Complex
/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/

/-! # The Airy kernel operator on `L²((0, ∞))`

The Airy kernel is the integral kernel

  `K(x, y) = ∫₀^∞ Ai(x + u) Ai(y + u) du`
           `= (Ai(x) Ai'(y) - Ai'(x) Ai(y)) / (x - y)`    (`x ≠ y`),

acting on `L²((s, ∞))`.  Its square-root factor is the **Airy–Hankel operator** `T_s`
with kernel `Ai(x + t)` on `(s, ∞) × (0, ∞)`; the Airy kernel operator is the product
`K_s = T_s T_s*`, hence trace class, and its Hilbert–Schmidt norm tends to `0` as
`s → ∞`.

## Main results

* `airyAiReal_abs_le_exp`: a global exponential bound `|Ai(u)| ≤ C e^{-u}` on the whole
  real line (from the `ℝ₋` bound `airyAiReal_abs_le_nonpos`, compactness on `[0, 9/4]`,
  and the super-exponential decay `airyAiReal_le` for `u ≥ 9/4`).
* `airyHankelKernel`, `memLp_airyHankelKernel`, `eLpNorm_airyHankelKernel_le`: the
  truncated kernel `Ai(x + t) 1_{s < x}` is in `L²(ν × ν)` (where `ν` is Lebesgue
  measure on `(0, ∞)`), with the decay `‖K̃_s‖_{L²} ≤ (C/2) e^{-s}` for `s ≥ 0`.
* `airyHankel`, `isHilbertSchmidt_airyHankel`, `tendsto_hsENorm_airyHankel`: the
  Airy–Hankel operator on `L²(ν)` is Hilbert–Schmidt with `‖T_s‖_HS → 0`.
* `airyKernelOp`, `isTraceClass_airyKernelOp`, `tendsto_hsENorm_airyKernelOp`: the Airy
  kernel operator `K_s = T_s T_s*` is trace class with `‖K_s‖_HS → 0`.
* `airyAiReal_sq_integral` (the energy identity) and `airyKernelWronskian`: the closed
  Wronskian form of the Airy kernel, from the energy derivative identity
  `E'(t) = -Ai(t)²` for `E(t) = Ai'(t)² - t Ai(t)²`.
* `continuous_airyKernelIntegral`: continuity of `(x, y) ↦ ∫₀^∞ Ai(x+u) Ai(y+u) du`.

## Notation

`ν` (`halfLineMeasure`) is Lebesgue measure restricted to `(0, ∞)`.
-/

open MeasureTheory Filter Complex
open scoped ENNReal Topology InnerProduct


/-- Lebesgue measure restricted to the positive half-line `(0, ∞)`: the ambient measure
of the Hilbert space `L²(ν)` on which the Airy kernel operator acts. -/
noncomputable abbrev halfLineMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioi 0)

section GlobalBound

/-- A global exponential bound for the real Airy function: `|Ai(u)| ≤ C e^{-u}` for all
`u : ℝ`.  Three regions: `u ≤ 0` uses the boundedness of `Ai` on `ℝ₋`
(`airyAiReal_abs_le_nonpos`), `0 ≤ u ≤ 9/4` uses compactness, and `u ≥ 9/4` uses the
super-exponential decay `airyAiReal_le`, where `(2/3) u^{3/2} ≥ u`. -/
theorem airyAiReal_abs_le_exp : ∃ C : ℝ, ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hC₀nn : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0 le_rfl)
  have hC₁nn : 0 ≤ C₁ := by
    have h1 := hC₁ 1 le_rfl
    rw [Real.one_rpow, Real.one_rpow, mul_one] at h1
    have hpos : (0 : ℝ) < airyAiReal 1 := airyAiReal_pos_of_nonneg zero_le_one
    exact le_of_lt (pos_of_mul_pos_left (hpos.trans_le h1) (Real.exp_pos _).le)
  have hcont : Continuous airyAiReal :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (0:ℝ) ≤ 9/4)) hcont.abs.continuousOn
  set M := |airyAiReal x₀| with hM_def
  have hMnn : 0 ≤ M := abs_nonneg _
  have hM : ∀ u ∈ Set.Icc 0 (9/4), |airyAiReal u| ≤ M := fun u hu => hmax hu
  refine ⟨max (max C₀ (M * Real.exp (9/4))) C₁, fun u => ?_⟩
  rcases le_total u 0 with hu | hu
  · -- `u ≤ 0`: `|Ai u| ≤ C₀ ≤ C₀ e^{-u}` since `e^{-u} ≥ 1`.
    have h1 : (1 : ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    calc |airyAiReal u| ≤ C₀ := hC₀ u hu
      _ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * Real.exp (-u) := mul_le_mul_of_nonneg_left h1 hC₀nn
      _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _))
            (Real.exp_pos _).le
  · by_cases hu2 : u ≤ 9/4
    · -- `0 ≤ u ≤ 9/4`: the compactness bound, inflated by `e^{9/4}`.
      have h1 : (1 : ℝ) ≤ Real.exp (9/4 - u) := Real.one_le_exp (by linarith)
      calc |airyAiReal u| ≤ M := hM u ⟨hu, hu2⟩
        _ = M * 1 := (mul_one M).symm
        _ ≤ M * Real.exp (9/4 - u) := mul_le_mul_of_nonneg_left h1 hMnn
        _ = (M * Real.exp (9/4)) * Real.exp (-u) := by
            rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv, ← Real.exp_neg]
            ring
        _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
              (Real.exp_pos _).le
    · -- `u > 9/4`: the super-exponential decay dominates `e^{-u}`.
      have hu2' : 9/4 < u := lt_of_not_ge hu2
      have hAipos : 0 < airyAiReal u := airyAiReal_pos_of_nonneg (by linarith)
      rw [abs_of_pos hAipos]
      have hu1 : (1 : ℝ) ≤ u := by linarith
      have hu0 : (0 : ℝ) < u := by linarith
      have hr1 : u ^ (-1/4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
      have hsqrt : (3 : ℝ)/2 ≤ Real.sqrt u := by
        have h94 : Real.sqrt (9/4 : ℝ) = 3/2 := by
          have h : (9/4 : ℝ) = (3/2)^2 := by norm_num
          rw [h, Real.sqrt_sq (by norm_num)]
        have h2 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 9/4) hu2'
        rw [h94] at h2
        exact h2.le
      have hr32 : u ^ (3/2 : ℝ) = Real.sqrt u * u := by
        rw [show (3/2 : ℝ) = 1/2 + 1 by norm_num, Real.rpow_add_one (ne_of_gt hu0),
          Real.sqrt_eq_rpow]
      have hexp : Real.exp (-(2/3 * u^(3/2:ℝ))) ≤ Real.exp (-u) := by
        apply Real.exp_le_exp.mpr
        rw [hr32]
        have h1 : (3:ℝ)/2 * u ≤ Real.sqrt u * u :=
          mul_le_mul_of_nonneg_right hsqrt hu0.le
        linarith
      calc airyAiReal u ≤ C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))) := hC₁ u hu1
        _ ≤ C₁ * 1 * Real.exp (-u) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr1 hC₁nn) hexp (Real.exp_pos _).le
              (mul_nonneg hC₁nn zero_le_one)
        _ = C₁ * Real.exp (-u) := by ring
        _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- A positive constant bounding `|Ai(u)|` by `C e^{-u}` globally. -/
theorem airyAiReal_abs_le_exp' :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u) := by
  obtain ⟨C, hC⟩ := airyAiReal_abs_le_exp
  have hCpos : 0 < C := by
    have h1 := hC 0
    rw [neg_zero, Real.exp_zero, mul_one] at h1
    exact (abs_pos.mpr (airyAiReal_pos_of_nonneg le_rfl).ne').trans_le h1
  exact ⟨C, hCpos, hC⟩

end GlobalBound

section OneDimIntegrals

/-- `(e^{-t})² = e^{-2t}`. -/
theorem exp_neg_sq (t : ℝ /- [definition] -/ ) : (Real.exp (-t))^2 = Real.exp (-(2*t)) := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- `e^{-2t}` is integrable on `(a, ∞)`. -/
theorem integrableOn_exp_neg_two_mul (a : ℝ /- [definition] -/ ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(2*t))) (Set.Ioi a) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi a) := integrableOn_exp_neg_Ioi a
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t))
      (volume.restrict (Set.Ioi a)) :=
    (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)), ‖Real.exp (-t)‖ ≤ Real.exp (-a) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have ht' : a < t := ht
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Integrable (fun t : ℝ => Real.exp (-t) * Real.exp (-t))
      (volume.restrict (Set.Ioi a)) := h1.bdd_mul hmeas hbound
  apply h2.congr (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp (-t) * Real.exp (-t) = Real.exp (-(2*t))
  rw [← Real.exp_add]
  ring_nf

/-- `∫_a^∞ e^{-2t} dt = e^{-2a} / 2`. -/
theorem integral_exp_neg_two_mul_Ioi (a : ℝ /- [definition] -/ ) :
    ∫ t in Set.Ioi a, Real.exp (-(2*t)) = Real.exp (-(2*a))/2 := by
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -Real.exp (-(2*x))/2) (Real.exp (-(2*x))) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => (2:ℝ) * x) 2 x := by
      simpa using (hasDerivAt_id' x).const_mul (2:ℝ)
    have h4 : HasDerivAt (fun x : ℝ => Real.exp (-(2*x))) (Real.exp (-(2*x)) * -2) x := by
      have h5 := (Real.hasDerivAt_exp (-(2*x))).comp x h2.neg
      exact h5
    have h6 := h4.neg.div_const 2
    convert! h6 using 1
    ring
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-(2*x))/2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-(2*x))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => (2:ℝ) * x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h0.neg.div_const 2
    simpa using h3
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => -Real.exp (-(2*x))/2) (f' := fun x : ℝ => Real.exp (-(2*x)))
    ((hF a).continuousAt.continuousWithinAt) (fun x _ => hF x)
    (integrableOn_exp_neg_two_mul a) hlim
  rw [hftc]
  ring

/-- The `lintegral` version: `∫⁻_a^∞ ofReal (e^{-2t}) = ofReal (e^{-2a} / 2)`. -/
theorem lintegral_exp_neg_two_mul_Ioi (a : ℝ /- [definition] -/ ) :
    ∫⁻ t in Set.Ioi a, ENNReal.ofReal (Real.exp (-(2*t))) =
      ENNReal.ofReal (Real.exp (-(2*a))/2) := by
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)), (0:ℝ) ≤ Real.exp (-(2*t)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_two_mul a) hnn,
    integral_exp_neg_two_mul_Ioi a]

end OneDimIntegrals

section HankelKernel

/-- `airyAiReal` is measurable (it is continuous). -/
theorem measurable_airyAiReal : Measurable airyAiReal :=
  (continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt).measurable

/-- The truncated Airy–Hankel kernel at level `s`: `K̃_s(x, t) = Ai(x + t)` for `x > s`,
`0` otherwise. -/
noncomputable def airyHankelKernel (s : ℝ /- [definition] -/ ) : ℝ × ℝ → ℝ :=
  fun p => if s < p.1 then airyAiReal (p.1 + p.2) else 0

/-- The cutoff set `{p | s < p.1}` is measurable. -/
theorem measurableSet_hankelCut (s : ℝ /- [definition] -/ ) : MeasurableSet {q : ℝ × ℝ | s < q.1} :=
  measurableSet_lt measurable_const measurable_fst

/-- The truncated Airy–Hankel kernel is measurable. -/
theorem measurable_airyHankelKernel (s : ℝ /- [definition] -/ ) : Measurable (airyHankelKernel s) :=
  Measurable.ite (measurableSet_hankelCut s)
    (measurable_airyAiReal.comp (measurable_fst.add measurable_snd)) measurable_const

/-- The squared dominating function for the Airy–Hankel kernel:
`F q = ofReal ((C e^{-(q.1 + q.2)})²)`. -/
noncomputable def hankelDom (C : ℝ /- [definition] -/ ) : ℝ × ℝ → ℝ≥0∞ :=
  fun q => ENNReal.ofReal ((C * Real.exp (-(q.1 + q.2)))^2)

/-- The squared dominating function is measurable. -/
theorem measurable_hankelDom (C : ℝ /- [definition] -/ ) : Measurable (hankelDom C) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_const.mul
      (Real.measurable_exp.comp (measurable_fst.add measurable_snd).neg)).pow_const 2)

/-- Pointwise domination: `‖K̃_s p‖ₑ² ≤ 1_{s < p.1} · ofReal ((C e^{-(p.1+p.2)})²)`. -/
theorem enorm_sq_airyHankelKernel_le {C : ℝ /- [definition] -/ } (_hCnn : 0 ≤ C /- [standing] -/ )
    (hC : ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u)  /- [standing] -/ ) (s : ℝ /- [definition] -/ ) (p : ℝ × ℝ /- [definition] -/ ) :
    ‖airyHankelKernel s p‖ₑ ^ 2 ≤
      ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p := by
  by_cases h : s < p.1
  · rw [Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | s < q.1} from h)]
    have hK : airyHankelKernel s p = airyAiReal (p.1 + p.2) := if_pos h
    rw [enorm_sq_eq_ofReal, hK, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hC _) 2)
  · rw [Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | s < q.1} from h)]
    have hK : airyHankelKernel s p = 0 := if_neg h
    rw [hK]
    simp

/-- The slice `lintegral` of the squared dominator:
`∫⁻ t in Ioi 0, ofReal ((C e^{-(x+t)})²) = ofReal (C² e^{-2x} / 2)`. -/
theorem lintegral_hankelDom_slice {C : ℝ /- [definition] -/ } (_hCnn : 0 ≤ C /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    ∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure = ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
  have h1 : ∀ t : ℝ, hankelDom C (x, t)
      = ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*t))) := by
    intro t
    show ENNReal.ofReal ((C * Real.exp (-(x + t)))^2) = _
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    congr 1
    rw [mul_pow, exp_neg_sq, show (2:ℝ) * (x + t) = 2*x + 2*t by ring, neg_add, Real.exp_add]
    ring
  have h2 : (∫⁻ t, ENNReal.ofReal (Real.exp (-(2*t))) ∂halfLineMeasure)
      = ENNReal.ofReal (Real.exp (-(2*(0:ℝ)))/2) := lintegral_exp_neg_two_mul_Ioi 0
  calc ∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure
      = ∫⁻ t, ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*t)))
          ∂halfLineMeasure := MeasureTheory.lintegral_congr h1
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x)))
          * ∫⁻ t, ENNReal.ofReal (Real.exp (-(2*t))) ∂halfLineMeasure :=
        MeasureTheory.lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp ((measurable_id'.const_mul 2).neg)))
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*(0:ℝ)))/2) := by
        rw [h2]
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
        congr 1
        rw [mul_zero, neg_zero, Real.exp_zero]
        ring

/-- `lintegral` over `ν` restricted further to `(s, ∞)` equals `lintegral` over
`(max s 0, ∞)`. -/
theorem setLIntegral_halfLineMeasure_Ioi (s : ℝ /- [definition] -/ ) (f : ℝ → ℝ≥0∞ /- [definition] -/ ) :
    ∫⁻ x in Set.Ioi s, f x ∂halfLineMeasure = ∫⁻ x in Set.Ioi (max s 0), f x := by
  show ∫⁻ x, f x ∂(halfLineMeasure.restrict (Set.Ioi s))
    = ∫⁻ x, f x ∂(volume.restrict (Set.Ioi (max s 0)))
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]

/-- The `L²`-norm computation for the dominating function: the `lintegral` of the squared
dominator over `{q | s < q.1}` equals `C² e^{-2 max(s, 0)} / 4`. -/
theorem lintegral_hankelDom_sq {C : ℝ /- [definition] -/ } (hCnn : 0 ≤ C /- [standing] -/ ) (s : ℝ /- [definition] -/ ) :
    ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
        ∂(halfLineMeasure.prod halfLineMeasure)
      = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) := by
  have hmeas : Measurable (({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C)) :=
    (measurable_hankelDom C).indicator (measurableSet_hankelCut s)
  calc ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
        ∂(halfLineMeasure.prod halfLineMeasure)
      = ∫⁻ x, ∫⁻ t, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
          ∂halfLineMeasure ∂halfLineMeasure :=
        MeasureTheory.lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ x, (Set.Ioi s).indicator
          (fun x' => ∫⁻ t, hankelDom C (x', t) ∂halfLineMeasure) x ∂halfLineMeasure := by
        apply MeasureTheory.lintegral_congr
        intro x
        by_cases hx : s < x
        · have h1 : ∀ t : ℝ, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
              = hankelDom C (x, t) := fun t =>
            Set.indicator_of_mem (show (x, t) ∈ {q : ℝ × ℝ | s < q.1} from hx) _
          rw [MeasureTheory.lintegral_congr h1,
            Set.indicator_of_mem (show x ∈ Set.Ioi s from hx) _]
        · have h1 : ∀ t : ℝ, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
              = 0 := fun t =>
            Set.indicator_of_notMem (show (x, t) ∉ {q : ℝ × ℝ | s < q.1} from hx) _
          rw [MeasureTheory.lintegral_congr h1, MeasureTheory.lintegral_zero,
            Set.indicator_of_notMem (show x ∉ Set.Ioi s from hx)]
    _ = ∫⁻ x in Set.Ioi s, (∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure) ∂halfLineMeasure :=
        MeasureTheory.lintegral_indicator measurableSet_Ioi _
    _ = ∫⁻ x in Set.Ioi s, ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) ∂halfLineMeasure := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
        exact fun x _ => lintegral_hankelDom_slice hCnn x
    _ = ∫⁻ x in Set.Ioi (max s 0), ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
        rw [setLIntegral_halfLineMeasure_Ioi s]
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) := by
        have h3 : ∀ x : ℝ, ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2)
            = ENNReal.ofReal (C^2/2) * ENNReal.ofReal (Real.exp (-(2*x))) := fun x => by
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C^2/2)]
          congr 1
          ring
        have h4 : (∫⁻ x in Set.Ioi (max s 0),
              ENNReal.ofReal (C^2/2) * ENNReal.ofReal (Real.exp (-(2*x))))
            = ENNReal.ofReal (C^2/2)
              * ∫⁻ x in Set.Ioi (max s 0), ENNReal.ofReal (Real.exp (-(2*x))) :=
          MeasureTheory.lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp ((measurable_id'.const_mul 2).neg)))
        rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi (fun x _ => h3 x), h4,
          lintegral_exp_neg_two_mul_Ioi (max s 0),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C^2/2)]
        congr 1
        ring

/-- The truncated Airy–Hankel kernel is square-integrable on `ν × ν`. -/
theorem memLp_airyHankelKernel (s : ℝ /- [definition] -/ ) :
    MemLp (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hlt : (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2 < ⊤ := by
    calc (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
        = ∫⁻ p, ‖airyHankelKernel s p‖ₑ ^ 2 ∂(halfLineMeasure.prod halfLineMeasure) :=
          eLpNorm_two_sq_eq_lintegral
            (measurable_airyHankelKernel s).aestronglyMeasurable
      _ ≤ ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
            ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.lintegral_mono (enorm_sq_airyHankelKernel_le hCpos.le hC s)
      _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) :=
          lintegral_hankelDom_sq hCpos.le s
      _ < ⊤ := ENNReal.ofReal_lt_top
  change eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure) < ⊤
  by_contra htop
  rw [lt_top_iff_ne_top, not_not] at htop
  rw [htop, ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0)] at hlt
  exact (lt_irrefl ⊤) hlt

/-- The quantitative decay of the kernel norm: for `s ≥ 0`,
`‖K̃_s‖_{L²(ν × ν)} ≤ (C/2) e^{-s}`. -/
theorem eLpNorm_airyHankelKernel_le {C : ℝ /- [definition] -/ } (hCnn : 0 ≤ C /- [standing] -/ )
    (hC : ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u)  /- [standing] -/ ) {s : ℝ /- [definition] -/ } (hs : 0 ≤ s /- [standing] -/ ) :
    eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)
      ≤ ENNReal.ofReal (C/2 * Real.exp (-s)) := by
  have hle : (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
      ≤ ENNReal.ofReal ((C/2 * Real.exp (-s))^2) := by
    calc (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
        = ∫⁻ p, ‖airyHankelKernel s p‖ₑ ^ 2 ∂(halfLineMeasure.prod halfLineMeasure) :=
          eLpNorm_two_sq_eq_lintegral
            (measurable_airyHankelKernel s).aestronglyMeasurable
      _ ≤ ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
            ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.lintegral_mono (enorm_sq_airyHankelKernel_le hCnn hC s)
      _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) :=
          lintegral_hankelDom_sq hCnn s
      _ = ENNReal.ofReal ((C/2 * Real.exp (-s))^2) := by
          congr 1
          rw [max_eq_left hs, mul_pow, div_pow, exp_neg_sq]
          ring
  calc eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)
      = ((eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2) ^ (1/2 : ℝ) :=
        (rpow_half_sq' _).symm
    _ ≤ (ENNReal.ofReal ((C/2 * Real.exp (-s))^2)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num : (0:ℝ) ≤ 1/2)
    _ = ((ENNReal.ofReal (C/2 * Real.exp (-s)))^2) ^ (1/2 : ℝ) := by
        rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ C/2 * Real.exp (-s)) 2]
    _ = ENNReal.ofReal (C/2 * Real.exp (-s)) := rpow_half_sq' _

end HankelKernel

section Operators

/-- The Airy–Hankel operator at level `s`: the integral operator on `L²(ν)` with kernel
`Ai(x + t)` for `x > s`.
Physical half-line interpretation requires s ≥ 0: the fixed source measure
discards negative x. For every real s use airyHankelShift/airyHankelGenuine. -/
noncomputable def airyHankel (s : ℝ /- [definition] -/ ) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  kernelOperator (memLp_airyHankelKernel s)

/-- The Airy–Hankel operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_airyHankel (s : ℝ /- [definition] -/ ) :
    IsHilbertSchmidt (airyHankel s) :=
  isHilbertSchmidt_kernelOperator (memLp_airyHankelKernel s)

/-- The Hilbert–Schmidt norm of the Airy–Hankel operator tends to `0` as `s → ∞`:
`‖T_s‖_HS ≤ (C/2) e^{-s}` for `s ≥ 0`. -/
theorem tendsto_hsENorm_airyHankel :
    Tendsto (fun s => hsENorm (airyHankel s)) atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ≥0∞))
    (h := fun s => ENNReal.ofReal (C/2 * Real.exp (-s)))
  · exact tendsto_const_nhds
  · have h0 : Tendsto (fun s : ℝ => C/2 * Real.exp (-s)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C/2)
      rwa [mul_zero] at h
    have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    rwa [ENNReal.ofReal_zero] at h1
  · exact Filter.Eventually.of_forall fun s => zero_le
  · filter_upwards [Filter.eventually_ge_atTop 0] with s hs
    exact (hsENorm_kernelOperator_le (memLp_airyHankelKernel s)).trans
      (eLpNorm_airyHankelKernel_le hCpos.le hC hs)

/-- The operator norm of the Airy–Hankel operator is bounded by its Hilbert–Schmidt
norm. -/
theorem enorm_airyHankel_le_hsENorm (s : ℝ /- [definition] -/ ) :
    ‖airyHankel s‖ₑ ≤ hsENorm (airyHankel s) :=
  opENorm_le_sumSq_rpow_half _ _

end Operators

section AiryKernelOperator

/-- The Airy kernel operator at level `s`: `K_s = T_s T_s*` on `L²(ν)`.
Physical half-line interpretation requires s ≥ 0; for every real s use
airyKernelShift/airyKernelGenuine, whose domains include negative cutoffs. -/
noncomputable def airyKernelOp (s : ℝ /- [definition] -/ ) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  airyHankel s ∘L (airyHankel s)†

/-- The Airy kernel operator is trace class (a product of two Hilbert–Schmidt
operators). -/
theorem isTraceClass_airyKernelOp (s : ℝ /- [definition] -/ ) : IsTraceClass (airyKernelOp s) :=
  ⟨airyHankel s, (airyHankel s)†, isHilbertSchmidt_airyHankel s,
    (isHilbertSchmidt_airyHankel s).adjoint, rfl⟩

/-- `‖K_s‖_HS ≤ ‖T_s‖_HS²`. -/
theorem hsENorm_airyKernelOp_le (s : ℝ /- [definition] -/ ) :
    hsENorm (airyKernelOp s)
      ≤ hsENorm (airyHankel s) * hsENorm (airyHankel s) :=
  (hsENorm_comp_le _ _).trans (by rw [hsENorm_adjoint])

/-- The Hilbert–Schmidt norm of the Airy kernel operator tends to `0` as `s → ∞`. -/
theorem tendsto_hsENorm_airyKernelOp :
    Tendsto (fun s => hsENorm (airyKernelOp s)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ≥0∞))
    (h := fun s => hsENorm (airyHankel s) * hsENorm (airyHankel s))
  · exact tendsto_const_nhds
  · have h := ENNReal.Tendsto.mul tendsto_hsENorm_airyHankel (Or.inr ENNReal.zero_ne_top)
      tendsto_hsENorm_airyHankel (Or.inr ENNReal.zero_ne_top)
    rwa [mul_zero] at h
  · exact Filter.Eventually.of_forall fun s => zero_le
  · exact Filter.Eventually.of_forall fun s => hsENorm_airyKernelOp_le s

end AiryKernelOperator

section Energy

/-- `Ai` is continuous (it is differentiable). -/
theorem continuous_airyAiReal : Continuous airyAiReal :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt

/-- `Ai` is differentiable everywhere, with derivative `deriv airyAiReal`. -/
theorem hasDerivAt_airyAiReal' (u : ℝ /- [definition] -/ ) : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
  have h := hasDerivAt_airyAiReal u
  rwa [← h.deriv] at h

/-- `Ai'` is continuous (it is differentiable). -/
theorem continuous_deriv_airyAiReal : Continuous (deriv airyAiReal) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_deriv_airyAiReal x).continuousAt

/-- The second derivative of `Ai` at a point, from the Airy ODE `Ai'' = x · Ai`. -/
theorem deriv_deriv_airyAiReal (u : ℝ /- [definition] -/ ) : deriv (deriv airyAiReal) u = u * airyAiReal u := by
  have h := iteratedDeriv_two_airyAiReal u
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  exact h

/-- The Airy energy `E(t) = Ai'(t)^2 - t·Ai(t)^2`, whose derivative is `-Ai(t)^2`. -/
noncomputable def airyEnergy (t : ℝ /- [definition] -/ ) : ℝ := (deriv airyAiReal t)^2 - t * (airyAiReal t)^2

/-- The energy derivative identity `E'(u) = -Ai(u)^2`: the cross terms cancel by the
Airy ODE. -/
theorem hasDerivAt_airyEnergy (u : ℝ /- [definition] -/ ) : HasDerivAt airyEnergy (-(airyAiReal u)^2) u := by
  show HasDerivAt (fun t => (deriv airyAiReal t)^2 - t * (airyAiReal t)^2)
    (-(airyAiReal u)^2) u
  have hAi : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
    have h := hasDerivAt_airyAiReal u
    rwa [← h.deriv] at h
  have hAi' : HasDerivAt (deriv airyAiReal) (u * airyAiReal u) u := by
    have h := hasDerivAt_deriv_airyAiReal u
    have hv : deriv (deriv airyAiReal) u = u * airyAiReal u := deriv_deriv_airyAiReal u
    rw [h.deriv] at hv
    rwa [hv] at h
  have h1 : HasDerivAt (fun t => (deriv airyAiReal t)^2)
      (deriv airyAiReal u * (u * airyAiReal u) + (u * airyAiReal u) * deriv airyAiReal u) u := by
    have h := hAi'.mul hAi'
    convert! h using 1
    · ext t
      exact sq (deriv airyAiReal t)
    · ring
  have hsq : HasDerivAt (fun t => (airyAiReal t)^2)
      (airyAiReal u * deriv airyAiReal u + deriv airyAiReal u * airyAiReal u) u := by
    have h := hAi.mul hAi
    convert! h using 1
    · ext t
      exact sq (airyAiReal t)
    · ring
  have h2 : HasDerivAt (fun t => t * (airyAiReal t)^2)
      (u * (airyAiReal u * deriv airyAiReal u + deriv airyAiReal u * airyAiReal u)
        + 1 * (airyAiReal u)^2) u := by
    have h := (hasDerivAt_id' u).mul hsq
    convert! h using 1
    ring
  exact (h1.sub h2).congr_deriv (by ring)

/-- The shifted energy derivative: `u ↦ E(x + u)` has derivative `-Ai(x + u)^2`. -/
theorem hasDerivAt_airyEnergy_comp_add (x u : ℝ /- [definition] -/ ) :
    HasDerivAt (fun t => airyEnergy (x + t)) (-(airyAiReal (x + u))^2) u := by
  have h := (hasDerivAt_airyEnergy (x + u)).comp u
    ((hasDerivAt_const u x).add (hasDerivAt_id' u))
  exact h.congr_deriv (by ring)

/-- `Ai²` is integrable on `(a, ∞)` (dominated by `C² e^{-2t}`). -/
theorem integrable_airyAiReal_sq_Ioi (a : ℝ /- [definition] -/ ) :
    IntegrableOn (fun t => (airyAiReal t)^2) (Set.Ioi a) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun t => (airyAiReal t)^2)
      (volume.restrict (Set.Ioi a)) :=
    (measurable_airyAiReal.pow_const 2).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)),
      ‖(airyAiReal t)^2‖ ≤ ‖C^2 * Real.exp (-(2*t))‖ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le), ← sq_abs]
    calc |airyAiReal t|^2 ≤ (C * Real.exp (-t))^2 := pow_le_pow_left₀ (abs_nonneg _) (hC t) 2
      _ = C^2 * Real.exp (-(2*t)) := by rw [mul_pow, exp_neg_sq]
  exact ((integrableOn_exp_neg_two_mul a).const_mul (C^2)).mono hmeas hbound

/-- The shifted square `u ↦ Ai(x + u)²` is integrable on `(0, ∞)`. -/
theorem integrable_airyAiReal_sq_comp_add_Ioi (x : ℝ /- [definition] -/ ) :
    IntegrableOn (fun u => (airyAiReal (x + u))^2) (Set.Ioi 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun u => (airyAiReal (x + u))^2)
      (volume.restrict (Set.Ioi 0)) :=
    ((measurable_airyAiReal.comp (measurable_const.add measurable_id')).pow_const
      2).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖(airyAiReal (x + u))^2‖ ≤ ‖C^2 * Real.exp (-(2*x)) * Real.exp (-(2*u))‖ := by
    apply Filter.Eventually.of_forall
    intro u
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le), ← sq_abs]
    calc |airyAiReal (x + u)|^2 ≤ (C * Real.exp (-(x + u)))^2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
      _ = C^2 * Real.exp (-(2*x)) * Real.exp (-(2*u)) := by
        rw [mul_pow, exp_neg_sq, show (2:ℝ) * (x + u) = 2*x + 2*u by ring, neg_add, Real.exp_add]
        ring
  exact ((integrableOn_exp_neg_two_mul 0).const_mul (C^2 * Real.exp (-(2*x)))).mono hmeas hbound

/-- The product `u ↦ Ai(x + u) Ai(y + u)` is integrable on `(0, ∞)`. -/
theorem integrable_airyAiReal_mul_Ioi (x y : ℝ /- [definition] -/ ) :
    IntegrableOn (fun u => airyAiReal (x + u) * airyAiReal (y + u)) (Set.Ioi 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun u => airyAiReal (x + u) * airyAiReal (y + u))
      (volume.restrict (Set.Ioi 0)) :=
    ((measurable_airyAiReal.comp (measurable_const.add measurable_id')).mul
      (measurable_airyAiReal.comp (measurable_const.add measurable_id'))).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖airyAiReal (x + u) * airyAiReal (y + u)‖
        ≤ ‖C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u))‖ := by
    apply Filter.Eventually.of_forall
    intro u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le)]
    calc |airyAiReal (x + u)| * |airyAiReal (y + u)|
        ≤ (C * Real.exp (-(x + u))) * (C * Real.exp (-(y + u))) :=
        mul_le_mul (hC _) (hC _) (abs_nonneg _) (mul_nonneg hCpos.le (Real.exp_pos _).le)
      _ = C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u)) := by
        rw [show C * Real.exp (-(x + u)) * (C * Real.exp (-(y + u)))
            = C^2 * (Real.exp (-(x + u)) * Real.exp (-(y + u))) by ring, ← Real.exp_add,
          show C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u))
            = C^2 * (Real.exp (-(x + y)) * Real.exp (-(2*u))) by ring, ← Real.exp_add]
        congr 1
        ring_nf
  exact ((integrableOn_exp_neg_two_mul 0).const_mul (C^2 * Real.exp (-(x + y)))).mono hmeas
    hbound

/-- The energy has a limit at infinity: `E(t) → E(0) - ∫₀^∞ Ai²`. -/
theorem airyEnergy_tendsto_nhds : ∃ L : ℝ, Tendsto airyEnergy atTop (𝓝 L) := by
  refine ⟨airyEnergy 0 + ∫ t in Set.Ioi 0, (-(airyAiReal t)^2), ?_⟩
  have hint : IntegrableOn (fun t => -(airyAiReal t)^2) (Set.Ioi 0) :=
    (integrable_airyAiReal_sq_Ioi 0).neg
  have h1 : Tendsto (fun t : ℝ => ∫ x in (0:ℝ)..t, (-(airyAiReal x)^2)) atTop
      (𝓝 (∫ x in Set.Ioi 0, (-(airyAiReal x)^2))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine (tendsto_const_nhds.add h1).congr fun t => ?_
  have hftc : ∫ x in (0:ℝ)..t, (-(airyAiReal x)^2) = airyEnergy t - airyEnergy 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyEnergy u)
      ((continuous_airyAiReal.pow 2).neg.intervalIntegrable 0 t)
  rw [hftc]
  ring

/-- The energy tends to `0` at infinity.  The limit `L` exists by
`airyEnergy_tendsto_nhds`; `L ≥ 0` since `(Ai'(t))² → L`; and `L > 0` would force
`Ai'` to keep a constant sign of magnitude `≥ √(L/2)` eventually (by continuity and the
intermediate value theorem), which is incompatible with `Ai(t) → 0`. -/
theorem airyEnergy_tendsto_zero : Tendsto airyEnergy atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  obtain ⟨L, hL⟩ := airyEnergy_tendsto_nhds
  -- `t · Ai(t)² → 0`, by `0 ≤ t Ai(t)² ≤ C² e^{-t}` for `t ≥ 0`.
  have htwist : Tendsto (fun t : ℝ => t * (airyAiReal t)^2) atTop (𝓝 0) := by
    apply squeeze_zero'
      (by filter_upwards [Filter.eventually_ge_atTop 0] with t ht
          exact mul_nonneg ht (sq_nonneg _))
      (by filter_upwards [Filter.eventually_ge_atTop 0] with t ht
          calc t * (airyAiReal t)^2 = t * |airyAiReal t|^2 := by rw [sq_abs]
            _ ≤ t * (C * Real.exp (-t))^2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hC t) 2) ht
            _ = C^2 * (t * Real.exp (-(2*t))) := by rw [mul_pow, exp_neg_sq]; ring
            _ ≤ C^2 * Real.exp (-t) := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
              have h1 : t ≤ Real.exp t :=
                (by linarith : t ≤ t + 1).trans (Real.add_one_le_exp t)
              calc t * Real.exp (-(2*t)) ≤ Real.exp t * Real.exp (-(2*t)) :=
                  mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
                _ = Real.exp (-t) := by rw [← Real.exp_add]; ring_nf)
      (by have h := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (C^2)
          rwa [mul_zero] at h)
  -- `(Ai'(t))² = E(t) + t Ai(t)² → L`, hence `L ≥ 0`.
  have hlim2 : Tendsto (fun t : ℝ => (deriv airyAiReal t)^2) atTop (𝓝 L) := by
    have h : Tendsto (fun t => airyEnergy t + t * (airyAiReal t)^2) atTop (𝓝 (L + 0)) :=
      hL.add htwist
    rw [add_zero] at h
    exact h.congr fun t => by
      show (deriv airyAiReal t)^2 - t * (airyAiReal t)^2 + t * (airyAiReal t)^2
        = (deriv airyAiReal t)^2
      ring
  have hLge : (0:ℝ) ≤ L :=
    ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun t => sq_nonneg (deriv airyAiReal t))
  -- `L ≤ 0`: otherwise `Ai'` keeps one sign of magnitude `≥ √(L/2)` eventually.
  have hLle : L ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hc_pos : (0:ℝ) < Real.sqrt (L/2) := Real.sqrt_pos_of_pos (by linarith)
    have hev : ∀ᶠ t in atTop, L / 2 < (deriv airyAiReal t)^2 :=
      hlim2.eventually (Ioi_mem_nhds (show L / 2 < L by linarith))
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hev
    set B₀ := max B 0 with hB₀
    have hc_lt : ∀ t, B₀ ≤ t → Real.sqrt (L/2) < |deriv airyAiReal t| := by
      intro t ht
      have h1 : L / 2 < (deriv airyAiReal t)^2 := hB t (le_trans (le_max_left _ _) ht)
      have h2 : Real.sqrt (L / 2) < Real.sqrt ((deriv airyAiReal t)^2) :=
        Real.sqrt_lt_sqrt (by linarith) h1
      rwa [Real.sqrt_sq_eq_abs] at h2
    have hsign : (∀ t, B₀ ≤ t → Real.sqrt (L/2) < deriv airyAiReal t)
        ∨ (∀ t, B₀ ≤ t → deriv airyAiReal t < -Real.sqrt (L/2)) := by
      by_contra h
      push Not at h
      obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := h
      have h₁' : deriv airyAiReal t₁ < -Real.sqrt (L/2) := by
        have h := hc_lt t₁ ht₁
        rcases lt_abs.mp h with h' | h'
        · linarith
        · linarith
      have h₂' : Real.sqrt (L/2) < deriv airyAiReal t₂ := by
        have h := hc_lt t₂ ht₂
        rcases lt_abs.mp h with h' | h'
        · exact h'
        · linarith
      rcases le_total t₁ t₂ with hle | hle
      · have hivt := intermediate_value_Icc hle continuous_deriv_airyAiReal.continuousOn
        have h0 : (0:ℝ) ∈ Set.Icc (deriv airyAiReal t₁) (deriv airyAiReal t₂) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨ξ, hξ, hξ0⟩ := hivt h0
        have := hc_lt ξ (le_trans ht₁ hξ.1)
        rw [hξ0, abs_zero] at this
        exact absurd this (not_lt.mpr hc_pos.le)
      · have hivt := intermediate_value_Icc' hle continuous_deriv_airyAiReal.continuousOn
        have h0 : (0:ℝ) ∈ Set.Icc (deriv airyAiReal t₁) (deriv airyAiReal t₂) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨ξ, hξ, hξ0⟩ := hivt h0
        have := hc_lt ξ (le_trans ht₂ hξ.1)
        rw [hξ0, abs_zero] at this
        exact absurd this (not_lt.mpr hc_pos.le)
    -- `Ai(t) → 0` as `t → ∞` (squeezed against `C e^{-t}`).
    have hAi0 : Tendsto airyAiReal atTop (𝓝 0) := by
      have hbound : ∀ᶠ u in atTop, ‖airyAiReal u‖ ≤ C * Real.exp (-u) :=
        Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs]
          exact hC u
      apply squeeze_zero_norm' hbound
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C
      rwa [mul_zero] at h
    rcases hsign with hgt | hlt
    · -- case `Ai' > √(L/2)` eventually: `Ai` grows without bound, contradicting `Ai → 0`.
      have hmono : ∀ t, B₀ ≤ t → airyAiReal B₀ + Real.sqrt (L/2) * (t - B₀)
          ≤ airyAiReal t := by
        intro t ht
        have hftc : ∫ u in B₀..t, deriv airyAiReal u = airyAiReal t - airyAiReal B₀ :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyAiReal' u)
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
        have hle : Real.sqrt (L/2) * (t - B₀) ≤ ∫ u in B₀..t, deriv airyAiReal u := by
          have hconst : ∫ u in B₀..t, (Real.sqrt (L/2) : ℝ) = Real.sqrt (L/2) * (t - B₀) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          rw [← hconst]
          apply intervalIntegral.integral_mono_on ht intervalIntegrable_const
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
          intro u hu
          exact le_of_lt (hgt u hu.1)
        rw [hftc] at hle
        linarith
      have htend : Tendsto (fun t : ℝ => airyAiReal B₀ + Real.sqrt (L/2) * (t - B₀))
          atTop atTop := by
        have hbase : Tendsto (fun t : ℝ => t - B₀) atTop atTop :=
          (tendsto_atTop_add_const_right atTop (-B₀) tendsto_id).congr
            (fun t => by simp only [id_eq]; ring)
        exact tendsto_atTop_add_const_left atTop (airyAiReal B₀)
          (Filter.Tendsto.const_mul_atTop hc_pos hbase)
      obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (((htend.eventually (Filter.eventually_gt_atTop 1)).and
        (hAi0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))).and
        (Filter.eventually_ge_atTop B₀)).exists
      have := hmono t h3
      linarith
    · -- case `Ai' < -√(L/2)` eventually: `Ai → -∞`, contradicting `Ai → 0`.
      have hanti : ∀ t, B₀ ≤ t → airyAiReal t
          ≤ airyAiReal B₀ - Real.sqrt (L/2) * (t - B₀) := by
        intro t ht
        have hftc : ∫ u in B₀..t, deriv airyAiReal u = airyAiReal t - airyAiReal B₀ :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyAiReal' u)
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
        have hle : ∫ u in B₀..t, deriv airyAiReal u ≤ -Real.sqrt (L/2) * (t - B₀) := by
          have hconst : ∫ u in B₀..t, (-Real.sqrt (L/2) : ℝ) = -Real.sqrt (L/2) * (t - B₀) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          rw [← hconst]
          apply intervalIntegral.integral_mono_on ht
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t) intervalIntegrable_const
          intro u hu
          exact le_of_lt (hlt u hu.1)
        rw [hftc] at hle
        linarith
      have htend : Tendsto (fun t : ℝ => airyAiReal B₀ - Real.sqrt (L/2) * (t - B₀))
          atTop atBot := by
        have hbase : Tendsto (fun t : ℝ => t - B₀) atTop atTop :=
          (tendsto_atTop_add_const_right atTop (-B₀) tendsto_id).congr
            (fun t => by simp only [id_eq]; ring)
        have h2 := Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -Real.sqrt (L/2) < 0)
          hbase
        have h3 := tendsto_atBot_add_const_left atTop (airyAiReal B₀) h2
        exact h3.congr fun t => by ring
      obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (((htend.eventually (Iio_mem_atBot (-1))).and
        (hAi0.eventually (Ioi_mem_nhds (by norm_num : (-1:ℝ) < 0)))).and
        (Filter.eventually_ge_atTop B₀)).exists
      have := hanti t h3
      linarith
  -- hence `L = 0`.
  have hL0 : L = 0 := le_antisymm hLle hLge
  rwa [hL0] at hL

/-- The energy identity (the diagonal case of the Airy kernel closed form):
`∫₀^∞ Ai(x + u)² du = Ai'(x)² - x Ai(x)²`. -/
theorem airyAiReal_sq_integral (x : ℝ /- [definition] -/ ) :
    ∫ u in Set.Ioi 0, (airyAiReal (x + u))^2
      = (deriv airyAiReal x)^2 - x * (airyAiReal x)^2 := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u => -airyEnergy (x + u)) ((airyAiReal (x + u))^2) u := by
    intro u
    have h := (hasDerivAt_airyEnergy_comp_add x u).neg
    rwa [neg_neg] at h
  have hT : Tendsto (fun u => -airyEnergy (x + u)) atTop (𝓝 0) := by
    have h := airyEnergy_tendsto_zero.comp (tendsto_atTop_add_const_left atTop x tendsto_id)
    have h2 := h.neg
    rwa [neg_zero] at h2
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => -airyEnergy (x + u)) (f' := fun u : ℝ => (airyAiReal (x + u))^2)
    ((hF 0).continuousAt.continuousWithinAt) (fun u _ => hF u)
    (integrable_airyAiReal_sq_comp_add_Ioi x) hT
  rw [hftc, add_zero]
  show 0 - -((deriv airyAiReal x)^2 - x * (airyAiReal x)^2)
    = (deriv airyAiReal x)^2 - x * (airyAiReal x)^2
  ring

end Energy


end source17

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace


noncomputable abbrev halfLineShiftMeasure (s : ℝ /- [definition] -/) : Measure ℝ :=
  volume.restrict (Ioi s)

theorem measurePreserving_shift_add (s : ℝ /- [definition] -/) :
    MeasurePreserving (fun x : ℝ => x + s) (halfLineShiftMeasure 0)
      (halfLineShiftMeasure s) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) s).restrict_preimage
    (s := Ioi s) measurableSet_Ioi
  have hpre : (fun x : ℝ => x + s) ⁻¹' Ioi s = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hx <;> linarith
  simpa only [hpre] using h

theorem measurePreserving_shift_sub (s : ℝ /- [definition] -/) :
    MeasurePreserving (fun x : ℝ => x - s) (halfLineShiftMeasure s)
      (halfLineShiftMeasure 0) := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) s).restrict_preimage
    (s := Ioi 0) measurableSet_Ioi
  have hpre : (fun x : ℝ => x - s) ⁻¹' Ioi 0 = Ioi s := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hx <;> linarith
  simpa only [hpre] using h

noncomputable def shiftIsometry (s : ℝ /- [definition] -/) :
    Lp ℝ 2 (halfLineShiftMeasure s) ≃ₗᵢ[ℝ] Lp ℝ 2 (halfLineShiftMeasure 0) where
  toFun := Lp.compMeasurePreserving (fun x : ℝ => x + s) (measurePreserving_shift_add s)
  invFun := Lp.compMeasurePreserving (fun x : ℝ => x - s) (measurePreserving_shift_sub s)
  left_inv f := by
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [Function.comp_def, sub_add_cancel, add_sub_cancel_right]
    exact Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [Function.comp_def, sub_add_cancel, add_sub_cancel_right]
    exact Lp.compMeasurePreserving_id_apply f
  map_add' := (Lp.compMeasurePreserving (fun x : ℝ => x + s)
    (measurePreserving_shift_add s)).map_add
  map_smul' c f := (Lp.compMeasurePreservingₗ ℝ (fun x : ℝ => x + s)
    (measurePreserving_shift_add s)).map_smul c f
  norm_map' f := Lp.norm_compMeasurePreserving f (measurePreserving_shift_add s)

theorem shiftIsometry_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 (halfLineShiftMeasure s) /- [definition] -/ ) :
    shiftIsometry s f =ᵐ[halfLineShiftMeasure 0] fun x => f (x + s) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_shift_add s)

theorem shiftIsometry_symm_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 (halfLineShiftMeasure 0) /- [definition] -/ ) :
    (shiftIsometry s).symm f =ᵐ[halfLineShiftMeasure s] fun x => f (x - s) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_shift_sub s)

-- Nonzero measure guard for every real level, including negative levels.
theorem shifted_unit_interval_measure (s : ℝ /- [definition] -/) :
    halfLineShiftMeasure s (Ioo s (s + 1)) = 1 := by
  rw [halfLineShiftMeasure, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioi_self), Real.volume_Ioo]
  norm_num

-- Inhabitation witness with norm one, rather than the zero vector.
noncomputable def shiftedUnitVector (s : ℝ /- [definition] -/) :
    Lp ℝ 2 (halfLineShiftMeasure s) :=
  indicatorConstLp (s := Ioo s (s + 1)) (μ := halfLineShiftMeasure s) 2 measurableSet_Ioo
    (by rw [shifted_unit_interval_measure s]; exact ENNReal.one_ne_top) (1 : ℝ)

theorem shiftedUnitVector_norm (s : ℝ /- [definition] -/) : ‖shiftedUnitVector s‖ = 1 := by
  rw [shiftedUnitVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
  change ‖(1 : ℝ)‖ * ((halfLineShiftMeasure s) (Ioo s (s + 1))).toReal ^
    (1 / (2 : ℝ≥0∞).toReal) = 1
  rw [shifted_unit_interval_measure s]
  simp

theorem shiftedUnitVector_ne_zero (s : ℝ /- [definition] -/) : shiftedUnitVector s ≠ 0 := by
  intro h
  have hn := shiftedUnitVector_norm s
  rw [h, norm_zero] at hn
  exact zero_ne_one hn



/- Additions authorized by the 2026-10-07 domain decision. Upstream API is retained. -/

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable def airyHankelShiftKernel (s : ℝ /- [definition] -/) : ℝ × ℝ → ℝ :=
  fun p => airyAiReal (p.1 + p.2 + s)

theorem measurable_airyHankelShiftKernel (s : ℝ /- [definition] -/) :
    Measurable (airyHankelShiftKernel s) :=
  measurable_airyAiReal.comp ((measurable_fst.add measurable_snd).add_const s)

theorem airyHankelShiftKernel_swap (s : ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/) (t : ℝ /- [definition] -/) :
    airyHankelShiftKernel s (x, t) = airyHankelShiftKernel s (t, x) := by
  simp only [airyHankelShiftKernel, add_comm x t]

theorem memLp_expWeight : MemLp (fun x : ℝ => Real.exp (-x)) 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq
    (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable).2
  simpa only [IntegrableOn, halfLineMeasure, Function.comp_apply, exp_neg_sq] using integrableOn_exp_neg_two_mul 0

theorem memLp_expPair :
    MemLp (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2)) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have h := memLp_expWeight.integrable_sq.mul_prod memLp_expWeight.integrable_sq
  exact h.congr (Eventually.of_forall fun p => (mul_pow _ _ 2).symm)

theorem airyHankelShiftKernel_bound (s : ℝ /- [definition] -/) :
    ∃ D : ℝ, 0 < D ∧ ∀ p : ℝ × ℝ,
      |airyHankelShiftKernel s p| ≤ D * (Real.exp (-p.1) * Real.exp (-p.2)) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  refine ⟨C * Real.exp (-s), mul_pos hCpos (Real.exp_pos _), ?_⟩
  intro p
  calc |airyHankelShiftKernel s p| ≤ C * Real.exp (-(p.1 + p.2 + s)) := hC _
    _ = (C * Real.exp (-s)) * (Real.exp (-p.1) * Real.exp (-p.2)) := by
      simp only [neg_add, Real.exp_add]
      ring

theorem memLp_airyHankelShiftKernel (s : ℝ /- [definition] -/) :
    MemLp (airyHankelShiftKernel s) 2 (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨D, hD, hbound⟩ := airyHankelShiftKernel_bound s
  apply (memLp_expPair.const_smul D).of_le
    (measurable_airyHankelShiftKernel s).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (mul_pos hD (mul_pos (Real.exp_pos _) (Real.exp_pos _)))] using hbound p

noncomputable def airyHankelShift (s : ℝ /- [definition] -/) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  kernelOperator (memLp_airyHankelShiftKernel s)

theorem isHilbertSchmidt_airyHankelShift (s : ℝ /- [definition] -/) :
    IsHilbertSchmidt (airyHankelShift s) :=
  isHilbertSchmidt_kernelOperator (memLp_airyHankelShiftKernel s)

theorem airyHankelShift_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    airyHankelShift s f =ᵐ[halfLineMeasure]
      fun x => ∫ t, airyAiReal (x + t + s) * f t ∂halfLineMeasure :=
  kernelOperator_apply_ae (memLp_airyHankelShiftKernel s) f

theorem integrable_expWeight_mul_abs (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    Integrable (fun x : ℝ => Real.exp (-x) * |f x|) halfLineMeasure := by
  have h := memLp_expWeight.integrable_mul (Lp.memLp f).norm
  change Integrable (fun x : ℝ => Real.exp (-x) * ‖f x‖) halfLineMeasure at h
  simpa only [Real.norm_eq_abs] using h

theorem integrable_airyHankelShift_pair (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/)
    (g : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    Integrable (fun p : ℝ × ℝ => airyHankelShiftKernel s p * f p.2 * g p.1)
      (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨D, hD, hbound⟩ := airyHankelShiftKernel_bound s
  have hdom := ((integrable_expWeight_mul_abs g).mul_prod
    (integrable_expWeight_mul_abs f)).const_mul D
  apply hdom.mono'
    (((measurable_airyHankelShiftKernel s).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f).comp_snd).mul (Lp.aestronglyMeasurable g).comp_fst)
  apply Eventually.of_forall
  intro p
  change ‖airyHankelShiftKernel s p * f p.2 * g p.1‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |airyHankelShiftKernel s p| * |f p.2| * |g p.1|
      ≤ (D * (Real.exp (-p.1) * Real.exp (-p.2))) * |f p.2| * |g p.1| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound p) (abs_nonneg _)) (abs_nonneg _)
    _ = D * ((Real.exp (-p.1) * |g p.1|) * (Real.exp (-p.2) * |f p.2|)) := by ring

theorem airyHankelShift_inner (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/)
    (g : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ⟪airyHankelShift s f, g⟫_ℝ =
      ∫ x, ∫ t, airyHankelShiftKernel s (x, t) * f t * g x
        ∂halfLineMeasure ∂halfLineMeasure := by
  rw [MeasureTheory.L2.inner_def]
  calc (∫ x, ⟪(airyHankelShift s f) x, g x⟫_ℝ ∂halfLineMeasure)
      = ∫ x, (∫ t, airyHankelShiftKernel s (x, t) * f t ∂halfLineMeasure) * g x
          ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [airyHankelShift_apply_ae s f] with x hx
        simp only [Real.inner_apply, hx, airyHankelShiftKernel]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_mul_const (g x) _).symm

theorem isSelfAdjoint_airyHankelShift (s : ℝ /- [definition] -/) :
    IsSelfAdjoint (airyHankelShift s) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro f g
  change ⟪airyHankelShift s f, g⟫_ℝ = ⟪f, airyHankelShift s g⟫_ℝ
  rw [airyHankelShift_inner, real_inner_comm, airyHankelShift_inner]
  rw [integral_integral_swap (integrable_airyHankelShift_pair s f g)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change airyHankelShiftKernel s (x, t) * f t * g x =
        airyHankelShiftKernel s (t, x) * g x * f t
      rw [airyHankelShiftKernel_swap s x t]
      ring

noncomputable def airyKernelShift (s : ℝ /- [definition] -/) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  airyHankelShift s ∘L airyHankelShift s

theorem isTraceClass_airyKernelShift (s : ℝ /- [definition] -/) :
    IsTraceClass (airyKernelShift s) :=
  ⟨airyHankelShift s, airyHankelShift s, isHilbertSchmidt_airyHankelShift s,
    isHilbertSchmidt_airyHankelShift s, rfl⟩


/- Scalar Airy kernel and its genuine half-line realization. -/

noncomputable def airyKernelIntegral (x : ℝ /- [definition] -/)
    (y : ℝ /- [definition] -/) : ℝ :=
  ∫ t in Set.Ioi 0, airyAiReal (x + t) * airyAiReal (y + t)

theorem airyKernelIntegral_symm (x : ℝ /- [definition] -/)
    (y : ℝ /- [definition] -/) : airyKernelIntegral x y = airyKernelIntegral y x := by
  apply integral_congr_ae
  exact Eventually.of_forall fun t => mul_comm _ _

theorem memLp_airyHankelShiftSlice (s : ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    MemLp (fun t => star (airyHankelShiftKernel s (x, t))) 2 halfLineMeasure := by
  have hmeas : Measurable (fun t : ℝ => airyAiReal (x + t + s)) :=
    measurable_airyAiReal.comp ((measurable_const.add measurable_id).add_const s)
  have hsq : Integrable (fun t : ℝ => airyAiReal (x + t + s) ^ 2) halfLineMeasure := by
    simpa only [IntegrableOn, halfLineMeasure, add_assoc, add_left_comm, add_comm] using
      integrable_airyAiReal_sq_comp_add_Ioi (x + s)
  simpa only [airyHankelShiftKernel, star_trivial] using
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq

theorem airyHankelShift_slice_apply_ae (s : ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    airyHankelShift s (sliceLp halfLineMeasure (airyHankelShiftKernel s) x)
      =ᵐ[halfLineMeasure] fun y => airyKernelIntegral (y + s) (x + s) := by
  filter_upwards [airyHankelShift_apply_ae s
    (sliceLp halfLineMeasure (airyHankelShiftKernel s) x)] with y hy
  rw [hy]
  apply integral_congr_ae
  filter_upwards [sliceLp_apply_ae (memLp_airyHankelShiftSlice s x)] with t ht
  simpa only [airyHankelShiftKernel, star_trivial, add_assoc, add_left_comm, add_comm] using
    congrArg (fun a : ℝ => airyAiReal (y + t + s) * a) ht

theorem airyKernelShift_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    airyKernelShift s f =ᵐ[halfLineMeasure]
      fun x => ∫ y, airyKernelIntegral (x + s) (y + s) * f y ∂halfLineMeasure := by
  filter_upwards [kernelOperator_eval_inner_ae (memLp_airyHankelShiftKernel s)
    (airyHankelShift s f)] with x hx
  change (airyHankelShift s (airyHankelShift s f)) x =
    ⟪sliceLp halfLineMeasure (airyHankelShiftKernel s) x, airyHankelShift s f⟫_ℝ at hx
  change (airyHankelShift s (airyHankelShift s f)) x = _
  have hs := (isSelfAdjoint_airyHankelShift s).isSymmetric
    (sliceLp halfLineMeasure (airyHankelShiftKernel s) x) f
  change ⟪airyHankelShift s (sliceLp halfLineMeasure (airyHankelShiftKernel s) x), f⟫_ℝ =
    ⟪sliceLp halfLineMeasure (airyHankelShiftKernel s) x, airyHankelShift s f⟫_ℝ at hs
  rw [hx, ← hs, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyHankelShift_slice_apply_ae s x] with y hy
  rw [Real.inner_apply, hy, airyKernelIntegral_symm (y + s) (x + s)]

/-- The operator on the actual space L²(s,∞); the following theorem verifies its kernel. -/
noncomputable def airyKernelGenuine (s : ℝ /- [definition] -/) :
    Lp ℝ 2 (halfLineShiftMeasure s) →L[ℝ] Lp ℝ 2 (halfLineShiftMeasure s) :=
  (shiftIsometry s).symm.toLinearIsometry.toContinuousLinearMap ∘L airyKernelShift s ∘L
    (shiftIsometry s).toLinearIsometry.toContinuousLinearMap

theorem airyKernelGenuine_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 (halfLineShiftMeasure s) /- [definition] -/ ) :
    airyKernelGenuine s f =ᵐ[halfLineShiftMeasure s]
      fun x => ∫ y, airyKernelIntegral x y * f y ∂halfLineShiftMeasure s := by
  have hK := (measurePreserving_shift_sub s).quasiMeasurePreserving.ae
    (airyKernelShift_apply_ae s (shiftIsometry s f))
  filter_upwards [shiftIsometry_symm_apply_ae s
    (airyKernelShift s (shiftIsometry s f)), hK] with x hU hKx
  change ((shiftIsometry s).symm (airyKernelShift s (shiftIsometry s f))) x = _
  rw [hU, hKx]
  simp only [sub_add_cancel]
  calc (∫ t, airyKernelIntegral x (t + s) * (shiftIsometry s f) t ∂halfLineMeasure)
      = ∫ t, airyKernelIntegral x (t + s) * f (t + s) ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [shiftIsometry_apply_ae s f] with t ht
        rw [ht]
    _ = _ := (measurePreserving_shift_add s).integral_comp
      (MeasurableEquiv.addRight s).measurableEmbedding (fun y => airyKernelIntegral x y * f y)

theorem shiftIsometry_conjugates_airyKernelGenuine (s : ℝ /- [definition] -/) :
    (shiftIsometry s).toLinearIsometry.toContinuousLinearMap ∘L airyKernelGenuine s ∘L
      (shiftIsometry s).symm.toLinearIsometry.toContinuousLinearMap = airyKernelShift s := by
  ext f
  simp [airyKernelGenuine, ContinuousLinearMap.comp_apply]

noncomputable def airyHankelGenuine (s : ℝ /- [definition] -/) :
    Lp ℝ 2 (halfLineShiftMeasure s) →L[ℝ] Lp ℝ 2 (halfLineShiftMeasure s) :=
  (shiftIsometry s).symm.toLinearIsometry.toContinuousLinearMap ∘L airyHankelShift s ∘L
    (shiftIsometry s).toLinearIsometry.toContinuousLinearMap

theorem isHilbertSchmidt_airyHankelGenuine (s : ℝ /- [definition] -/) :
    IsHilbertSchmidt (airyHankelGenuine s) := by
  let U := (shiftIsometry s).toLinearIsometry.toContinuousLinearMap
  let V := (shiftIsometry s).symm.toLinearIsometry.toContinuousLinearMap
  let b := canonicalBasis ℝ (Lp ℝ 2 (halfLineShiftMeasure s))
  let c := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  apply isHilbertSchmidt_of_sumSq_ne_top
  apply ne_of_lt
  change sumSq (V ∘L (airyHankelShift s ∘L U)) b < ⊤
  calc sumSq (V ∘L (airyHankelShift s ∘L U)) b
      ≤ ‖V‖ₑ ^ 2 * sumSq (airyHankelShift s ∘L U) b := sumSq_comp_le _ _ _
    _ ≤ ‖V‖ₑ ^ 2 * (‖U‖ₑ ^ 2 * sumSq (airyHankelShift s) c) :=
      mul_le_mul_right (sumSq_comp_le_right _ _ b c) _
    _ < ⊤ := ENNReal.mul_lt_top (by finiteness)
      (ENNReal.mul_lt_top (by finiteness)
        (lt_top_iff_ne_top.mpr (isHilbertSchmidt_airyHankelShift s).sumSq_ne_top))

theorem isTraceClass_airyKernelGenuine (s : ℝ /- [definition] -/) :
    IsTraceClass (airyKernelGenuine s) := by
  refine ⟨airyHankelGenuine s, airyHankelGenuine s,
    isHilbertSchmidt_airyHankelGenuine s, isHilbertSchmidt_airyHankelGenuine s, ?_⟩
  ext f
  simp [airyKernelGenuine, airyHankelGenuine, airyKernelShift, ContinuousLinearMap.comp_apply]

theorem airyKernelIntegral_diagonal (x : ℝ /- [definition] -/) :
    airyKernelIntegral x x = (deriv airyAiReal x)^2 - x * (airyAiReal x)^2 := by
  simpa only [airyKernelIntegral, ← pow_two] using airyAiReal_sq_integral x

/-- Joint measurability needed for the finite-dimensional Fredholm integrals. -/
theorem measurable_airyKernelIntegral :
    Measurable (fun p : ℝ × ℝ => airyKernelIntegral p.1 p.2) := by
  have h : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      airyAiReal (q.1.1 + q.2) * airyAiReal (q.1.2 + q.2)) := by
    exact ((continuous_airyAiReal.comp (continuous_fst.fst.add continuous_snd)).mul
      (continuous_airyAiReal.comp (continuous_fst.snd.add continuous_snd))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- Separable exponential domination for the Fredholm coefficient estimates. -/
theorem airyKernelIntegral_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ x y : ℝ,
      |airyKernelIntegral x y| ≤ D * (Real.exp (-x) * Real.exp (-y)) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  refine ⟨C ^ 2 / 2, by positivity, ?_⟩
  intro x y
  have hprod : ∀ t : ℝ, |airyAiReal (x + t) * airyAiReal (y + t)| ≤
      (C ^ 2 * (Real.exp (-x) * Real.exp (-y))) * Real.exp (-(2 * t)) := by
    intro t
    rw [abs_mul]
    calc |airyAiReal (x + t)| * |airyAiReal (y + t)|
        ≤ (C * Real.exp (-(x + t))) * (C * Real.exp (-(y + t))) :=
          mul_le_mul (hC _) (hC _) (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [neg_add, neg_add, Real.exp_add, Real.exp_add,
          show -(2 * t) = -t + -t by ring, Real.exp_add]
        ring
  have hi : Integrable (fun t : ℝ => airyAiReal (x + t) * airyAiReal (y + t))
      halfLineMeasure := integrable_airyAiReal_mul_Ioi x y
  have hd : Integrable (fun t : ℝ =>
      (C ^ 2 * (Real.exp (-x) * Real.exp (-y))) * Real.exp (-(2 * t)))
      halfLineMeasure := (integrableOn_exp_neg_two_mul 0).const_mul _
  calc |airyKernelIntegral x y|
      ≤ ∫ t, |airyAiReal (x + t) * airyAiReal (y + t)| ∂halfLineMeasure := by
        simpa only [airyKernelIntegral, halfLineMeasure, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun t : ℝ =>
            airyAiReal (x + t) * airyAiReal (y + t)) (μ := halfLineMeasure)
    _ ≤ ∫ t, (C ^ 2 * (Real.exp (-x) * Real.exp (-y))) * Real.exp (-(2 * t))
        ∂halfLineMeasure := integral_mono hi.norm hd hprod
    _ = _ := by
      rw [integral_const_mul]
      change C ^ 2 * (Real.exp (-x) * Real.exp (-y)) *
        (∫ t in Set.Ioi 0, Real.exp (-(2 * t))) = _
      rw [integral_exp_neg_two_mul_Ioi]
      simp only [mul_zero, neg_zero, Real.exp_zero]
      ring


noncomputable abbrev quadrantMeasure : Measure (ℝ × ℝ) :=
  halfLineMeasure.prod halfLineMeasure

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_eq_zero_iff
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_eq_zero_right
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_eq_zero_left
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_add_one
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_add_one_div_self
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_zero_neg_nat_add_one
#print axioms RMTFoundations.Airy.multiset_prod_eq_pow_mul_multiset_prod
#print axioms RMTFoundations.Airy.complex_multiset_prod_div_multiset_prod_mul
#print axioms RMTFoundations.Airy.complex_regularizedHGFunSeries
#print axioms RMTFoundations.Airy.complex_regularizedHGFunSeries_coeff
#print axioms RMTFoundations.Airy.complex_regularizedHGFunSeries_eq_zero
#print axioms RMTFoundations.Airy.complex_regularizedHGFun
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_eq_top_of_finite
#print axioms RMTFoundations.Airy.complex_eventually_atTop_regularizedHGFunCoeff_ne_zero
#print axioms RMTFoundations.Airy.tendsto_multiset_prod_div_add_one
#print axioms RMTFoundations.Airy.tendsto_multiset_prod_div_multiset_prod_mul
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_eq_top
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_zero_eq_top
#print axioms RMTFoundations.Airy.complex_analyticOnNhd_regularizedHGFun_of_card_le
#print axioms RMTFoundations.Airy.complex_analyticAt_regularizedHGFun_of_card_le
#print axioms RMTFoundations.Airy.complex_analyticOnNhd_regularizedHGFun_zero
#print axioms RMTFoundations.Airy.complex_analyticAt_regularizedHGFun_zero
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_eq_one
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_ge_one
#print axioms RMTFoundations.Airy.complex_analyticOnNhd_regularizedHGFun_of_card_eq_add_one
#print axioms RMTFoundations.Airy.complex_analyticAt_regularizedHGFun_of_card_eq_add_one
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_singleton_neg_nat_add_one
#print axioms RMTFoundations.Airy.complex_regularizedHGFunSeries_zero_zero
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_zero
#print axioms RMTFoundations.Airy.complex_regularizedGaussHGFunSeries
#print axioms RMTFoundations.Airy.complex_regularizedGaussHGFun
#print axioms RMTFoundations.Airy.complex_regularizedGaussHGFunSeries_symm
#print axioms RMTFoundations.Airy.complex_regularizedGaussHGFun_symm
#print axioms RMTFoundations.Airy.complex_Gamma_add_nat_mul
#print axioms RMTFoundations.Airy.complex_Gamma_add_nat_div_Gamma_eq
#print axioms RMTFoundations.Airy.complex_coeff_regularizedGaussHGFunSeries
#print axioms RMTFoundations.Airy.complex_Gamma_inv_mul_ordinaryHypergeometricSeries_eq
#print axioms RMTFoundations.Airy.complex_ordinaryHypergeometric_div_Gamma_eq
#print axioms RMTFoundations.Airy.complex_radius_regularizedGaussHGFunSeries_eq_top_of_left
#print axioms RMTFoundations.Airy.complex_radius_regularizedGaussHGFunSeries_eq_top_of_right
#print axioms RMTFoundations.Airy.complex_radius_regularizedGaussHGFunSeries_eq_one
#print axioms RMTFoundations.Airy.complex_radius_regularizedGaussHGFunSeries_ge_one
#print axioms RMTFoundations.Airy.complex_airyAi
#print axioms RMTFoundations.Airy.complex_airyBi
#print axioms RMTFoundations.Airy.complex_airyAi_def
#print axioms RMTFoundations.Airy.complex_airyBi_def
#print axioms RMTFoundations.Airy.complex_analyticAt_airyAi
#print axioms RMTFoundations.Airy.complex_analyticOnNhd_airyAi
#print axioms RMTFoundations.Airy.complex_analyticAt_airyBi
#print axioms RMTFoundations.Airy.complex_analyticOnNhd_airyBi
#print axioms RMTFoundations.Airy.complex_airyAi_zero
#print axioms RMTFoundations.Airy.complex_airyBi_zero
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_singleton_eq_tsum
#print axioms RMTFoundations.Airy.complex_regularizedHGFunCoeff_zero_singleton_succ
#print axioms RMTFoundations.Airy.complex_radius_regularizedHGFunSeries_zero_singleton_succ
#print axioms RMTFoundations.Airy.complex_hasDerivAt_partialSum_regularizedHGFunSeries_zero_singleton
#print axioms RMTFoundations.Airy.complex_hasDerivAt_regularizedHGFun_zero_singleton
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_singleton_recurrence
#print axioms RMTFoundations.Airy.complex_hasDerivAt_cube_div_nine
#print axioms RMTFoundations.Airy.complex_hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine
#print axioms RMTFoundations.Airy.complex_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine
#print axioms RMTFoundations.Airy.complex_hasDerivAt_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine
#print axioms RMTFoundations.Airy.complex_two_thirds_add_nat_ne_zero
#print axioms RMTFoundations.Airy.complex_four_thirds_add_nat_ne_zero
#print axioms RMTFoundations.Airy.complex_hasDerivAt_deriv_u_two_thirds
#print axioms RMTFoundations.Airy.complex_hasDerivAt_z_mul_four_thirds
#print axioms RMTFoundations.Airy.complex_deriv_z_mul_four_thirds
#print axioms RMTFoundations.Airy.complex_hasDerivAt_deriv_z_mul_four_thirds
#print axioms RMTFoundations.Airy.complex_airyAi_eq
#print axioms RMTFoundations.Airy.complex_airyBi_eq
#print axioms RMTFoundations.Airy.complex_deriv_airyAi
#print axioms RMTFoundations.Airy.complex_deriv_airyBi
#print axioms RMTFoundations.Airy.complex_iteratedDeriv_two_airyAi
#print axioms RMTFoundations.Airy.complex_iteratedDeriv_two_airyBi
#print axioms RMTFoundations.Airy.complex_star_regularizedHGFunCoeff_zero_singleton_real
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_singleton_real_conj
#print axioms RMTFoundations.Airy.complex_airyAi_conj
#print axioms RMTFoundations.Airy.complex_airyBi_conj
#print axioms RMTFoundations.Airy.complex_three_cpow_ofReal
#print axioms RMTFoundations.Airy.complex_Gamma_four_thirds
#print axioms RMTFoundations.Airy.complex_regularizedHGFun_zero_singleton_apply_zero
#print axioms RMTFoundations.Airy.complex_deriv_airyAi_zero
#print axioms RMTFoundations.Airy.complex_deriv_airyBi_zero
#print axioms RMTFoundations.Airy.complex_differentiableAt_deriv_airyAi
#print axioms RMTFoundations.Airy.complex_differentiableAt_deriv_airyBi
#print axioms RMTFoundations.Airy.airyAiReal
#print axioms RMTFoundations.Airy.airyBiReal
#print axioms RMTFoundations.Airy.airyAiReal_ofReal
#print axioms RMTFoundations.Airy.airyBiReal_ofReal
#print axioms RMTFoundations.Airy.hasDerivAt_airyAiReal
#print axioms RMTFoundations.Airy.hasDerivAt_airyBiReal
#print axioms RMTFoundations.Airy.deriv_airyAiReal
#print axioms RMTFoundations.Airy.deriv_airyBiReal
#print axioms RMTFoundations.Airy.hasDerivAt_deriv_airyAiReal
#print axioms RMTFoundations.Airy.hasDerivAt_deriv_airyBiReal
#print axioms RMTFoundations.Airy.iteratedDeriv_two_airyAiReal
#print axioms RMTFoundations.Airy.iteratedDeriv_two_airyBiReal
#print axioms RMTFoundations.Airy.deriv_airyAiReal_zero
#print axioms RMTFoundations.Airy.deriv_airyBiReal_zero
#print axioms RMTFoundations.Airy.airyAiReal_zero
#print axioms RMTFoundations.Airy.airyBiReal_zero
#print axioms RMTFoundations.Airy.real_Gamma_four_thirds
#print axioms RMTFoundations.Airy.airyAiReal_zero_pos
#print axioms RMTFoundations.Airy.deriv_airyAiReal_zero_neg
#print axioms RMTFoundations.Airy.airyBiReal_zero_pos
#print axioms RMTFoundations.Airy.deriv_airyBiReal_zero_pos
#print axioms RMTFoundations.Airy.gaussianTail
#print axioms RMTFoundations.Airy.hasDerivAt_exp_neg_sq_div
#print axioms RMTFoundations.Airy.integrableOn_exp_neg_sq_div_Ioi
#print axioms RMTFoundations.Airy.integrableOn_mul_exp_neg_sq_div_Ioi
#print axioms RMTFoundations.Airy.integrableOn_neg_mul_exp_neg_sq_div_Ioi
#print axioms RMTFoundations.Airy.tendsto_exp_neg_sq_div_atTop
#print axioms RMTFoundations.Airy.integral_Ioi_neg_mul_exp_neg_sq_div
#print axioms RMTFoundations.Airy.gaussianTail_le
#print axioms RMTFoundations.Airy.integrableOn_exp_neg_sq_div_div_pow
#print axioms RMTFoundations.Airy.intervalIntegral_exp_neg_sq_div
#print axioms RMTFoundations.Airy.gaussianTail_eq
#print axioms RMTFoundations.Airy.intervalIntegral_exp_neg_sq_div_div_sq
#print axioms RMTFoundations.Airy.integral_Ioi_exp_neg_sq_div_div_sq
#print axioms RMTFoundations.Airy.gaussianTail_sub_eq
#print axioms RMTFoundations.Airy.gaussianTail_asymptotic
#print axioms RMTFoundations.Airy.gaussianTail_isEquivalent
#print axioms RMTFoundations.Airy.one_add_sq_div_two_le_cosh
#print axioms RMTFoundations.Airy.cosh_le_exp_abs
#print axioms RMTFoundations.Airy.schlaefliK13
#print axioms RMTFoundations.Airy.schlaefliK13_integrand_le
#print axioms RMTFoundations.Airy.integrable_schlaefliK13_dom
#print axioms RMTFoundations.Airy.integrable_schlaefliK13_integrand
#print axioms RMTFoundations.Airy.integrableOn_schlaefliK13_integrand
#print axioms RMTFoundations.Airy.schlaefliK13_pos
#print axioms RMTFoundations.Airy.schlaefliK13_le
#print axioms RMTFoundations.Airy.airyK13_schlaefli_le
#print axioms RMTFoundations.Airy.schlaefliJ1
#print axioms RMTFoundations.Airy.schlaefliJ2
#print axioms RMTFoundations.Airy.schlaefliK13_eq_s_form
#print axioms RMTFoundations.Airy.continuousOn_schlaefliJ_kernel
#print axioms RMTFoundations.Airy.integrableOn_schlaefliJ_kernel
#print axioms RMTFoundations.Airy.schlaefli_sIntegrand_split
#print axioms RMTFoundations.Airy.schlaefliK13_eq_J12
#print axioms RMTFoundations.Airy.integrable_schlaefli_dom
#print axioms RMTFoundations.Airy.hasDerivAt_schlaefliK13
#print axioms RMTFoundations.Airy.hasDerivAt_schlaefliK13_two
#print axioms RMTFoundations.Airy.hasDerivAt_deriv_schlaefliK13
#print axioms RMTFoundations.Airy.schlaefliK13Antideriv
#print axioms RMTFoundations.Airy.schlaefliK13Comb
#print axioms RMTFoundations.Airy.hasDerivAt_schlaefliK13Antideriv
#print axioms RMTFoundations.Airy.schlaefliK13Antideriv_zero
#print axioms RMTFoundations.Airy.tendsto_schlaefliK13Antideriv_atTop
#print axioms RMTFoundations.Airy.integral_schlaefliK13Comb
#print axioms RMTFoundations.Airy.schlaefliK13_bessel_eq
#print axioms RMTFoundations.Airy.airyBesselY
#print axioms RMTFoundations.Airy.airyBesselY1
#print axioms RMTFoundations.Airy.sqrt_div_three
#print axioms RMTFoundations.Airy.hasDerivAt_rpow_half
#print axioms RMTFoundations.Airy.hasDerivAt_rpow_neg_half
#print axioms RMTFoundations.Airy.hasDerivAt_g
#print axioms RMTFoundations.Airy.hasDerivAt_airyBesselY
#print axioms RMTFoundations.Airy.hasDerivAt_airyBesselY1
#print axioms RMTFoundations.Airy.iteratedDeriv_two_airyBesselY
#print axioms RMTFoundations.Airy.real_Gamma_one_third_mul_Gamma_two_thirds
#print axioms RMTFoundations.Airy.airyBesselY0_eq
#print axioms RMTFoundations.Airy.airyBesselY1_eq
#print axioms RMTFoundations.Airy.integrableOn_and_integral_rpow_Ioi
#print axioms RMTFoundations.Airy.integral_Ioo_rpow
#print axioms RMTFoundations.Airy.integrableOn_and_integral_Ioc_zero_rpow
#print axioms RMTFoundations.Airy.schlaefliJ2ConstAntideriv
#print axioms RMTFoundations.Airy.hasDerivAt_schlaefliJ2ConstAntideriv
#print axioms RMTFoundations.Airy.schlaefliJ2ConstAntideriv_zero
#print axioms RMTFoundations.Airy.continuousWithinAt_schlaefliJ2ConstAntideriv_zero
#print axioms RMTFoundations.Airy.tendsto_schlaefliJ2ConstAntideriv_atTop
#print axioms RMTFoundations.Airy.integrableOn_rpow_mul_exp_neg_sub_one
#print axioms RMTFoundations.Airy.integrableOn_rpow_mul_exp_neg
#print axioms RMTFoundations.Airy.schlaefliJ2_const
#print axioms RMTFoundations.Airy.integrableOn_exp_sub_one_mul_rpow
#print axioms RMTFoundations.Airy.schlaefliJ2_sub_eq_integral
#print axioms RMTFoundations.Airy.integrableOn_centeredJ2
#print axioms RMTFoundations.Airy.centeredJ2_split
#print axioms RMTFoundations.Airy.integrableOn_Ioo_rpow_of_pos
#print axioms RMTFoundations.Airy.tendsto_centeredJ2_Ioi_one
#print axioms RMTFoundations.Airy.tendsto_airyAsympK_Ioo
#print axioms RMTFoundations.Airy.abs_centeredJ2_diff_le
#print axioms RMTFoundations.Airy.continuousOn_centeredJ2_diff
#print axioms RMTFoundations.Airy.tendsto_centeredJ2_diff_Ioo
#print axioms RMTFoundations.Airy.centeredJ2_Ioc_eq_add
#print axioms RMTFoundations.Airy.schlaefliJ2_sub_tendsto
#print axioms RMTFoundations.Airy.integrableOn_Ioc_rpow_of_pos
#print axioms RMTFoundations.Airy.abs_exp_sub_one_mul_rpow_le
#print axioms RMTFoundations.Airy.schlaefliJ1_decomp
#print axioms RMTFoundations.Airy.abs_schlaefliJ1_R1_le
#print axioms RMTFoundations.Airy.abs_schlaefliJ1_R2_le_aux
#print axioms RMTFoundations.Airy.abs_schlaefliJ1_R2_le
#print axioms RMTFoundations.Airy.schlaefliJ1_isBigO
#print axioms RMTFoundations.Airy.airyODE_ftc
#print axioms RMTFoundations.Airy.airyODE_int_lim
#print axioms RMTFoundations.Airy.airyODE_deriv_lim
#print axioms RMTFoundations.Airy.airyODE_deriv_lim_zero
#print axioms RMTFoundations.Airy.airyODE_deriv_zero
#print axioms RMTFoundations.Airy.airy_ode_uniqueness
#print axioms RMTFoundations.Airy.rpow_three_inv
#print axioms RMTFoundations.Airy.airyG_half_rpow_pos
#print axioms RMTFoundations.Airy.airyG_half_rpow_neg
#print axioms RMTFoundations.Airy.sqrt_div_three_rpow
#print axioms RMTFoundations.Airy.coeffJ1
#print axioms RMTFoundations.Airy.coeffJ2
#print axioms RMTFoundations.Airy.tendsto_airyG
#print axioms RMTFoundations.Airy.schlaefliJ1_tendsto
#print axioms RMTFoundations.Airy.mul_rpow_neg_half
#print axioms RMTFoundations.Airy.airyBesselY_eq_J12
#print axioms RMTFoundations.Airy.airyBesselY_tendsto_zero_right
#print axioms RMTFoundations.Airy.airyBesselY_slope_tendsto
#print axioms RMTFoundations.Airy.hasDerivAt_deriv_airyAiReal'
#print axioms RMTFoundations.Airy.airyBesselYExt
#print axioms RMTFoundations.Airy.airyBesselYExt_eq
#print axioms RMTFoundations.Airy.airyIdentityW
#print axioms RMTFoundations.Airy.hW0
#print axioms RMTFoundations.Airy.hdiff
#print axioms RMTFoundations.Airy.hcont
#print axioms RMTFoundations.Airy.hW''
#print axioms RMTFoundations.Airy.hslopes
#print axioms RMTFoundations.Airy.airyBesselY_eq_pi_airyAiReal
#print axioms RMTFoundations.Airy.airyAiReal_eq_airyBesselY_div_pi
#print axioms RMTFoundations.Airy.airyBesselY_pos
#print axioms RMTFoundations.Airy.airyAiReal_pos
#print axioms RMTFoundations.Airy.airyAiReal_pos_of_nonneg
#print axioms RMTFoundations.Airy.airyAiReal_le
#print axioms RMTFoundations.Airy.airyLaplace_exp_identity
#print axioms RMTFoundations.Airy.airyLaplace_weight_le
#print axioms RMTFoundations.Airy.airyAiReal_sq_le
#print axioms RMTFoundations.Airy.airyLaplace_sq_subst
#print axioms RMTFoundations.Airy.airyAiReal_laplace_half
#print axioms RMTFoundations.Airy.airyEnergyFull
#print axioms RMTFoundations.Airy.hasDerivAt_airyEnergyFull
#print axioms RMTFoundations.Airy.airyEnergy_monotoneOn
#print axioms RMTFoundations.Airy.airyAiReal_abs_le_nonpos
#print axioms RMTFoundations.Airy.airyAiReal_laplace
#print axioms RMTFoundations.Airy.enorm_sq_eq_ofReal
#print axioms RMTFoundations.Airy.inner_mul_inner_eq_norm_sq
#print axioms RMTFoundations.Airy.norm_sq_eq_tsum_norm_inner
#print axioms RMTFoundations.Airy.summable_norm_inner_sq
#print axioms RMTFoundations.Airy.enorm_sq_eq_tsum
#print axioms RMTFoundations.Airy.sumSq
#print axioms RMTFoundations.Airy.sumSq_eq_sumSq_adjoint
#print axioms RMTFoundations.Airy.canonicalIndex
#print axioms RMTFoundations.Airy.canonicalBasis
#print axioms RMTFoundations.Airy.sumSq_independent
#print axioms RMTFoundations.Airy.hsENorm
#print axioms RMTFoundations.Airy.hsENorm_eq_tsum_basis
#print axioms RMTFoundations.Airy.IsHilbertSchmidt
#print axioms RMTFoundations.Airy.rankOne
#print axioms RMTFoundations.Airy.rankOne_apply
#print axioms RMTFoundations.Airy.sumSq_rankOne
#print axioms RMTFoundations.Airy.isHilbertSchmidt_rankOne
#print axioms RMTFoundations.Airy.eLpNorm_two_sq_eq_lintegral
#print axioms RMTFoundations.Airy.enorm_rpow_two
#print axioms RMTFoundations.Airy.rpow_half_sq
#print axioms RMTFoundations.Airy.rpow_half_sq'
#print axioms RMTFoundations.Airy.slice_measurable_finite_ae
#print axioms RMTFoundations.Airy.memLp_conj_slice_ae
#print axioms RMTFoundations.Airy.sliceLp
#print axioms RMTFoundations.Airy.sliceLp_eq_toLp
#print axioms RMTFoundations.Airy.sliceLp_apply_ae
#print axioms RMTFoundations.Airy.enorm_sliceLp_sq
#print axioms RMTFoundations.Airy.kernelIntegralFun
#print axioms RMTFoundations.Airy.kernelIntegralFun_aestronglyMeasurable
#print axioms RMTFoundations.Airy.integrable_kernelFun_slice_ae
#print axioms RMTFoundations.Airy.kernelIntegralFun_enorm_sq_le
#print axioms RMTFoundations.Airy.eLpNorm_kernelIntegral_le
#print axioms RMTFoundations.Airy.memLp_kernelIntegral
#print axioms RMTFoundations.Airy.kernelIntegralFun_eq_inner_ae
#print axioms RMTFoundations.Airy.kernelIntegralFun_add_ae
#print axioms RMTFoundations.Airy.kernelIntegralFun_smul_ae
#print axioms RMTFoundations.Airy.kernelOperator
#print axioms RMTFoundations.Airy.kernelOperator_apply_ae
#print axioms RMTFoundations.Airy.kernelOperator_eval_inner_ae
#print axioms RMTFoundations.Airy.enorm_kernelOperator_le
#print axioms RMTFoundations.Airy.sumSq_kernelOperator_le
#print axioms RMTFoundations.Airy.isHilbertSchmidt_kernelOperator
#print axioms RMTFoundations.Airy.hsENorm_kernelOperator_le
#print axioms RMTFoundations.Airy.sumSq_kernelOperator_eq
#print axioms RMTFoundations.Airy.hsENorm_kernelOperator
#print axioms RMTFoundations.Airy.sumSq_comp_le
#print axioms RMTFoundations.Airy.enorm_adjoint
#print axioms RMTFoundations.Airy.sumSq_comp_le_right
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.sumSq_ne_top
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.sumSq_ne_top_basis
#print axioms RMTFoundations.Airy.isHilbertSchmidt_of_sumSq_ne_top
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.adjoint
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.comp_left
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.comp_right
#print axioms RMTFoundations.Airy.enorm_sq_apply_le_sumSq_mul
#print axioms RMTFoundations.Airy.opENorm_le_sumSq_rpow_half
#print axioms RMTFoundations.Airy.IsTraceClass
#print axioms RMTFoundations.Airy.IsTraceClass.isHilbertSchmidt
#print axioms RMTFoundations.Airy.summable_norm_sq_apply_basis
#print axioms RMTFoundations.Airy.summable_norm_inner_diagonal
#print axioms RMTFoundations.Airy.summable_inner_diagonal
#print axioms RMTFoundations.Airy.summable_norm_sq_inner_adjoint_fst
#print axioms RMTFoundations.Airy.summable_norm_sq_inner_snd
#print axioms RMTFoundations.Airy.summable_uncurry_inner_mul_inner
#print axioms RMTFoundations.Airy.tsum_inner_comp_eq
#print axioms RMTFoundations.Airy.trace
#print axioms RMTFoundations.Airy.trace_eq_tsum_inner
#print axioms RMTFoundations.Airy.trace_comp_comm
#print axioms RMTFoundations.Airy.basisTruncation
#print axioms RMTFoundations.Airy.basisTruncation_apply_basis
#print axioms RMTFoundations.Airy.sumSq_sub_basisTruncation
#print axioms RMTFoundations.Airy.tendsto_sumSq_tail
#print axioms RMTFoundations.Airy.tendsto_sumSq_tail_rpow
#print axioms RMTFoundations.Airy.tendsto_basisTruncation
#print axioms RMTFoundations.Airy.isCompactOperator_inner_smul
#print axioms RMTFoundations.Airy.isCompactOperator_basisTruncation
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.isCompactOperator
#print axioms RMTFoundations.Airy.IsTraceClass.isCompactOperator
#print axioms RMTFoundations.Airy.IsTraceClass.comp_right
#print axioms RMTFoundations.Airy.IsTraceClass.comp_left
#print axioms RMTFoundations.Airy.pow_eq_comp_one_sub
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.isTraceClass_pow
#print axioms RMTFoundations.Airy.hsNorm
#print axioms RMTFoundations.Airy.hsNorm_nonneg
#print axioms RMTFoundations.Airy.hsENorm_adjoint
#print axioms RMTFoundations.Airy.hsNorm_adjoint
#print axioms RMTFoundations.Airy.hsENorm_comp_le
#print axioms RMTFoundations.Airy.toReal_pow
#print axioms RMTFoundations.Airy.pow_succ_eq_comp
#print axioms RMTFoundations.Airy.hsENorm_pow_le
#print axioms RMTFoundations.Airy.hsNorm_pow_le
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.pow
#print axioms RMTFoundations.Airy.tsum_mul_sq_le
#print axioms RMTFoundations.Airy.norm_trace_comp_le
#print axioms RMTFoundations.Airy.norm_trace_pow_le
#print axioms RMTFoundations.Airy.fredholmDetTwoCoeff
#print axioms RMTFoundations.Airy.fredholmDetTwoCoeff_zero
#print axioms RMTFoundations.Airy.fredholmDetTwoCoeff_one
#print axioms RMTFoundations.Airy.norm_fredholmDetTwoCoeff_le
#print axioms RMTFoundations.Airy.summable_norm_fredholmDetTwoCoeff_mul_pow
#print axioms RMTFoundations.Airy.summable_norm_fredholmDetTwoTerm
#print axioms RMTFoundations.Airy.fredholmDetTwoSeries
#print axioms RMTFoundations.Airy.inv_hsNorm_le_radius
#print axioms RMTFoundations.Airy.fredholmDetTwoSeries_radius_pos
#print axioms RMTFoundations.Airy.fredholmDetTwo
#print axioms RMTFoundations.Airy.fredholmDetTwo_eq_exp_tsum
#print axioms RMTFoundations.Airy.fredholmDetTwo_zero
#print axioms RMTFoundations.Airy.hasFDerivAt_fredholmDetTwo_zero
#print axioms RMTFoundations.Airy.deriv_fredholmDetTwo_zero
#print axioms RMTFoundations.Airy.differentiableOn_fredholmDetTwo
#print axioms RMTFoundations.Airy.differentiable_fredholmDetTwo_of_hsNorm_eq_zero
#print axioms RMTFoundations.Airy.trace_add_of_summable
#print axioms RMTFoundations.Airy.trace_add
#print axioms RMTFoundations.Airy.trace_sub
#print axioms RMTFoundations.Airy.trace_smul
#print axioms RMTFoundations.Airy.trace_sum
#print axioms RMTFoundations.Airy.smul_pow_clm
#print axioms RMTFoundations.Airy.neg_pow_clm
#print axioms RMTFoundations.Airy.hsENorm_neg
#print axioms RMTFoundations.Airy.hsNorm_neg
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.neg
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.isTraceClass_comp
#print axioms RMTFoundations.Airy.hsNorm_comp_le
#print axioms RMTFoundations.Airy.IsHilbertSchmidt.sub
#print axioms RMTFoundations.Airy.trace_pow_comp_comm
#print axioms RMTFoundations.Airy.plemeljSummable
#print axioms RMTFoundations.Airy.summable_trace_pow_div
#print axioms RMTFoundations.Airy.summable_norm_trace_pow_div
#print axioms RMTFoundations.Airy.summable_norm_trace_pow_div_tail
#print axioms RMTFoundations.Airy.summable_trace_pow_div_tail
#print axioms RMTFoundations.Airy.tsum_norm_trace_pow_div_tail_le
#print axioms RMTFoundations.Airy.tsum_norm_trace_pow_div_tail_le_of_le_half
#print axioms RMTFoundations.Airy.norm_tsum_trace_pow_div_tail_le
#print axioms RMTFoundations.Airy.norm_tsum_trace_pow_div_tail_le_of_le_half
#print axioms RMTFoundations.Airy.tsum_trace_pow_div_eq_trace_add_tail
#print axioms RMTFoundations.Airy.hasSum_pow_div_factorial
#print axioms RMTFoundations.Airy.summable_pow_div_factorial
#print axioms RMTFoundations.Airy.tsum_pow_div_factorial
#print axioms RMTFoundations.Airy.summable_norm_pow_div_factorial
#print axioms RMTFoundations.Airy.tsum_norm_pow_div_factorial
#print axioms RMTFoundations.Airy.norm_exp_le
#print axioms RMTFoundations.Airy.norm_exp_sub_one_le
#print axioms RMTFoundations.Airy.norm_exp_sub_one_sub_le
#print axioms RMTFoundations.Airy.fredholmDetOne
#print axioms RMTFoundations.Airy.fredholmDetOne_zero
#print axioms RMTFoundations.Airy.fredholmDetOne_one_eq_exp_neg_tsum
#print axioms RMTFoundations.Airy.fredholmDetOne_eq_exp_neg_trace_mul_detTwo
#print axioms RMTFoundations.Airy.fredholmDetOne_cyclic
#print axioms RMTFoundations.Airy.norm_one_sub_fredholmDetOne_one_sub_trace_le
#print axioms RMTFoundations.Airy.comp_sum
#print axioms RMTFoundations.Airy.sub_pow_eq_sum_comp
#print axioms RMTFoundations.Airy.norm_trace_sub_pow_le
#print axioms RMTFoundations.Airy.summable_norm_trace_pow_div_tail_of_hs
#print axioms RMTFoundations.Airy.summable_trace_pow_div_tail_of_hs
#print axioms RMTFoundations.Airy.tsum_norm_trace_pow_div_tail_le_of_hs
#print axioms RMTFoundations.Airy.norm_tsum_trace_pow_div_tail_le_of_hs
#print axioms RMTFoundations.Airy.norm_trace_pow_div_tail_sub_le
#print axioms RMTFoundations.Airy.norm_exp_neg_trace_pow_div_tail_sub_le
#print axioms RMTFoundations.Airy.halfLineMeasure
#print axioms RMTFoundations.Airy.airyAiReal_abs_le_exp
#print axioms RMTFoundations.Airy.airyAiReal_abs_le_exp'
#print axioms RMTFoundations.Airy.exp_neg_sq
#print axioms RMTFoundations.Airy.integrableOn_exp_neg_two_mul
#print axioms RMTFoundations.Airy.integral_exp_neg_two_mul_Ioi
#print axioms RMTFoundations.Airy.lintegral_exp_neg_two_mul_Ioi
#print axioms RMTFoundations.Airy.measurable_airyAiReal
#print axioms RMTFoundations.Airy.airyHankelKernel
#print axioms RMTFoundations.Airy.measurableSet_hankelCut
#print axioms RMTFoundations.Airy.measurable_airyHankelKernel
#print axioms RMTFoundations.Airy.hankelDom
#print axioms RMTFoundations.Airy.measurable_hankelDom
#print axioms RMTFoundations.Airy.enorm_sq_airyHankelKernel_le
#print axioms RMTFoundations.Airy.lintegral_hankelDom_slice
#print axioms RMTFoundations.Airy.setLIntegral_halfLineMeasure_Ioi
#print axioms RMTFoundations.Airy.lintegral_hankelDom_sq
#print axioms RMTFoundations.Airy.memLp_airyHankelKernel
#print axioms RMTFoundations.Airy.eLpNorm_airyHankelKernel_le
#print axioms RMTFoundations.Airy.airyHankel
#print axioms RMTFoundations.Airy.isHilbertSchmidt_airyHankel
#print axioms RMTFoundations.Airy.tendsto_hsENorm_airyHankel
#print axioms RMTFoundations.Airy.enorm_airyHankel_le_hsENorm
#print axioms RMTFoundations.Airy.airyKernelOp
#print axioms RMTFoundations.Airy.isTraceClass_airyKernelOp
#print axioms RMTFoundations.Airy.hsENorm_airyKernelOp_le
#print axioms RMTFoundations.Airy.tendsto_hsENorm_airyKernelOp
#print axioms RMTFoundations.Airy.continuous_airyAiReal
#print axioms RMTFoundations.Airy.hasDerivAt_airyAiReal'
#print axioms RMTFoundations.Airy.continuous_deriv_airyAiReal
#print axioms RMTFoundations.Airy.deriv_deriv_airyAiReal
#print axioms RMTFoundations.Airy.airyEnergy
#print axioms RMTFoundations.Airy.hasDerivAt_airyEnergy
#print axioms RMTFoundations.Airy.hasDerivAt_airyEnergy_comp_add
#print axioms RMTFoundations.Airy.integrable_airyAiReal_sq_Ioi
#print axioms RMTFoundations.Airy.integrable_airyAiReal_sq_comp_add_Ioi
#print axioms RMTFoundations.Airy.integrable_airyAiReal_mul_Ioi
#print axioms RMTFoundations.Airy.airyEnergy_tendsto_nhds
#print axioms RMTFoundations.Airy.airyEnergy_tendsto_zero
#print axioms RMTFoundations.Airy.airyAiReal_sq_integral
#print axioms RMTFoundations.Airy.halfLineShiftMeasure
#print axioms RMTFoundations.Airy.measurePreserving_shift_add
#print axioms RMTFoundations.Airy.measurePreserving_shift_sub
#print axioms RMTFoundations.Airy.shiftIsometry
#print axioms RMTFoundations.Airy.shiftIsometry_apply_ae
#print axioms RMTFoundations.Airy.shiftIsometry_symm_apply_ae
#print axioms RMTFoundations.Airy.shifted_unit_interval_measure
#print axioms RMTFoundations.Airy.shiftedUnitVector
#print axioms RMTFoundations.Airy.shiftedUnitVector_norm
#print axioms RMTFoundations.Airy.shiftedUnitVector_ne_zero
#print axioms RMTFoundations.Airy.airyHankelShiftKernel
#print axioms RMTFoundations.Airy.measurable_airyHankelShiftKernel
#print axioms RMTFoundations.Airy.airyHankelShiftKernel_swap
#print axioms RMTFoundations.Airy.memLp_expWeight
#print axioms RMTFoundations.Airy.memLp_expPair
#print axioms RMTFoundations.Airy.airyHankelShiftKernel_bound
#print axioms RMTFoundations.Airy.memLp_airyHankelShiftKernel
#print axioms RMTFoundations.Airy.airyHankelShift
#print axioms RMTFoundations.Airy.isHilbertSchmidt_airyHankelShift
#print axioms RMTFoundations.Airy.airyHankelShift_apply_ae
#print axioms RMTFoundations.Airy.integrable_expWeight_mul_abs
#print axioms RMTFoundations.Airy.integrable_airyHankelShift_pair
#print axioms RMTFoundations.Airy.airyHankelShift_inner
#print axioms RMTFoundations.Airy.isSelfAdjoint_airyHankelShift
#print axioms RMTFoundations.Airy.airyKernelShift
#print axioms RMTFoundations.Airy.isTraceClass_airyKernelShift
#print axioms RMTFoundations.Airy.airyKernelIntegral
#print axioms RMTFoundations.Airy.airyKernelIntegral_symm
#print axioms RMTFoundations.Airy.memLp_airyHankelShiftSlice
#print axioms RMTFoundations.Airy.airyHankelShift_slice_apply_ae
#print axioms RMTFoundations.Airy.airyKernelShift_apply_ae
#print axioms RMTFoundations.Airy.airyKernelGenuine
#print axioms RMTFoundations.Airy.airyKernelGenuine_apply_ae
#print axioms RMTFoundations.Airy.shiftIsometry_conjugates_airyKernelGenuine
#print axioms RMTFoundations.Airy.airyHankelGenuine
#print axioms RMTFoundations.Airy.isHilbertSchmidt_airyHankelGenuine
#print axioms RMTFoundations.Airy.isTraceClass_airyKernelGenuine
#print axioms RMTFoundations.Airy.airyKernelIntegral_diagonal
#print axioms RMTFoundations.Airy.measurable_airyKernelIntegral
#print axioms RMTFoundations.Airy.airyKernelIntegral_bound
#print axioms RMTFoundations.Airy.quadrantMeasure
