import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt

/-!
Scalar binomial walk-count majorants.
These inequalities bound algebraic expressions; combinatorial counting hypotheses
remain explicit where required.
-/

namespace RMTFoundations.WalkMajorant

/--
The degenerate case `s = 0` is handled separately: there `v ≤ k` may fail
(at `k = 0`, `v = 1`), but both `v^(2s)` and `k^(2s)` are then `1`. 
-/
theorem walk_count_majorant (k v s : ℕ /- [definition] -/ ) (hv : 1 ≤ v /- [standing] -/ ) (hk : k + 2 = 2 * v + s /- [standing] -/ ) :
    (k.choose (2 * v - 2) : ℝ) * (v : ℝ) ^ (2 * s) * 2 ^ (2 * v - 2)
      ≤ 2 ^ k * (k : ℝ) ^ (3 * s) := by
  have hsk : s ≤ k := by omega
  have hks : k - s = 2 * v - 2 := by omega
  have hchooseNat : k.choose (2 * v - 2) ≤ k ^ s := by
    rw [← hks, Nat.choose_symm hsk]
    exact Nat.choose_le_pow k s
  have hchoose : (k.choose (2 * v - 2) : ℝ) ≤ (k : ℝ) ^ s := by exact_mod_cast hchooseNat
  have hvk : (v : ℝ) ^ (2 * s) ≤ (k : ℝ) ^ (2 * s) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; norm_num
    · refine pow_le_pow_left₀ (by positivity) ?_ _
      have hvle : v ≤ k := by omega
      exact_mod_cast hvle
  have htwo : (2 : ℝ) ^ (2 * v - 2) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : s + 2 * s = 3 * s := by ring
  have hexp : (k : ℝ) ^ s * (k : ℝ) ^ (2 * s) = (k : ℝ) ^ (3 * s) := by
    rw [← pow_add, hsum]
  calc (k.choose (2 * v - 2) : ℝ) * (v : ℝ) ^ (2 * s) * 2 ^ (2 * v - 2)
      ≤ (k : ℝ) ^ s * (k : ℝ) ^ (2 * s) * 2 ^ k := by
        have hfirst : (k.choose (2 * v - 2) : ℝ) * (v : ℝ) ^ (2 * s)
            ≤ (k : ℝ) ^ s * (k : ℝ) ^ (2 * s) :=
          mul_le_mul hchoose hvk (by positivity) (by positivity)
        exact mul_le_mul hfirst htwo (by positivity) (by positivity)
    _ = 2 ^ k * (k : ℝ) ^ (3 * s) := by rw [hexp]; ring

/-- The majorant is attained at `k = 2`, `v = 2`, `s = 0`: both sides are `4`.

So the three ingredients together lose nothing at the defect-free end of the
range, and the bound cannot be sharpened by a constant factor. -/
theorem walk_count_majorant_tight :
    ((2 : ℕ).choose (2 * 2 - 2) : ℝ) * ((2 : ℕ) : ℝ) ^ (2 * 0) * 2 ^ (2 * 2 - 2)
      = 2 ^ (2 : ℕ) * ((2 : ℕ) : ℝ) ^ (3 * 0) := by
  norm_num

/--
The proof is the comparison itself: the tail bound
`geom_sum_Ico_le_of_lt_one` at base point `0` gives `∑_{s < m} x^s ≤ 1/(1-x)`,
and `x ≤ 1/2` makes `1 - x ≥ 1/2`. 
-/
theorem geom_range_le_two {x : ℝ /- [definition] -/ } (hx0 : 0 ≤ x /- [standing] -/ ) (hx : x ≤ 1 / 2 /- [standing] -/ ) (m : ℕ /- [definition] -/ ) :
    ∑ s ∈ Finset.range m, x ^ s ≤ 2 := by
  have hlt : x < 1 := by linarith
  have hden : (0 : ℝ) < 1 - x := by linarith
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hx0 hlt
  rw [← Finset.range_eq_Ico] at h
  simp only [pow_zero] at h
  refine h.trans ?_
  rw [div_le_iff₀ hden]
  linarith

/-- The hypothesis `x ≤ 1/2` is load-bearing: at `x = 1` already three terms
exceed `2`.  So the constant `2` is a consequence of the smallness of
`k^3 q`, not a generic feature of the finite sum. -/
theorem geom_ratio_hypothesis_load_bearing :
    ¬ ((∑ s ∈ Finset.range 3, (1 : ℝ) ^ s) ≤ 2) := by
  norm_num

/-- At even orders, the powers of two and of the aspect-ratio constant combine into one power. -/
theorem two_sqrt_pow (C : ℝ /- [definition] -/ ) (hC : 0 ≤ C /- [standing] -/ ) (m : ℕ /- [definition] -/ ) :
    (2 * Real.sqrt C) ^ (2 * m) = 2 ^ (2 * m) * C ^ m := by
  rw [mul_pow, pow_mul (Real.sqrt C) 2 m, Real.sq_sqrt hC]

/--
The count majorant `2^(2m) k^(3s)` of `walk_count_majorant` at even order
`k = 2m`, multiplied by a walk weight of exactly the shape that `WalkWeight`
delivers, `N₀ * C_asp^m * q^s`, is the printed summand
`N₀ (2 sqrt C_asp)^(2m) (k^3 q)^s`.

This is an identity, not an estimate: all the loss in the display is in the
count majorant and in the weight bound, and none of it is here. 
-/
theorem assembled_term (N₀ Casp q : ℝ /- [definition] -/ ) (k m s : ℕ /- [definition] -/ ) (hCasp : 0 ≤ Casp /- [standing] -/ ) :
    (2 ^ (2 * m) * (k : ℝ) ^ (3 * s)) * (N₀ * Casp ^ m * q ^ s)
      = N₀ * (2 * Real.sqrt Casp) ^ (2 * m) * (((k : ℝ) ^ 3 * q) ^ s) := by
  rw [two_sqrt_pow Casp hCasp m, mul_pow, ← pow_mul]
  ring

/-- **The absorption step**, in its abstract form: a quantity dominated by a
constant times a finite geometric sum of ratio at most `1/2` is dominated by
twice that constant.

`M` stands for the whole prefactor `N₀ (2 sqrt C_asp)^k` and `x` for the ratio
`k^3 q`.  Keeping them abstract is deliberate: this step knows nothing about
traces, walks or matrices. -/
theorem trace_moment_geometric_majorant {T M x : ℝ /- [definition] -/ } {m : ℕ /- [definition] -/ }
    (hM : 0 ≤ M /- [standing] -/ ) (hx0 : 0 ≤ x /- [standing] -/ ) (hx : x ≤ 1 / 2 /- [standing] -/ )
    (hT : T ≤ M * ∑ s ∈ Finset.range m, x ^ s /- [standing] -/ ) :
    T ≤ 2 * M := by
  refine hT.trans ?_
  have h := geom_range_le_two hx0 hx m
  calc M * ∑ s ∈ Finset.range m, x ^ s ≤ M * 2 := mul_le_mul_of_nonneg_left h hM
    _ = 2 * M := by ring

/--
    0 ≤ E Tr H_X^k ≤ N₀ (2 sqrt C_asp)^k Σ_s (k^3 q)^s ≤ 2 N₀ (2 sqrt C_asp)^k.

`T` stands for `E Tr H_X^k` and is an arbitrary real: its nonnegativity and the
middle inequality are hypotheses, supplied from the probabilistic part of the
argument that this file does not touch.  What is proved is exactly the step the
obligation asks for, namely that the finite sum over admissible defects is
absorbed into the constant `2`.
-/
theorem trace_moment_display {T N₀ Casp q : ℝ /- [definition] -/ } {k m : ℕ /- [definition] -/ }
    (hT0 : 0 ≤ T /- [standing] -/ ) (hN₀ : 0 ≤ N₀ /- [standing] -/ )
    (hx0 : 0 ≤ (k : ℝ) ^ 3 * q /- [standing] -/ ) (hx : (k : ℝ) ^ 3 * q ≤ 1 / 2 /- [standing] -/ )
    (hT : T ≤ N₀ * (2 * Real.sqrt Casp) ^ k
            * ∑ s ∈ Finset.range m, ((k : ℝ) ^ 3 * q) ^ s /- [standing] -/ ) :
    0 ≤ T ∧ T ≤ 2 * (N₀ * (2 * Real.sqrt Casp) ^ k) := by
  refine ⟨hT0, trace_moment_geometric_majorant ?_ hx0 hx hT⟩
  exact mul_nonneg hN₀ (pow_nonneg (by positivity) k)

end RMTFoundations.WalkMajorant

#print axioms RMTFoundations.WalkMajorant.walk_count_majorant
#print axioms RMTFoundations.WalkMajorant.walk_count_majorant_tight
#print axioms RMTFoundations.WalkMajorant.geom_range_le_two
#print axioms RMTFoundations.WalkMajorant.geom_ratio_hypothesis_load_bearing
#print axioms RMTFoundations.WalkMajorant.two_sqrt_pow
#print axioms RMTFoundations.WalkMajorant.assembled_term
#print axioms RMTFoundations.WalkMajorant.trace_moment_geometric_majorant
#print axioms RMTFoundations.WalkMajorant.trace_moment_display
