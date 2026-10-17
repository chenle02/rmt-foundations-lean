import Mathlib.Probability.Moments.Basic

/-!
# Optimised Chernoff bounds

Mathlib proves the *single-parameter* Chernoff bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf`, namely
`μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t` for one fixed `t ≥ 0`, and
the analogous lower-tail and `cgf` variants.  What mathlib does *not* state is
the step that actually makes Chernoff's method useful: the optimisation of that
family over `t`, and the resulting Cramér rate function.  This file supplies
exactly that layer, plus a two-sided version.

## What is proved here

* `measure_ge_le_iInf_exp_mul_mgf` — the upper tail is bounded by the
  infimum over `t ≥ 0` of `exp (-t * ε) * mgf X μ t`.
* `measure_le_le_iInf_exp_mul_mgf` — the matching lower-tail statement,
  infimum over `t ≤ 0`.
* `measure_abs_ge_le_exp_mul_mgf` — two-sided bound at a fixed `t ≥ 0`.
* `measure_abs_ge_le_iInf_exp_mul_mgf` — the optimised two-sided bound.
* `cramerRate` — the Legendre-type transform
  `⨆ t ≥ 0, (t * ε - cgf X μ t)`, and
  `measure_ge_le_exp_neg_cramerRate`, `cramerRate_nonneg`.

## What is NOT proved here

* No Cramér large-deviation *theorem*: there is no lower bound matching
  `measure_ge_le_exp_neg_cramerRate`, and no identification of `cramerRate`
  with the convex conjugate in any structural sense.  Only the easy
  (upper-bound) half of Cramér's theorem is here.
* `cramerRate` is a plain real supremum, so when the family
  `t ↦ t * ε - cgf X μ t` is unbounded above it takes mathlib's junk value `0`
  rather than `⊤`.  The tail bound below is still *true* in that case (it
  degenerates to `≤ 1`), but it carries no information there.  Nothing in this
  file asserts that the supremum is attained or finite.
* No concentration inequality of any specific shape (Hoeffding, Bernstein,
  Bennett) is derived here; this file is only the optimisation scaffolding.
-/

namespace RMTFoundations.Concentration

open MeasureTheory Real
open ProbabilityTheory

variable {Ω : Type* /- [definition] -/ } {mΩ : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ } {X : Ω → ℝ /- [definition] -/ } {t ε : ℝ /- [definition] -/ }

section Optimisation

/-- **Optimised Chernoff bound**, upper tail.  The single-`t` bound of
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` holds simultaneously for every
`t ≥ 0`, hence for the infimum. -/
theorem measure_ge_le_iInf_exp_mul_mgf [IsFiniteMeasure μ /- [standing] -/ ]
    (h_int : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ exp (t * X ω)) μ /- [standing] -/ ) (ε : ℝ /- [definition] -/ ) :
    μ.real {ω | ε ≤ X ω} ≤ ⨅ t : {t : ℝ // 0 ≤ t}, exp (-t.1 * ε) * mgf X μ t.1 := by
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  exact le_ciInf fun t ↦ measure_ge_le_exp_mul_mgf ε t.2 (h_int t.1 t.2)

/-- **Optimised Chernoff bound**, lower tail. -/
theorem measure_le_le_iInf_exp_mul_mgf [IsFiniteMeasure μ /- [standing] -/ ]
    (h_int : ∀ t : ℝ, t ≤ 0 → Integrable (fun ω ↦ exp (t * X ω)) μ /- [standing] -/ ) (ε : ℝ /- [definition] -/ ) :
    μ.real {ω | X ω ≤ ε} ≤ ⨅ t : {t : ℝ // t ≤ 0}, exp (-t.1 * ε) * mgf X μ t.1 := by
  have : Nonempty {t : ℝ // t ≤ 0} := ⟨⟨0, le_rfl⟩⟩
  exact le_ciInf fun t ↦ measure_le_le_exp_mul_mgf ε t.2 (h_int t.1 t.2)

end Optimisation

section TwoSided

/-- Two-sided Chernoff bound at a fixed `t ≥ 0`.  The two tails are controlled
by `mgf X μ t` and `mgf X μ (-t)` respectively. -/
theorem measure_abs_ge_le_exp_mul_mgf [IsFiniteMeasure μ /- [standing] -/ ] (ht : 0 ≤ t /- [standing] -/ )
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ /- [standing] -/ )
    (h_int' : Integrable (fun ω ↦ exp (-t * X ω)) μ /- [definition] -/ ) :
    μ.real {ω | ε ≤ |X ω|} ≤ exp (-t * ε) * (mgf X μ t + mgf X μ (-t)) := by
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | X ω ≤ -ε} := by
    intro ω hω
    rcases abs_cases (X ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by rw [Set.mem_setOf_eq]; rw [Set.mem_setOf_eq, h1] at hω; exact hω)
    · refine Or.inr ?_
      rw [Set.mem_setOf_eq]
      rw [Set.mem_setOf_eq, h1] at hω
      linarith
  have h1 : μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t :=
    measure_ge_le_exp_mul_mgf ε ht h_int
  have h2 : μ.real {ω | X ω ≤ -ε} ≤ exp (-t * ε) * mgf X μ (-t) := by
    have := measure_le_le_exp_mul_mgf (μ := μ) (X := X) (t := -t) (-ε)
      (neg_nonpos.mpr ht) h_int'
    have heq : -(-t) * -ε = -t * ε := by ring
    rwa [heq] at this
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | X ω ≤ -ε}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | X ω ≤ -ε} := measureReal_union_le _ _
    _ ≤ exp (-t * ε) * mgf X μ t + exp (-t * ε) * mgf X μ (-t) := by gcongr
    _ = exp (-t * ε) * (mgf X μ t + mgf X μ (-t)) := by ring

/-- **Optimised two-sided Chernoff bound.** -/
theorem measure_abs_ge_le_iInf_exp_mul_mgf [IsFiniteMeasure μ /- [standing] -/ ]
    (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ /- [standing] -/ ) :
    μ.real {ω | ε ≤ |X ω|} ≤
      ⨅ t : {t : ℝ // 0 ≤ t}, exp (-t.1 * ε) * (mgf X μ t.1 + mgf X μ (-t.1)) := by
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  exact le_ciInf fun t ↦
    measure_abs_ge_le_exp_mul_mgf t.2 (h_int t.1) (h_int (-t.1))

end TwoSided

section CramerRate

/-- The **Cramér rate function** of `X` at level `ε`: the Legendre-type
transform `⨆ t ≥ 0, (t * ε - cgf X μ t)` of the cumulant generating function.

This is a plain real supremum.  If the family is unbounded above it evaluates to
mathlib's junk value `0`; see the module docstring. -/
noncomputable def cramerRate (X : Ω → ℝ /- [definition] -/ ) (μ : Measure Ω /- [definition] -/ ) (ε : ℝ /- [definition] -/ ) : ℝ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, (t.1 * ε - cgf X μ t.1)

/-- The rate function is nonnegative whenever the defining family is bounded
above: the value at `t = 0` is `0`. -/
theorem cramerRate_nonneg [IsZeroOrProbabilityMeasure μ /- [definition] -/ ]
    (hbdd : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ t.1 * ε - cgf X μ t.1)  /- [standing] -/ ) :
    0 ≤ cramerRate X μ ε := by
  have hval : ((⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t}) : ℝ) * ε -
      cgf X μ ((⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t}) : ℝ) = 0 := by
    show (0 : ℝ) * ε - cgf X μ 0 = 0
    rw [cgf_zero]; ring
  have hle := le_ciSup hbdd (⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t})
  rw [hval] at hle
  exact hle

/-- **Chernoff bound in rate-function form.**  This is the easy half of
Cramér's theorem: the upper tail decays at least as fast as `exp (-I(ε))`,
where `I` is the Cramér rate function.  No matching lower bound is proved. -/
theorem measure_ge_le_exp_neg_cramerRate [IsProbabilityMeasure μ /- [standing] -/ ]
    (h_int : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ exp (t * X ω)) μ /- [standing] -/ ) (ε : ℝ /- [definition] -/ ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-cramerRate X μ ε) := by
  set S : Set ℝ := Set.range fun t : {t : ℝ // 0 ≤ t} ↦ t.1 * ε - cgf X μ t.1 with hS
  have hle_one : μ.real {ω | ε ≤ X ω} ≤ 1 := by
    have := measureReal_mono (μ := μ) (Set.subset_univ {ω | ε ≤ X ω}) (measure_ne_top _ _)
    rwa [probReal_univ] at this
  by_cases hbdd : BddAbove S
  · by_contra hcon
    rw [not_le] at hcon
    have hpos : 0 < μ.real {ω | ε ≤ X ω} := lt_of_le_of_lt (exp_pos _).le hcon
    have hlog : -cramerRate X μ ε < log (μ.real {ω | ε ≤ X ω}) := by
      rw [← Real.exp_log hpos] at hcon
      exact Real.exp_lt_exp.mp hcon
    have hlt : -log (μ.real {ω | ε ≤ X ω}) < cramerRate X μ ε := by linarith
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup (f := fun t : {t : ℝ // 0 ≤ t} ↦
      t.1 * ε - cgf X μ t.1) hlt
    have hbound : μ.real {ω | ε ≤ X ω} ≤ exp (-t.1 * ε + cgf X μ t.1) :=
      measure_ge_le_exp_cgf ε t.2 (h_int t.1 t.2)
    have : exp (-t.1 * ε + cgf X μ t.1) < μ.real {ω | ε ≤ X ω} := by
      rw [← Real.exp_log hpos]
      refine Real.exp_lt_exp.mpr ?_
      have : -log (μ.real {ω | ε ≤ X ω}) < t.1 * ε - cgf X μ t.1 := ht
      linarith
    linarith
  · have : cramerRate X μ ε = 0 := Real.iSup_of_not_bddAbove (by rwa [← hS])
    rw [this, neg_zero, Real.exp_zero]
    exact hle_one

end CramerRate

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.measure_ge_le_iInf_exp_mul_mgf
#print axioms RMTFoundations.Concentration.measure_le_le_iInf_exp_mul_mgf
#print axioms RMTFoundations.Concentration.measure_abs_ge_le_exp_mul_mgf
#print axioms RMTFoundations.Concentration.measure_abs_ge_le_iInf_exp_mul_mgf
#print axioms RMTFoundations.Concentration.cramerRate
#print axioms RMTFoundations.Concentration.cramerRate_nonneg
#print axioms RMTFoundations.Concentration.measure_ge_le_exp_neg_cramerRate
