import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Increments of an `L²` martingale

This file proves the orthogonality of martingale increments in `L²`, which is the
single analytic fact that the whole first rung of the Itô integral rests on.

Everything here is stated for an arbitrary `Preorder` index type `ι`, so it applies
verbatim to discrete time (`ι = ℕ`) and to continuous time (`ι = ℝ≥0`, `ι = ℝ`).
Mathlib's `MeasureTheory.Martingale` is already index-generic; what is missing there
is any statement about products of increments, and that is what is supplied here.

## What is proved

* `condExp_increment_ae_eq_zero`: for a martingale `M` and `s ≤ t`, the conditional
  expectation of the increment `M t - M s` given the past is a.e. zero.
* `integral_mul_increment_eq_zero`: if `X` is measurable with respect to the past
  `ℱ s` and the product is integrable, then `E[X · (M t - M s)] = 0`.  This is the
  pull-out property of conditional expectation combined with the previous lemma.
* `integral_increment_mul_increment_eq_zero`: increments of an `L²` martingale over
  two non-overlapping intervals `[s, t]` and `[u, v]` with `t ≤ u` are orthogonal
  in `L²`.
* `integral_sq_increment`: the `L²` Pythagoras identity
  `E[(M t - M s)²] = E[(M t)²] - E[(M s)²]`.

## What is *not* proved here

Nothing about quadratic variation, no Doob `L²` inequality, no continuity of paths,
no localisation. Those are listed in `RMTFoundations/Stochastic/Basic.lean` with the
reason each one is out of reach.
-/

namespace RMTFoundations.Stochastic

open MeasureTheory
open scoped ENNReal

variable {Ω ι : Type* /- [definition] -/ } [Preorder ι /- [definition] -/ ] {m0 : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ }
  {ℱ : Filtration ι m0} {M : ι → Ω → ℝ}

section Integrability

/-- A real function in `L²` has an integrable square. -/
theorem integrable_sq_of_memLp_two {f : Ω → ℝ /- [definition] -/ } (hf : MemLp f 2 μ /- [standing] -/ ) :
    Integrable (fun ω => f ω ^ 2) μ := by
  have h : Integrable (f * f) μ := hf.integrable_mul hf
  refine h.congr ?_
  filter_upwards with ω
  rw [Pi.mul_apply, ← pow_two]

/-- The product of two real functions in `L²` is integrable. -/
theorem integrable_mul_of_memLp_two {f g : Ω → ℝ /- [definition] -/ } (hf : MemLp f 2 μ /- [standing] -/ ) (hg : MemLp g 2 μ /- [standing] -/ ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have h : Integrable (f * g) μ := hf.integrable_mul hg
  exact h

end Integrability

section Orthogonality

/-- The conditional expectation of a martingale increment given the past vanishes. -/
theorem condExp_increment_ae_eq_zero [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) {s t : ι /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) :
    μ[M t - M s | ℱ s] =ᵐ[μ] 0 := by
  have h1 := condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
  have h2 := hM.condExp_ae_eq hst
  have h3 : (μ[M s | ℱ s]) = M s :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyMeasurable s) (hM.integrable s)
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1, Pi.sub_apply, hω2, h3, sub_self, Pi.zero_apply]

/-- **Pull-out orthogonality.** If `X` is measurable with respect to the past `ℱ s`
and `X · (M t - M s)` is integrable, then `X` is orthogonal in `L¹` to the increment
of the martingale `M` over `[s, t]`. -/
theorem integral_mul_increment_eq_zero [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) {s t : ι /- [definition] -/ } (hst : s ≤ t /- [standing] -/ )
    {X : Ω → ℝ /- [definition] -/ } (hX : StronglyMeasurable[ℱ s] X /- [standing] -/ )
    (hXM : Integrable (fun ω => X ω * (M t ω - M s ω)) μ /- [standing] -/ ) :
    ∫ ω, X ω * (M t ω - M s ω) ∂μ = 0 := by
  have hint : Integrable (M t - M s) μ := (hM.integrable t).sub (hM.integrable s)
  have hXM' : Integrable (X * (M t - M s)) μ := hXM
  have h1 : μ[X * (M t - M s) | ℱ s] =ᵐ[μ] X * μ[M t - M s | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left hX hXM' hint
  have h2 := condExp_increment_ae_eq_zero hM hst
  have h3 : μ[X * (M t - M s) | ℱ s] =ᵐ[μ] 0 := by
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2, Pi.zero_apply, mul_zero]
  have h4 : ∫ ω, (μ[X * (M t - M s) | ℱ s]) ω ∂μ = ∫ ω, (X * (M t - M s)) ω ∂μ :=
    integral_condExp (ℱ.le s)
  have h5 : ∫ ω, (μ[X * (M t - M s) | ℱ s]) ω ∂μ = 0 := by
    rw [integral_congr_ae h3]
    exact integral_zero Ω ℝ
  have h6 : ∫ ω, X ω * (M t ω - M s ω) ∂μ = ∫ ω, (X * (M t - M s)) ω ∂μ := rfl
  rw [h6, ← h4, h5]

/-- **Orthogonality of martingale increments over non-overlapping intervals.**
For `s ≤ t ≤ u ≤ v`, the increments `M t - M s` and `M v - M u` of an `L²` martingale
are orthogonal in `L²`. -/
theorem integral_increment_mul_increment_eq_zero [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    {s t u v : ι /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) (htu : t ≤ u /- [standing] -/ ) (huv : u ≤ v /- [standing] -/ ) :
    ∫ ω, (M t ω - M s ω) * (M v ω - M u ω) ∂μ = 0 := by
  have hXmeas : StronglyMeasurable[ℱ u] (M t - M s) := by
    have ht : StronglyMeasurable[ℱ u] (M t) := (hM.stronglyMeasurable t).mono (ℱ.mono htu)
    have hs : StronglyMeasurable[ℱ u] (M s) := (hM.stronglyMeasurable s).mono (ℱ.mono (hst.trans htu))
    exact ht.sub hs
  have hX2 : MemLp (M t - M s) 2 μ := (hM2 t).sub (hM2 s)
  have hY2 : MemLp (M v - M u) 2 μ := (hM2 v).sub (hM2 u)
  have hint : Integrable (fun ω => (M t ω - M s ω) * (M v ω - M u ω)) μ :=
    integrable_mul_of_memLp_two hX2 hY2
  exact integral_mul_increment_eq_zero hM huv hXmeas hint

/-- **`L²` Pythagoras for martingale increments.** -/
theorem integral_sq_increment [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ ) {s t : ι /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂μ = (∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ := by
  have hcross : ∫ ω, M s ω * (M t ω - M s ω) ∂μ = 0 :=
    integral_mul_increment_eq_zero hM hst (hM.stronglyMeasurable s)
      (integrable_mul_of_memLp_two (hM2 s) ((hM2 t).sub (hM2 s)))
  have hit : Integrable (fun ω => M t ω ^ 2) μ := integrable_sq_of_memLp_two (hM2 t)
  have his : Integrable (fun ω => M s ω ^ 2) μ := integrable_sq_of_memLp_two (hM2 s)
  have hcr : Integrable (fun ω => M s ω * (M t ω - M s ω)) μ :=
    integrable_mul_of_memLp_two (hM2 s) ((hM2 t).sub (hM2 s))
  have hpt : ∀ ω, (M t ω - M s ω) ^ 2
      = M t ω ^ 2 - M s ω ^ 2 - 2 * (M s ω * (M t ω - M s ω)) := by
    intro ω
    ring
  calc ∫ ω, (M t ω - M s ω) ^ 2 ∂μ
      = ∫ ω, (M t ω ^ 2 - M s ω ^ 2 - 2 * (M s ω * (M t ω - M s ω))) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ ω, (M t ω ^ 2 - M s ω ^ 2) ∂μ) - ∫ ω, 2 * (M s ω * (M t ω - M s ω)) ∂μ := by
        exact integral_sub (hit.sub his) (hcr.const_mul 2)
    _ = ((∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ) - 2 * ∫ ω, M s ω * (M t ω - M s ω) ∂μ := by
        rw [integral_sub hit his, integral_const_mul]
    _ = (∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ := by
        rw [hcross, mul_zero, sub_zero]

end Orthogonality

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.integrable_sq_of_memLp_two
#print axioms RMTFoundations.Stochastic.integrable_mul_of_memLp_two
#print axioms RMTFoundations.Stochastic.condExp_increment_ae_eq_zero
#print axioms RMTFoundations.Stochastic.integral_mul_increment_eq_zero
#print axioms RMTFoundations.Stochastic.integral_increment_mul_increment_eq_zero
#print axioms RMTFoundations.Stochastic.integral_sq_increment
