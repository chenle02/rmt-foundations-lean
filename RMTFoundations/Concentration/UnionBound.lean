import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Union bounds over finite deterministic grids and derivative-based grid interpolation.
The union bound controls simultaneous events; a finite covering grid and a derivative
bound extend pointwise estimates across a compact interval.
-/

namespace RMTFoundations.Concentration

open MeasureTheory Set Finset

variable {Ω ι : Type* /- [definition] -/ } [MeasurableSpace Ω /- [definition] -/ ] {μ : Measure Ω /- [definition] -/ }

section UnionBound

/-- Union bound with a uniform per-event bound. -/
theorem measureReal_biUnion_le_card_mul {s : Finset ι /- [definition] -/ } {A : ι → Set Ω /- [definition] -/ } {p : ℝ /- [definition] -/ }
    (h : ∀ i ∈ s, μ.real (A i) ≤ p /- [standing] -/ ) :
    μ.real (⋃ i ∈ s, A i) ≤ s.card * p := by
  refine (measureReal_biUnion_finset_le s A).trans ?_
  calc ∑ i ∈ s, μ.real (A i) ≤ ∑ _i ∈ s, p := Finset.sum_le_sum h
    _ = s.card * p := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The union bound read as a simultaneous statement: every `A i` fails with
probability at most `p`, so all of them hold at once with probability at least
`1 - card * p`. -/
theorem one_sub_card_mul_le_measureReal_biInter_compl [IsProbabilityMeasure μ /- [standing] -/ ]
    {s : Finset ι /- [definition] -/ } {A : ι → Set Ω /- [definition] -/ } {p : ℝ /- [definition] -/ }
    (hm : ∀ i ∈ s, MeasurableSet (A i)  /- [standing] -/ ) (h : ∀ i ∈ s, μ.real (A i) ≤ p /- [standing] -/ ) :
    1 - s.card * p ≤ μ.real (⋂ i ∈ s, (A i)ᶜ) := by
  classical
  have hmeas : MeasurableSet (⋃ i ∈ s, A i) :=
    (s.finite_toSet).measurableSet_biUnion (fun i hi => hm i (by simpa using hi))
  have hcompl : (⋂ i ∈ s, (A i)ᶜ) = (⋃ i ∈ s, A i)ᶜ := by
    simp [Set.compl_iUnion]
  rw [hcompl, measureReal_compl hmeas, probReal_univ]
  have := measureReal_biUnion_le_card_mul (μ := μ) h
  linarith

end UnionBound

section PolynomialGrid

/--
The hypothesis `C ≤ N` is what absorbs the constant, and the `+ 1` in the
exponent is what pays for it; an informal argument that drops either produces
`C * N ^ (-D)` and not `N ^ (-D)`. 
-/
theorem measureReal_biUnion_le_rpow {s : Finset ι /- [definition] -/ } {A : ι → Set Ω /- [definition] -/ } {N C D k : ℝ /- [definition] -/ }
    (hN : 1 ≤ N /- [standing] -/ ) (hC : C ≤ N /- [standing] -/ )
    (hcard : (s.card : ℝ) ≤ C * N ^ k /- [standing] -/ )
    (h : ∀ i ∈ s, μ.real (A i) ≤ N ^ (-(D + k + 1))  /- [standing] -/ ) :
    μ.real (⋃ i ∈ s, A i) ≤ N ^ (-D) := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hp0 : (0 : ℝ) ≤ N ^ (-(D + k + 1)) := Real.rpow_nonneg hN0.le _
  refine (measureReal_biUnion_le_card_mul h).trans ?_
  have hstep : (s.card : ℝ) * N ^ (-(D + k + 1)) ≤ (C * N ^ k) * N ^ (-(D + k + 1)) := by
    exact mul_le_mul_of_nonneg_right hcard hp0
  refine hstep.trans ?_
  have hcombine : (C * N ^ k) * N ^ (-(D + k + 1)) = C * N ^ (-(D + 1)) := by
    rw [mul_assoc, ← Real.rpow_add hN0]
    ring_nf
  rw [hcombine]
  have hCN : C * N ^ (-(D + 1)) ≤ N * N ^ (-(D + 1)) :=
    mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN0.le _)
  refine hCN.trans ?_
  have : N * N ^ (-(D + 1)) = N ^ (-D) := by
    nth_rewrite 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hN0]
    ring_nf
  exact le_of_eq this

end PolynomialGrid

section GridInterpolation

/--
 **Grid interpolation.** A function whose derivative is bounded by `L` on
`Icc a b`, and which is bounded by `ε` at every point of a set `G` that is
`δ`-dense in `Icc a b`, is bounded by `ε + L * δ` on all of `Icc a b`.
-/
theorem abs_le_of_forall_grid {f f' : ℝ → ℝ /- [definition] -/ } {a b L δ ε : ℝ /- [definition] -/ } {G : Set ℝ /- [definition] -/ }
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x /- [standing] -/ )
    (hbound : ∀ x ∈ Icc a b, |f' x| ≤ L /- [standing] -/ )
    (hdense : ∀ x ∈ Icc a b, ∃ g ∈ G, g ∈ Icc a b ∧ |x - g| ≤ δ /- [standing] -/ )
    (hgrid : ∀ g ∈ G, g ∈ Icc a b → |f g| ≤ ε /- [standing] -/ ) :
    ∀ x ∈ Icc a b, |f x| ≤ ε + L * δ := by
  intro x hx
  obtain ⟨g, hgG, hgI, hgx⟩ := hdense x hx
  have hlip : ‖f x - f g‖ ≤ L * ‖x - g‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => hf y hy) (fun y hy => by simpa [Real.norm_eq_abs] using hbound y hy)
      hgI hx
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hbound x hx)
  have hstep : |f x - f g| ≤ L * δ := by
    refine le_trans (by simpa [Real.norm_eq_abs] using hlip) ?_
    have : ‖x - g‖ ≤ δ := by simpa [Real.norm_eq_abs] using hgx
    exact mul_le_mul_of_nonneg_left this hL0
  have hg' : |f g| ≤ ε := hgrid g hgG hgI
  have h1 : f g ≤ |f g| := le_abs_self _
  have h2 : -|f g| ≤ f g := neg_abs_le _
  have h3 : f x - f g ≤ |f x - f g| := le_abs_self _
  have h4 : -|f x - f g| ≤ f x - f g := neg_abs_le _
  rw [abs_le]
  constructor <;> linarith

end GridInterpolation


section DeterministicNet

/-- The explicit arithmetic grid on `[a, b]` with mesh `δ`: the points
`a + k * δ` for `k ≤ n`, each clipped to `b` so the grid never leaves the
interval. -/
noncomputable def arithGrid (a b δ : ℝ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) : Finset ℝ :=
  (Finset.range (n + 1)).image (fun k : ℕ => min (a + (k : ℝ) * δ) b)

theorem arithGrid_mem_Icc {a b δ : ℝ /- [definition] -/ } (hab : a ≤ b /- [standing] -/ ) (hδ : 0 ≤ δ /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∀ g ∈ arithGrid a b δ n, g ∈ Icc a b := by
  intro g hg
  simp only [arithGrid, Finset.mem_image, Finset.mem_range] at hg
  obtain ⟨k, _, rfl⟩ := hg
  have hk : (0 : ℝ) ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
  exact ⟨le_min (by linarith) hab, min_le_right _ _⟩

theorem arithGrid_card_le (a b δ : ℝ /- [definition] -/ ) (n : ℕ /- [definition] -/ ) : (arithGrid a b δ n).card ≤ n + 1 :=
  le_trans Finset.card_image_le (by simp)

/--
 **The deterministic net.** Every point of `[a, b]` lies within the mesh `δ`
of a grid point, and the grid has at most `(b - a) / δ + 2` points.
-/
theorem exists_dense_grid {a b δ : ℝ /- [definition] -/ } (hab : a ≤ b /- [standing] -/ ) (hδ : 0 < δ /- [standing] -/ ) :
    ∃ G : Finset ℝ, (∀ g ∈ G, g ∈ Icc a b) ∧ (G.card : ℝ) ≤ (b - a) / δ + 2 ∧
      ∀ x ∈ Icc a b, ∃ g ∈ G, g ∈ Icc a b ∧ |x - g| ≤ δ := by
  classical
  have hba : (0 : ℝ) ≤ (b - a) / δ := div_nonneg (by linarith) hδ.le
  set n : ℕ := ⌈(b - a) / δ⌉₊ with hn
  refine ⟨arithGrid a b δ n, arithGrid_mem_Icc hab hδ.le n, ?_, ?_⟩
  · have hcard : ((arithGrid a b δ n).card : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast arithGrid_card_le a b δ n
    have hceil : (n : ℝ) < (b - a) / δ + 1 := by
      rw [hn]; exact Nat.ceil_lt_add_one hba
    linarith
  · intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have hxa : (0 : ℝ) ≤ (x - a) / δ := div_nonneg (by linarith) hδ.le
    set k : ℕ := ⌊(x - a) / δ⌋₊ with hk
    have hkn : k ≤ n := by
      have h1 : k ≤ ⌊(b - a) / δ⌋₊ :=
        Nat.floor_le_floor (by gcongr)
      have h2 : ⌊(b - a) / δ⌋₊ ≤ n := by
        rw [hn]; exact_mod_cast (Nat.floor_le hba).trans (Nat.le_ceil _)
      exact h1.trans h2
    have hfl : (k : ℝ) ≤ (x - a) / δ := Nat.floor_le hxa
    have hlow : a + k * δ ≤ x := by
      have h1 : (k : ℝ) * δ ≤ ((x - a) / δ) * δ := mul_le_mul_of_nonneg_right hfl hδ.le
      rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h1
      linarith
    have hfu : (x - a) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hhigh : x - (a + k * δ) ≤ δ := by
      have h2 : ((x - a) / δ) * δ < ((k : ℝ) + 1) * δ := mul_lt_mul_of_pos_right hfu hδ
      rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h2
      nlinarith
    have hmem : min (a + k * δ) b ∈ arithGrid a b δ n := by
      simp only [arithGrid, Finset.mem_image, Finset.mem_range]
      exact ⟨k, by omega, rfl⟩
    refine ⟨min (a + k * δ) b, hmem, arithGrid_mem_Icc hab hδ.le n _ hmem, ?_⟩
    have hmin : min (a + k * δ) b = a + k * δ := min_eq_left (by linarith)
    rw [hmin, abs_le]
    constructor <;> linarith

end DeterministicNet

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.measureReal_biUnion_le_card_mul
#print axioms RMTFoundations.Concentration.one_sub_card_mul_le_measureReal_biInter_compl
#print axioms RMTFoundations.Concentration.measureReal_biUnion_le_rpow
#print axioms RMTFoundations.Concentration.abs_le_of_forall_grid
#print axioms RMTFoundations.Concentration.arithGrid
#print axioms RMTFoundations.Concentration.arithGrid_mem_Icc
#print axioms RMTFoundations.Concentration.arithGrid_card_le
#print axioms RMTFoundations.Concentration.exists_dense_grid
