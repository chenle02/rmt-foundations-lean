import RMTFoundations.Concentration.NonCrossing
import RMTFoundations.Concentration.SemicircleMoments

/-

# The Catalan count of non-crossing pair partitions

`RMTFoundations.Concentration.NonCrossing` defines non-crossing pair partitions of `Fin n`
and proves their structure theory, but leaves the count open: there, only `n = 0, 2, 4` are
settled, and those by `decide` rather than by an argument.  This file closes the count for
every `n`, by the first-return decomposition that matches mathlib's `catalan_succ`.

## The argument

Fix a non-crossing pairing `f` of `Fin n` and look at the arc `{0, f 0}` through the leftmost
point.  `IsNonCrossing.odd_sub` forces `f 0` to sit at an odd position `a + 1`;
`IsNonCrossing.mem_Ioo` says the `a` points strictly inside that arc are matched among
themselves, and `IsNonCrossing.notMem_Ioo` says the `b` points to its right are too.  So `f`
splits into a non-crossing pairing of `Fin a` and one of `Fin b` with `n = a + b + 2`, and
`glue` puts any such pair back together.  Summing the resulting product formula over the
fibres of `f ↦ f 0` is exactly the Catalan convolution.

All of the re-indexing is done through `extendVal` and `glueVal`, which describe the glued
pairing as a function `ℕ → ℕ`; `Fin` enters only through one boundedness lemma
(`glueVal_lt`).  The restriction maps `insidePart` and `outsidePart` are total, using a `min`
clamp as a junk value, so that `Finset.card_nbij'` applies with no dependent transport.

## What is proved here

* `glue`, `insidePart`, `outsidePart` — the decomposition maps, with `glue_isPairing`,
  `glue_isNonCrossing`, `insidePart_isPairing`, `insidePart_isNonCrossing`,
  `outsidePart_isPairing`, `outsidePart_isNonCrossing`, and the two inverse-composition identities
  `glue_parts`, `insidePart_glue` / `outsidePart_glue`.
* `card_fibre_even` — the fibre of `f ↦ f 0` over an even position is empty.
* `card_fibre_odd` — **the product formula**: the fibre over position `a + 1` has
  `#(nonCrossingPairings a) * #(nonCrossingPairings b)` elements when `n = a + b + 2`.
* `card_nonCrossingPairings` — **the count**:
  `(nonCrossingPairings (2 * k)).card = catalan k`, for all `k`.
* `card_nonCrossingPairings_of_even`, `card_nonCrossingPairings_of_not_even`,
  `card_nonCrossingPairings_six` — restatements and the first case that `decide` cannot do.
* `semicircleMoment_eq_card_nonCrossingPairings` — the `2 k`-th moment of the semicircle
  density equals the number of non-crossing pairings of `2 k` points.  This is the theorem
  that joins `SemicircleMoments` to `NonCrossing`; before it, the two occurrences of
  `catalan k` in this library were unconnected coincidences.

## What is NOT proved here
-/

namespace RMTFoundations.Concentration

open Finset

section Extend

/-- `extendVal m g x` is `g x` read as a natural number, extended by the junk value `0`
outside `Fin m`.  Working at the level of `ℕ` keeps the gluing construction below free of
dependent-type transport. -/
def extendVal (m : ℕ /- [definition] -/ ) (g : Fin m → Fin m /- [definition] -/ ) (x : ℕ /- [definition] -/ ) : ℕ :=
  if h : x < m then (g ⟨x, h⟩ : ℕ) else 0

theorem extendVal_of_lt {m : ℕ /- [definition] -/ } (g : Fin m → Fin m /- [definition] -/ ) {x : ℕ /- [definition] -/ } (hx : x < m /- [standing] -/ ) :
    extendVal m g x = (g ⟨x, hx⟩ : ℕ) := dif_pos hx

theorem extendVal_lt {m : ℕ /- [definition] -/ } (g : Fin m → Fin m /- [definition] -/ ) {x : ℕ /- [definition] -/ } (hx : x < m /- [standing] -/ ) :
    extendVal m g x < m := by
  rw [extendVal_of_lt g hx]
  exact (g ⟨x, hx⟩).isLt

theorem extendVal_extendVal {m : ℕ /- [definition] -/ } {g : Fin m → Fin m /- [definition] -/ } (hg : IsPairing g /- [standing] -/ ) {x : ℕ /- [definition] -/ }
    (hx : x < m /- [standing] -/ ) : extendVal m g (extendVal m g x) = x := by
  have h2 : ((g ⟨x, hx⟩ : Fin m) : ℕ) < m := (g ⟨x, hx⟩).isLt
  rw [extendVal_of_lt g hx, extendVal_of_lt g h2, Fin.eta, hg.1 ⟨x, hx⟩]

theorem extendVal_ne {m : ℕ /- [definition] -/ } {g : Fin m → Fin m /- [definition] -/ } (hg : IsPairing g /- [standing] -/ ) {x : ℕ /- [definition] -/ } (hx : x < m /- [standing] -/ ) :
    extendVal m g x ≠ x := by
  rw [extendVal_of_lt g hx]
  exact fun hcon ↦ hg.2 ⟨x, hx⟩ (Fin.ext hcon)

end Extend

section Indices

/-- The left endpoint of the ground set `Fin (a + b + 2)`. -/
def leftEnd (a b : ℕ /- [definition] -/ ) : Fin (a + b + 2) := ⟨0, by omega⟩

@[simp] theorem leftEnd_val (a b : ℕ /- [definition] -/ ) : ((leftEnd a b : Fin (a + b + 2)) : ℕ) = 0 := rfl

/-- The `j`-th point strictly inside the arc `{0, a+1}` of `Fin (a + b + 2)`. -/
theorem insideIdx_lt (a b : ℕ /- [definition] -/ ) (j : Fin a /- [definition] -/ ) : (j : ℕ) + 1 < a + b + 2 := by
  have := j.isLt; omega

/-- The `j`-th point strictly outside the arc `{0, a+1}` of `Fin (a + b + 2)`. -/
theorem outsideIdx_lt (a b : ℕ /- [definition] -/ ) (j : Fin b /- [definition] -/ ) : (j : ℕ) + a + 2 < a + b + 2 := by
  have := j.isLt; omega

end Indices

section Glue

variable {a b : ℕ /- [definition] -/ }

/-- The natural-number description of the pairing obtained by gluing a pairing `g` of the
inside of the arc `{0, a+1}` to a pairing `h` of the outside. -/
def glueVal (a b : ℕ /- [definition] -/ ) (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) (x : ℕ /- [definition] -/ ) : ℕ :=
  if x = 0 then a + 1
  else if x ≤ a then extendVal a g (x - 1) + 1
  else if x = a + 1 then 0
  else extendVal b h (x - (a + 2)) + (a + 2)

theorem glueVal_zero (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) : glueVal a b g h 0 = a + 1 := by
  simp [glueVal]

theorem glueVal_inside (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) {x : ℕ /- [definition] -/ } (h1 : 1 ≤ x /- [standing] -/ )
    (h2 : x ≤ a /- [standing] -/ ) : glueVal a b g h x = extendVal a g (x - 1) + 1 := by
  rw [glueVal, if_neg (by omega), if_pos h2]

theorem glueVal_mid (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) :
    glueVal a b g h (a + 1) = 0 := by
  rw [glueVal, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem glueVal_outside (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) {x : ℕ /- [definition] -/ } (hx : a + 2 ≤ x /- [standing] -/ ) :
    glueVal a b g h x = extendVal b h (x - (a + 2)) + (a + 2) := by
  rw [glueVal, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem glueVal_inside_range (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) {x : ℕ /- [definition] -/ } (h1 : 1 ≤ x /- [standing] -/ )
    (h2 : x ≤ a /- [standing] -/ ) : 1 ≤ glueVal a b g h x ∧ glueVal a b g h x ≤ a := by
  rw [glueVal_inside g h h1 h2]
  have := extendVal_lt g (show x - 1 < a by omega)
  omega

theorem glueVal_outside_range (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) {x : ℕ /- [definition] -/ }
    (hx1 : a + 2 ≤ x /- [standing] -/ ) (hx2 : x < a + b + 2 /- [standing] -/ ) :
    a + 2 ≤ glueVal a b g h x ∧ glueVal a b g h x < a + b + 2 := by
  rw [glueVal_outside g h hx1]
  have := extendVal_lt h (show x - (a + 2) < b by omega)
  omega

theorem glueVal_lt (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) {x : ℕ /- [definition] -/ } (hx : x < a + b + 2 /- [standing] -/ ) :
    glueVal a b g h x < a + b + 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · rw [glueVal_zero]; omega
  by_cases hxa : x ≤ a
  · have := (glueVal_inside_range g h hx0 hxa).2; omega
  by_cases hxm : x = a + 1
  · subst hxm; rw [glueVal_mid]; omega
  · have := (glueVal_outside_range g h (by omega) hx).2; omega

theorem glueVal_glueVal (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) (hg : IsPairing g /- [standing] -/ )
    (hh : IsPairing h /- [standing] -/ ) {x : ℕ /- [definition] -/ } (hx : x < a + b + 2 /- [standing] -/ ) :
    glueVal a b g h (glueVal a b g h x) = x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · rw [glueVal_zero, glueVal_mid]
  by_cases hxa : x ≤ a
  · obtain ⟨hr1, hr2⟩ := glueVal_inside_range g h hx0 hxa
    rw [glueVal_inside g h hr1 hr2, glueVal_inside g h hx0 hxa]
    have key : extendVal a g (extendVal a g (x - 1)) = x - 1 :=
      extendVal_extendVal hg (show x - 1 < a by omega)
    have e : extendVal a g (x - 1) + 1 - 1 = extendVal a g (x - 1) := by omega
    rw [e, key]
    omega
  by_cases hxm : x = a + 1
  · subst hxm; rw [glueVal_mid, glueVal_zero]
  · obtain ⟨hr1, hr2⟩ := glueVal_outside_range g h (by omega) hx
    rw [glueVal_outside g h hr1, glueVal_outside g h (by omega)]
    have key : extendVal b h (extendVal b h (x - (a + 2))) = x - (a + 2) :=
      extendVal_extendVal hh (show x - (a + 2) < b by omega)
    have e : extendVal b h (x - (a + 2)) + (a + 2) - (a + 2) = extendVal b h (x - (a + 2)) := by
      omega
    rw [e, key]
    omega

theorem glueVal_ne (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) (hg : IsPairing g /- [standing] -/ )
    (hh : IsPairing h /- [standing] -/ ) {x : ℕ /- [definition] -/ } (hx : x < a + b + 2 /- [standing] -/ ) : glueVal a b g h x ≠ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · rw [glueVal_zero]; omega
  by_cases hxa : x ≤ a
  · rw [glueVal_inside g h hx0 hxa]
    have := extendVal_ne hg (show x - 1 < a by omega)
    omega
  by_cases hxm : x = a + 1
  · subst hxm; rw [glueVal_mid]; omega
  · rw [glueVal_outside g h (by omega)]
    have := extendVal_ne hh (show x - (a + 2) < b by omega)
    omega

/-- **The gluing map.**  Given a pairing `g` of `Fin a` (to be placed strictly inside the arc
`{0, a+1}`) and a pairing `h` of `Fin b` (to be placed strictly outside it), `glue a b g h` is
the pairing of `Fin (a + b + 2)` that matches `0` with `a + 1`, copies `g` onto `{1, …, a}` and
copies `h` onto `{a+2, …, a+b+1}`. -/
def glue (a b : ℕ /- [definition] -/ ) (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) :
    Fin (a + b + 2) → Fin (a + b + 2) :=
  fun i ↦ ⟨glueVal a b g h (i : ℕ), glueVal_lt g h i.isLt⟩

@[simp] theorem glue_val (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [definition] -/ ) (i : Fin (a + b + 2) /- [definition] -/ ) :
    ((glue a b g h i : Fin (a + b + 2)) : ℕ) = glueVal a b g h (i : ℕ) := rfl

theorem glue_leftEnd (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) :
    ((glue a b g h (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 := by
  rw [glue_val, leftEnd_val, glueVal_zero]

theorem glue_isPairing {g : Fin a → Fin a /- [definition] -/ } {h : Fin b → Fin b /- [standing] -/ } (hg : IsPairing g /- [standing] -/ )
    (hh : IsPairing h /- [standing] -/ ) : IsPairing (glue a b g h) := by
  constructor
  · intro i
    refine Fin.ext ?_
    show glueVal a b g h (glueVal a b g h (i : ℕ)) = (i : ℕ)
    exact glueVal_glueVal g h hg hh i.isLt
  · intro i hcon
    exact glueVal_ne g h hg hh i.isLt (congrArg Fin.val hcon)

theorem glue_isNonCrossing {g : Fin a → Fin a /- [definition] -/ } {h : Fin b → Fin b /- [standing] -/ }
    (hgc : IsNonCrossing g /- [standing] -/ ) (hhc : IsNonCrossing h /- [standing] -/ ) : IsNonCrossing (glue a b g h) := by
  intro x y hxy hyf hcon
  have hxy' : (x : ℕ) < (y : ℕ) := Fin.lt_def.1 hxy
  have hyf' : (y : ℕ) < glueVal a b g h (x : ℕ) := by
    have := Fin.lt_def.1 hyf; rwa [glue_val] at this
  have hcon' : glueVal a b g h (x : ℕ) < glueVal a b g h (y : ℕ) := by
    have := Fin.lt_def.1 hcon; rwa [glue_val, glue_val] at this
  have hx := x.isLt
  have hy := y.isLt
  rcases Nat.eq_zero_or_pos (x : ℕ) with hx0 | hx0
  · rw [hx0, glueVal_zero] at hyf' hcon'
    have := (glueVal_inside_range g h (show 1 ≤ (y : ℕ) by omega)
      (show (y : ℕ) ≤ a by omega)).2
    omega
  by_cases hxa : (x : ℕ) ≤ a
  · obtain ⟨hr1, hr2⟩ := glueVal_inside_range g h hx0 hxa
    have hy1 : 1 ≤ (y : ℕ) := by omega
    have hy2 : (y : ℕ) ≤ a := by omega
    have hxl : (x : ℕ) - 1 < a := by omega
    have hyl : (y : ℕ) - 1 < a := by omega
    rw [glueVal_inside g h hx0 hxa, extendVal_of_lt g hxl] at hyf' hcon'
    rw [glueVal_inside g h hy1 hy2, extendVal_of_lt g hyl] at hcon'
    refine hgc ⟨(x : ℕ) - 1, hxl⟩ ⟨(y : ℕ) - 1, hyl⟩ ?_ ?_ ?_
    · show (x : ℕ) - 1 < (y : ℕ) - 1
      omega
    · show (y : ℕ) - 1 < ((g ⟨(x : ℕ) - 1, hxl⟩ : Fin a) : ℕ)
      omega
    · show ((g ⟨(x : ℕ) - 1, hxl⟩ : Fin a) : ℕ) < ((g ⟨(y : ℕ) - 1, hyl⟩ : Fin a) : ℕ)
      omega
  by_cases hxm : (x : ℕ) = a + 1
  · rw [hxm, glueVal_mid] at hyf'
    omega
  · obtain ⟨hr1, hr2⟩ := glueVal_outside_range g h (show a + 2 ≤ (x : ℕ) by omega) hx
    have hy1 : a + 2 ≤ (y : ℕ) := by omega
    have hxl : (x : ℕ) - (a + 2) < b := by omega
    have hyl : (y : ℕ) - (a + 2) < b := by omega
    rw [glueVal_outside g h (show a + 2 ≤ (x : ℕ) by omega), extendVal_of_lt h hxl] at hyf' hcon'
    rw [glueVal_outside g h hy1, extendVal_of_lt h hyl] at hcon'
    refine hhc ⟨(x : ℕ) - (a + 2), hxl⟩ ⟨(y : ℕ) - (a + 2), hyl⟩ ?_ ?_ ?_
    · show (x : ℕ) - (a + 2) < (y : ℕ) - (a + 2)
      omega
    · show (y : ℕ) - (a + 2) < ((h ⟨(x : ℕ) - (a + 2), hxl⟩ : Fin b) : ℕ)
      omega
    · show ((h ⟨(x : ℕ) - (a + 2), hxl⟩ : Fin b) : ℕ) <
        ((h ⟨(y : ℕ) - (a + 2), hyl⟩ : Fin b) : ℕ)
      omega

end Glue

section Parts

variable {a b : ℕ /- [definition] -/ }

/-- The restriction of a pairing of `Fin (a + b + 2)` to the inside of the arc `{0, a+1}`,
re-indexed by `Fin a`.  The `min` is a junk-value clamp; `insidePart_val` shows it is inert
on the fibre of interest. -/
def insidePart (a b : ℕ /- [definition] -/ ) (f : Fin (a + b + 2) → Fin (a + b + 2)  /- [definition] -/ ) : Fin a → Fin a :=
  fun j ↦ ⟨min ((f ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : ℕ) - 1) (a - 1), by
    have := j.isLt; omega⟩

/-- The restriction of a pairing of `Fin (a + b + 2)` to the outside of the arc `{0, a+1}`,
re-indexed by `Fin b`. -/
def outsidePart (a b : ℕ /- [definition] -/ ) (f : Fin (a + b + 2) → Fin (a + b + 2)  /- [definition] -/ ) : Fin b → Fin b :=
  fun j ↦ ⟨min ((f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : ℕ) - (a + 2)) (b - 1), by
    have := j.isLt; omega⟩

variable {f : Fin (a + b + 2) → Fin (a + b + 2)  /- [definition] -/ }

/-- Inside the arc `{0, a+1}` a non-crossing pairing stays inside: this is
`IsNonCrossing.mem_Ioo` transported to natural numbers. -/
theorem inside_mem (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ )
    {x : ℕ /- [definition] -/ } (hx1 : 1 ≤ x /- [standing] -/ ) (hx2 : x ≤ a /- [standing] -/ ) (hx : x < a + b + 2 /- [standing] -/ ) :
    1 ≤ ((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) ∧ ((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) ≤ a := by
  have h1 : leftEnd a b < (⟨x, hx⟩ : Fin (a + b + 2)) :=
    Fin.lt_def.2 (by show (0 : ℕ) < x; omega)
  have h2 : (⟨x, hx⟩ : Fin (a + b + 2)) < f (leftEnd a b) :=
    Fin.lt_def.2 (by show x < ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ); omega)
  obtain ⟨hl, hr⟩ := hnc.mem_Ioo hp h1 h2
  have hl' := Fin.lt_def.1 hl
  have hr' := Fin.lt_def.1 hr
  rw [leftEnd_val] at hl'
  rw [h0] at hr'
  omega

/-- Outside the arc `{0, a+1}` a non-crossing pairing stays outside: this is
`IsNonCrossing.notMem_Ioo` transported to natural numbers. -/
theorem outside_mem (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ )
    {x : ℕ /- [definition] -/ } (hx1 : a + 2 ≤ x /- [standing] -/ ) (hx : x < a + b + 2 /- [standing] -/ ) :
    a + 2 ≤ ((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) := by
  have hne0 : ((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) ≠ 0 := by
    intro hcon
    have : f ⟨x, hx⟩ = leftEnd a b := Fin.ext (by rw [hcon, leftEnd_val])
    have h2 : (⟨x, hx⟩ : Fin (a + b + 2)) = f (leftEnd a b) := by
      rw [← this, hp.1]
    have := congrArg Fin.val h2
    rw [h0] at this
    simp only at this
    omega
  have hneP : ((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) ≠ a + 1 := by
    intro hcon
    have : f ⟨x, hx⟩ = f (leftEnd a b) := Fin.ext (by rw [hcon, h0])
    have h2 := hp.injective this
    have := congrArg Fin.val h2
    rw [leftEnd_val] at this
    simp only at this
    omega
  have hb : ¬ (leftEnd a b < (⟨x, hx⟩ : Fin (a + b + 2)) ∧
      (⟨x, hx⟩ : Fin (a + b + 2)) < f (leftEnd a b)) := by
    rintro ⟨-, h2⟩
    have := Fin.lt_def.1 h2
    rw [h0] at this
    simp only at this
    omega
  have := hnc.notMem_Ioo hp hb
  rw [not_and_or] at this
  rcases this with h | h
  · exfalso
    apply h
    exact Fin.lt_def.2 (by rw [leftEnd_val]; omega)
  · have : ¬ (((f ⟨x, hx⟩ : Fin (a + b + 2)) : ℕ) < ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ)) :=
      fun hc ↦ h (Fin.lt_def.2 hc)
    rw [h0] at this
    omega

theorem insidePart_val (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) (j : Fin a /- [definition] -/ ) :
    ((insidePart a b f j : Fin a) : ℕ) + 1 =
      ((f ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ) := by
  have hj := j.isLt
  have hb := inside_mem hp hnc h0 (x := (j : ℕ) + 1) (by omega) (by omega) (insideIdx_lt a b j)
  show min (((f ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ) - 1) (a - 1) + 1 = _
  omega

theorem outsidePart_val (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) (j : Fin b /- [definition] -/ ) :
    ((outsidePart a b f j : Fin b) : ℕ) + (a + 2) =
      ((f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ) := by
  have hj := j.isLt
  have hb := outside_mem hp hnc h0 (x := (j : ℕ) + a + 2) (by omega) (outsideIdx_lt a b j)
  have hlt := (f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)).isLt
  show min (((f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ) - (a + 2))
    (b - 1) + (a + 2) = _
  omega

theorem insidePart_isPairing (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) : IsPairing (insidePart a b f) := by
  constructor
  · intro j
    refine Fin.ext ?_
    have h1 := insidePart_val hp hnc h0 j
    have h2 := insidePart_val hp hnc h0 (insidePart a b f j)
    have key : (⟨((insidePart a b f j : Fin a) : ℕ) + 1,
        insideIdx_lt a b (insidePart a b f j)⟩ : Fin (a + b + 2)) =
        f ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ := Fin.ext h1
    rw [key, hp.1] at h2
    simp only at h2
    omega
  · intro j hcon
    have h1 := insidePart_val hp hnc h0 j
    rw [hcon] at h1
    have hj := j.isLt
    have hkey : f ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ = ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ :=
      Fin.ext (by simp only; omega)
    exact hp.2 _ hkey

theorem outsidePart_isPairing (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) :
    IsPairing (outsidePart a b f) := by
  constructor
  · intro j
    refine Fin.ext ?_
    have h1 := outsidePart_val hp hnc h0 j
    have h2 := outsidePart_val hp hnc h0 (outsidePart a b f j)
    have key : (⟨((outsidePart a b f j : Fin b) : ℕ) + a + 2,
        outsideIdx_lt a b (outsidePart a b f j)⟩ : Fin (a + b + 2)) =
        f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ := Fin.ext (by simp only; omega)
    rw [key, hp.1] at h2
    simp only at h2
    omega
  · intro j hcon
    have h1 := outsidePart_val hp hnc h0 j
    rw [hcon] at h1
    have hj := j.isLt
    have hkey : f ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ =
        ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ := Fin.ext (by simp only; omega)
    exact hp.2 _ hkey

theorem insidePart_isNonCrossing (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) :
    IsNonCrossing (insidePart a b f) := by
  intro x y hxy hyf hcon
  have ex := insidePart_val hp hnc h0 x
  have ey := insidePart_val hp hnc h0 y
  have hxy' := Fin.lt_def.1 hxy
  have hyf' := Fin.lt_def.1 hyf
  have hcon' := Fin.lt_def.1 hcon
  refine hnc ⟨(x : ℕ) + 1, insideIdx_lt a b x⟩ ⟨(y : ℕ) + 1, insideIdx_lt a b y⟩ ?_ ?_ ?_
  · show (x : ℕ) + 1 < (y : ℕ) + 1
    omega
  · show (y : ℕ) + 1 < ((f ⟨(x : ℕ) + 1, insideIdx_lt a b x⟩ : Fin (a + b + 2)) : ℕ)
    omega
  · exact Fin.lt_def.2 (by omega)

theorem outsidePart_isNonCrossing (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) :
    IsNonCrossing (outsidePart a b f) := by
  intro x y hxy hyf hcon
  have ex := outsidePart_val hp hnc h0 x
  have ey := outsidePart_val hp hnc h0 y
  have hxy' := Fin.lt_def.1 hxy
  have hyf' := Fin.lt_def.1 hyf
  have hcon' := Fin.lt_def.1 hcon
  refine hnc ⟨(x : ℕ) + a + 2, outsideIdx_lt a b x⟩ ⟨(y : ℕ) + a + 2, outsideIdx_lt a b y⟩
    ?_ ?_ ?_
  · show (x : ℕ) + a + 2 < (y : ℕ) + a + 2
    omega
  · show (y : ℕ) + a + 2 < ((f ⟨(x : ℕ) + a + 2, outsideIdx_lt a b x⟩ : Fin (a + b + 2)) : ℕ)
    omega
  · exact Fin.lt_def.2 (by omega)

/-- Gluing the two restrictions of a non-crossing pairing whose arc at `0` is `{0, a+1}`
recovers the pairing. -/
theorem glue_parts (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (h0 : ((f (leftEnd a b) : Fin (a + b + 2)) : ℕ) = a + 1 /- [standing] -/ ) :
    glue a b (insidePart a b f) (outsidePart a b f) = f := by
  funext i
  refine Fin.ext ?_
  rw [glue_val]
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
  · have hie : i = leftEnd a b := Fin.ext (by rw [leftEnd_val]; exact hi0)
    rw [hi0, glueVal_zero, hie, h0]
  by_cases hia : (i : ℕ) ≤ a
  · have hjl : (i : ℕ) - 1 < a := by omega
    set j : Fin a := ⟨(i : ℕ) - 1, hjl⟩ with hj
    have hval := insidePart_val hp hnc h0 j
    have hidx : (⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : Fin (a + b + 2)) = i :=
      Fin.ext (by simp only [hj]; omega)
    rw [hidx] at hval
    rw [glueVal_inside _ _ hi0 hia, extendVal_of_lt _ hjl]
    omega
  by_cases him : (i : ℕ) = a + 1
  · have hie : i = f (leftEnd a b) := Fin.ext (by rw [h0]; exact him)
    rw [him, glueVal_mid, hie, hp.1, leftEnd_val]
  · have hjl : (i : ℕ) - (a + 2) < b := by omega
    set j : Fin b := ⟨(i : ℕ) - (a + 2), hjl⟩ with hj
    have hval := outsidePart_val hp hnc h0 j
    have hidx : (⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)) = i :=
      Fin.ext (by simp only [hj]; omega)
    rw [hidx] at hval
    rw [glueVal_outside _ _ (by omega), extendVal_of_lt _ hjl]
    omega

theorem insidePart_glue (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) :
    insidePart a b (glue a b g h) = g := by
  funext j
  refine Fin.ext ?_
  have hj := j.isLt
  have hgj := (g j).isLt
  have hv : ((glue a b g h ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ)
      = ((g j : Fin a) : ℕ) + 1 := by
    rw [glue_val]
    show glueVal a b g h ((j : ℕ) + 1) = _
    rw [glueVal_inside g h (by omega) (by omega)]
    have : (j : ℕ) + 1 - 1 = (j : ℕ) := by omega
    rw [this, extendVal_of_lt g hj, Fin.eta]
  show min (((glue a b g h ⟨(j : ℕ) + 1, insideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ) - 1)
    (a - 1) = _
  omega

theorem outsidePart_glue (g : Fin a → Fin a /- [definition] -/ ) (h : Fin b → Fin b /- [standing] -/ ) :
    outsidePart a b (glue a b g h) = h := by
  funext j
  refine Fin.ext ?_
  have hj := j.isLt
  have hhj := (h j).isLt
  have hv : ((glue a b g h ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ)
      = ((h j : Fin b) : ℕ) + (a + 2) := by
    rw [glue_val]
    show glueVal a b g h ((j : ℕ) + a + 2) = _
    rw [glueVal_outside g h (by omega)]
    have : (j : ℕ) + a + 2 - (a + 2) = (j : ℕ) := by omega
    rw [this, extendVal_of_lt h hj, Fin.eta]
  show min (((glue a b g h ⟨(j : ℕ) + a + 2, outsideIdx_lt a b j⟩ : Fin (a + b + 2)) : ℕ)
    - (a + 2)) (b - 1) = _
  omega

end Parts

section Fibres

/-- The fibre of the map `f ↦ f 0` over an *even* value is empty: by `IsNonCrossing.odd_sub`
the partner of the leftmost point is always at an odd position. -/
theorem card_fibre_even {n : ℕ /- [definition] -/ } (z : Fin n /- [definition] -/ ) (hz : (z : ℕ) = 0 /- [standing] -/ ) (m : ℕ /- [definition] -/ ) (hm : m % 2 = 0 /- [standing] -/ ) :
    (Finset.filter (fun f ↦ ((f z : Fin n) : ℕ) = m) (nonCrossingPairings n)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf hcon
  rw [mem_nonCrossingPairings] at hf
  obtain ⟨hp, hnc⟩ := hf
  have hne : ((f z : Fin n) : ℕ) ≠ 0 := by
    intro h
    exact hp.2 z (Fin.ext (by rw [h, hz]))
  have hlt : z < f z := Fin.lt_def.2 (by omega)
  have := hnc.odd_sub hp hlt
  rw [hz, Nat.sub_zero, hcon] at this
  rw [Nat.odd_iff] at this
  omega

/-- **The fibrewise product formula.**  Restricting to the inside and the outside of the arc
`{0, a+1}` is a bijection from the non-crossing pairings of `Fin n` whose leftmost point is
matched to position `a + 1` onto the pairs consisting of a non-crossing pairing of `Fin a` and
one of `Fin b`. -/
theorem card_fibre_odd {n a b : ℕ /- [definition] -/ } (hn : n = a + b + 2 /- [standing] -/ ) (z : Fin n /- [definition] -/ ) (hz : (z : ℕ) = 0 /- [standing] -/ )
    (m : ℕ /- [definition] -/ ) (hm : m = a + 1 /- [standing] -/ ) :
    (Finset.filter (fun f ↦ ((f z : Fin n) : ℕ) = m) (nonCrossingPairings n)).card
      = (nonCrossingPairings a).card * (nonCrossingPairings b).card := by
  subst hn
  subst hm
  obtain rfl : z = leftEnd a b := Fin.ext (by rw [leftEnd_val]; exact hz)
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun f ↦ (insidePart a b f, outsidePart a b f))
    (fun q ↦ glue a b q.1 q.2) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_nonCrossingPairings] at hf
    obtain ⟨⟨hp, hnc⟩, h0⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_product, mem_nonCrossingPairings]
    exact ⟨⟨insidePart_isPairing hp hnc h0, insidePart_isNonCrossing hp hnc h0⟩,
      ⟨outsidePart_isPairing hp hnc h0, outsidePart_isNonCrossing hp hnc h0⟩⟩
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_product, mem_nonCrossingPairings] at hq
    obtain ⟨⟨hg, hgc⟩, ⟨hh, hhc⟩⟩ := hq
    simp only [Finset.mem_coe, Finset.mem_filter, mem_nonCrossingPairings]
    exact ⟨⟨glue_isPairing hg hh, glue_isNonCrossing hgc hhc⟩, glue_leftEnd q.1 q.2⟩
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_nonCrossingPairings] at hf
    obtain ⟨⟨hp, hnc⟩, h0⟩ := hf
    exact glue_parts hp hnc h0
  · intro q hq
    exact Prod.ext (insidePart_glue q.1 q.2) (outsidePart_glue q.1 q.2)

end Fibres

section Count

/-- Splitting a sum over `range (2 * N)` into its even and odd halves. -/
theorem sum_range_two_mul_direct (G : ℕ → ℕ /- [definition] -/ ) (N : ℕ /- [definition] -/ ) :
    ∑ x ∈ Finset.range (2 * N), G x = ∑ c ∈ Finset.range N, (G (2 * c) + G (2 * c + 1)) := by
  induction N with
  | zero => simp
  | succ N ihN =>
    have h : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ihN]
    omega

/-- Splitting a sum over `range M` into its even and odd halves, with the length supplied as
an equation so that no type index has to be rewritten. -/
theorem sum_range_two_mul (G : ℕ → ℕ /- [definition] -/ ) {M N : ℕ /- [definition] -/ } (hM : M = 2 * N /- [standing] -/ ) :
    ∑ x ∈ Finset.range M, G x = ∑ c ∈ Finset.range N, (G (2 * c) + G (2 * c + 1)) := by
  subst hM; exact sum_range_two_mul_direct G N

/-- **The Catalan count.**  There are exactly `catalan k` non-crossing pair partitions of a
linearly ordered set with `2 * k` elements. -/
theorem card_nonCrossingPairings (k : ℕ /- [definition] -/ ) :
    (nonCrossingPairings (2 * k)).card = catalan k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simpa using card_nonCrossingPairings_zero
    | (k + 1) =>
      have hz : 0 < 2 * k + 2 := by omega
      have hrw : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [hrw]
      set z : Fin (2 * k + 2) := ⟨0, hz⟩ with hzdef
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun f : Fin (2 * k + 2) → Fin (2 * k + 2) ↦ ((f z : Fin (2 * k + 2)) : ℕ))
        (t := Finset.range (2 * k + 2)) (fun f _ ↦ Finset.mem_range.2 (f z).isLt)]
      have hz0 : (z : ℕ) = 0 := rfl
      rw [sum_range_two_mul _ (show 2 * k + 2 = 2 * (k + 1) by ring)]
      have hterm : ∀ c ∈ Finset.range (k + 1),
          (Finset.filter (fun f : Fin (2 * k + 2) → Fin (2 * k + 2) ↦
              ((f z : Fin (2 * k + 2)) : ℕ) = 2 * c) (nonCrossingPairings (2 * k + 2))).card
            + (Finset.filter (fun f : Fin (2 * k + 2) → Fin (2 * k + 2) ↦
              ((f z : Fin (2 * k + 2)) : ℕ) = 2 * c + 1)
                (nonCrossingPairings (2 * k + 2))).card
            = catalan c * catalan (k - c) := by
        intro c hc
        rw [Finset.mem_range] at hc
        rw [card_fibre_even z hz0 (2 * c) (by omega)]
        rw [card_fibre_odd (a := 2 * c) (b := 2 * (k - c)) (by omega) z hz0 (2 * c + 1) (by omega)]
        rw [ih c (by omega), ih (k - c) (by omega)]
        omega
      rw [Finset.sum_congr rfl hterm, catalan_succ,
        Fin.sum_univ_eq_sum_range (fun c ↦ catalan c * catalan (k - c)) (k + 1)]

/-- The count in the form used by the three base cases already in `NonCrossing`:
for an even ground set of size `n`, there are `catalan (n / 2)` non-crossing pairings. -/
theorem card_nonCrossingPairings_of_even {n : ℕ /- [definition] -/ } (hn : Even n /- [standing] -/ ) :
    (nonCrossingPairings n).card = catalan (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [show m + m = 2 * m by ring, card_nonCrossingPairings]
  congr 1
  omega

/-- An odd ground set carries no pairing at all, so the count is `0` there. -/
theorem card_nonCrossingPairings_of_not_even {n : ℕ /- [definition] -/ } (hn : ¬ Even n /- [standing] -/ ) :
    (nonCrossingPairings n).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro f hf
  rw [mem_nonCrossingPairings] at hf
  exact hn hf.1.even_card

/-- The first case beyond the reach of kernel enumeration: `6 ^ 6 = 46656` functions on
`Fin 6` is already too many for `decide`, and this is a consequence of the general count. -/
theorem card_nonCrossingPairings_six : (nonCrossingPairings 6).card = 5 := by
  have hc : catalan 3 = 5 := by rw [catalan_eq_centralBinom_div]; decide
  have h := card_nonCrossingPairings 3
  rw [show (2 * 3 : ℕ) = 6 from rfl, hc] at h
  exact h

end Count

section Moments

/-- **The moment method's index set, finally identified.**  The `2 k`-th moment of the
semicircle density, computed in `SemicircleMoments` as an interval integral, equals the
number of non-crossing pair partitions of `2 k` points.

Both sides were previously known to equal `catalan k` by unrelated arguments — the integral
by a recursion on `∫ sin ^ n`, the count only for `k ≤ 2` and only by `decide`.  This theorem
is what makes the two statements one statement. -/
theorem semicircleMoment_eq_card_nonCrossingPairings (k : ℕ /- [definition] -/ ) :
    semicircleMoment (2 * k) = ((nonCrossingPairings (2 * k)).card : ℝ) := by
  rw [semicircleMoment_two_mul, card_nonCrossingPairings]

end Moments

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.extendVal
#print axioms RMTFoundations.Concentration.extendVal_of_lt
#print axioms RMTFoundations.Concentration.extendVal_lt
#print axioms RMTFoundations.Concentration.extendVal_extendVal
#print axioms RMTFoundations.Concentration.extendVal_ne
#print axioms RMTFoundations.Concentration.leftEnd
#print axioms RMTFoundations.Concentration.insideIdx_lt
#print axioms RMTFoundations.Concentration.outsideIdx_lt
#print axioms RMTFoundations.Concentration.glueVal
#print axioms RMTFoundations.Concentration.glueVal_zero
#print axioms RMTFoundations.Concentration.glueVal_inside
#print axioms RMTFoundations.Concentration.glueVal_mid
#print axioms RMTFoundations.Concentration.glueVal_outside
#print axioms RMTFoundations.Concentration.glueVal_inside_range
#print axioms RMTFoundations.Concentration.glueVal_outside_range
#print axioms RMTFoundations.Concentration.glueVal_lt
#print axioms RMTFoundations.Concentration.glueVal_glueVal
#print axioms RMTFoundations.Concentration.glueVal_ne
#print axioms RMTFoundations.Concentration.glue
#print axioms RMTFoundations.Concentration.glue_leftEnd
#print axioms RMTFoundations.Concentration.glue_isPairing
#print axioms RMTFoundations.Concentration.glue_isNonCrossing
#print axioms RMTFoundations.Concentration.insidePart
#print axioms RMTFoundations.Concentration.outsidePart
#print axioms RMTFoundations.Concentration.inside_mem
#print axioms RMTFoundations.Concentration.outside_mem
#print axioms RMTFoundations.Concentration.insidePart_val
#print axioms RMTFoundations.Concentration.outsidePart_val
#print axioms RMTFoundations.Concentration.insidePart_isPairing
#print axioms RMTFoundations.Concentration.outsidePart_isPairing
#print axioms RMTFoundations.Concentration.insidePart_isNonCrossing
#print axioms RMTFoundations.Concentration.outsidePart_isNonCrossing
#print axioms RMTFoundations.Concentration.glue_parts
#print axioms RMTFoundations.Concentration.insidePart_glue
#print axioms RMTFoundations.Concentration.outsidePart_glue
#print axioms RMTFoundations.Concentration.card_fibre_even
#print axioms RMTFoundations.Concentration.card_fibre_odd
#print axioms RMTFoundations.Concentration.sum_range_two_mul_direct
#print axioms RMTFoundations.Concentration.sum_range_two_mul
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_of_even
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_of_not_even
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_six
#print axioms RMTFoundations.Concentration.semicircleMoment_eq_card_nonCrossingPairings
#print axioms RMTFoundations.Concentration.leftEnd_val
#print axioms RMTFoundations.Concentration.glue_val
