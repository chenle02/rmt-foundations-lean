import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Order.Interval.Finset.Fin

/-!
# Non-crossing pair partitions

Mathlib has Catalan numbers and Dyck words (and proves
`DyckWord.card_dyckWord_semilength_eq_catalan`), but it has no notion of a
*pair partition* of a linearly ordered finite set, and no notion of a
*non-crossing* one.  Non-crossing pair partitions are the combinatorial index
set of the moment method for the semicircle law: the `2k`-th moment of the
semicircle law counts them, and the crossing pairings are exactly the ones whose
contribution vanishes in the large-`N` limit.

A pair partition of `Fin n` is encoded as a fixed-point-free involution
`f : Fin n → Fin n`; the blocks are the orbits `{i, f i}`.  It is non-crossing
when no two arcs interleave, i.e. there is no `a < b` with `b < f a < f b`.

## What is proved here

* `IsPairing`, `IsNonCrossing`, `nonCrossingPairings` — the definitions.
* `IsPairing.injective`, `IsPairing.surjective` — a pairing is a bijection.
* `even_card_of_involutive_of_no_fixed` — a finset carrying a fixed-point-free
  involution has even cardinality.  Mathlib does not have this.
* `IsPairing.even_card` — the ground set of a pairing has even cardinality.
* `IsNonCrossing.mem_Ioo` — **the structure lemma**: in a non-crossing pairing,
  if `i < f i` then the open interval `(i, f i)` is invariant under `f`.  Every
  point strictly inside an arc is matched strictly inside that same arc.
* `IsNonCrossing.nested_or_disjoint` — equivalently, any two arcs are either
  nested or disjoint.
* `IsNonCrossing.odd_sub` — consequently `f i - i` is odd for every arc: an arc
  always spans an even number of interior points.
* `IsNonCrossing.notMem_Ioo` — the region outside an arc is invariant as well.
* `IsNonCrossing.exists_adjacent` — every non-crossing pairing of a nonempty
  ground set contains an *innermost* arc `{i, i + 1}`.  This is exactly what
  fails for crossing pairings.
* `card_nonCrossingPairings_zero`, `card_nonCrossingPairings_two`,
  `card_nonCrossingPairings_four` — the counts `1, 1, 2` for `n = 0, 2, 4`,
  matching `catalan 0, catalan 1, catalan 2`.

## What is NOT proved here

* **The count is not proved in this file.**  The theorem
  `(nonCrossingPairings (2 * k)).card = catalan k` is *not* established here;
  only the three base cases `k = 0, 1, 2` are, and those by `decide`, not by a
  general argument.  What is here is the structural half of the standard proof
  (the interval lemma), which is what makes the recursive decomposition
  possible.  Nothing in *this* file should be read as a claim about `catalan`.
  The general count is proved in
  `RMTFoundations.Concentration.NonCrossingCount`, which imports this file and
  uses `mem_Ioo`, `notMem_Ioo` and `odd_sub` as its only structural input; the
  bijection with Dyck words is still not constructed there either.
* No connection to `Mathlib.Combinatorics.Enumerative.DyckWord` is made beyond
  the import; no map to or from `DyckWord` is defined.
* Nothing about moments: the semicircle law, its moments, and the statement
  that the `2k`-th moment is `catalan k` are absent.  So is any statement about
  `E [tr (H ^ k)]`.
* Crossing pairings are not counted, and there is no asymptotic statement about
  their contribution.
-/

namespace RMTFoundations.Concentration

open Finset

section Involution

/-- A finset carrying a fixed-point-free involution has even cardinality.
Mathlib has this for perfect matchings of a simple graph
(`SimpleGraph.IsPerfectMatching.even_card`) but not for a bare involution. -/
theorem even_card_of_involutive_of_no_fixed {α : Type* /- [definition] -/ } [DecidableEq α /- [definition] -/ ] (g : α → α /- [definition] -/ )
    (s : Finset α /- [definition] -/ ) (hmaps : ∀ a ∈ s, g a ∈ s /- [standing] -/ ) (hinv : ∀ a ∈ s, g (g a) = a /- [standing] -/ )
    (hfix : ∀ a ∈ s, g a ≠ a /- [standing] -/ ) : Even s.card := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, rfl⟩
    · have hga : g a ∈ s := hmaps a ha
      have hne : g a ≠ a := hfix a ha
      have hga' : g a ∈ s.erase a := mem_erase.2 ⟨hne, hga⟩
      have hsub : (s.erase a).erase (g a) ⊂ s :=
        lt_of_le_of_lt (erase_subset _ _) (erase_ssubset ha)
      have hmaps' : ∀ b ∈ (s.erase a).erase (g a), g b ∈ (s.erase a).erase (g a) := by
        intro b hb
        have hb1 : b ≠ g a := (mem_erase.1 hb).1
        have hb2 : b ≠ a := (mem_erase.1 (mem_erase.1 hb).2).1
        have hbs : b ∈ s := (mem_erase.1 (mem_erase.1 hb).2).2
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, hmaps b hbs⟩⟩
        · intro hcon
          exact hb2 (by rw [← hinv b hbs, hcon, hinv a ha])
        · intro hcon
          exact hb1 (by rw [← hcon, hinv b hbs])
      have hinv' : ∀ b ∈ (s.erase a).erase (g a), g (g b) = b := by
        intro b hb
        exact hinv b (mem_erase.1 (mem_erase.1 hb).2).2
      have hfix' : ∀ b ∈ (s.erase a).erase (g a), g b ≠ b := by
        intro b hb
        exact hfix b (mem_erase.1 (mem_erase.1 hb).2).2
      have hrec := ih _ hsub hmaps' hinv' hfix'
      have hc1 : ((s.erase a).erase (g a)).card + 1 = (s.erase a).card :=
        card_erase_add_one hga'
      have hc2 : (s.erase a).card + 1 = s.card := card_erase_add_one ha
      obtain ⟨m, hm⟩ := hrec
      refine ⟨m + 1, ?_⟩
      omega

end Involution

section Definitions

/-- `f : Fin n → Fin n` is a **pair partition** of `Fin n`: a fixed-point-free
involution.  Its blocks are the two-element orbits `{i, f i}`. -/
def IsPairing {n : ℕ /- [definition] -/ } (f : Fin n → Fin n /- [definition] -/ ) : Prop :=
  (∀ i, f (f i) = i) ∧ ∀ i, f i ≠ i

/-- `f` is **non-crossing**: no two arcs interleave.  Arcs `{a, f a}` and
`{b, f b}` cross exactly when `a < b < f a < f b`. -/
def IsNonCrossing {n : ℕ /- [definition] -/ } (f : Fin n → Fin n /- [definition] -/ ) : Prop :=
  ∀ a b : Fin n, a < b → b < f a → ¬ f a < f b

instance decidableIsPairing {n : ℕ /- [definition] -/ } (f : Fin n → Fin n /- [definition] -/ ) : Decidable (IsPairing f) :=
  decidable_of_iff ((∀ i, f (f i) = i) ∧ ∀ i, f i ≠ i) Iff.rfl

instance decidableIsNonCrossing {n : ℕ /- [definition] -/ } (f : Fin n → Fin n /- [definition] -/ ) : Decidable (IsNonCrossing f) :=
  decidable_of_iff (∀ a b : Fin n, a < b → b < f a → ¬ f a < f b) Iff.rfl

/-- The finset of non-crossing pair partitions of `Fin n`. -/
def nonCrossingPairings (n : ℕ /- [definition] -/ ) : Finset (Fin n → Fin n) :=
  {f ∈ Finset.univ | IsPairing f ∧ IsNonCrossing f}

theorem mem_nonCrossingPairings {n : ℕ /- [definition] -/ } {f : Fin n → Fin n /- [definition] -/ } :
    f ∈ nonCrossingPairings n ↔ IsPairing f ∧ IsNonCrossing f := by
  rw [nonCrossingPairings, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

end Definitions

section Basic

variable {n : ℕ /- [definition] -/ } {f : Fin n → Fin n /- [definition] -/ }

theorem IsPairing.injective (hp : IsPairing f /- [standing] -/ ) : Function.Injective f :=
  Function.Involutive.injective hp.1

theorem IsPairing.surjective (hp : IsPairing f /- [standing] -/ ) : Function.Surjective f :=
  Function.Involutive.surjective hp.1

/-- The ground set of a pair partition has even cardinality. -/
theorem IsPairing.even_card (hp : IsPairing f /- [standing] -/ ) : Even n := by
  have h := even_card_of_involutive_of_no_fixed f (Finset.univ : Finset (Fin n))
    (fun a _ ↦ Finset.mem_univ _) (fun a _ ↦ hp.1 a) (fun a _ ↦ hp.2 a)
  rwa [Finset.card_univ, Fintype.card_fin] at h

end Basic

section Structure

variable {n : ℕ /- [definition] -/ } {f : Fin n → Fin n /- [definition] -/ }

/-- **The structure lemma for non-crossing pairings.**  If `i < f i` then the
open interval `(i, f i)` is invariant under `f`: every point strictly inside the
arc `{i, f i}` is matched strictly inside that same arc.

This is what makes a non-crossing pairing recursively decomposable, and it is
the step that the bijection with Dyck words rests on. -/
theorem IsNonCrossing.mem_Ioo (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    {i b : Fin n /- [definition] -/ } (h1 : i < b /- [standing] -/ ) (h2 : b < f i /- [standing] -/ ) : i < f b ∧ f b < f i := by
  have hfb_ne : f b ≠ f i := fun hcon ↦ absurd (hp.injective hcon) (ne_of_gt h1)
  have hlt : f b < f i := by
    rcases lt_trichotomy (f b) (f i) with h | h | h
    · exact h
    · exact absurd h hfb_ne
    · exact absurd h (hnc i b h1 h2)
  refine ⟨?_, hlt⟩
  have hfb_ne_i : f b ≠ i := by
    intro hcon
    have : f i = b := by rw [← hcon, hp.1 b]
    rw [this] at h2
    exact lt_irrefl b h2
  rcases lt_trichotomy (f b) i with h | h | h
  · exfalso
    have hfa : f (f b) = b := hp.1 b
    have hbi : f b < i := h
    have h3 : i < f (f b) := by rw [hfa]; exact h1
    have h4 : f (f b) < f i := by rw [hfa]; exact h2
    exact hnc (f b) i hbi h3 h4
  · exact absurd h hfb_ne_i
  · exact h

/-- Two arcs of a non-crossing pairing are nested or disjoint: if `a < b` and
both are left endpoints, then either `f b < f a` (nested) or `f a < b`
(disjoint). -/
theorem IsNonCrossing.nested_or_disjoint (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    {a b : Fin n /- [definition] -/ } (ha : a < f a /- [standing] -/ ) (hb : b < f b /- [standing] -/ ) (hab : a < b /- [standing] -/ ) :
    f b < f a ∨ f a < b := by
  rcases lt_trichotomy b (f a) with h | h | h
  · exact Or.inl ((hnc.mem_Ioo hp hab h).2)
  · exfalso
    rw [h, hp.1 a] at hb
    exact absurd ha (asymm hb)
  · exact Or.inr h

/-- In a non-crossing pairing every arc spans an even number of interior points,
i.e. `f i - i` is odd. -/
theorem IsNonCrossing.odd_sub (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    {i : Fin n /- [definition] -/ } (hi : i < f i /- [standing] -/ ) : Odd ((f i : ℕ) - (i : ℕ)) := by
  classical
  have hmaps : ∀ b ∈ Finset.Ioo i (f i), f b ∈ Finset.Ioo i (f i) := by
    intro b hb
    rw [Finset.mem_Ioo] at hb ⊢
    exact hnc.mem_Ioo hp hb.1 hb.2
  have hinv : ∀ b ∈ Finset.Ioo i (f i), f (f b) = b := fun b _ ↦ hp.1 b
  have hfix : ∀ b ∈ Finset.Ioo i (f i), f b ≠ b := fun b _ ↦ hp.2 b
  have heven := even_card_of_involutive_of_no_fixed f (Finset.Ioo i (f i)) hmaps hinv hfix
  rw [Fin.card_Ioo] at heven
  obtain ⟨m, hm⟩ := heven
  have hlt : (i : ℕ) < (f i : ℕ) := hi
  refine ⟨m, ?_⟩
  omega


/-- The region outside an arc is invariant too: if `i < f i` and `b` lies
outside the closed interval `[i, f i]`, then so does `f b`. -/
theorem IsNonCrossing.notMem_Ioo (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    {i b : Fin n /- [definition] -/ } (hb : ¬ (i < b ∧ b < f i)  /- [standing] -/ ) : ¬ (i < f b ∧ f b < f i) := by
  rintro ⟨h1, h2⟩
  have h := hnc.mem_Ioo hp h1 h2
  rw [hp.1 b] at h
  exact hb h

/-- **Every non-crossing pairing of a nonempty ground set has an innermost
arc**: some `i` is matched to its immediate successor `i + 1`.

This is the fact that lets one peel a non-crossing pairing apart one block at a
time, and it fails for crossing pairings (e.g. `{1,3}, {2,4}` on `Fin 4`). -/
theorem IsNonCrossing.exists_adjacent (hp : IsPairing f /- [standing] -/ ) (hnc : IsNonCrossing f /- [standing] -/ )
    (hn : 0 < n /- [standing] -/ ) : ∃ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 ∧ f i = j := by
  classical
  set O : Finset (Fin n) := {i ∈ Finset.univ | i < f i} with hO
  have hOne : O.Nonempty := by
    refine ⟨⟨0, hn⟩, ?_⟩
    rw [hO, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Fin.lt_def.2 ?_⟩
    have hz : (f ⟨0, hn⟩ : ℕ) ≠ 0 := by
      intro h0
      exact hp.2 ⟨0, hn⟩ (Fin.ext h0)
    have : ((⟨0, hn⟩ : Fin n) : ℕ) = 0 := rfl
    omega
  obtain ⟨i, hiO, hmin⟩ := O.exists_min_image (fun i ↦ (f i : ℕ) - (i : ℕ)) hOne
  have hi : i < f i := by
    rw [hO, Finset.mem_filter] at hiO
    exact hiO.2
  have hilt : (i : ℕ) < (f i : ℕ) := Fin.lt_def.1 hi
  have hblt : (i : ℕ) + 1 < n := by
    have := (f i).isLt
    omega
  refine ⟨i, ⟨(i : ℕ) + 1, hblt⟩, rfl, ?_⟩
  by_contra hcon
  have hne : (i : ℕ) + 1 ≠ (f i : ℕ) := by
    intro heq
    exact hcon (Fin.ext heq.symm)
  obtain ⟨b, hbval⟩ : ∃ b : Fin n, (b : ℕ) = (i : ℕ) + 1 := ⟨⟨(i : ℕ) + 1, hblt⟩, rfl⟩
  have hb1 : i < b := Fin.lt_def.2 (by omega)
  have hb2 : b < f i := Fin.lt_def.2 (by omega)
  obtain ⟨hl, hr⟩ := hnc.mem_Ioo hp hb1 hb2
  have hlN : (i : ℕ) < (f b : ℕ) := Fin.lt_def.1 hl
  have hrN : (f b : ℕ) < (f i : ℕ) := Fin.lt_def.1 hr
  have hbne : (f b : ℕ) ≠ (b : ℕ) := fun h ↦ hp.2 b (Fin.ext h)
  have hbopen : b < f b := Fin.lt_def.2 (by omega)
  have hbO : b ∈ O := by
    rw [hO, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hbopen⟩
  have hmm : (f i : ℕ) - (i : ℕ) ≤ (f b : ℕ) - (b : ℕ) := hmin b hbO
  omega

end Structure

section SmallCases

/-- There is exactly one non-crossing pairing of the empty set, matching
`catalan 0 = 1`. -/
theorem card_nonCrossingPairings_zero : (nonCrossingPairings 0).card = catalan 0 := by
  rw [catalan_zero]
  decide

/-- There is exactly one non-crossing pairing of two points, matching
`catalan 1 = 1`. -/
theorem card_nonCrossingPairings_two : (nonCrossingPairings 2).card = catalan 1 := by
  rw [catalan_one]
  decide

/-- There are exactly two non-crossing pairings of four points (the crossing one
`{1,3}, {2,4}` being excluded), matching `catalan 2 = 2`. -/
theorem card_nonCrossingPairings_four : (nonCrossingPairings 4).card = catalan 2 := by
  rw [catalan_two]
  decide

end SmallCases

end RMTFoundations.Concentration

#print axioms RMTFoundations.Concentration.even_card_of_involutive_of_no_fixed
#print axioms RMTFoundations.Concentration.IsPairing
#print axioms RMTFoundations.Concentration.IsNonCrossing
#print axioms RMTFoundations.Concentration.nonCrossingPairings
#print axioms RMTFoundations.Concentration.mem_nonCrossingPairings
#print axioms RMTFoundations.Concentration.IsPairing.injective
#print axioms RMTFoundations.Concentration.IsPairing.surjective
#print axioms RMTFoundations.Concentration.IsPairing.even_card
#print axioms RMTFoundations.Concentration.IsNonCrossing.mem_Ioo
#print axioms RMTFoundations.Concentration.IsNonCrossing.nested_or_disjoint
#print axioms RMTFoundations.Concentration.IsNonCrossing.odd_sub
#print axioms RMTFoundations.Concentration.IsNonCrossing.notMem_Ioo
#print axioms RMTFoundations.Concentration.IsNonCrossing.exists_adjacent
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_zero
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_two
#print axioms RMTFoundations.Concentration.card_nonCrossingPairings_four
#print axioms RMTFoundations.Concentration.decidableIsPairing
#print axioms RMTFoundations.Concentration.decidableIsNonCrossing
