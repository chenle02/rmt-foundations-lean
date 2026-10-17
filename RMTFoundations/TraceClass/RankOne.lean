import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Trace

/-

# The trace of a rank-one operator on a Hilbert space

* `summable_norm_inner_diag_rankOne` : for *any* orthonormal family `v` (not
  necessarily a basis, not necessarily countable), the diagonal
  `i ↦ ⟪v i, rankOne 𝕜 x y (v i)⟫` is absolutely summable.  The proof is
  Cauchy-Schwarz against Bessel's inequality in both slots.
* `hasSum_inner_diag_rankOne` : for a Hilbert basis `b`, that family sums to
  `⟪y, x⟫`, which does not mention `b`.
* `tsum_inner_diag_rankOne_eq_of_hilbertBasis` and
  `tsum_inner_diag_rankOne_basis_independent` : basis independence, in the
  strong form that two Hilbert bases indexed by *different* types give the same
  value.

Finite-dimensional basis independence for a general operator is also recorded
(`sum_inner_diag_eq_of_orthonormalBasis`); there it is immediate from mathlib's
`LinearMap.trace_eq_sum_inner`, because `LinearMap.trace` is basis-free by
construction.

## What is NOT proved here, and what it would need

There is no `IsTraceClass` predicate for general operators, and deliberately so:
a predicate here would be a definition named after a theorem.  To get from the
rank-one case to the general one, the missing mathlib infrastructure is, in
order:

1. the polar decomposition `T = U |T|` for a bounded operator, hence `|T|` as a
   positive square root — mathlib has `ContinuousLinearMap.IsPositive` and a
   square root for positive operators, but not the polar decomposition;
2. singular values, i.e. the spectral decomposition of the *compact* positive
   operator `|T|` — mathlib's spectral theorem is for compact self-adjoint
   operators, so this is the nearest of the three;
3. the Schatten ideal `S_1` with its norm, and the fact that the trace is
   independent of the orthonormal basis for every `T ∈ S_1`, which is where the
   rank-one computation below is the base case of a limiting argument.

Without 1-3 there is no Fredholm determinant of an operator, and in particular
nothing in this repository defines the Tracy-Widom distribution.

-/

namespace RMTFoundations.TraceClass

open scoped InnerProductSpace
open InnerProductSpace

variable {𝕜 E ι : Type* /- [definition] -/ } [RCLike 𝕜 /- [definition] -/ ] [NormedAddCommGroup E /- [definition] -/ ] [InnerProductSpace 𝕜 E /- [definition] -/ ]

/-- The diagonal entry of a rank-one operator against a vector. -/
theorem inner_diag_rankOne (x y z : E /- [definition] -/ ) :
    ⟪z, (rankOne 𝕜 x y) z⟫_𝕜 = ⟪y, z⟫_𝕜 * ⟪z, x⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_right]

/-- **Absolute summability of the diagonal of a rank-one operator.**  For any
orthonormal family `v` — no basis property, no countability — the family
`i ↦ ⟪v i, rankOne 𝕜 x y (v i)⟫` is absolutely summable.  This is the rank-one
case of the trace-class condition. -/
theorem summable_norm_inner_diag_rankOne {v : ι → E /- [definition] -/ } (hv : Orthonormal 𝕜 v /- [standing] -/ ) (x y : E /- [definition] -/ ) :
    Summable fun i => ‖⟪v i, (rankOne 𝕜 x y) (v i)⟫_𝕜‖ := by
  have hbound : ∀ i, ‖⟪v i, (rankOne 𝕜 x y) (v i)⟫_𝕜‖ ≤
      (‖⟪v i, y⟫_𝕜‖ ^ 2 + ‖⟪v i, x⟫_𝕜‖ ^ 2) / 2 := by
    intro i
    rw [inner_diag_rankOne, norm_mul, ← norm_inner_symm (𝕜 := 𝕜) (v i) y]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm _ (2 : ℝ), ← mul_assoc]
    exact two_mul_le_add_sq _ _
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound ?_
  exact (((hv.inner_products_summable y).add (hv.inner_products_summable x)).div_const 2)

/-- **The trace of a rank-one operator.**  For every Hilbert basis `b`, the
diagonal sums to `⟪y, x⟫`, a quantity in which `b` does not appear. -/
theorem hasSum_inner_diag_rankOne [CompleteSpace E /- [definition] -/ ] (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x y : E /- [definition] -/ ) :
    HasSum (fun i => ⟪b i, (rankOne 𝕜 x y) (b i)⟫_𝕜) ⟪y, x⟫_𝕜 := by
  have h : (fun i => ⟪b i, (rankOne 𝕜 x y) (b i)⟫_𝕜) = fun i => ⟪y, b i⟫_𝕜 * ⟪b i, x⟫_𝕜 := by
    funext i
    exact inner_diag_rankOne x y (b i)
  rw [h]
  exact b.hasSum_inner_mul_inner y x

theorem tsum_inner_diag_rankOne_eq_of_hilbertBasis [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (x y : E /- [definition] -/ ) :
    ∑' i, ⟪b i, (rankOne 𝕜 x y) (b i)⟫_𝕜 = ⟪y, x⟫_𝕜 :=
  (hasSum_inner_diag_rankOne b x y).tsum_eq

/-- **Basis independence of the rank-one trace**, in the strong form: two
Hilbert bases indexed by different types give the same diagonal sum. -/
theorem tsum_inner_diag_rankOne_basis_independent {κ : Type* /- [definition] -/ } [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι 𝕜 E /- [definition] -/ ) (b' : HilbertBasis κ 𝕜 E /- [definition] -/ ) (x y : E /- [definition] -/ ) :
    ∑' i, ⟪b i, (rankOne 𝕜 x y) (b i)⟫_𝕜 = ∑' j, ⟪b' j, (rankOne 𝕜 x y) (b' j)⟫_𝕜 := by
  rw [tsum_inner_diag_rankOne_eq_of_hilbertBasis b x y,
    tsum_inner_diag_rankOne_eq_of_hilbertBasis b' x y]

/-! ### Finite dimensions: basis independence for an arbitrary operator -/

/-- In finite dimensions the diagonal sum of *any* operator is basis
independent, because it equals `LinearMap.trace`, which is basis-free.  This is
the statement whose infinite-dimensional generalisation is the content of the
trace-class theory. -/
theorem sum_inner_diag_eq_of_orthonormalBasis {κ : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [Fintype κ /- [definition] -/ ]
    (T : E →ₗ[𝕜] E /- [definition] -/ ) (b : OrthonormalBasis ι 𝕜 E /- [definition] -/ ) (b' : OrthonormalBasis κ 𝕜 E /- [definition] -/ ) :
    ∑ i, ⟪b i, T (b i)⟫_𝕜 = ∑ j, ⟪b' j, T (b' j)⟫_𝕜 := by
  rw [← LinearMap.trace_eq_sum_inner T b, ← LinearMap.trace_eq_sum_inner T b']

end RMTFoundations.TraceClass

#print axioms RMTFoundations.TraceClass.inner_diag_rankOne
#print axioms RMTFoundations.TraceClass.summable_norm_inner_diag_rankOne
#print axioms RMTFoundations.TraceClass.hasSum_inner_diag_rankOne
#print axioms RMTFoundations.TraceClass.tsum_inner_diag_rankOne_eq_of_hilbertBasis
#print axioms RMTFoundations.TraceClass.tsum_inner_diag_rankOne_basis_independent
#print axioms RMTFoundations.TraceClass.sum_inner_diag_eq_of_orthonormalBasis
