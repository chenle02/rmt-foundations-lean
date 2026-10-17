import Mathlib.Analysis.InnerProductSpace.Spectrum
import RMTFoundations.TraceClass.Fredholm
import RMTFoundations.TraceClass.TraceDeriv
import RMTFoundations.TraceClass.RankOne

/-
* `RMTFoundations.TraceClass.Fredholm` — the finite-dimensional Fredholm
  expansion of `det (1 + t * K)` into sums of principal minors, multiplicativity,
  the scaled Sylvester identity, and the relation to the characteristic
  polynomial and the eigenvalues.
* `RMTFoundations.TraceClass.TraceDeriv` — `d/dt det (1 + t * K) at 0 = tr K`,
  with an `O(t ^ 2)` remainder bound.
* `RMTFoundations.TraceClass.RankOne` — the one infinite-dimensional result:
  for a rank-one operator on a Hilbert space the diagonal
  `i ↦ ⟪e i, T (e i)⟫` is absolutely summable against any orthonormal family
  and sums, over any Hilbert basis, to a basis-independent value.

## What is NOT here
-/


