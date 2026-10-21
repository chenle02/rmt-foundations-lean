import RMTFoundations.TracyWidom.GUEExtendedHermite
import RMTFoundations.TracyWidom.GUEDensity
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEChainIdentity
open Matrix Finset
open RMTFoundations.TracyWidom.GUEExtendedHermite RMTFoundations.TracyWidom.GUEProjection

/-- Unit determinant of the block quarter-turn, proved by three elementary shears. -/
lemma block_rotation_det (N : ℕ /- [definition] -/) :
    (Matrix.fromBlocks (0 : Matrix (Fin N) (Fin N) ℝ) (-1 : Matrix (Fin N) (Fin N) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) 0).det = 1 := by
  have hid : Matrix.fromBlocks (0 : Matrix (Fin N) (Fin N) ℝ) (-1 : Matrix (Fin N) (Fin N) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) 0 =
      Matrix.fromBlocks 1 (-1) 0 1 * Matrix.fromBlocks 1 0 1 1 *
        Matrix.fromBlocks 1 (-1) 0 1 := by
    simp [Matrix.fromBlocks_multiply]
  rw [hid, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]
  simp

lemma block_corner_det (N : ℕ /- [definition] -/)
    (A P D : Matrix (Fin N) (Fin N) ℝ /- [definition] -/) :
    (Matrix.fromBlocks A (-P) D 0).det = D.det * P.det := by
  have hid : Matrix.fromBlocks A (-P) D 0 =
      Matrix.fromBlocks 1 0 0 D * Matrix.fromBlocks 1 A 0 1 *
        Matrix.fromBlocks 0 (-1) 1 0 * Matrix.fromBlocks 1 0 0 P := by
    simp [Matrix.fromBlocks_multiply]
  rw [hid, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    block_rotation_det, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Algebraic two-time full-occupancy Eynard-Mehta identity; no invertibility or
probability/Fredholm hypothesis is used. -/
theorem two_time_block_det (N : ℕ /- [definition] -/)
    (A B C D P : Matrix (Fin N) (Fin N) ℝ /- [definition] -/) :
    (Matrix.fromBlocks (A*B) (A*C-P) (D*B) (D*C)).det =
      D.det * P.det * B.det := by
  have hid : Matrix.fromBlocks (A*B) (A*C-P) (D*B) (D*C) =
      Matrix.fromBlocks A (-P) D 0 * Matrix.fromBlocks B C 0 1 := by
    simp [Matrix.fromBlocks_multiply, sub_eq_add_neg]
  rw [hid, Matrix.det_mul, block_corner_det, Matrix.det_fromBlocks_zero₂₁]
  simp

noncomputable def modeEval (N : ℕ /- [definition] -/)
    (t : ℝ /- [definition] -/) (x : Fin N → ℝ /- [definition] -/) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i k => hermiteFunction k.val (x i) * Real.exp ((k.val:ℝ)*t)

noncomputable def dualEval (N : ℕ /- [definition] -/)
    (t : ℝ /- [definition] -/) (x : Fin N → ℝ /- [definition] -/) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun k i => Real.exp (-((k.val:ℝ)*t)) * hermiteFunction k.val (x i)

lemma mode_dual_product (N : ℕ /- [definition] -/)
    (t r : ℝ /- [definition] -/) (x y : Fin N → ℝ /- [definition] -/) :
    modeEval N t x * dualEval N r y =
      fun i j => occupiedKernel N t r (x i) (y j) := by
  ext i j
  simp only [Matrix.mul_apply, modeEval, dualEval, occupiedKernel]
  apply Finset.sum_congr rfl
  intro k hk
  have he : Real.exp ((k.val:ℝ)*t) * Real.exp (-((k.val:ℝ)*r)) =
      Real.exp ((k.val:ℝ)*(t-r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp ((k.val:ℝ)*t) * Real.exp (-((k.val:ℝ)*r))) *
        hermiteFunction k.val (x i) * hermiteFunction k.val (y j) := by ring
    _ = _ := by rw [he]

/-- Physical two-time correlation determinant for exactly N positions at each
slice. The subtraction is the literal  Mehler propagator. This proves
an algebraic identity, not its identification with a normalized path law. -/
theorem physical_two_time_full_occupancy (N : ℕ /- [definition] -/)
    (t r : ℝ /- [definition] -/) (x y : Fin N → ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    (Matrix.fromBlocks
      (fun i j => extendedHermiteKernel N t (x i) t (x j))
      (fun i j => extendedHermiteKernel N t (x i) r (y j))
      (fun i j => extendedHermiteKernel N r (y i) t (x j))
      (fun i j => extendedHermiteKernel N r (y i) r (y j))).det =
      (modeEval N r y).det *
        (Matrix.det (fun i j => mehlerKernel (t-r) (x i) (y j))) *
          (dualEval N t x).det := by
  have h := two_time_block_det N (modeEval N t x) (dualEval N t x)
    (dualEval N r y) (modeEval N r y)
    (fun i j => mehlerKernel (t-r) (x i) (y j))
  rw [mode_dual_product, mode_dual_product, mode_dual_product, mode_dual_product] at h
  convert h using 2
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [extendedHermiteKernel, occupiedKernel_diagonal, htr, not_lt.mpr htr.le, Matrix.fromBlocks] <;> rfl

lemma modeEval_det (N : ℕ /- [definition] -/)
    (t : ℝ /- [definition] -/) (x : Fin N → ℝ /- [definition] -/) :
    (modeEval N t x).det =
      Real.exp (∑ k : Fin N, (k.val:ℝ)*t) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i))) := by
  have h := Matrix.det_mul_row (fun k : Fin N => Real.exp ((k.val:ℝ)*t))
    (fun i k : Fin N => hermiteFunction k.val (x i))
  have hid : modeEval N t x = Matrix.of
      (fun i k : Fin N => Real.exp ((k.val:ℝ)*t) * hermiteFunction k.val (x i)) := by
    ext i k
    simp [modeEval, mul_comm]
  rw [hid, h, ← Real.exp_sum]

lemma dualEval_det (N : ℕ /- [definition] -/)
    (t : ℝ /- [definition] -/) (x : Fin N → ℝ /- [definition] -/) :
    (dualEval N t x).det =
      Real.exp (∑ k : Fin N, -((k.val:ℝ)*t)) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i))) := by
  have he : dualEval N t x = (modeEval N (-t) x).transpose := by
    ext i j
    simp [dualEval, modeEval, mul_comm]
  rw [he, Matrix.det_transpose, modeEval_det]
  simp

/-- Explicit two-time physical endpoint-chain weight. Its exponential is the
finite occupied-mode normalization, not an assumed stochastic input. -/
theorem physical_two_time_chain_weight (N : ℕ /- [definition] -/)
    (t r : ℝ /- [definition] -/) (x y : Fin N → ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    (Matrix.fromBlocks
      (fun i j => extendedHermiteKernel N t (x i) t (x j))
      (fun i j => extendedHermiteKernel N t (x i) r (y j))
      (fun i j => extendedHermiteKernel N r (y i) t (x j))
      (fun i j => extendedHermiteKernel N r (y i) r (y j))).det =
      Real.exp (∑ k : Fin N, (k.val:ℝ)*(r-t)) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i))) *
        (Matrix.det (fun i j : Fin N => mehlerKernel (t-r) (x i) (y j))) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (y i))) := by
  rw [physical_two_time_full_occupancy N t r x y htr, modeEval_det, dualEval_det]
  have he : Real.exp (∑ k : Fin N, (k.val:ℝ)*r) *
      Real.exp (∑ k : Fin N, -((k.val:ℝ)*t)) =
      Real.exp (∑ k : Fin N, (k.val:ℝ)*(r-t)) := by
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ = (Real.exp (∑ k : Fin N, (k.val:ℝ)*r) *
          Real.exp (∑ k : Fin N, -((k.val:ℝ)*t))) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i))) *
        (Matrix.det (fun i j : Fin N => mehlerKernel (t-r) (x i) (y j))) *
        (Matrix.det (fun i k : Fin N => hermiteFunction k.val (y i))) := by ring
    _ = _ := by rw [he]

/-- All arguments of the algebraic seam coexist at a nonzero, two-mode instance.
No analytic or probability hypothesis is present in this algebraic identity. -/
theorem block_all_binder_joint_probe :
    ∃ (N : ℕ) (A B C D P : Matrix (Fin N) (Fin N) ℝ),
      N = 2 ∧ A.det ≠ 0 ∧ B.det ≠ 0 ∧ C.det ≠ 0 ∧ D.det ≠ 0 ∧ P.det ≠ 0 ∧
      (Matrix.fromBlocks (A*B) (A*C-P) (D*B) (D*C)).det = 1 ∧
      (Matrix.fromBlocks (A*B) (A*C-P) (D*B) (D*C)).det =
        D.det * P.det * B.det := by
  refine ⟨2,1,1,1,1,1,rfl,by simp,by simp,by simp,by simp,by simp,?_,?_⟩
  · rw [two_time_block_det]
    simp
  · exact two_time_block_det 2 1 1 1 1 1

/-- All physical binders coexist at strictly separated times and positions;
the physical two-time determinant is strictly positive at N=1. -/
theorem physical_chain_all_binder_joint_probe :
    ∃ (N : ℕ) (t r : ℝ) (x y : Fin N → ℝ),
      0 < N ∧ t < r ∧ t ≠ r ∧ (∀ i, x i ≠ y i) ∧
      (∀ i j, 0 < mehlerKernel (t-r) (x i) (y j)) ∧
      0 < (modeEval N r y).det ∧ 0 < (dualEval N t x).det ∧
      0 < (Matrix.fromBlocks
        (fun i j => extendedHermiteKernel N t (x i) t (x j))
        (fun i j => extendedHermiteKernel N t (x i) r (y j))
        (fun i j => extendedHermiteKernel N r (y i) t (x j))
        (fun i j => extendedHermiteKernel N r (y i) r (y j))).det ∧
      (Matrix.fromBlocks
        (fun i j => extendedHermiteKernel N t (x i) t (x j))
        (fun i j => extendedHermiteKernel N t (x i) r (y j))
        (fun i j => extendedHermiteKernel N r (y i) t (x j))
        (fun i j => extendedHermiteKernel N r (y i) r (y j))).det =
          (modeEval N r y).det *
          (Matrix.det (fun i j => mehlerKernel (t-r) (x i) (y j))) *
          (dualEval N t x).det := by
  let x : Fin 1 → ℝ := fun _ => 0
  let y : Fin 1 → ℝ := fun _ => 1
  have htr : (0:ℝ) < 1 := by norm_num
  have hm : 0 < (modeEval 1 1 y).det := by
    simp [modeEval, y, hermiteFunction_zero_pos]
  have hd : 0 < (dualEval 1 0 x).det := by
    simp [dualEval, x, hermiteFunction_zero_pos]
  have hp : 0 < Matrix.det (fun i j : Fin 1 => mehlerKernel (0-1) (x i) (y j)) := by
    change 0 < Matrix.det (Matrix.of (fun i j : Fin 1 => mehlerKernel (0-1) (x i) (y j)))
    rw [Matrix.det_fin_one]
    exact mehlerKernel_pos (0-1) (x 0) (y 0) (by norm_num)
  refine ⟨1,0,1,x,y,by norm_num,htr,by norm_num,?_,?_,hm,hd,?_,
    physical_two_time_full_occupancy 1 0 1 x y htr⟩
  · intro i
    norm_num [x,y]
  · intro i j
    exact mehlerKernel_pos (0-1) (x i) (y j) (by norm_num)
  · rw [physical_two_time_full_occupancy 1 0 1 x y htr]
    exact mul_pos (mul_pos hm hp) hd

end RMTFoundations.TracyWidom.GUEChainIdentity

#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.block_rotation_det
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.block_corner_det
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.two_time_block_det
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.modeEval
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.dualEval
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.mode_dual_product
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.physical_two_time_full_occupancy
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.modeEval_det
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.dualEval_det
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.physical_two_time_chain_weight
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.block_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEChainIdentity.physical_chain_all_binder_joint_probe
