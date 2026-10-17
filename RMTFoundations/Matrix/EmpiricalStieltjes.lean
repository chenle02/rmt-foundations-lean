import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Matrix Set Filter
open scoped BigOperators Topology

noncomputable section

namespace RMTFoundations.EmpiricalStieltjes

theorem real_trace_spectrum {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [DecidableEq ι /- [definition] -/ ]
    (X : Matrix ι ι ℝ /- [definition] -/ ) (hX : X.IsHermitian /- [standing] -/ ) (x : ℝ /- [definition] -/ )
    (hx : ∀ i, hX.eigenvalues i - x ≠ 0 /- [standing] -/ ) :
    Matrix.trace ((X - x • 1)⁻¹) = ∑ i, (hX.eigenvalues i - x)⁻¹ := by
  let U := hX.eigenvectorUnitary
  let a : ι → ℝ := fun i => hX.eigenvalues i - x
  have hu : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hv : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hd : diagonal a = diagonal (RCLike.ofReal ∘ hX.eigenvalues) - x • 1 := by
    ext i j
    by_cases h : i = j
    · subst j; simp [a]
    · simp [h]
  have hs : X - x • 1 = (U : Matrix ι ι ℝ) * diagonal a * star (U : Matrix ι ι ℝ) := by
    change X - x • 1 = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U (diagonal a)
    rw [hd, map_sub, map_smul, map_one, ← hX.spectral_theorem]
  have hi : (diagonal a)⁻¹ = diagonal (fun i => (a i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [diagonal_mul_diagonal]
    simp [a, hx]
  rw [hs, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_eq_right_inv hu, Matrix.inv_eq_right_inv hv, hi]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, hv, one_mul, Matrix.trace_diagonal]

theorem inverse_derivative (a x : ℝ /- [definition] -/ ) (hx : a - x ≠ 0 /- [standing] -/ ) :
    HasDerivAt (fun y : ℝ => (a-y)⁻¹) ((a-x)⁻¹ ^ 2) x := by
  convert ((hasDerivAt_const x a).sub (hasDerivAt_id x)).inv hx using 1 <;>
    first | rfl | simp [Pi.sub_apply, one_div, inv_pow]

theorem inverse_square_derivative (a x : ℝ /- [definition] -/ ) (hx : a - x ≠ 0 /- [standing] -/ ) :
    HasDerivAt (fun y : ℝ => (a-y)⁻¹ ^ 2) (2 * (a-x)⁻¹ ^ 3) x := by
  convert (inverse_derivative a x hx).pow 2 using 1 <;> first | rfl | ring

theorem twice_inverse_cube_derivative (a x : ℝ /- [definition] -/ ) (hx : a - x ≠ 0 /- [standing] -/ ) :
    HasDerivAt (fun y : ℝ => 2 * (a-y)⁻¹ ^ 3) (6 * (a-x)⁻¹ ^ 4) x := by
  convert ((inverse_derivative a x hx).pow 3).const_mul 2 using 1 <;> first | rfl | ring

def mean0 {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (v i-x)⁻¹
def mean1 {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (v i-x)⁻¹ ^ 2
def mean2 {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, 2 * (v i-x)⁻¹ ^ 3
def mean3 {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, 6 * (v i-x)⁻¹ ^ 4

theorem mean0_derivative {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ )
    (hx : ∀ i, v i-x ≠ 0 /- [standing] -/ ) : HasDerivAt (mean0 v) (mean1 v x) x := by
  unfold mean0 mean1
  convert (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => inverse_derivative (v i) x (hx i))).const_mul
      (Fintype.card ι : ℝ)⁻¹ using 1

theorem mean1_derivative {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ )
    (hx : ∀ i, v i-x ≠ 0 /- [standing] -/ ) : HasDerivAt (mean1 v) (mean2 v x) x := by
  unfold mean1 mean2
  convert (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => inverse_square_derivative (v i) x (hx i))).const_mul
      (Fintype.card ι : ℝ)⁻¹ using 1

theorem mean2_derivative {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] (v : ι → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ )
    (hx : ∀ i, v i-x ≠ 0 /- [standing] -/ ) : HasDerivAt (mean2 v) (mean3 v x) x := by
  unfold mean2 mean3
  convert (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => twice_inverse_cube_derivative (v i) x (hx i))).const_mul
      (Fintype.card ι : ℝ)⁻¹ using 1

def empiricalTrace {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [DecidableEq ι /- [definition] -/ ]
    (X : Matrix ι ι ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Matrix.trace ((X-x•1)⁻¹)

theorem empirical_trace_derivative {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [DecidableEq ι /- [definition] -/ ]
    (X : Matrix ι ι ℝ /- [definition] -/ ) (hX : X.IsHermitian /- [standing] -/ ) (x : ℝ /- [definition] -/ )
    (hx : ∀ i, hX.eigenvalues i-x ≠ 0 /- [standing] -/ ) :
    HasDerivAt (empiricalTrace X) (mean1 hX.eigenvalues x) x := by
  apply (mean0_derivative hX.eigenvalues x hx).congr_of_eventuallyEq
  have he : ∀ᶠ y in 𝓝 x, ∀ i, hX.eigenvalues i-y ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact (continuous_const.sub continuous_id).continuousAt.eventually_ne (hx i)
  filter_upwards [he] with y hy
  unfold empiricalTrace mean0
  rw [real_trace_spectrum X hX y hy]

theorem interval_gap {ι : Type* /- [definition] -/ } (v : ι → ℝ /- [definition] -/ ) (u g x : ℝ /- [definition] -/ )
    (hgap : ∀ i, g ≤ |v i-u| /- [standing] -/ ) (hx : |x-u| ≤ g/2 /- [standing] -/ ) :
    ∀ i, g/2 ≤ |v i-x| := by
  intro i
  have ht := abs_sub_le (v i) x u
  have hi := hgap i
  linarith

theorem third_bound {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [Nonempty ι /- [definition] -/ ]
    (v : ι → ℝ /- [definition] -/ ) (x d : ℝ /- [definition] -/ ) (hd : 0 < d /- [standing] -/ ) (hgap : ∀ i, d ≤ |v i-x| /- [standing] -/ ) :
    |mean3 v x| ≤ 6/d^4 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hni : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  have hp : ∀ i, (v i-x)⁻¹ ^ 4 ≤ d⁻¹ ^ 4 := by
    intro i
    have hi : |(v i-x)⁻¹| ≤ d⁻¹ := by
      simpa only [abs_inv, one_div] using one_div_le_one_div_of_le hd (hgap i)
    calc
      (v i-x)⁻¹ ^ 4 = |(v i-x)⁻¹| ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ d⁻¹ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hi 4
  have hnon : 0 ≤ mean3 v x := by
    unfold mean3
    exact mul_nonneg hni (Finset.sum_nonneg (fun i _ => by positivity))
  rw [abs_of_nonneg hnon]
  calc
    mean3 v x ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, 6*d⁻¹^4 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (by norm_num))) hni
    _ = 6/d^4 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem interval_third_bound {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [Nonempty ι /- [definition] -/ ]
    (v : ι → ℝ /- [definition] -/ ) (u g x : ℝ /- [definition] -/ ) (hg : 0 < g /- [standing] -/ )
    (hgap : ∀ i, g ≤ |v i-u| /- [standing] -/ ) (hx : |x-u| ≤ g/2 /- [standing] -/ ) :
    |mean3 v x| ≤ 96/g^4 := by
  have h := third_bound v x (g/2) (by linarith) (interval_gap v u g x hgap hx)
  convert h using 1
  field_simp
  ring

theorem empirical_interval {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [DecidableEq ι /- [definition] -/ ] [Nonempty ι /- [definition] -/ ]
    (X : Matrix ι ι ℝ /- [definition] -/ ) (hX : X.IsHermitian /- [standing] -/ ) (u g : ℝ /- [definition] -/ ) (hg : 0 < g /- [standing] -/ )
    (hgap : ∀ i, g ≤ |hX.eigenvalues i-u| /- [standing] -/ ) :
    ∀ x, |x-u| ≤ g/2 →
      HasDerivAt (empiricalTrace X) (mean1 hX.eigenvalues x) x ∧
      HasDerivAt (mean1 hX.eigenvalues) (mean2 hX.eigenvalues x) x ∧
      HasDerivAt (mean2 hX.eigenvalues) (mean3 hX.eigenvalues x) x ∧
      |mean3 hX.eigenvalues x| ≤ 96/g^4 := by
  intro x hx
  have hd : ∀ i, hX.eigenvalues i-x ≠ 0 := by
    intro i hi
    have hb := interval_gap hX.eigenvalues u g x hgap hx i
    rw [hi, abs_zero] at hb
    linarith
  exact ⟨empirical_trace_derivative X hX x hd,
    mean1_derivative hX.eigenvalues x hd, mean2_derivative hX.eigenvalues x hd,
    interval_third_bound hX.eigenvalues u g x hg hgap hx⟩

theorem scaled_third_bound {ι : Type* /- [definition] -/ } [Fintype ι /- [definition] -/ ] [Nonempty ι /- [definition] -/ ]
    (v : ι → ℝ /- [definition] -/ ) (u c t x : ℝ /- [definition] -/ ) (hc : 0 < c /- [standing] -/ ) (ht : 0 < t /- [standing] -/ )
    (hgap : ∀ i, c*t^2 ≤ |v i-u| /- [standing] -/ ) (hx : |x-u| ≤ c*t^2/2 /- [standing] -/ ) :
    |mean3 v x| ≤ (96/c^4)/t^8 := by
  have h := interval_third_bound v u (c*t^2) x (by positivity) hgap hx
  convert h using 1
  field_simp

end RMTFoundations.EmpiricalStieltjes

#print axioms RMTFoundations.EmpiricalStieltjes.real_trace_spectrum
#print axioms RMTFoundations.EmpiricalStieltjes.inverse_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.inverse_square_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.twice_inverse_cube_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.mean0
#print axioms RMTFoundations.EmpiricalStieltjes.mean1
#print axioms RMTFoundations.EmpiricalStieltjes.mean2
#print axioms RMTFoundations.EmpiricalStieltjes.mean3
#print axioms RMTFoundations.EmpiricalStieltjes.mean0_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.mean1_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.mean2_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.empiricalTrace
#print axioms RMTFoundations.EmpiricalStieltjes.empirical_trace_derivative
#print axioms RMTFoundations.EmpiricalStieltjes.interval_gap
#print axioms RMTFoundations.EmpiricalStieltjes.third_bound
#print axioms RMTFoundations.EmpiricalStieltjes.interval_third_bound
#print axioms RMTFoundations.EmpiricalStieltjes.empirical_interval
#print axioms RMTFoundations.EmpiricalStieltjes.scaled_third_bound
