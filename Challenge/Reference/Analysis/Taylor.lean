import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Real-parameter, complex-valued Taylor calculus with signed displacement.
This specializes mathlib's integral remainder; it asserts no probability law.
Developed with AI assistance; actual source and kernel checks are separate. -/

namespace RMTFoundations.Taylor

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval

def polynomial (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ ) (h : ℝ /- [standing] -/ ) : ℂ :=
  ∑ j ∈ Finset.range (K+1), (h^j / (j.factorial : ℝ)) • iteratedDeriv j F 0

def remainder (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ ) (h : ℝ /- [standing] -/ ) : ℂ :=
  F h - polynomial F K h

theorem polynomial_zero (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ ) : polynomial F K 0 = F 0 := by
  unfold polynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp

theorem remainder_zero (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ ) : remainder F K 0 = 0 := by
  simp [remainder, polynomial_zero]

theorem remainder_eq_interval_integral (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ )
    (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h : ℝ /- [standing] -/ ) :
    remainder F K h = ∫ t in (0:ℝ)..h,
      ((h-t)^K / (K.factorial : ℝ)) • iteratedDeriv (K+1) F t := by
  by_cases hh : h=0
  · subst h
    simp [remainder_zero]
  have hu : UniqueDiffOn ℝ (uIcc 0 h) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hh with hh | hh <;> simp [le_of_lt hh,hh])
  have hd (j : ℕ) (hj : j ≤ K+1) (t : ℝ) (ht : t ∈ uIcc 0 h) :
      iteratedDerivWithin j F (uIcc 0 h) t = iteratedDeriv j F t :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hF.of_le (by exact_mod_cast hj)).contDiffAt ht
  have hp : taylorWithinEval F K (uIcc 0 h) 0 h = polynomial F K h := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hd j (by simp only [Finset.mem_range] at hj; omega) 0 (left_mem_uIcc)]
    simp [div_eq_mul_inv,mul_comm]
  have ht := taylor_integral_remainder (x₀:=0) (x:=h) (n:=K) hF.contDiffOn
  rw [hp] at ht
  rw [remainder,ht]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hd (K+1) le_rfl t ht]

theorem remainder_eq_unit_integral (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ )
    (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h : ℝ /- [standing] -/ ) :
    remainder F K h = (h^(K+1) / (K.factorial : ℝ)) •
      ∫ r in (0:ℝ)..1, (1-r)^K • iteratedDeriv (K+1) F (r*h) := by
  rw [remainder_eq_interval_integral F K hF h]
  have hc := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => ((h-t)^K / (K.factorial : ℝ)) • iteratedDeriv (K+1) F t)
    (a:=0) (b:=1) h
  simp only [mul_zero,mul_one] at hc
  rw [← hc]
  have heq : (fun r : ℝ => ((h-h*r)^K / (K.factorial : ℝ)) •
      iteratedDeriv (K+1) F (h*r)) =
      fun r : ℝ => (h^K / (K.factorial : ℝ)) •
        ((1-r)^K • iteratedDeriv (K+1) F (r*h)) := by
    funext r
    rw [show h-h*r = h*(1-r) by ring,mul_pow,smul_smul,mul_comm h r]
    congr 1
    ring
  rw [heq,intervalIntegral.integral_smul,smul_smul]
  congr 1
  rw [pow_succ]
  ring

theorem expansion (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ ) (h : ℝ /- [standing] -/ ) :
    F h = polynomial F K h + remainder F K h := by
  simp [remainder]

theorem integral_kernel (K : ℕ /- [definition] -/ ) :
    (∫ r in (0:ℝ)..1, (1-r)^K) = 1/(K+1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^K) 1]
  simp [integral_pow]

theorem norm_remainder_le (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ )
    (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h M : ℝ /- [standing] -/ )
    (hM : ∀ x ∈ uIcc 0 h, ‖iteratedDeriv (K+1) F x‖ ≤ M /- [standing] -/ ) :
    ‖remainder F K h‖ ≤ M * |h|^(K+1) / ((K+1).factorial : ℝ) := by
  have hseg (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : r*h ∈ uIcc 0 h := by
    rcases le_total 0 h with hh | hh
    · rw [uIcc_of_le hh]
      constructor
      · exact mul_nonneg hr.1 hh
      · nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) hh]
    · rw [uIcc_of_ge hh]
      constructor
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2) hh]
      · exact mul_nonpos_of_nonneg_of_nonpos hr.1 hh
  have hi : ‖∫ r in (0:ℝ)..1, (1-r)^K • iteratedDeriv (K+1) F (r*h)‖ ≤
      M / (K+1 : ℝ) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (a:=0) (b:=1)
      (μ:=volume)
      (f:=fun r : ℝ => (1-r)^K • iteratedDeriv (K+1) F (r*h))
      (g:=fun r : ℝ => (1-r)^K * M) (by norm_num)
      (Filter.Eventually.of_forall (fun r hr => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by linarith [hr.2]) K)]
        exact mul_le_mul_of_nonneg_left (hM (r*h) (hseg r ⟨le_of_lt hr.1,hr.2⟩))
          (pow_nonneg (by linarith [hr.2]) K)))
      (by exact (by fun_prop : Continuous (fun r : ℝ => (1-r)^K*M)).intervalIntegrable 0 1)
    simpa [intervalIntegral.integral_mul_const,integral_kernel,div_eq_mul_inv,mul_comm] using hb
  rw [remainder_eq_unit_integral F K hF h,norm_smul,Real.norm_eq_abs,
    abs_div,abs_pow,abs_of_pos (by positivity : (0:ℝ)<(K.factorial:ℝ))]
  calc
    _ ≤ (|h|^(K+1)/(K.factorial:ℝ))*(M/(K+1:ℝ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      field_simp

theorem iterated_iterated (F : ℝ → ℂ /- [definition] -/ ) (r j : ℕ /- [definition] -/ ) :
    iteratedDeriv r (iteratedDeriv j F) = iteratedDeriv (r+j) F := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

theorem iterated_contDiff (F : ℝ → ℂ /- [definition] -/ ) (n j : ℕ /- [definition] -/ )
    (hF : ContDiff ℝ (n+j : ℕ) F /- [standing] -/ ) : ContDiff ℝ n (iteratedDeriv j F) := by
  rw [contDiff_nat_iff_iteratedDeriv]
  constructor
  · intro m hm
    rw [iterated_iterated]
    exact hF.continuous_iteratedDeriv (m+j) (by exact_mod_cast (show m+j ≤ n+j by omega))
  · intro m hm
    rw [iterated_iterated]
    exact hF.differentiable_iteratedDeriv (m+j) (by exact_mod_cast (show m+j < n+j by omega))

theorem iterated_expansion (F : ℝ → ℂ /- [definition] -/ ) (K j : ℕ /- [definition] -/ ) (h : ℝ /- [standing] -/ ) :
    iteratedDeriv j F h =
      (∑ r ∈ Finset.range (K-j+1), (h^r / (r.factorial : ℝ)) • iteratedDeriv (r+j) F 0)
        + remainder (iteratedDeriv j F) (K-j) h := by
  simpa only [polynomial,iterated_iterated] using expansion (iteratedDeriv j F) (K-j) h

theorem iterated_remainder_eq_unit_integral (F : ℝ → ℂ /- [definition] -/ ) (K j : ℕ /- [definition] -/ )
    (hj : j ≤ K /- [standing] -/ ) (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h : ℝ /- [standing] -/ ) :
    remainder (iteratedDeriv j F) (K-j) h =
      (h^(K-j+1) / ((K-j).factorial : ℝ)) •
        ∫ r in (0:ℝ)..1, (1-r)^(K-j) • iteratedDeriv (K+1) F (r*h) := by
  have he : K-j+1+j = K+1 := by omega
  have hd := iterated_contDiff F (K-j+1) j (by simpa only [he] using hF)
  simpa only [iterated_iterated,he] using remainder_eq_unit_integral (iteratedDeriv j F) (K-j) hd h

theorem iterated_norm_remainder_le (F : ℝ → ℂ /- [definition] -/ ) (K j : ℕ /- [definition] -/ )
    (hj : j ≤ K /- [standing] -/ ) (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h M : ℝ /- [standing] -/ )
    (hM : ∀ x ∈ uIcc 0 h, ‖iteratedDeriv (K+1) F x‖ ≤ M /- [standing] -/ ) :
    ‖remainder (iteratedDeriv j F) (K-j) h‖ ≤
      M * |h|^(K-j+1) / ((K-j+1).factorial : ℝ) := by
  have he : K-j+1+j = K+1 := by omega
  have hd := iterated_contDiff F (K-j+1) j (by simpa only [he] using hF)
  apply norm_remainder_le (iteratedDeriv j F) (K-j) hd h M
  simpa only [iterated_iterated,he] using hM

end

end RMTFoundations.Taylor

#print axioms RMTFoundations.Taylor.polynomial
#print axioms RMTFoundations.Taylor.remainder
#print axioms RMTFoundations.Taylor.polynomial_zero
#print axioms RMTFoundations.Taylor.remainder_zero
#print axioms RMTFoundations.Taylor.remainder_eq_interval_integral
#print axioms RMTFoundations.Taylor.remainder_eq_unit_integral
#print axioms RMTFoundations.Taylor.expansion
#print axioms RMTFoundations.Taylor.integral_kernel
#print axioms RMTFoundations.Taylor.norm_remainder_le
#print axioms RMTFoundations.Taylor.iterated_iterated
#print axioms RMTFoundations.Taylor.iterated_contDiff
#print axioms RMTFoundations.Taylor.iterated_expansion
#print axioms RMTFoundations.Taylor.iterated_remainder_eq_unit_integral
#print axioms RMTFoundations.Taylor.iterated_norm_remainder_le
