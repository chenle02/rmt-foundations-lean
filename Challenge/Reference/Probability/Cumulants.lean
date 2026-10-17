import Mathlib.Probability.Moments.MGFAnalytic

/-!
Cumulants and analytic moment-cumulant recursion.
Exponential integrability gives the analytic identities and derivative bounds.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace RMTFoundations.Cumulants

variable {Ω : Type* /- [definition] -/ } {m : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ } {X : Ω → ℝ /- [definition] -/ }

/-- The n-th cumulant is defined by the n-th derivative at zero of the cumulant-generating function. -/
noncomputable def cumulant (n : ℕ /- [definition] -/ ) (X : Ω → ℝ /- [definition] -/ ) (μ : Measure Ω /- [definition] -/ ) : ℝ :=
  iteratedDeriv n (cgf X μ) 0

@[simp]
theorem cumulant_one_eq_deriv_cgf :
    cumulant 1 X μ = deriv (cgf X μ) 0 := by
  simp [cumulant, iteratedDeriv_one]

/-- On the interior of the integrability set the mgf is the exponential of the
cgf, as functions. -/
theorem mgf_eq_exp_cgf_eventually [NeZero μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) :
    mgf X μ =ᶠ[𝓝 0] fun t => Real.exp (cgf X μ t) := by
  filter_upwards [isOpen_interior.mem_nhds h] with t ht
  exact (exp_cgf (interior_subset (s := integrableExpSet X μ) ht)).symm

/-- **`mgf' = cgf' · mgf`** near zero, the differentiated form of
`exp (cgf) = mgf`. -/
theorem deriv_mgf_eventuallyEq [NeZero μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) :
    deriv (mgf X μ) =ᶠ[𝓝 0] deriv (cgf X μ) * mgf X μ := by
  filter_upwards [isOpen_interior.mem_nhds h] with t ht
  have hint : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    interior_subset (s := integrableExpSet X μ) ht
  have hpos : 0 < mgf X μ t := mgf_pos' (NeZero.ne μ) hint
  have hd : deriv (cgf X μ) t = deriv (mgf X μ) t / mgf X μ t := by
    have : cgf X μ =ᶠ[𝓝 t] fun s => Real.log (mgf X μ s) := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s _ using rfl
    rw [this.deriv_eq, deriv.log (differentiableAt_mgf ht) hpos.ne']
  simp only [Pi.mul_apply, hd]
  field_simp

/-- `cgf` is `C^∞` at zero on the interior of the integrability set. -/
theorem contDiffAt_cgf {n : ℕ /- [definition] -/ } (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) :
    ContDiffAt ℝ n (cgf X μ) 0 :=
  (analyticAt_cgf h).contDiffAt

/-- and so is `mgf`. -/
theorem contDiffAt_mgf {n : ℕ /- [definition] -/ } (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) :
    ContDiffAt ℝ n (mgf X μ) 0 :=
  (analyticAt_mgf h).contDiffAt

/--
 **The moment–cumulant recursion.**

`E[X^{n+1}] = Σ_{j ≤ n} C(n,j) κ_{j+1} E[X^{n-j}]`.
-/
theorem moment_succ_eq_sum_cumulant_mul_moment [NeZero μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    μ[X ^ (n + 1)] = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * cumulant (j + 1) X μ * μ[X ^ (n - j)] := by
  have hdc : ContDiffAt ℝ n (deriv (cgf X μ)) 0 := (analyticAt_cgf h).deriv.contDiffAt
  have hm : ContDiffAt ℝ n (mgf X μ) 0 := (analyticAt_mgf h).contDiffAt
  calc μ[X ^ (n + 1)]
      = iteratedDeriv (n + 1) (mgf X μ) 0 := (iteratedDeriv_mgf_zero h (n + 1)).symm
    _ = iteratedDeriv n (deriv (mgf X μ)) 0 := by rw [iteratedDeriv_succ']
    _ = iteratedDeriv n (deriv (cgf X μ) * mgf X μ) 0 :=
        (deriv_mgf_eventuallyEq h).iteratedDeriv_eq n
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * iteratedDeriv j (deriv (cgf X μ)) 0 * iteratedDeriv (n - j) (mgf X μ) 0 :=
        iteratedDeriv_mul hdc hm
    _ = ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * cumulant (j + 1) X μ * μ[X ^ (n - j)] := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [iteratedDeriv_mgf_zero h, cumulant, iteratedDeriv_succ']

/-- `E[X^0] = 1` for a probability measure, the base the recursion unwinds on. -/
theorem moment_zero [IsProbabilityMeasure μ /- [standing] -/ ] : μ[X ^ 0] = 1 := by simp

/--
 **The recursion solved for the top cumulant.**

`κ_{n+1} = E[X^{n+1}] - Σ_{j < n} C(n,j) κ_{j+1} E[X^{n-j}]`.
-/
theorem cumulant_succ_eq_moment_sub [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    cumulant (n + 1) X μ = μ[X ^ (n + 1)] - ∑ j ∈ Finset.range n,
      (n.choose j : ℝ) * cumulant (j + 1) X μ * μ[X ^ (n - j)] := by
  have hsplit := moment_succ_eq_sum_cumulant_mul_moment (μ := μ) (X := X) h n
  rw [Finset.sum_range_succ] at hsplit
  simp only [Nat.choose_self, Nat.sub_self, moment_zero, Nat.cast_one, one_mul, mul_one]
    at hsplit
  linarith [hsplit]

/-- The first cumulant is the mean. -/
theorem cumulant_one [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) :
    cumulant 1 X μ = μ[X] := by
  rw [cumulant_one_eq_deriv_cgf, deriv_cgf_zero h]
  simp

section Centered

variable [IsProbabilityMeasure μ /- [standing] -/ ]

/-- For a centred variable the first cumulant vanishes. -/
theorem cumulant_one_eq_zero_of_centered
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (hc : μ[X] = 0 /- [standing] -/ ) :
    cumulant 1 X μ = 0 := by
  rw [cumulant_one h, hc]

/-- For a centred variable the second cumulant is the second moment. -/
theorem cumulant_two_eq_moment_of_centered
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (hc : μ[X] = 0 /- [standing] -/ ) :
    cumulant 2 X μ = μ[X ^ 2] := by
  have := cumulant_succ_eq_moment_sub (μ := μ) (X := X) h 1
  simpa [Finset.sum_range_one, cumulant_one_eq_zero_of_centered h hc] using this

/--
 **For a centred variable the third cumulant IS the third moment.**
-/
theorem cumulant_three_eq_moment_of_centered
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (hc : μ[X] = 0 /- [standing] -/ ) :
    cumulant 3 X μ = μ[X ^ 3] := by
  have h2 := cumulant_succ_eq_moment_sub (μ := μ) (X := X) h 2
  simp [Finset.sum_range_succ, cumulant_one_eq_zero_of_centered h hc, hc] at h2
  simpa using h2

end Centered

/-- **The triangle bound the induction runs on.**

`|κ_{n+1}| ≤ |E[X^{n+1}]| + Σ_{j<n} C(n,j) |κ_{j+1}| |E[X^{n-j}]|`.

Bounding every cumulant from the moments by strong induction needs exactly
this, and it follows from the solved recursion by the triangle inequality. -/
theorem abs_cumulant_succ_le [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    |cumulant (n + 1) X μ| ≤ |μ[X ^ (n + 1)]| + ∑ j ∈ Finset.range n,
      (n.choose j : ℝ) * |cumulant (j + 1) X μ| * |μ[X ^ (n - j)]| := by
  rw [cumulant_succ_eq_moment_sub h n]
  refine (abs_sub _ _).trans ?_
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n.choose j : ℝ))]

/-! ## Comparison of power scales -/

/--
 **`n^{-a} q^{r-2a} ≤ n^{-2} q^{r-4}` for `a ≥ 2`**, given `n⁻¹ ≤ q²`.

    n^{-a} q^{r-2a} / (n^{-2} q^{r-4}) = (n^{-1} q^{-2})^{a-2} ≤ 1,

The ratio is at most one under the stated positivity and scale hypotheses.
-/
theorem scale_collapse {n q a r : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ )
    (hnq : n ^ (-(1 : ℝ)) ≤ q ^ (2 : ℝ)  /- [standing] -/ ) (ha : 2 ≤ a /- [standing] -/ ) :
    n ^ (-a) * q ^ (r - 2 * a) ≤ n ^ (-(2 : ℝ)) * q ^ (r - 4) := by
  set c : ℝ := n ^ (-(1 : ℝ)) * q ^ (-(2 : ℝ)) with hc
  have hcpos : 0 < c := by positivity
  have hcle : c ≤ 1 := by
    rw [hc, Real.rpow_neg hq.le, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact hnq
  have key : c ^ (a - 2) ≤ 1 := Real.rpow_le_one hcpos.le hcle (by linarith)
  have hexp : n ^ (-a) * q ^ (r - 2 * a)
      = (n ^ (-(2 : ℝ)) * q ^ (r - 4)) * c ^ (a - 2) := by
    rw [hc, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hn.le, ← Real.rpow_mul hq.le]
    rw [show n ^ (-(2 : ℝ)) * q ^ (r - 4) * (n ^ (-1 * (a - 2)) * q ^ (-2 * (a - 2)))
          = (n ^ (-(2 : ℝ)) * n ^ (-1 * (a - 2))) * (q ^ (r - 4) * q ^ (-2 * (a - 2))) from by
        ring]
    rw [← Real.rpow_add hn, ← Real.rpow_add hq]
    ring_nf
  rw [hexp]
  have hbase : 0 < n ^ (-(2 : ℝ)) * q ^ (r - 4) := by positivity
  nlinarith [key, hbase]

/-! ## Capped power scales -/

/-- Capped moment exponent: half the smaller of j and four. -/
noncomputable def scaleExp (j : ℕ /- [definition] -/ ) : ℝ := ((min j 4 : ℕ) : ℝ) / 2

/-- Moment scale with the capped exponent: n to the negative exponent times q to the remaining order. -/
noncomputable def scale (n q : ℝ /- [definition] -/ ) (j : ℕ /- [definition] -/ ) : ℝ :=
  n ^ (-(scaleExp j)) * q ^ ((j : ℝ) - 2 * scaleExp j)

theorem one_le_scaleExp {j : ℕ /- [definition] -/ } (hj : 2 ≤ j /- [standing] -/ ) : 1 ≤ scaleExp j := by
  unfold scaleExp
  have h2 : (2 : ℕ) ≤ min j 4 := Nat.le_min.mpr ⟨hj, by norm_num⟩
  have : (2 : ℝ) ≤ ((min j 4 : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

theorem scaleExp_of_four_le {j : ℕ /- [definition] -/ } (hj : 4 ≤ j /- [standing] -/ ) : scaleExp j = 2 := by
  unfold scaleExp
  rw [Nat.min_eq_right hj]; norm_num

/--
 **Multiplication bound for the capped power scale.**

`S_j · S_k ≤ S_{j+k}` whenever `j, k ≥ 2`.
-/
theorem scale_mul_le {n q : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ )
    (hnq : n ^ (-(1 : ℝ)) ≤ q ^ (2 : ℝ)  /- [standing] -/ ) {j k : ℕ /- [definition] -/ } (hj : 2 ≤ j /- [standing] -/ ) (hk : 2 ≤ k /- [standing] -/ ) :
    scale n q j * scale n q k ≤ scale n q (j + k) := by
  have hsum : (4 : ℕ) ≤ j + k := by omega
  have hA : 2 ≤ scaleExp j + scaleExp k := by
    have := one_le_scaleExp hj; have := one_le_scaleExp hk; linarith
  have hcomb : scale n q j * scale n q k
      = n ^ (-(scaleExp j + scaleExp k))
        * q ^ (((j + k : ℕ) : ℝ) - 2 * (scaleExp j + scaleExp k)) := by
    unfold scale
    rw [show n ^ (-(scaleExp j)) * q ^ ((j : ℝ) - 2 * scaleExp j)
          * (n ^ (-(scaleExp k)) * q ^ ((k : ℝ) - 2 * scaleExp k))
        = (n ^ (-(scaleExp j)) * n ^ (-(scaleExp k)))
          * (q ^ ((j : ℝ) - 2 * scaleExp j) * q ^ ((k : ℝ) - 2 * scaleExp k)) from by ring]
    rw [← Real.rpow_add hn, ← Real.rpow_add hq]
    push_cast
    ring_nf
  rw [hcomb, scale, scaleExp_of_four_le hsum, show (2:ℝ) * 2 = 4 from by norm_num]
  exact scale_collapse hn hq hnq hA

theorem scale_pos {n q : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ ) (j : ℕ /- [definition] -/ ) : 0 < scale n q j := by
  unfold scale; positivity

/-- A cumulant-moment product with both orders at least two is bounded
by the product of its constants times the capped scale at the sum of the orders. -/
theorem cumulant_moment_term_le {n q Cj Kk : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ )
    (hnq : n ^ (-(1 : ℝ)) ≤ q ^ (2 : ℝ)  /- [standing] -/ ) {j k : ℕ /- [definition] -/ } (hj : 2 ≤ j /- [standing] -/ ) (hk : 2 ≤ k /- [standing] -/ )
    (hCj : 0 ≤ Cj /- [standing] -/ ) (hKk : 0 ≤ Kk /- [standing] -/ )
    (hcj : |cumulant j X μ| ≤ Cj * scale n q j /- [standing] -/ )
    (hmk : |μ[X ^ k]| ≤ Kk * scale n q k /- [standing] -/ ) :
    |cumulant j X μ| * |μ[X ^ k]| ≤ (Cj * Kk) * scale n q (j + k) := by
  have hsj := scale_pos hn hq j
  have hsk := scale_pos hn hq k
  calc |cumulant j X μ| * |μ[X ^ k]|
      ≤ (Cj * scale n q j) * (Kk * scale n q k) :=
        mul_le_mul hcj hmk (abs_nonneg _) (by positivity)
    _ = (Cj * Kk) * (scale n q j * scale n q k) := by ring
    _ ≤ (Cj * Kk) * scale n q (j + k) := by
        exact mul_le_mul_of_nonneg_left (scale_mul_le hn hq hnq hj hk) (by positivity)

/-- For a centered variable, the fourth cumulant equals the fourth moment
minus three times the square of the second moment. -/
theorem cumulant_four_eq_of_centered [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (hc : μ[X] = 0 /- [standing] -/ ) :
    cumulant 4 X μ = μ[X ^ 4] - 3 * (μ[X ^ 2]) ^ 2 := by
  have h3 := cumulant_succ_eq_moment_sub (μ := μ) (X := X) h 3
  simp [Finset.sum_range_succ, cumulant_one_eq_zero_of_centered h hc,
    cumulant_two_eq_moment_of_centered h hc, hc] at h3
  rw [h3]
  simp only [Pi.pow_apply]
  ring

/-- `scale n q 2` squared is `scale n q 4`: the identity behind the `r = 4`
bound, since `a₂ = 1` and `a₄ = 2` give `n⁻¹·n⁻¹ = n⁻²` with no `q`. -/
theorem scale_two_sq {n q : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (_hq : 0 < q /- [standing] -/ ) :
    scale n q 2 * scale n q 2 = scale n q 4 := by
  unfold scale scaleExp
  norm_num
  rw [← Real.rpow_add hn]
  norm_num

/-- Uniform cumulant and moment bounds for a centered variable imply
`|κ_{r+1}| ≤ (K + 2^r·C·K)·scale(r+1)` for `r ≥ 2`. -/
theorem cumulant_succ_bound {n q C K : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ )
    (hnq : n ^ (-(1 : ℝ)) ≤ q ^ (2 : ℝ)  /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ )
    (hC : 0 ≤ C /- [standing] -/ ) (hK : 0 ≤ K /- [standing] -/ ) {r : ℕ /- [definition] -/ } (hr : 2 ≤ r /- [standing] -/ )
    (hIH : ∀ j, 2 ≤ j → j ≤ r → |cumulant j X μ| ≤ C * scale n q j /- [standing] -/ )
    (hmom : ∀ j, 2 ≤ j → |μ[X ^ j]| ≤ K * scale n q j /- [standing] -/ )
    (hc : μ[X] = 0 /- [standing] -/ ) :
    |cumulant (r + 1) X μ| ≤ (K + 2 ^ r * (C * K)) * scale n q (r + 1) := by
  have hs := scale_pos hn hq (r + 1)
  -- each recursion term is at most `C(r,i) · (C·K) · scale(r+1)`
  have hterm : ∀ i ∈ Finset.range r,
      (r.choose i : ℝ) * |cumulant (i + 1) X μ| * |μ[X ^ (r - i)]|
        ≤ (r.choose i : ℝ) * ((C * K) * scale n q (r + 1)) := by
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hch : (0 : ℝ) ≤ (r.choose i : ℝ) := by positivity
    rcases eq_or_ne i 0 with rfl | hi0
    · -- κ₁ = 0
      rw [cumulant_one_eq_zero_of_centered h hc]
      simp only [abs_zero, mul_zero, zero_mul]
      positivity
    rcases eq_or_ne i (r - 1) with rfl | hilast
    · -- E[X^1] = E[X] = 0
      have : r - (r - 1) = 1 := by omega
      rw [this]
      have h1 : |μ[X ^ 1]| = 0 := by simp [hc]
      rw [h1, mul_zero]
      positivity
    · -- both indices in [2, r], summing to r+1
      have h2i : 2 ≤ i + 1 := by omega
      have hik : 2 ≤ r - i := by omega
      have hle : i + 1 ≤ r := by omega
      have hsum : (i + 1) + (r - i) = r + 1 := by omega
      have := cumulant_moment_term_le (μ := μ) (X := X) hn hq hnq h2i hik hC hK
        (hIH _ h2i hle) (hmom _ hik)
      rw [hsum] at this
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left this hch
  calc |cumulant (r + 1) X μ|
      ≤ |μ[X ^ (r + 1)]| + ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * |cumulant (i + 1) X μ| * |μ[X ^ (r - i)]| :=
        abs_cumulant_succ_le h r
    _ ≤ K * scale n q (r + 1)
          + ∑ i ∈ Finset.range r, (r.choose i : ℝ) * ((C * K) * scale n q (r + 1)) :=
        add_le_add (hmom _ (by omega)) (Finset.sum_le_sum hterm)
    _ = K * scale n q (r + 1)
          + (∑ i ∈ Finset.range r, (r.choose i : ℝ)) * ((C * K) * scale n q (r + 1)) := by
        rw [Finset.sum_mul]
    _ ≤ K * scale n q (r + 1) + 2 ^ r * ((C * K) * scale n q (r + 1)) := by
        have hsumch : (∑ i ∈ Finset.range r, (r.choose i : ℝ)) ≤ 2 ^ r := by
          have : (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)) = 2 ^ r := by
            exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose r)
          rw [Finset.sum_range_succ] at this
          have : (∑ i ∈ Finset.range r, (r.choose i : ℝ)) + 1 = 2 ^ r := by
            simpa using this
          linarith
        have hpos : (0 : ℝ) ≤ (C * K) * scale n q (r + 1) := by positivity
        nlinarith [hsumch, hpos]
    _ = (K + 2 ^ r * (C * K)) * scale n q (r + 1) := by ring

/--
 **A uniform cumulant bound of every order.**
-/
theorem exists_uniform_cumulant_bound {n q K : ℝ /- [definition] -/ } (hn : 0 < n /- [standing] -/ ) (hq : 0 < q /- [standing] -/ )
    (hnq : n ^ (-(1 : ℝ)) ≤ q ^ (2 : ℝ)  /- [standing] -/ ) [IsProbabilityMeasure μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (hK : 0 ≤ K /- [standing] -/ )
    (hmom : ∀ j, 2 ≤ j → |μ[X ^ j]| ≤ K * scale n q j /- [standing] -/ ) (hc : μ[X] = 0 /- [standing] -/ ) :
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, 2 ≤ j → j ≤ r → |cumulant j X μ| ≤ C * scale n q j := by
  intro r
  induction r with
  | zero => exact ⟨0, le_rfl, fun j hj hj0 => by omega⟩
  | succ r ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨C + K + 2 ^ r * (C * K), by positivity, fun j hj hjr => ?_⟩
    have hs := scale_pos hn hq j
    rcases Nat.lt_or_ge j (r + 1) with hlt | hge
    · -- already covered by the inductive hypothesis
      refine (hC j hj (by omega)).trans ?_
      have hnn : (0 : ℝ) ≤ 2 ^ r * (C * K) := by positivity
      have hle : C ≤ C + K + 2 ^ r * (C * K) := by linarith
      exact mul_le_mul_of_nonneg_right hle hs.le
    · -- j = r + 1
      have hje : j = r + 1 := by omega
      subst hje
      rcases Nat.lt_or_ge r 2 with hr1 | hr2
      · -- r = 1, so j = 2 and κ₂ = E[X²]
        have hr1' : r = 1 := by omega
        subst hr1'
        rw [show (1 : ℕ) + 1 = 2 from rfl, cumulant_two_eq_moment_of_centered h hc]
        refine (hmom 2 le_rfl).trans ?_
        have hnn : (0 : ℝ) ≤ 2 ^ (1 : ℕ) * (C * K) := by positivity
        have hle : K ≤ C + K + 2 ^ (1 : ℕ) * (C * K) := by linarith
        exact mul_le_mul_of_nonneg_right hle hs.le
      · refine (cumulant_succ_bound hn hq hnq h hC0 hK hr2 hC hmom hc).trans ?_
        have : K + 2 ^ r * (C * K) ≤ C + K + 2 ^ r * (C * K) := by linarith
        exact mul_le_mul_of_nonneg_right this hs.le

end RMTFoundations.Cumulants

#print axioms RMTFoundations.Cumulants.cumulant
#print axioms RMTFoundations.Cumulants.cumulant_one_eq_deriv_cgf
#print axioms RMTFoundations.Cumulants.mgf_eq_exp_cgf_eventually
#print axioms RMTFoundations.Cumulants.deriv_mgf_eventuallyEq
#print axioms RMTFoundations.Cumulants.contDiffAt_cgf
#print axioms RMTFoundations.Cumulants.contDiffAt_mgf
#print axioms RMTFoundations.Cumulants.moment_succ_eq_sum_cumulant_mul_moment
#print axioms RMTFoundations.Cumulants.moment_zero
#print axioms RMTFoundations.Cumulants.cumulant_succ_eq_moment_sub
#print axioms RMTFoundations.Cumulants.cumulant_one
#print axioms RMTFoundations.Cumulants.cumulant_one_eq_zero_of_centered
#print axioms RMTFoundations.Cumulants.cumulant_two_eq_moment_of_centered
#print axioms RMTFoundations.Cumulants.cumulant_three_eq_moment_of_centered
#print axioms RMTFoundations.Cumulants.abs_cumulant_succ_le
#print axioms RMTFoundations.Cumulants.scale_collapse
#print axioms RMTFoundations.Cumulants.scaleExp
#print axioms RMTFoundations.Cumulants.scale
#print axioms RMTFoundations.Cumulants.one_le_scaleExp
#print axioms RMTFoundations.Cumulants.scaleExp_of_four_le
#print axioms RMTFoundations.Cumulants.scale_mul_le
#print axioms RMTFoundations.Cumulants.scale_pos
#print axioms RMTFoundations.Cumulants.cumulant_moment_term_le
#print axioms RMTFoundations.Cumulants.cumulant_four_eq_of_centered
#print axioms RMTFoundations.Cumulants.scale_two_sq
#print axioms RMTFoundations.Cumulants.cumulant_succ_bound
#print axioms RMTFoundations.Cumulants.exists_uniform_cumulant_bound
