import RMTFoundations.TracyWidom.Functions
import Mathlib



set_option autoImplicit false

namespace RMTFoundations.TracyWidom.GUEIdentification

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open RMTFoundations.AiryKernel (TW2R TW2)

/-- Literal independent standard real Gaussian source. Redundant entries give
one simple source law; the Hermitian symmetrization below discards redundancy. -/
noncomputable def gueMeasure (n : ℕ /- [definition] -/) :
    Measure ((Fin (n+1) × Fin (n+1) × Fin 2) → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance gueMeasure_probability (n : ℕ /- [definition] -/) :
    IsProbabilityMeasure (gueMeasure n) := by
  unfold gueMeasure
  infer_instance

/-- GUE with diagonal variance 1 and independent off-diagonal real/imaginary
parts of variance 1/2: H=(X+X^T)/2 + i(Y-Y^T)/2. Edge is 2 sqrt(N). -/
noncomputable def gueMatrix (n : ℕ /- [definition] -/)
    (x : (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ /- [definition] -/) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j =>
  (((x (i,j,0) + x (j,i,0)) / 2 : ℝ) : ℂ) +
    Complex.I * (((x (i,j,1) - x (j,i,1)) / 2 : ℝ) : ℂ)

lemma gueMatrix_hermitian (n : ℕ /- [definition] -/)
    (x : (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ /- [definition] -/) :
    (gueMatrix n x).IsHermitian := by
  ext i j
  change star (gueMatrix n x j i) = gueMatrix n x i j
  apply Complex.ext <;>
    simp only [gueMatrix, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
    ring

lemma gueMatrix_diagonal (n : ℕ /- [definition] -/)
    (x : (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ /- [definition] -/)
    (i : Fin (n+1) /- [definition] -/) :
    gueMatrix n x i i = (x (i,i,0) : ℂ) := by
  simp only [gueMatrix, sub_self, zero_div, Complex.ofReal_zero, mul_zero, add_zero]
  congr 1
  ring

/-- A full-rank deterministic instance of the same literal source map. -/
def gueIdentityCoordinates (n : ℕ /- [definition] -/) :
    (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ :=
  fun q => if q.1 = q.2.1 then 1 else 0

lemma gueMatrix_identity_fixture (n : ℕ /- [definition] -/) :
    gueMatrix n (gueIdentityCoordinates n) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [gueMatrix, gueIdentityCoordinates]
  · have hji := Ne.symm hij
    simp [gueMatrix, gueIdentityCoordinates, hij, hji]

/-- Literal maximum event: no ordering convention or good-flow event appears. -/
noncomputable def gueCDF (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : ℝ :=
  (gueMeasure n).real {x | ∀ i, (gueMatrix_hermitian n x).eigenvalues i ≤
    2 * Real.sqrt (n+1 : ℕ) + s / ((n+1 : ℕ) : ℝ) ^ (1/6 : ℝ)}

/-- The standard unnormalized GUE largest-eigenvalue limit. -/
def GUELimit (F : ℝ → ℝ /- [definition] -/) : Prop :=
  ∀ s, Tendsto (fun n => gueCDF n s) atTop (𝓝 (F s))

/-- A distinct beta=2 identification; it carries a registered limit-identification hypothesis.
This is uniqueness of the limit, not a Lean proof of Hermite edge asymptotics. -/
theorem gaussian_unitary_limit_eq_TW2R
    (Fgue : ℝ → ℝ /- [definition] -/)
    (hgue : GUELimit Fgue /- [standing] -/)
    (hFredholm : GUELimit TW2R /- [standing] -/) :
    Fgue = TW2R := by
  funext s
  exact tendsto_nhds_unique (hgue s) (hFredholm s)

theorem gaussian_unitary_limit_eq_physical_fredholm
    (Fgue : ℝ → ℝ /- [definition] -/)
    (hgue : GUELimit Fgue /- [standing] -/)
    (hFredholm : GUELimit TW2R /- [standing] -/)
    (s : ℝ /- [definition] -/) :
    (Fgue s : ℂ) = TW2 s := by
  rw [gaussian_unitary_limit_eq_TW2R Fgue hgue hFredholm]
  exact RMTFoundations.AiryKernel.TW2R_coe s

/-- Transfer the supplied GUE convergence to a beta-two source family using the stated comparison. -/
theorem application_cdf_at_TW2R
    (cdf : ℕ → ℝ → ℝ /- [definition] -/)
    (Fgue : ℝ → ℝ /- [definition] -/)
    (hgue : GUELimit Fgue /- [standing] -/)
    (hFredholm : GUELimit TW2R /- [standing] -/)
    (hsource : ∀ s, Tendsto (fun n => cdf n s) atTop (𝓝 (Fgue s)) /- [standing] -/) :
    ∀ s, Tendsto (fun n => cdf n s) atTop (𝓝 (TW2R s)) := by
  rw [gaussian_unitary_limit_eq_TW2R Fgue hgue hFredholm] at hsource
  exact hsource

/-- Complete joint probe: all data and all non-import premises are terms on
one actual Gaussian source, n+1 grows, positive coordinate variance, nonzero H.
The sole retained mathematical input is the GUE-Fredholm limit-identification hypothesis. -/
theorem identification_all_binder_joint_probe
    (hFredholm : GUELimit TW2R /- [standing] -/) :
    ∃ Fgue : ℝ → ℝ,
      GUELimit Fgue ∧ Fgue = TW2R ∧
      (∀ s, (Fgue s : ℂ) = TW2 s) ∧
      (∀ s, Tendsto (fun n => gueCDF n s) atTop (𝓝 (Fgue s))) ∧
      (∀ n, IsProbabilityMeasure (gueMeasure n)) ∧
      (0 < (1 : ℝ)) ∧
      (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
      (∀ n, gueMatrix n (gueIdentityCoordinates n) ≠ 0) ∧
      (∀ n, Matrix.det (gueMatrix n (gueIdentityCoordinates n)) = 1) ∧
      (∀ n, ∀ x : (Fin (n+1) × Fin (n+1) × Fin 2) → ℝ,
        (gueMatrix n x).IsHermitian) := by
  refine ⟨TW2R, hFredholm,
    gaussian_unitary_limit_eq_TW2R TW2R hFredholm hFredholm,
    gaussian_unitary_limit_eq_physical_fredholm TW2R hFredholm hFredholm,
    application_cdf_at_TW2R gueCDF TW2R hFredholm hFredholm hFredholm,
    fun n => inferInstance, by norm_num,
    fun K => ⟨K, Nat.lt_succ_self K⟩, ?_, ?_, gueMatrix_hermitian⟩
  · intro n hzero
    rw [gueMatrix_identity_fixture] at hzero
    have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M 0 0) hzero
    norm_num [Matrix.one_apply] at h
  · intro n
    rw [gueMatrix_identity_fixture, Matrix.det_one]

end RMTFoundations.TracyWidom.GUEIdentification

#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMeasure
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMeasure_probability
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMatrix
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMatrix_hermitian
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMatrix_diagonal
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueCDF
#print axioms RMTFoundations.TracyWidom.GUEIdentification.GUELimit
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gaussian_unitary_limit_eq_TW2R
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gaussian_unitary_limit_eq_physical_fredholm
#print axioms RMTFoundations.TracyWidom.GUEIdentification.application_cdf_at_TW2R
#print axioms RMTFoundations.TracyWidom.GUEIdentification.identification_all_binder_joint_probe

#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueIdentityCoordinates
#print axioms RMTFoundations.TracyWidom.GUEIdentification.gueMatrix_identity_fixture
