import RMTFoundations.TracyWidom.GUEHermite
import RMTFoundations.TracyWidom.HermiteEdgeScale
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

set_option autoImplicit false

namespace RMTFoundations.TracyWidom.HermiteEdgeNormalization

open Filter Topology
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeScale

/-- The literal factorial correction after the coalescing-saddle powers cancel.
This is not an assumption about the Hermite mode or an Airy connection formula. -/
noncomputable def amplitude (N : ℕ /- [definition] -/) : ℝ :=
  Real.sqrt (Stirling.stirlingSeq N / Real.sqrt Real.pi)

lemma amplitude_pos (n : ℕ /- [definition] -/) :
    0 < amplitude (n+1) := by
  apply Real.sqrt_pos.mpr
  exact div_pos (Stirling.stirlingSeq'_pos n) (by positivity)

lemma amplitude_ge_one (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : 1 ≤ amplitude N := by
  have h := Stirling.sqrt_pi_le_stirlingSeq (Nat.ne_of_gt hN)
  unfold amplitude
  rw [Real.one_le_sqrt]
  exact (le_div_iff₀ (by positivity)).mpr (by simpa using h)

lemma amplitude_antitone : Antitone (fun n : ℕ => amplitude (n+1)) := by
  intro n m hnm
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
    (Stirling.stirlingSeq'_antitone hnm) (by positivity))

/-- An effective uniform bound, valid at every positive dimension. -/
lemma amplitude_upper (n : ℕ /- [definition] -/) :
    amplitude (n+1) ≤ amplitude 1 := by
  simpa using amplitude_antitone (Nat.zero_le n)

/-- Mathlib's proved Stirling theorem fixes this scalar correction to one. -/
theorem amplitude_tendsto :
    Tendsto (fun n : ℕ => amplitude (n+1)) atTop (𝓝 1) := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
    (tendsto_add_atTop_nat 1)).div_const (Real.sqrt Real.pi)
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  simpa [amplitude, hp] using h.sqrt

lemma log_amplitude (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    Real.log (amplitude N) =
      Real.log (N.factorial : ℝ) / 2 - (N : ℝ) * Real.log N / 2 +
      (N : ℝ) / 2 - Real.log N / 4 - Real.log (2 * Real.pi) / 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Stirling.stirlingSeq N := by
    unfold Stirling.stirlingSeq
    positivity
  rw [amplitude, Real.log_sqrt (by positivity),
    Real.log_div (ne_of_gt hs) (by positivity), Stirling.log_stirlingSeq_formula,
    Real.log_sqrt (by positivity), Real.log_mul (by norm_num) (ne_of_gt hn),
    Real.log_div (ne_of_gt hn) (by positivity), Real.log_exp,
    Real.log_mul (by norm_num) (by positivity)]
  ring

/-- This connects the factorial correction to the existing literal Hermite normalizer. -/
lemma log_normalizer_factorial (N : ℕ /- [definition] -/) :
    Real.log (hermiteNormalizer N * (N.factorial : ℝ)) =
      Real.log (N.factorial : ℝ) / 2 - Real.log (2 * Real.pi) / 4 := by
  rw [Real.log_mul (ne_of_gt (hermiteNormalizer_pos N)) (by positivity)]
  unfold hermiteNormalizer
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
    Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity)]
  ring

/-- Exact external prefactor for He_N's standard generating-contour saddle at sqrt(N).
The contour integral identity and its asymptotic evaluation remain separate obligations. -/
noncomputable def saddlePrefactor (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  (N : ℝ)^(1/12 : ℝ) * hermiteNormalizer N * (N.factorial : ℝ) *
    Real.exp (-(edgePoint N x)^2/4 + 3*(N : ℝ)/2 +
      Real.sqrt N * edgeScale N * x - (N : ℝ)/2 * Real.log N) *
    (N : ℝ)^(-1/3 : ℝ)

/-- All powers/exponentials simplify exactly, including the finite Gaussian correction. -/
theorem saddle_prefactor_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    saddlePrefactor N x = amplitude N *
      Real.exp (-x^2 * (edgeScale N)^2 / 4) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < amplitude N := by
    unfold amplitude Stirling.stirlingSeq
    positivity
  have hf : 0 < hermiteNormalizer N * (N.factorial : ℝ) :=
    mul_pos (hermiteNormalizer_pos N) (by positivity)
  have hs := Real.sq_sqrt hn.le
  have he : -(edgePoint N x)^2/4 + 3*(N : ℝ)/2 +
      Real.sqrt N * edgeScale N * x - (N : ℝ)/2 * Real.log N =
      (N : ℝ)/2 - (N : ℝ)/2 * Real.log N - x^2*(edgeScale N)^2/4 := by
    unfold edgePoint
    nlinarith [hs]
  rw [saddlePrefactor, he, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn]
  have hfac : hermiteNormalizer N * (N.factorial : ℝ) =
      Real.exp (Real.log (N.factorial : ℝ)/2 - Real.log (2*Real.pi)/4) := by
    rw [← log_normalizer_factorial, Real.exp_log hf]
  have haa : amplitude N = Real.exp (Real.log (N.factorial : ℝ)/2 -
      (N : ℝ)*Real.log N/2 + (N : ℝ)/2 - Real.log N/4 -
      Real.log (2*Real.pi)/4) := by
    rw [← log_amplitude N hN, Real.exp_log ha]
  rw [haa]
  calc
    _ = Real.exp (Real.log N*(1/12)) *
        (hermiteNormalizer N * (N.factorial : ℝ)) *
        Real.exp ((N : ℝ)/2 - (N : ℝ)/2*Real.log N - x^2*(edgeScale N)^2/4) *
        Real.exp (Real.log N*(-1/3)) := by ring
    _ = _ := by
      rw [hfac, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

lemma exp_negative_error (t : ℝ /- [definition] -/)
    (ht : 0 ≤ t /- [standing] -/) :
    |Real.exp (-t) - 1| ≤ t := by
  have h1 : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -t ≤ 0 by linarith)
  rw [abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-t)]

/-- Quantitative compact error separates the proved factorial correction from
any still-unproved asymptotics of the Hermite contour integral. -/
theorem saddle_prefactor_compact_error (n : ℕ /- [definition] -/)
    (R x : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hx : |x| ≤ R /- [standing] -/) :
    |saddlePrefactor (n+1) x - 1| ≤
      |amplitude (n+1) - 1| + amplitude 1 * R^2 * (edgeScale (n+1))^2 / 4 := by
  rw [saddle_prefactor_identity _ (by omega)]
  have ha := (amplitude_pos n).le
  have hp := amplitude_upper n
  have hx2 : x^2 ≤ R^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have he := exp_negative_error (x^2*(edgeScale (n+1))^2/4) (by positivity)
  calc
    _ = |(amplitude (n+1)-1) + amplitude (n+1)*
        (Real.exp (-(x^2*(edgeScale (n+1))^2/4))-1)| := by congr 1; ring
    _ ≤ |amplitude (n+1)-1| + |amplitude (n+1)*
        (Real.exp (-(x^2*(edgeScale (n+1))^2/4))-1)| := abs_add_le _ _
    _ = |amplitude (n+1)-1| + amplitude (n+1)*
        |Real.exp (-(x^2*(edgeScale (n+1))^2/4))-1| := by
      rw [abs_mul, abs_of_nonneg ha]
    _ ≤ |amplitude (n+1)-1| + amplitude (n+1)*(x^2*(edgeScale (n+1))^2/4) := by
      gcongr
    _ ≤ _ := by
      have hh := mul_le_mul hp hx2 (sq_nonneg x) (amplitude_pos 0).le
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (edgeScale (n+1)))]

/-- Local uniform convergence of the actual extracted prefactor, with no PR premise. -/
theorem saddle_prefactor_locally_uniform (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ R →
      |saddlePrefactor (n+1) x - 1| < ε := by
  have h1 : Tendsto (fun n : ℕ => |amplitude (n+1)-1|) atTop (𝓝 0) := by
    simpa using (amplitude_tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/3 by norm_num)).comp hn
  have h3 : Tendsto (fun n : ℕ => |amplitude (n+1)-1| +
      amplitude 1*R^2*(edgeScale (n+1))^2/4) atTop (𝓝 0) := by
    simp_rw [edgeScale_square]
    have hh := h1.add (h2.const_mul (amplitude 1*R^2/4))
    convert hh using 1
    · funext n
      dsimp only [Function.comp_apply]
      ring
    · norm_num
  filter_upwards [h3.eventually (gt_mem_nhds hε)] with n hn x hx
  exact lt_of_le_of_lt (saddle_prefactor_compact_error n R x hR hx) hn

/-- Complete growing joint example: every finite standing binder is supplied by
terms at the same literal Hermite normalizer and positive scale; the limit is proved. -/
theorem normalization_all_binder_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < amplitude (n+1) ∧ 1 ≤ amplitude (n+1) ∧
      amplitude (n+1) ≤ amplitude 1 ∧
      saddlePrefactor (n+1) 1 = amplitude (n+1) * Real.exp (-(edgeScale (n+1))^2/4) ∧
      |saddlePrefactor (n+1) 1 - 1| ≤ |amplitude (n+1)-1| +
        amplitude 1*3^2*(edgeScale (n+1))^2/4) ∧
    Tendsto (fun n : ℕ => amplitude (n+1)) atTop (𝓝 1) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ 3 →
      |saddlePrefactor (n+1) x - 1| < ε) := by
  refine ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, ?_, amplitude_tendsto, ?_⟩
  · intro n
    refine ⟨amplitude_pos n, amplitude_ge_one _ (by omega), amplitude_upper n, ?_,
      saddle_prefactor_compact_error n 3 1 (by norm_num) (by norm_num)⟩
    simpa using saddle_prefactor_identity (n+1) (by omega) 1
  · intro ε hε
    exact saddle_prefactor_locally_uniform 3 (by norm_num) ε hε

end RMTFoundations.TracyWidom.HermiteEdgeNormalization

#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude_pos
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude_ge_one
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude_antitone
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude_upper
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.amplitude_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.log_amplitude
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.log_normalizer_factorial
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.saddlePrefactor
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.saddle_prefactor_identity
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.exp_negative_error
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.saddle_prefactor_compact_error
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.saddle_prefactor_locally_uniform
#print axioms RMTFoundations.TracyWidom.HermiteEdgeNormalization.normalization_all_binder_joint_probe
