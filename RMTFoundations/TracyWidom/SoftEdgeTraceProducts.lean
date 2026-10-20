import RMTFoundations.Airy.Continuity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.SoftEdgeTraceProducts
open Filter MeasureTheory
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryContinuity

/-- Product error for actual Hilbert-Schmidt factors. -/
theorem trace_product_error
    (A B C D : AiryOp /- [definition] -/) :
    traceENorm (A ∘L B-C ∘L D) ≤
      hsENorm (A-C)*hsENorm B+hsENorm C*hsENorm (B-D) := by
  have he : A ∘L B-C ∘L D = (A-C) ∘L B+C ∘L (B-D) := by
    change A*B-C*D = (A-C)*B+C*(B-D)
    simp only [sub_mul,mul_sub]
    abel
  rw [he]
  exact (traceENorm_add_le _ _).trans
    (add_le_add (traceENorm_comp_le _ _) (traceENorm_comp_le _ _))

/-- HS convergence to finite HS factors implies trace-norm convergence of products.
No uniform norm bound on the approximants is assumed. -/
theorem trace_product_tendsto_of_hs
    (A B : ℕ → AiryOp /- [definition] -/)
    (C D : AiryOp /- [definition] -/)
    (hC : hsENorm C ≠ ⊤ /- [standing] -/)
    (hD : hsENorm D ≠ ⊤ /- [standing] -/)
    (hA : Tendsto (fun n => hsENorm (A n-C)) atTop (𝓝 0) /- [standing] -/)
    (hB : Tendsto (fun n => hsENorm (B n-D)) atTop (𝓝 0) /- [standing] -/) :
    Tendsto (fun n => traceENorm (A n ∘L B n-C ∘L D)) atTop (𝓝 0) := by
  have hsize (n : ℕ) : traceENorm (A n ∘L B n-C ∘L D) ≤
      hsENorm (A n-C)*hsENorm (B n-D)+
      hsENorm (A n-C)*hsENorm D+hsENorm C*hsENorm (B n-D) := by
    have he : A n ∘L B n-C ∘L D =
        ((A n-C) ∘L (B n-D)+(A n-C) ∘L D)+C ∘L (B n-D) := by
      change A n*B n-C*D = ((A n-C)*(B n-D)+(A n-C)*D)+C*(B n-D)
      simp only [sub_mul,mul_sub]
      abel
    rw [he]
    exact (traceENorm_add_le _ _).trans
      (add_le_add ((traceENorm_add_le _ _).trans
        (add_le_add (traceENorm_comp_le _ _) (traceENorm_comp_le _ _)))
        (traceENorm_comp_le _ _))
  have hquadratic := ENNReal.Tendsto.mul hA (Or.inr ENNReal.zero_ne_top)
    hB (Or.inr ENNReal.zero_ne_top)
  have hl := ENNReal.Tendsto.mul hA (Or.inr hD)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => hsENorm D) atTop (𝓝 (hsENorm D)))
    (Or.inr ENNReal.zero_ne_top)
  have hr := ENNReal.Tendsto.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => hsENorm C) atTop (𝓝 (hsENorm C)))
    (Or.inr ENNReal.zero_ne_top) hB (Or.inr hC)
  have hh := (hquadratic.add hl).add hr
  simp only [zero_mul,mul_zero,zero_add] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hsize)

end RMTFoundations.TracyWidom.SoftEdgeTraceProducts

#print axioms RMTFoundations.TracyWidom.SoftEdgeTraceProducts.trace_product_error
#print axioms RMTFoundations.TracyWidom.SoftEdgeTraceProducts.trace_product_tendsto_of_hs
