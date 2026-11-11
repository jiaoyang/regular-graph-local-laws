import LocalLaw.ComponentFiniteLocalization

/-!
# Endpoint Green row sums from actual component incidence

Only endpoints in the same finite component contribute. An actual bound on
the number of endpoint indices in each component therefore gives uniform
row and column sums, independently of the total number of sampled edges.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance endpointKernelRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Literal finite support counting for one row. Repeated endpoint maps are
allowed and are counted with their actual multiplicity. -/
theorem finite_supported_norm_sum {I : Type*} [Fintype I] (f : I → ℂ)
    (p : I → Prop) (B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : Nat.card {i : I // p i} ≤ B)
    (hcap : ∀ i, ‖f i‖ ≤ C) (hzero : ∀ i, ¬p i → f i = 0) :
    ∑ i, ‖f i‖ ≤ (B : ℝ) * C := by
  have hpoint : ∀ i, ‖f i‖ ≤ (if p i then C else 0) := by
    intro i
    by_cases hi : p i
    · simpa only [hi, if_true] using hcap i
    · simp only [hi, if_false, hzero i hi, norm_zero, le_refl]
  calc
    _ ≤ ∑ i, if p i then C else 0 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (Nat.card {i : I // p i} : ℝ) * C := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) hC

namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

/-- Genuine model endpoint sums use component incidence and the proved
finite reference kernel. No inverse-sum estimate is a premise. -/
theorem componentwise_endpoint_green_rows (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget) (f : I → V) (B : ℕ)
    (hcount : ∀ c : g.graph.ConnectedComponent, Nat.card {i : I // f i ∈ c.supp} ≤ B)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ v w, g.graph.dist v w ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) :
    (∀ v, ∑ i, ‖g.extensionGreen q z v (f i)‖ ≤ 2 * (B : ℝ) * finiteExtraReferenceConstant d) ∧
      (∀ v, ∑ i, ‖g.extensionGreen q z (f i) v‖ ≤ 2 * (B : ℝ) * finiteExtraReferenceConstant d) := by
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have ht : 0 ≤ physicalTransfer d z := norm_nonneg _
  have htone : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hcap (u v : V) : ‖g.extensionGreen q z u v‖ ≤ 2 * finiteExtraReferenceConstant d :=
    (g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small u v).trans
      (mul_le_of_le_one_right hC (pow_le_one₀ ht htone))
  have hrow (v : V) : ∑ i, ‖g.extensionGreen q z v (f i)‖ ≤
      2 * (B : ℝ) * finiteExtraReferenceConstant d := by
    let c := g.graph.connectedComponentMk v
    have hh := finite_supported_norm_sum (fun i => g.extensionGreen q z v (f i))
      (fun i => f i ∈ c.supp) B (2 * finiteExtraReferenceConstant d) hC (hcount c)
      (fun i => hcap v (f i)) (fun i hi =>
        g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq v rfl (f i) hi)
    exact hh.trans_eq (by ring)
  refine ⟨hrow, ?_⟩
  intro v
  simpa only [(g.extensionGreen_isSymm q z).apply] using hrow v

end DeficientGraph
end LocalLaw
