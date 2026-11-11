import LocalLaw.ComponentwiseReferenceBounds
import LocalLaw.SourceGreenCaps
import LocalLaw.SourceSurgeryCorrections

/-!
# A physical endpoint pivot from its actual base-class model component

Only the component containing the specified endpoint needs the base finite
reference budget. Its genuine inverse block supplies diagonal comparability,
and the actual boundary perturbation and endpoint approximation transfer it
to the physical diagonal.
-/

noncomputable section
namespace LocalLaw
local instance endpointPivotTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
local instance (priority := high) canonicalEndpointPivotMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem reference_diagonal_lower_of_component_budget (g : DeficientGraph V d) (hd : 3 ≤ d)
    (c : g.graph.ConnectedComponent)
    (hbudget : (∑ v, (g.restrict c.supp).deficit v) + graphExcess (g.restrict c.supp).graph ≤ finiteOmega d)
    (v : V) (hv : v ∈ c.supp) (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) :
    1 / (finiteReferenceConstant d * (B + 2)) ≤ ‖g.extensionGreen (semicircleRoot z) z v v‖ := by
  have hh := (finiteOmega_reference_diagonal_bounds d hd (g.restrict c.supp)
    c.connected_induce_supp hbudget z hz B hB ⟨v, hv⟩).1
  rw [g.component_extensionGreen hd c c.supp rfl (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le] at hh
  exact hh

theorem endpoint_pivot_cap_of_component_model (g : DeficientGraph V d) (hd : 3 ≤ d)
    (c : g.graph.ConnectedComponent)
    (hbudget : (∑ v, (g.restrict c.supp).deficit v) + graphExcess (g.restrict c.supp).graph ≤ finiteOmega d)
    (v : V) (hv : v ∈ c.supp) (z q t : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B δ : ℝ) (hB : ‖z‖ ≤ B) (_hδ : 0 ≤ δ)
    (happrox : ‖t - g.extensionGreen q z v v‖ ≤ δ)
    (R : ℕ) (hR : ∀ x y, g.graph.dist x y ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (hsmall : δ + pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤
      1 / (2 * finiteReferenceConstant d * (B + 2))) :
    ‖t⁻¹‖ ≤ sourceGreenPivotCap d B := by
  have hC := finiteReferenceConstant_ge_one d hd
  have hB0 : 0 ≤ B := (norm_nonneg z).trans hB
  have hpositive : 0 < 1 / (2 * finiteReferenceConstant d * (B + 2)) := by positivity
  have href := g.reference_diagonal_lower_of_component_budget hd c hbudget v hv z hz B hB
  have hmodel := g.isolated_finiteOmega_boundary_uniform_stability hd c.supp (g.component_cut c)
    c.connected_induce_supp hbudget z q hz hq R hR small ⟨v, hv⟩ ⟨v, hv⟩
  change ‖g.extensionGreen q z v v - g.extensionGreen (semicircleRoot z) z v v‖ ≤
    pairSensitivityConstant d * ‖q - semicircleRoot z‖ at hmodel
  have hdist : ‖g.extensionGreen (semicircleRoot z) z v v - t‖ ≤
      pairSensitivityConstant d * ‖q - semicircleRoot z‖ + δ := by
    exact (norm_sub_le_norm_sub_add_norm_sub _ (g.extensionGreen q z v v) _).trans
      (add_le_add (by simpa only [norm_sub_rev] using hmodel)
        (by simpa only [norm_sub_rev] using happrox))
  have hlower : 1 / (2 * finiteReferenceConstant d * (B + 2)) ≤ ‖t‖ := by
    have hh := norm_sub_norm_le (g.extensionGreen (semicircleRoot z) z v v) t
    have hsplit : 1 / (finiteReferenceConstant d * (B + 2)) =
        2 * (1 / (2 * finiteReferenceConstant d * (B + 2))) := by field_simp; ring
    linarith
  rw [norm_inv]
  exact (inv_anti₀ hpositive hlower).trans_eq (by simp only [sourceGreenPivotCap, one_div, inv_inv])

end DeficientGraph
end LocalLaw
