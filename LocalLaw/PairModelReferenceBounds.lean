import LocalLaw.PairComponentExcess
import LocalLaw.ComponentwiseReferenceBounds

/-!
# Actual pair-model reference and boundary estimates

The original structural event supplies every connected pair-model component's
reference budget. Its inverse blocks and the true 4r+1 diameter cap yield
uniform physical-reference and boundary-sensitivity estimates, even for a
disconnected union of balls. No pair-model reference estimate is an input.
-/

namespace LocalLaw
noncomputable section
local instance pairReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

/-- The componentwise budget for the concrete physical pair model. -/
theorem pairModel_componentReferenceBudget (g : RegularGraph N d) (i j : Fin N) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d) :
    (g.pairModel i j r).ComponentReferenceBudget :=
  fun c => g.pairModel_component_budget i j r R hmargin hballs c

theorem pairP_reference_entry_bound (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    ‖g.P r z (semicircleRoot z) i j‖ ≤ finiteReferenceConstant d := by
  have hh := (g.pairModel i j r).componentwise_reference_entry_bound hd
    (g.pairModel_componentReferenceBudget i j r R hmargin hballs) z hz
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)
  rw [g.pairModel_P] at hh
  exact hh

theorem pairP_reference_im_bound (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    |(g.P r z (semicircleRoot z) i j).im| ≤ finiteReferenceConstant d * (graphKestenMcKayReference d z).im := by
  have hh := (g.pairModel i j r).componentwise_reference_im_bound hd
    (g.pairModel_componentReferenceBudget i j r R hmargin hballs) z hz
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)
  rw [g.pairModel_P] at hh
  exact hh

theorem pairP_reference_diagonal_bounds (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) (i : Fin N) :
    1 / (finiteReferenceConstant d * (B + 2)) ≤ ‖g.P r z (semicircleRoot z) i i‖ ∧
      ‖g.P r z (semicircleRoot z) i i‖ ≤ finiteReferenceConstant d := by
  have hh := (g.pairModel i i r).componentwise_reference_diagonal_bounds hd
    (g.pairModel_componentReferenceBudget i i r R hmargin hballs) z hz B hB
    (pairBallLeft g.graph i i r)
  have heq : pairBallLeft g.graph i i r = pairBallRight g.graph i i r := Subtype.ext rfl
  rw [heq, ← heq] at hh
  change 1 / (finiteReferenceConstant d * (B + 2)) ≤
      ‖(g.pairModel i i r).extensionGreen (semicircleRoot z) z
        (pairBallLeft g.graph i i r) (pairBallRight g.graph i i r)‖ ∧ _ at hh
  rw [g.pairModel_P] at hh
  exact ⟨hh.1, g.pairP_reference_entry_bound hd r R hmargin hballs z hz i i⟩

/-- Degree-dependent uniform boundary correction for the actual pair model. -/
theorem pairP_boundary_uniform_stability (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2) (i j : Fin N) :
    ‖g.P r z q i j - g.P r z (semicircleRoot z) i j‖ ≤
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) * ‖q - semicircleRoot z‖ := by
  have hs : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (((4 * r + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    have heq : (((4 * r + 1 : ℕ) : ℝ) + 1) = 4 * (r : ℝ) + 2 := by push_cast; ring
    rw [heq]
    exact small
  have hh := (g.pairModel i j r).componentwise_boundary_uniform_stability hd
    (g.pairModel_componentReferenceBudget i j r R hmargin hballs) z q hz hq (4 * r + 1)
    (pairBall_distance_bound g.graph i j r) hs (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)
  rw [g.pairModel_P, g.pairModel_P] at hh
  exact hh

theorem pairP_perturbed_entry_bound (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2) (i j : Fin N) :
    ‖g.P r z q i j‖ ≤ finiteReferenceConstant d +
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) * ‖q - semicircleRoot z‖ := by
  have hh := norm_add_le (g.P r z (semicircleRoot z) i j) (g.P r z q i j - g.P r z (semicircleRoot z) i j)
  rw [add_sub_cancel] at hh
  exact hh.trans (add_le_add (g.pairP_reference_entry_bound hd r R hmargin hballs z hz i j)
    (g.pairP_boundary_uniform_stability hd r R hmargin hballs z q hz hq small i j))

end RegularGraph
end
end LocalLaw
