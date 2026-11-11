import SpectralConsequences.IndexedDeletionQuadratic
import SpectralConsequences.SelectedPhysicalInverse
import LocalLaw.SelectedFirstDeletion

/-! # The switched tip kernel is quadratically close to the literal common minor

Deleting every accepted sampled first vertex erases all outside switching.
Every analytic input in the quadratic Schur estimate is derived from the old
source event and endpoint surgery.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance switchedTipCommonDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def selectedTipOutsideFirsts {V : Type} {T : Set V} {ι : Type} [Fintype ι]
    (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)) :=
  ⟨s.admissibleSecondVertex selector i, by
    rintro ⟨j, hj⟩
    exact selected_first_ne_second s selector i j hj⟩

theorem eventually_switched_tip_common_comparison (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ)^b/(N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀ v, graphBallExcess g.graph v (logarithmicRadius (c/4) d N) ≤ finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      let new := (g.labelledResampledGraph T labels samples selector).deficient.delete T
      let common := (g.deficient.delete T).delete (s.selectedFirstSet selector)
      let μ : ℝ := Nat.card (BoundaryOrientedEdge g.graph T)
      let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z
      ∀ i j : s.AdmissibleSampleIndex selector,
        ‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j)-
          common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)‖ ≤
            μ*(2*sourcePartialFirstInverseCap d B)*δ^2 := by
  filter_upwards [eventually_switched_selected_inverse_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_selected_tip_cross_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_ge_atTop 1] with N hinverse hcross hN
  intro g o z hz hfloor hzB Cq badCount hplus hstrong ι _ labels samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let s := g.admissibleState T labels samples
  let I := s.AdmissibleSampleIndex selector
  let new := (g.labelledResampledGraph T labels samples selector).deficient.delete T
  let W := s.selectedFirstSet selector
  let e := s.selectedFirstEmbedding selector
  let φ : I ≃ W := Equiv.ofInjective e e.injective
  let C := 2*sourcePartialFirstInverseCap d B
  let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z
  have hC : 0 ≤ C := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C,sourcePartialFirstInverseCap]
    positivity
  have hδ : 0 ≤ δ := by
    have hh := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    dsimp only [δ,sourceEndpointErrorConstant,RegularGraph.sourcePrime,inflatedPrime]
    positivity
  have hi := hinverse g o z hz hfloor hzB Cq badCount hplus hstrong labels samples
  have hcros := hcross g o z hz hfloor hzB Cq badCount hplus labels samples
  have hsym : (new.G z).IsSymm := by
    have hh := new.extensionGreen_isSymm (0 : ℂ) z
    simpa only [DeficientGraph.extensionGreen,DeficientGraph.G,boundaryGreen,boundaryMatrix,
      zero_smul,sub_zero,green] using hh
  intro i j
  let x := selectedTipOutsideFirsts s selector i
  let y := selectedTipOutsideFirsts s selector j
  have hx : ∀ k : I, ‖green new.H z x.val (e k)‖ ≤ δ := hcros i
  have hy : ∀ k : I, ‖green new.H z (e k) y.val‖ ≤ δ := by
    intro k
    change ‖new.G z (e k) y.val‖ ≤ δ
    rw [hsym.apply y.val (e k)]
    exact hcros j k
  have hh := physical_indexed_deletion_quadratic_bound new.H
    (normalizedAdjacency_isHermitian new.graph d) W φ z hz C δ hC hδ hi.2.1 x y hx hy
  rw [←new.H_delete W] at hh
  change ‖new.G z x.val y.val-(new.delete W).G z x y‖ ≤ (Fintype.card I : ℝ)*C*δ^2 at hh
  have hcommon := g.labelledResampled_delete_selectedFirst_eq T labels samples selector
  change new.delete W=(g.deficient.delete T).delete W at hcommon
  rw [hcommon] at hh
  have hcard : (Fintype.card I : ℝ) ≤ (Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) := by
    have hsub : Nat.card I ≤ Nat.card ι := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hι := Nat.card_congr labels
    have hn : Nat.card I ≤ Nat.card (BoundaryOrientedEdge g.graph T) := hsub.trans_eq hι
    simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α := ℝ).mpr hn)
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hC) (sq_nonneg δ))

end SpectralConsequences
