import LocalLaw.SwitchingQLocalParameters
import LocalLaw.ActualGuardedGreenCaps
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.AdmissibleGreenBlock
import LocalLaw.SourceResamplingStructural

/-!
# The actual source Q change on the restricted second stage

The enlarged old event supplies its local diagonal and edge caps. The
retained weak event of the switched target supplies its global entry caps.
The true finite switching Ward estimate absorbs their cavity-average change
at the nominal error scale, with no old global cap assumed.
-/

noncomputable section
namespace LocalLaw
local instance actualSwitchingQChangeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_switching_Q_change (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let gnew := g.labelledResampledGraph T boundary samples (logarithmicRadius (c / 4) d N / 4)
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ‖g.Q z - gnew.Q z‖ ≤
        graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let C := guardedGreenEntryCap d + sourceGreenEntryCap d
  let L := sourceGreenPivotCap d B
  have hguard : 0 ≤ guardedGreenEntryCap d := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    unfold guardedGreenEntryCap commonGreenEntryCap
    linarith
  have hsource : 0 ≤ sourceGreenEntryCap d := by
    have hh := finiteReferenceConstant_ge_one d hd
    unfold sourceGreenEntryCap
    linarith
  have hC : 0 ≤ C := add_nonneg hguard hsource
  have hL : 0 ≤ L := by
    have hh := finiteReferenceConstant_ge_one d hd
    dsimp only [L, sourceGreenPivotCap]
    positivity
  filter_upwards [LabelledResamplingState.eventually_selected_fullResample_cavity_change_local_small
    a b d C L B ha hb hd hC hL hB,
    eventually_actualGuardedGreenCaps a b d c β C1 B ha hb hd hc hβ hβc hC1 hB,
    eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB]
    with N hchange hold hnew
  intro g o z hz hzB hfloor Cq badCount hplus ι _ boundary samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let s := g.admissibleState T boundary samples
  let selector := logarithmicRadius (c / 4) d N / 4
  let gnew := g.labelledResampledGraph T boundary samples selector
  intro htarget
  have oldCaps := hold g o z hz hzB hfloor Cq badCount hplus
  have newCaps := hnew gnew z badCount hz hzB hfloor htarget
  have hOld : guardedGreenEntryCap d ≤ C := by dsimp only [C]; linarith
  have hNew : sourceGreenEntryCap d ≤ C := by dsimp only [C]; linarith
  have hh := hchange g o z hz hzB hfloor ι s selector (logarithmicRadius β d N) rfl
    (fun i => (oldCaps.full_diag i).trans hOld)
    (fun i j hij => (oldCaps.full_adj i j hij).trans hOld)
    (fun i j => (newCaps.1 i j).trans hNew)
    oldCaps.full_pivot newCaps.2
  exact hh

end RegularGraph
end LocalLaw
