import LocalLaw.FirstStageComparisonPacket
import LocalLaw.SourceFullBoundaryChange
import LocalLaw.SourceDeletedBoundaryChange

/-! # First-stage boundary changes follow from the frozen physical comparisons

Only the full/deleted physical estimates at Qold remain as comparison fields.
The actual Q-change, new Q-prior, and both model boundary changes are derived.
-/

noncomputable section
namespace LocalLaw
local instance firstStageBoundaryAssemblyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

structure FirstStageFrozenComparisons (g h : RegularGraph N d) (T : Set (Fin N))
    (a r rn : ℕ) (z : ℂ) (Dfull Ddeleted : ℝ) : Prop where
  full : ∀ i j,‖h.G z i j-h.P r z (g.Q z) i j‖≤Dfull/Real.log (N:ℝ)
  deleted : ∀i j:(Tᶜ:Set (Fin N)),
    ‖(h.deficient.delete T).G z i j-h.deletedP T r z (g.Q z) i j‖≤Ddeleted*g.sourcePrime a rn z

theorem eventually_firstStage_packet_of_frozen (a b d Bnear : ℕ) (c β B Dfull Ddeleted : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β)
    (hβc : β≤c/32) (hB : 0≤B) (hD : 1≤Dfull) :
    ∀ᶠ N : ℕ in Filter.atTop,∀(g : RegularGraph N d)(o : Fin N)(z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount Cq:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let T := graphBallVertices g.graph o ell
      let R := logarithmicRadius (c/4) d N
      let r := effectiveModelRadius a d N β
      let rn := logarithmicRadius β d N
      let h := g.labelledResampledGraph T labels samples (R/4)
      h.SourceStructuralPlus R (finiteOmega d) Cq badCount →
      (∀v:(Tᶜ:Set (Fin N)),(tripleNearIndices g.graph T (R/2) samples v).card≤Bnear) →
      FirstStageFrozenComparisons g h T a r rn z Dfull Ddeleted →
      FirstStageComparisonPacket g h T a r rn z Dfull Ddeleted := by
  filter_upwards [eventually_firstStage_Q_change_of_near_comparison a b d c β B Dfull ha hb hd hc hβ hβc hB hD,
    eventually_firstStage_Q_prior_of_near_comparison a b d c β B Dfull ha hb hd hc hβ hβc hB hD,
    eventually_source_full_boundary_change a b d c β B 2 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_deleted_boundary_change a b d Bnear c β B 2 ha hb hd hc hβ hβc (by norm_num),
    Filter.eventually_ge_atTop 1] with N hchange hprior hfull hdeleted hN
  intro g o z hz hzB hfloor badCount Cq hsource ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let h := g.labelledResampledGraph T labels samples (R/4)
  intro hstruct hnear F
  have hfrozen : g.nearFrozenBoundaryComparison h r Dfull z := fun i j _=>F.full i j
  have hcq := hchange g o z hz hzB hfloor badCount hsource labels samples hstruct.1 hfrozen
  have hqnew := hprior g o z hz hzB hfloor badCount hsource labels samples hstruct.1 hfrozen
  have hε : 0≤graphPaperError a d N rn z := graphPaperError_nonnegative a d N rn z hN hz.le
  have hqold : ‖g.Q z-semicircleRoot z‖≤2*scalarScale (spectralScale z) (graphPaperError a d N rn z) := by
    have hh := hsource.2.1
    change ‖g.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) (graphPaperError a d N rn z) at hh
    linarith [scalarScale_nonneg (s:=spectralScale z) hε]
  change ‖h.Q z-semicircleRoot z‖≤2*scalarScale (spectralScale z) (graphPaperError a d N rn z) at hqnew
  refine ⟨F.full,F.deleted,?_,?_⟩
  · exact hfull g o z (g.Q z) (h.Q z) hz hzB hfloor (g.Q_im_nonnegative z hz)
      (h.Q_im_nonnegative z hz) hqold hqnew hcq hsource.1.1 labels samples
  · exact hdeleted g o z (g.Q z) (h.Q z) hz hzB hfloor (g.Q_im_nonnegative z hz)
      (h.Q_im_nonnegative z hz) hqold hqnew hcq hsource.1.1 labels samples hnear

end RegularGraph
end LocalLaw
