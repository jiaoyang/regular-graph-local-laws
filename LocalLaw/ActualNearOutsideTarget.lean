import LocalLaw.SourceOmegaPlusTransferEffective
import LocalLaw.SourceEndpointApproximation
import LocalLaw.SourceObservationParameters

/-! Direct target-boundary outside comparison on an actual finite restriction. -/
noncomputable section
namespace LocalLaw
local instance actualNearOutsideTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_target_near_outside_comparison (a b d : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let r:=effectiveModelRadius a d N β
      ∀ (S : Set (Tᶜ : Set (Fin N))), ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget →
      ∀ R : ℕ, (∀ u v,((g.deficient.delete T).restrict S).graph.dist u v≤R) →
      (R:ℝ)+1≤sourceObservationLogCap d β*Real.log (N:ℝ) →
      ∀ {I : Type} (e : I↪S), (∀ i,graphBallVertices (outsideGraph g.graph T) (e i).val r⊆S) →
      ∀ i j, ‖(g.deficient.delete T).G z (e i).val (e j).val-
        ((g.deficient.delete T).restrict S).extensionGreen (g.Q z) z (e i) (e j)‖≤
          2*C1*g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq] with N hnum hplus
  intro g o z hz hzB hfloor badCount target
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let r:=effectiveModelRadius a d N β
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let L:=Real.log (N:ℝ)
  intro S hbudget R hdiam hRlog I e hcapture i j
  have hp:=hplus g o z badCount hz hzB hfloor target
  have hpair : ∀ u v, ‖(g.deficient.delete T).G z (e u).val (e v).val-
      (g.deficient.delete T).P r z (g.Q z) (e u).val (e v).val‖≤C1*L^3*ε := by
    intro u v
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hp.deleted (e u).val (e v).val
  have hh:=(g.deficient.delete T).source_endpoint_restriction_approximation hd S e r R z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B C1 ε L (sourceObservationLogCap d β) hzB (hnum z hz hfloor)
    hbudget hdiam hRlog hcapture hp.cavity hpair i j
  exact hh.trans_eq (by unfold sourcePrime inflatedPrime; ring)

end RegularGraph
end LocalLaw
