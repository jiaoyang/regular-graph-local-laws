import LocalLaw.ActualOutsideColumnGood

/-! Actual outside strong-row forcing from genuine finite sampling events. -/
noncomputable section
namespace LocalLaw
local instance actualOutsideRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
theorem eventually_actual_outside_row_of_counts (a b d J : ℕ) (c β B C1 Kbad Knear : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq)
    (hKbad : 0≤Kbad) (hKnear : 0≤Knear) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let R:=logarithmicRadius (c/4) d N
      let r:=effectiveModelRadius a d N β
      let selector:=R/4
      let s:=g.admissibleState T labels samples
      let gnew:=g.labelledResampledGraph T labels samples selector
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let φ:=correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ selector (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T selector samples).card≤J →
      ∀ good : Finset ι,
      (∀ i∈good,s.Eligible selector i ∧ labels i∈g.sourceCorrelationGoodLabels T z φ selector samples) →
      (((Finset.univ\good).card:ℕ):ℝ)≤Kbad*L^2 →
      (∀ x : (Tᶜ : Set (Fin N)),(g.correlatedSampleIndices T z φ selector x samples).card≤Nat.ceil L) →
      (∀ x : (Tᶜ : Set (Fin N)),
        ((tripleNearIndices (s.fullResample selector).graph T selector (s.fullResample selector).samples x).card:ℝ)≤Knear*L) →
      ∀ y∉T, ‖gnew.G z o y-gnew.P r z (gnew.Q z) o y‖≤
        sourceOutsideRowBaseConstant d J β C1 (sourceOutsideColumnErrorConstant d B C1 Kbad Knear)*ε/L+
          sourceOutsideRowFeedbackConstant d β B*L^2*gnew.sourceFeedback z := by
  let Eout:=sourceOutsideColumnErrorConstant d B C1 Kbad Knear
  have hCextra:=finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤guardedGreenEntryCap d := by unfold guardedGreenEntryCap commonGreenEntryCap; linarith
  have hP : 0≤sourceGreenPivotCap d B := by unfold sourceGreenPivotCap; have hh:=finiteReferenceConstant_ge_one d hd; positivity
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  have hD:=sourceEndpointErrorConstant_nonnegative d C1 hC10
  have hEout : 0≤Eout := by
    dsimp only [Eout,sourceOutsideColumnErrorConstant,sourceGoodExternalColumnConstant]
    have hw : 0≤endpointSurgeryCouplingCap d := by unfold endpointSurgeryCouplingCap; positivity
    positivity
  filter_upwards [eventually_sourceOutsideColumnGood_of_counts a b d c β B C1 Kbad Knear Cq
    ha hb hd hc hβ hβc hB hC1 hCdel hCq hKbad hKnear,
    eventually_source_outside_row_from_column a b d J c β B C1 Eout
      ha hb hd hc hβ hβc hC1 hB hEout] with N hcolumn hrow
  intro g o z hz hzB hfloor badCount hplus ι _ labels samples
  dsimp only
  intro target hisolation hrejected good hgood hbad hcorr hnewNear
  have hcol:=hcolumn g o z hz hzB hfloor badCount hplus labels samples target good hgood hbad hcorr hnewNear
  exact hrow g o z hz hzB hfloor Cq badCount hplus labels samples target hisolation hrejected hcol

end RegularGraph
end LocalLaw
