import LocalLaw.ActualOutsideColumnLabels
import LocalLaw.SourceOutsideRowFromColumn

/-! Actual named outside-column good event from literal finite counts. -/
noncomputable section
namespace LocalLaw
local instance actualOutsideColumnGoodDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
theorem eventually_sourceOutsideColumnGood_of_counts (a b d : ℕ) (c β B C1 Kbad Knear : ℝ) (Cq : ℕ)
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
      ∀ good : Finset ι,
      (∀ i∈good,s.Eligible selector i ∧ labels i∈g.sourceCorrelationGoodLabels T z φ selector samples) →
      (((Finset.univ\good).card:ℕ):ℝ)≤Kbad*L^2 →
      (∀ x : (Tᶜ : Set (Fin N)),(g.correlatedSampleIndices T z φ selector x samples).card≤Nat.ceil L) →
      (∀ x : (Tᶜ : Set (Fin N)),
        ((tripleNearIndices (s.fullResample selector).graph T selector (s.fullResample selector).samples x).card:ℝ)≤Knear*L) →
      g.SourceOutsideColumnGood a c β (sourceOutsideColumnErrorConstant d B C1 Kbad Knear) o z labels samples := by
  filter_upwards [eventually_actual_outside_column_labels a b d c β B C1 Kbad Knear Cq
    ha hb hd hc hβ hβc hB hC1 hCdel hCq hKbad hKnear] with N hlabels
  intro g o z hz hzB hfloor badCount hplus ι _ labels samples
  dsimp only
  intro target good hgood hbad hcorr hnewNear
  have H:=hlabels g o z hz hzB hfloor badCount hplus labels samples target good hgood hbad hcorr hnewNear
  dsimp only [SourceOutsideColumnGood]
  intro y hy
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let gnew:=g.labelledResampledGraph T labels samples selector
  let K:=g.singleTargetOutsideVertices T labels samples selector r y
  let hK:=g.singleTargetOutside_boundary_capture T labels samples selector r y
  let j:=g.singleTargetOutsideTargetVertex T labels samples selector r y hy
  let F : BoundaryOrientedEdge gnew.graph T→ℝ := fun α =>
    ‖(gnew.deficient.delete T).G z (boundaryOutsideVertex gnew.graph T α) j.val-
      ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
        (gnew.filledBoundaryVertex T K hK α) j‖
  have hh:=H y hy
  have hh' : (∑i:ι,F ((s.fullResample selector).boundary i))≤
      sourceOutsideColumnErrorConstant d B C1 Kbad Knear*Real.log (N:ℝ)^5*
        graphPaperError a d N (logarithmicRadius β d N) z := by
    exact hh.trans_eq (by unfold sourcePrime inflatedPrime; ring)
  rw [(s.fullResample selector).boundary.sum_comp F] at hh'
  exact hh'

end RegularGraph
end LocalLaw
