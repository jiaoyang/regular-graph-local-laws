import LocalLaw.SourceCavityDiagonalForcing
import LocalLaw.SourceCavityOffdiag
import LocalLaw.SourceCavityMinorRemainder
import LocalLaw.CavityMinorRowSplit
import LocalLaw.CenteredSmallBallExcess

/-! # Actual neighbor cavity estimates on the target tree event

The target tree hypothesis is pulled backwards through the involution.
The resulting smaller source tree contains every reference neighborhood.
The complete physical estimate is assembled from proved diagonal forcing,
sparse off-diagonal forcing, and the nonlinear minor remainder.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCavityEstimateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceCavityEstimateConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  sourceCavityDiagonalConstant d J β C1+sourceCavityOffdiagConstant d J C1+1

namespace RegularGraph

theorem eventually_source_neighbor_cavity_estimate (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∀ badCount : ℕ, badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let Rstruct := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) Rstruct (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (Rstruct/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (Rstruct/4) samples).card≤J →
      g.SourceCavityWeightGood a c β C1 o z samples →
      (graphBall gnew.graph o Rstruct).IsTree → ∀ j : g.graph.neighborSet o,
      ‖green (deletedMatrix gnew.H j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩-
        cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖≤
        sourceCavityEstimateConstant d J β C1*(ε/L^4) := by
  filter_upwards [eventually_source_cavity_diagonal_forcing a b d J c β γ B C1 Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_source_cavity_offdiag a b d J c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_cavity_minor_remainder a b d J c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hdiag hoff hrem hrad hmargin hnum
  intro g o z hz hzB hfloor badCount hbadCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let Rstruct := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
  let D := g.sourceTruncatedBoundaryDefect T labels samples (Rstruct/4) (g.Q z) z
  let Dcanonical := g.sourceBoundaryDefect T labels samples (Rstruct/4) r (g.Q z) z
  intro htarget hisolation hrejected hconcentration hTree j
  have num := hnum z hz hfloor
  have hε : 0≤ε := num.error_nonnegative
  have hL : 1≤L := num.log_one
  have hroom : ell+r+1≤Rstruct/8 := by
    have hh := hrad.2.2.2 z
    change r+ell+1≤Rstruct/8 at hh
    omega
  have hTreeSmall : (graphBall g.graph o (Rstruct/8)).IsTree :=
    s.fullResample_tree_implies_source_eighth_tree Rstruct o ell rfl (by omega) hTree
  have hTreeEll := graphBall_tree_mono g.graph o (show ell≤Rstruct/8 by omega) hTreeSmall
  have hTreeSucc := graphBall_tree_mono g.graph o (show ell+1≤Rstruct/8 by omega) hTreeSmall
  have hdiag := hdiag g o z hz hzB hfloor badCount hbadCount hplus hTreeSmall labels samples
    htarget hisolation hrejected hconcentration j
  obtain ⟨hell,hoff⟩ := hoff g o z hz hfloor hzB Cq badCount hplus hTreeEll labels samples hisolation hrejected
  obtain ⟨hellrem,hrem⟩ := hrem g o z hz hfloor hzB Cq badCount hplus hTreeSmall labels samples hisolation hrejected
  have hell' : 2≤ell := hell
  let jT := g.cavityNeighborInBall o ell hell' j
  have hjo : g.graph.Adj jT.val o := j.property.symm
  let P := ((g.deficient.restrict T).deleteVertex jT).extensionGreen (g.Q z) z
  let R := gnew.retainedPhysicalMinor T jT z
  let root := g.truncatedCavityRoot o ell jT hjo
  let l := fun α => g.truncatedCavityBoundaryInner o ell hell jT hjo (labels α)
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  have hsplit := g.cavity_minor_diagonal_norm_split hd o ell hell jT hjo labels samples
    (Rstruct/4) (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hdiag' : ‖∑ α,g.truncatedCavityWeight o ell hell jT hjo (g.Q z) z (labels α)*D α α‖≤
      sourceCavityDiagonalConstant d J β C1*(ε/L^4) := by
    change ‖∑ α,g.cavityMinorWeights o ell (g.Q z) z j (labels α)*D α α‖≤_ at hdiag
    simpa only [cavityMinorWeights,dif_pos hell'] using hdiag
  have hsep : 2*r+2≤Rstruct/4 := by dsimp only [r,Rstruct]; omega
  have hr : r+2≤Rstruct/4 := by dsimp only [r,Rstruct]; omega
  have hdecomp := g.sourceTruncatedBoundaryDefect_tree_decomposition hd o ell (Rstruct/4) r (Rstruct/8)
    hsep hr hroom hTreeSmall labels samples (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hoff' : ‖∑ α,∑ β,if α=β then 0 else P root (l α)*D α β*P (l β) root‖≤
      sourceCavityOffdiagConstant d J C1*(ε/L^4) := by
    dsimp only [D]
    rw [hdecomp,offdiag_add_scalar_identity]
    exact hoff jT hjo
  have hrem' : ‖coeff*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) root)‖≤ε/(2*L^4) :=
    hrem jT hjo root
  have hestimate : ‖R root root-P root root‖≤sourceCavityEstimateConstant d J β C1*(ε/L^4) := by
    apply hsplit.trans
    apply (add_le_add (add_le_add hdiag' hoff') hrem').trans
    have hhalf : ε/(2*L^4)≤ε/L^4 := div_le_div_of_nonneg_left hε
      (pow_pos (by linarith : 0<L) 4) (by nlinarith [pow_nonneg (show 0≤L by linarith) 4])
    dsimp only [sourceCavityEstimateConstant]
    nlinarith only [hhalf]
  have hY := g.truncated_neighbor_cavity_diagonal hd o ell jT hjo hTreeSucc (g.Q z) z hz
    (g.Q_im_nonnegative z hz)
  have hY' : P root root=cavityIterate z (g.Q z) (ell+1) := hY
  have hdepth : ell+1=actualCavityDepth a d N z := by dsimp only [ell] at *; omega
  have hphysical : R root root=green (deletedMatrix gnew.H j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩ := by
    change (gnew.deficient.deleteVertex j.val).G z _ _= _
    rw [gnew.deficient.deleteVertex_G]
    rfl
  change ‖_ - _‖≤_ at hestimate
  rw [hphysical,hY',hdepth] at hestimate
  exact hestimate

end RegularGraph
end LocalLaw
