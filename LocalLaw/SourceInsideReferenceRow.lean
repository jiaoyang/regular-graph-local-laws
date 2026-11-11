import LocalLaw.SourceRetainedRowSplit
import LocalLaw.SourceRetainedDiagonalForcing
import LocalLaw.SourceRetainedOffdiag
import LocalLaw.SourceRetainedRemainder

/-!
# Actual inside-row improvement against the fixed finite reference

All three source Schur terms are estimated from the actual source event and
proved sampling good events. No row, matrix-error, or nonlinear estimate is
left as an analytic hypothesis.
-/

noncomputable section
namespace LocalLaw
local instance sourceInsideReferenceRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceInsideReferenceBaseConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  sourceRetainedDiagonalConstant d J β C1 + sourceRetainedOffdiagConstant d J C1 + 1

namespace RegularGraph

theorem eventually_source_inside_reference_row (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∀ badCount : ℕ, badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      let P := g.sourceRetainedReference T r (g.Q z) z
      let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      g.SourceRetainedWeightGood a c β C1 o z samples → ∀ y : T,
      ‖gnew.G z o y.val-P root y‖≤
        sourceInsideReferenceBaseConstant d J β C1*(ε/L^2)+
          sourceRetainedDiagonalFeedbackConstant d β B*L^2*gnew.sourceFeedback z := by
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  have hdiag0 : 0≤sourceRetainedDiagonalConstant d J β C1 := by
    dsimp only [sourceRetainedDiagonalConstant,actualFixedWeightLeadingConstant,
      sourceRetainedWeightL1Constant,sourceRetainedWeightNoiseConstant,sourceRetainedWeightMaxConstant,
      sourceEndpointErrorConstant,DeficientGraph.singletonObservationConstant]
    positivity
  filter_upwards [eventually_source_retained_diagonal_forcing a b d J c β γ B C1 Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_source_retained_offdiag a b d J c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_retained_nonlinear_remainder a b d J c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hdiag hoff hrem hmargin hnum
  intro g o z hz hzB hfloor badCount hbad hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  intro htarget hisolation hrejected hweights y
  have hdg := hdiag g o z hz hzB hfloor badCount hbad hplus labels samples htarget hisolation hrejected hweights y
  have hof := hoff g o z hz hfloor hzB Cq badCount hplus labels samples hisolation hrejected y
  have hrm := hrem g o z hz hfloor hzB Cq badCount hplus labels samples hisolation hrejected y
  have hsep : 2*r+2≤R/4 := by dsimp only [r,R]; omega
  have hrs : r+2≤R/4 := by dsimp only [r,R]; omega
  have hsplit := g.sourceRetained_row_norm_split hd o ell (R/4) r hsep hrs labels samples
    (g.Q z) z hz (g.Q_im_nonnegative z hz) y
  have num := hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hε : 0≤ε := num.error_nonnegative
  apply hsplit.trans
  apply (add_le_add (add_le_add hdg hof) hrm).trans
  have hsmall : sourceRetainedDiagonalConstant d J β C1*(ε/L^4) ≤
      sourceRetainedDiagonalConstant d J β C1*(ε/L^2) := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left hε (pow_pos hLp 2) (pow_le_pow_right₀ hL (show 2≤4 by omega))) hdiag0
  have hhalf : ε/(2*L^2)≤ε/L^2 := by
    have hh : ε/(2*L^2)=(ε/L^2)/2 := by ring
    rw [hh]
    exact div_le_self (div_nonneg hε (pow_nonneg hLp.le 2)) (by norm_num : (1:ℝ)≤2)
  dsimp only [sourceInsideReferenceBaseConstant]
  nlinarith only [hsmall,hhalf]

end RegularGraph
end LocalLaw
