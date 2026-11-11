import LocalLaw.StrongSourceCertificate
import LocalLaw.SourceOutsideCompleteColumn
import LocalLaw.SourceFinalAnalyticKernel

/-! # Complete second-stage strong certificate from proved sampling events -/

noncomputable section
namespace LocalLaw
local instance completeStrongCertificateDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceSecondColumnConstant (d Cq qReject qGeo:ℕ)(B C1:ℝ):ℝ:=
  sourceOutsideCompleteColumnConstant d (sourceRejectionConstant Cq qReject) Cq qGeo B C1

def sourceSecondU (d Cq qReject qGeo:ℕ)(β B C1:ℝ):ℝ:=
  sourceStrongRowU d (sourceRejectionConstant Cq qReject) β C1 (sourceSecondColumnConstant d Cq qReject qGeo B C1)

def sourceSecondV (d:ℕ)(β B:ℝ):ℝ:=sourceStrongRowV d β B

def sourceSecondM (d Cq qReject:ℕ)(β C1:ℝ):ℝ:=sourceStrongResidualM d (sourceRejectionConstant Cq qReject) β C1

namespace RegularGraph

theorem eventually_source_complete_strong_certificate (a b d qReject qGeo Cq:ℕ)(c β γ B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hgap:γ+β<1)(hB:0≤B)(hC1:1≤C1)
    (hCdel:sourceDeletionConstant d β B≤C1)(hCq:finiteOmega d≤Cq):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let T:=graphBallVertices g.graph o ell
      let r:=effectiveModelRadius a d N β
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let L:=Real.log (N:ℝ)
      let φ:=correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew:=g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      g.SourceAnalyticGood a qReject Cq c β C1 o z samples →
      SourceFullGeometricGood g.graph o ell (R/2) Cq (qGeo-1) (qGeo-1) (2*qGeo*(2*(qGeo-1)+1)) (qGeo-1) samples →
      (∀x:(Tᶜ:Set (Fin N)),(g.correlatedSampleIndices T z φ (R/4) x samples).card≤Nat.ceil L) →
      ∀D:StrongClosureBudget z (semicircleRoot z) (spectralScale z) ε,
      D.depth=actualCavityDepth a d N z → D.L=L → D.U=sourceSecondU d Cq qReject qGeo β B C1 →
      D.V=sourceSecondV d β B → D.residualConstant=sourceSecondM d Cq qReject β C1 →
      D.rowBase=D.U*ε/D.L → D.rowFeedback=D.V*D.L^2 → D.cavityError=D.residualConstant*ε/(2*D.L^4) →
      StrongCavityRowCertificate (gnew.Q z) (semicircleRoot z) z (spectralScale z) ε D
        (gnew.G z) (fun w=>gnew.P r z w) (cavityAtVertex gnew.graph d z) (nonTreeCenters gnew.graph R) o:=by
  let J:=sourceRejectionConstant Cq qReject
  let E:=sourceSecondColumnConstant d Cq qReject qGeo B C1
  have hE:0≤E:=sourceOutsideCompleteColumnConstant_nonnegative d J Cq qGeo B C1 hd hB (by linarith)
  filter_upwards [eventually_source_strong_certificate_of_column a b d qReject Cq c β γ B C1 E
    ha hb hd hc hβ hβc hγ hgap hB hC1 hE hCdel hCq,
    eventually_sourceOutsideColumnGood_complete a b d J qGeo c β B C1 Cq
    ha hb hd hc hβ hβc hB hC1 hCdel hCq] with N hcert hcolumn
  intro g o z hz hzB hfloor badCount hbad hplus ι _ labels samples
  dsimp only
  intro htarget hgood hgeometry hcorr D hdepth hlog hU hV hM hbase hfeedback hcavity
  have hc:=hcolumn g o z hz hzB hfloor badCount hplus labels samples htarget hgood.1 hgood.2.1 hcorr hgeometry
  exact hcert g o z hz hzB hfloor badCount hbad hplus labels samples htarget hgood hc D
    hdepth hlog hU hV hM hbase hfeedback hcavity

end RegularGraph
end LocalLaw
