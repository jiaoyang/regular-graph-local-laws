import SpectralConsequences.BallComplexDisintegration
import LocalLaw.SourceResamplingStructural

/-! The canonical conditional state uses precisely the literal graph
resampling appearing in the actual local drift theorems. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem canonicalBallLabelledState_project (N d:ℕ)(o:Fin N)(ell:ℕ)(g:RegularGraph N d)
    (data:graphLabelledFiber N d (graphBallVertices g.graph o ell) g):
    ballLabelledProject (canonicalBallLabelledState N d o ell g data)=g:=by rfl

theorem canonicalBallLabelledState_chosen (N d:ℕ)(o:Fin N)(ell:ℕ)(g:RegularGraph N d)
    (data:graphLabelledFiber N d (graphBallVertices g.graph o ell) g):
    ChosenResamplingBall o ell (canonicalBallLabelledState N d o ell g data).1
      (ballLabelledProject (canonicalBallLabelledState N d o ell g data)):=by rfl

theorem canonicalBallLabelledState_resample_project (N d:ℕ)(o:Fin N)(ell selector:ℕ)
    (g:RegularGraph N d)
    (labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
      BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)):
    ballLabelledProject (ballLabelledResample N d selector
      (canonicalBallLabelledState N d o ell g (labels,samples)))=
      g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples selector:=by
  apply Subtype.ext
  rfl

theorem canonicalBallLabelledState_permutation_project (N d:ℕ)(o:Fin N)(ell selector:ℕ)
    (g:RegularGraph N d)
    (labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
      BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)):
    ballLabelledProject (ballLabelledPermutation N d selector
      (canonicalBallLabelledState N d o ell g (labels,samples)))=
      g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples selector:=by
  exact canonicalBallLabelledState_resample_project N d o ell selector g labels samples

end SpectralConsequences
