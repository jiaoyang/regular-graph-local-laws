import SpectralConsequences.LabelledComplexDisintegration

/-! Exact graph/labels/samples disintegration on the chosen-ball kernel.
The chosen vertex set is selected by its actual support indicator. -/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance ballComplexDisintegrationDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def canonicalBallLabelledState (N d:ℕ)(o:Fin N)(ell:ℕ)(g:RegularGraph N d)
    (data:graphLabelledFiber N d (graphBallVertices g.graph o ell) g):BallLabelledSpace N d:=
  ⟨graphBallVertices g.graph o ell,canonicalGlobalLabelledState N d _ g data⟩

def ballLabelledConditionalMean (N d:ℕ)(o:Fin N)(ell:ℕ)
    (f:BallLabelledSpace N d→ℂ)(g:RegularGraph N d):ℂ:=
  globalLabelledConditionalMean N d (graphBallVertices g.graph o ell)
    (fun ω=>f ⟨graphBallVertices g.graph o ell,ω⟩) g

theorem ball_labelled_complex_disintegration (N d:ℕ)(o:Fin N)(ell:ℕ)
    (f:BallLabelledSpace N d→ℂ):
    finiteExpectation (ballLabelledWeight N d o ell) f=
      finiteExpectation (RegularGraph.weight (N:=N) (d:=d))
        (ballLabelledConditionalMean N d o ell f):=by
  have hcond (T:Set (Fin N))(g:RegularGraph N d):
      globalLabelledConditionalMean N d T
        (fun ω=>if ChosenResamplingBall o ell T (globalLabelledProject ω) then f ⟨T,ω⟩ else 0) g=
      if ChosenResamplingBall o ell T g then
        globalLabelledConditionalMean N d T (fun ω=>f ⟨T,ω⟩) g else 0:=by
    unfold globalLabelledConditionalMean
    simp only [canonicalGlobalLabelledState_project]
    by_cases h:ChosenResamplingBall o ell T g
    · simp only [h,if_true]
    · simp only [h,if_false,finiteComplexMean,Finset.sum_const_zero,smul_zero]
  calc
    _=∑T:Set (Fin N),finiteExpectation (globalLabelledWeight N d T)
        (fun ω=>if ChosenResamplingBall o ell T (globalLabelledProject ω) then f ⟨T,ω⟩ else 0):=by
      unfold finiteExpectation
      change (∑ω:(ΣT:Set (Fin N),GlobalLabelledSpace N d T),
        (ballLabelledWeight N d o ell ω:ℂ)*f ω)=_
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro ω _
      unfold ballLabelledWeight ballRestrictedWeight
      by_cases h:ChosenResamplingBall o ell T (globalLabelledProject ω)
      · simp only [h,if_true]
      · simp only [h,if_false,Complex.ofReal_zero,zero_mul,mul_zero]
    _=∑T:Set (Fin N),finiteExpectation (RegularGraph.weight (N:=N) (d:=d))
        (fun g=>if ChosenResamplingBall o ell T g then
          globalLabelledConditionalMean N d T (fun ω=>f ⟨T,ω⟩) g else 0):=by
      apply Finset.sum_congr rfl
      intro T _
      rw [global_labelled_complex_disintegration]
      congr 1
      funext g
      exact hcond T g
    _=finiteExpectation (RegularGraph.weight (N:=N) (d:=d))
        (fun g=>∑T:Set (Fin N),if ChosenResamplingBall o ell T g then
          globalLabelledConditionalMean N d T (fun ω=>f ⟨T,ω⟩) g else 0):=by
      unfold finiteExpectation
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
    _=_:=by
      congr 1
      funext g
      simp only [ChosenResamplingBall]
      rw [Finset.sum_ite_eq,if_pos (Finset.mem_univ _)]
      rfl

theorem ballLabelledConditionalMean_prod (N d:ℕ)(o:Fin N)(ell:ℕ)
    (f:BallLabelledSpace N d→ℂ)(g:RegularGraph N d):
    ballLabelledConditionalMean N d o ell f g=
      finiteComplexMean (fun labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
        BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)=>
          finiteComplexMean (fun samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)=>
            f (canonicalBallLabelledState N d o ell g (labels,samples)))):=by
  exact globalLabelledConditionalMean_prod N d _ _ g

end SpectralConsequences
#print axioms SpectralConsequences.ball_labelled_complex_disintegration
