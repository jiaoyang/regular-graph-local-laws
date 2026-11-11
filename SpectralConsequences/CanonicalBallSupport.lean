import SpectralConsequences.CanonicalBallResampling

/-! The canonical conditional parametrization covers every state carrying
nonzero actual chosen-ball weight. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance canonicalBallSupportDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem globalLabelledState_canonical (N d:ℕ)(T:Set (Fin N))(ω:GlobalLabelledSpace N d T):
    ∃g:RegularGraph N d,∃data:graphLabelledFiber N d T g,
      ω=canonicalGlobalLabelledState N d T g data:=by
  let s:Σg:RegularGraph N d,graphLabelledFiber N d T g:=globalGraphFiberEquiv N d T ω
  refine ⟨s.1,s.2,?_⟩
  exact ((globalGraphFiberEquiv N d T).symm_apply_apply ω).symm

private theorem canonicalBall_of_chosen (N d:ℕ)(o:Fin N)(ell:ℕ)(T:Set (Fin N))
    (g:RegularGraph N d)(data:graphLabelledFiber N d T g)
    (hT:graphBallVertices g.graph o ell=T):
    ∃chosen:graphLabelledFiber N d (graphBallVertices g.graph o ell) g,
      (⟨T,canonicalGlobalLabelledState N d T g data⟩:BallLabelledSpace N d)=
        canonicalBallLabelledState N d o ell g chosen:=by
  subst T
  exact ⟨data,rfl⟩

theorem canonicalBallLabelledState_support_surjective (N d:ℕ)(o:Fin N)(ell:ℕ)
    (ω:BallLabelledSpace N d)(hw:ballLabelledWeight N d o ell ω≠0):
    ∃g:RegularGraph N d,∃data:graphLabelledFiber N d (graphBallVertices g.graph o ell) g,
      ω=canonicalBallLabelledState N d o ell g data:=by
  obtain ⟨T,ξ⟩:=ω
  have hBall:ChosenResamplingBall o ell T (globalLabelledProject ξ):=by
    by_contra hnot
    apply hw
    simp only [ballLabelledWeight,ballRestrictedWeight,hnot,if_false]
  obtain ⟨g,data,hξ⟩:=globalLabelledState_canonical N d T ξ
  have hT:graphBallVertices g.graph o ell=T:=by
    rw [hξ,canonicalGlobalLabelledState_project] at hBall
    exact hBall
  obtain ⟨chosen,hchosen⟩:=canonicalBall_of_chosen N d o ell T g data hT
  exact ⟨g,chosen,(congrArg (fun x:GlobalLabelledSpace N d T=>(⟨T,x⟩:BallLabelledSpace N d)) hξ).trans hchosen⟩

theorem canonicalBallLabelledState_support_fiber (N d:ℕ)(o:Fin N)(ell:ℕ)
    (ω:BallLabelledSpace N d)(hw:ballLabelledWeight N d o ell ω≠0):
    ∃data:graphLabelledFiber N d (graphBallVertices (ballLabelledProject ω).graph o ell)
      (ballLabelledProject ω),ω=canonicalBallLabelledState N d o ell (ballLabelledProject ω) data:=by
  obtain ⟨g,data,hω⟩:=canonicalBallLabelledState_support_surjective N d o ell ω hw
  have hg:g=ballLabelledProject ω:=by rw [hω];rfl
  subst g
  exact ⟨data,hω⟩

end SpectralConsequences
