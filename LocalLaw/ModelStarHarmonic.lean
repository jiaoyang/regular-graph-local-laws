import LocalLaw.MatchedStarReduction

/-! # Actual harmonic coefficients in the finite sampled-star reduction -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance modelStarHarmonicDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) modelStarHarmonicRangeDecidable {L W:Type} (a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V I J:Type} [Fintype V] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq I] [DecidableEq J] {d:ℕ}

theorem actual_star_reduction (g:DeficientGraph V d)(hd:3≤d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))
    (hng:∀v j,g.graph.Adj v.val (a j)→v∈Set.range e)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let A:=(g.delete (Set.range a)).extensionMatrix q z
    let U:=(g.extensionMatrix q z).submatrix (Subtype.val:((Set.range a)ᶜ:Set V)→V) a
    let W:=(g.extensionMatrix q z).submatrix a (Subtype.val:((Set.range a)ᶜ:Set V)→V)
    let D:=(g.extensionMatrix q z).submatrix a a
    let S:=finiteStarMatrix A U W D e
    IsUnit S ∧ S⁻¹=(g.extensionGreen q z).submatrix (embeddedStarEmbedding a e) (embeddedStarEmbedding a e) := by
  dsimp only
  let φ:=embeddedStarPartition a
  let A:=(g.delete (Set.range a)).extensionMatrix q z
  let U:=(g.extensionMatrix q z).submatrix (Subtype.val:((Set.range a)ᶜ:Set V)→V) a
  let W:=(g.extensionMatrix q z).submatrix a (Subtype.val:((Set.range a)ᶜ:Set V)→V)
  let D:=(g.extensionMatrix q z).submatrix a a
  have hM:Matrix.fromBlocks A U W D=(g.extensionMatrix q z).submatrix φ φ:=by
    ext x y
    cases x <;>cases y
    · exact congrFun (congrFun (g.extensionMatrix_delete (Set.range a) q z) _) _
    · rfl
    · rfl
    · rfl
  have hMu:IsUnit (Matrix.fromBlocks A U W D):=by
    rw[hM]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hUs:∀v j,v∉Set.range e→U v j=0:=by
    intro v j hv
    have hne:v.val≠a j:=fun he=>v.property ⟨j,he.symm⟩
    have hn:¬g.graph.Adj v.val (a j):=fun hh=>hv (hng v j hh)
    simp [U,extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
      Matrix.diagonal_apply,Matrix.one_apply,H,normalizedAdjacency,SimpleGraph.adjMatrix_apply,hne,hn]
  have hWs:∀j v,v∉Set.range e→W j v=0:=by
    intro j v hv
    exact ((g.extensionMatrix_isSymm q z).apply v.val (a j)).trans (hUs v j hv)
  have hh:=finite_star_reduction A U W D e
    ((g.delete (Set.range a)).extensionMatrix_isUnit hd q z hz hq) hMu
    ((g.delete (Set.range a)).extensionGreen_submatrix_isUnit hd e q z hz hq) hUs hWs
  have hmi:(Matrix.fromBlocks A U W D)⁻¹=(g.extensionGreen q z).submatrix φ φ:=by
    rw[hM]
    exact Matrix.inv_submatrix_equiv (g.extensionMatrix q z) φ φ
  rw[hmi] at hh
  exact hh

/-- Both harmonic coefficient formulas, including targets in the sampled set. -/
theorem actual_star_harmonic_entries (g:DeficientGraph V d)(hd:3≤d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))
    (hng:∀v j,g.graph.Adj v.val (a j)→v∈Set.range e)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let R:=((g.delete (Set.range a)).extensionGreen q z).submatrix e e
    let E:=embeddedStarEmbedding a e
    let G:=(g.extensionGreen q z).submatrix E E
    (∀(x:I⊕J)(u:I),(G.submatrix id Sum.inl*R⁻¹) x u=
      (if x=.inl u then 1 else 0)-∑b:J,G x (.inr b)*g.extensionMatrix q z (a b) (e u).val) ∧
    (∀(u:I)(y:I⊕J),(R⁻¹*G.submatrix Sum.inl id) u y=
      (if (.inl u:I⊕J)=y then 1 else 0)-∑b:J,g.extensionMatrix q z (e u).val (a b)*G (.inr b) y) := by
  dsimp only
  let A:=(g.delete (Set.range a)).extensionMatrix q z
  let U:=(g.extensionMatrix q z).submatrix (Subtype.val:((Set.range a)ᶜ:Set V)→V) a
  let W:=(g.extensionMatrix q z).submatrix a (Subtype.val:((Set.range a)ᶜ:Set V)→V)
  let D:=(g.extensionMatrix q z).submatrix a a
  let S:=finiteStarMatrix A U W D e
  have hh:=g.actual_star_reduction hd a e hng q z hz hq
  have h11:S.toBlocks₁₁=(A⁻¹.submatrix e e)⁻¹:=rfl
  constructor
  · intro x u
    have hf:=left_core_lift_entry S hh.1 (A⁻¹.submatrix e e) h11 x u
    rw[hh.2] at hf
    exact hf
  · intro u y
    have hf:=right_core_lift_entry S hh.1 (A⁻¹.submatrix e e) h11 u y
    rw[hh.2] at hf
    exact hf

end DeficientGraph
end LocalLaw
