import LocalLaw.CapturedStarReduction

/-! # Exact finite-star lifting for two different actual graph models

The two core graphs and their deficits may differ. Only their captured sampled
precision rows agree. Both core Green blocks and all matrix units are derived
from the actual finite models in the upper half plane.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance matchedStarDecidable (p:Prop):Decidable p:=Classical.propDecidable p

variable {V I J : Type}
local instance (priority := 2000) matchedStarRangeDecidable (a:J↪V) :
    DecidablePred (fun v:V=>v∈Set.range a) := fun _=>Classical.propDecidable _

def embeddedStarPartition (a:J↪V) : (((Set.range a)ᶜ:Set V)⊕J)≃V :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective (a:J→V) a.injective)).trans
    (capturedStarGlobalPartition (Set.range a))

def embeddedStarEmbedding (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V)) : I⊕J↪V :=
  (Function.Embedding.sumMap e (Function.Embedding.refl J)).trans (embeddedStarPartition a).toEmbedding

namespace DeficientGraph
variable {W:Type} [Fintype V] [Fintype W] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq W] [DecidableEq I] [DecidableEq J] {d:ℕ}

theorem matched_star_inverse_difference (g:DeficientGraph V d)(h:DeficientGraph W d)(hd:3≤d)
    (a:J↪V)(b:J↪W)(e:I↪((Set.range a)ᶜ:Set V))(f:I↪((Set.range b)ᶜ:Set W))
    (hng:∀v j,g.graph.Adj v.val (a j)→v∈Set.range e)
    (hnh:∀w j,h.graph.Adj w.val (b j)→w∈Set.range f)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hD:∀i j,g.extensionMatrix q z (a i) (a j)=h.extensionMatrix q z (b i) (b j))
    (hU:∀i j,g.extensionMatrix q z (e i).val (a j)=h.extensionMatrix q z (f i).val (b j)) :
    let E:=embeddedStarEmbedding a e
    let F:=embeddedStarEmbedding b f
    let R:=((g.delete (Set.range a)).extensionGreen q z).submatrix e e
    let P:=((h.delete (Set.range b)).extensionGreen q z).submatrix f f
    let GM:=(g.extensionGreen q z).submatrix E E
    let GN:=(h.extensionGreen q z).submatrix F F
    IsUnit R ∧ IsUnit P ∧
      GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let φ:=embeddedStarPartition a
  let ψ:=embeddedStarPartition b
  let A:=(g.delete (Set.range a)).extensionMatrix q z
  let B:=(h.delete (Set.range b)).extensionMatrix q z
  let U:=(g.extensionMatrix q z).submatrix (Subtype.val:((Set.range a)ᶜ:Set V)→V) a
  let Vt:=(g.extensionMatrix q z).submatrix a (Subtype.val:((Set.range a)ᶜ:Set V)→V)
  let U':=(h.extensionMatrix q z).submatrix (Subtype.val:((Set.range b)ᶜ:Set W)→W) b
  let Vt':=(h.extensionMatrix q z).submatrix b (Subtype.val:((Set.range b)ᶜ:Set W)→W)
  let D:=(g.extensionMatrix q z).submatrix a a
  have hM:Matrix.fromBlocks A U Vt D=(g.extensionMatrix q z).submatrix φ φ := by
    ext x y
    cases x <;>cases y
    · exact congrFun (congrFun (g.extensionMatrix_delete (Set.range a) q z) _) _
    · rfl
    · rfl
    · rfl
  have hN:Matrix.fromBlocks B U' Vt' D=(h.extensionMatrix q z).submatrix ψ ψ := by
    ext x y
    cases x <;>cases y
    · exact congrFun (congrFun (h.extensionMatrix_delete (Set.range b) q z) _) _
    · rfl
    · rfl
    · exact hD _ _
  have hAu: IsUnit A:=(g.delete (Set.range a)).extensionMatrix_isUnit hd q z hz hq
  have hBu: IsUnit B:=(h.delete (Set.range b)).extensionMatrix_isUnit hd q z hz hq
  have hMu:IsUnit (Matrix.fromBlocks A U Vt D):=by
    rw [hM]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hNu:IsUnit (Matrix.fromBlocks B U' Vt' D):=by
    rw [hN]
    exact (Matrix.isUnit_submatrix_equiv ψ ψ).mpr (h.extensionMatrix_isUnit hd q z hz hq)
  have hR:=(g.delete (Set.range a)).extensionGreen_submatrix_isUnit hd e q z hz hq
  have hP:=(h.delete (Set.range b)).extensionGreen_submatrix_isUnit hd f q z hz hq
  have hUs:∀v j,v∉Set.range e→U v j=0:=by
    intro v j hv
    have hne:v.val≠a j:=fun he=>v.property ⟨j,he.symm⟩
    have hn:¬g.graph.Adj v.val (a j):=fun hh=>hv (hng v j hh)
    simp [U,extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
      Matrix.diagonal_apply,Matrix.one_apply,H,normalizedAdjacency,SimpleGraph.adjMatrix_apply,hne,hn]
  have hVs:∀j v,v∉Set.range e→Vt j v=0:=by
    intro j v hv
    exact ((g.extensionMatrix_isSymm q z).apply v.val (a j)).trans (hUs v j hv)
  have hUs':∀v j,v∉Set.range f→U' v j=0:=by
    intro v j hv
    have hne:v.val≠b j:=fun he=>v.property ⟨j,he.symm⟩
    have hn:¬h.graph.Adj v.val (b j):=fun hh=>hv (hnh v j hh)
    simp [U',extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
      Matrix.diagonal_apply,Matrix.one_apply,H,normalizedAdjacency,SimpleGraph.adjMatrix_apply,hne,hn]
  have hVs':∀j v,v∉Set.range f→Vt' j v=0:=by
    intro j v hv
    exact ((h.extensionMatrix_isSymm q z).apply v.val (b j)).trans (hUs' v j hv)
  have hleft:U.submatrix e id=U'.submatrix f id:=by ext i j;exact hU i j
  have hright:Vt.submatrix id e=Vt'.submatrix id f:=by
    ext i j
    exact ((g.extensionMatrix_isSymm q z).apply (a i) (e j).val).symm.trans
      ((hU j i).trans ((h.extensionMatrix_isSymm q z).apply (b i) (f j).val))
  have hh:=finite_star_inverse_difference A B U Vt U' Vt' D e f hAu hBu hMu hNu hR hP
    hUs hVs hUs' hVs' hleft hright
  have hmi:(Matrix.fromBlocks A U Vt D)⁻¹=(g.extensionGreen q z).submatrix φ φ:=by
    rw[hM]
    exact Matrix.inv_submatrix_equiv (g.extensionMatrix q z) φ φ
  have hni:(Matrix.fromBlocks B U' Vt' D)⁻¹=(h.extensionGreen q z).submatrix ψ ψ:=by
    rw[hN]
    exact Matrix.inv_submatrix_equiv (h.extensionMatrix q z) ψ ψ
  dsimp only at hh
  rw[hmi,hni] at hh
  exact ⟨hR,hP,hh⟩

end DeficientGraph
end LocalLaw
