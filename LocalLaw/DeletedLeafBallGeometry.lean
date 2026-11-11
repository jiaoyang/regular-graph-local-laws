import LocalLaw.DeletedLeafOriginalMap
import LocalLaw.ImmersionForest

/-! # Literal leaf balls map to the original removed-vertex balls

The map preserves all edges and is injective on every neighbor set, despite
the distinct global copies of a removed vertex. Zero inherited deficit on
the original ball gives zero deficit throughout the actual leaf ball.
-/

noncomputable section
namespace LocalLaw
local instance deletedLeafBallGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}[Fintype V]

def deletedLeafBallOriginalHom (G:SimpleGraph V)(T:Set V)(l:DeletedLeafIndex G T)(r:ℕ) :
    graphBall (multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)) (.inr l) r→g
      graphBall G l.2.val.val r where
  toFun v:=⟨deletedLeafOriginalVertex G T v.val,
    (graphHom_edist_le (deletedLeafOriginalHom G T) (.inr l) v.val).trans v.property⟩
  map_rel':=fun h=>(deletedLeafOriginalHom G T).map_rel h

omit [Fintype V] in
theorem deletedLeafBallOriginal_locally_injective (G:SimpleGraph V)(T:Set V)
    (l:DeletedLeafIndex G T)(r:ℕ)
    (x a b:graphBallVertices (multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)) (.inr l) r)
    (ha:(graphBall (multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)) (.inr l) r).Adj x a)
    (hb:(graphBall (multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)) (.inr l) r).Adj x b)
    (he:deletedLeafBallOriginalHom G T l r a=deletedLeafBallOriginalHom G T l r b) : a=b := by
  apply Subtype.ext
  exact deletedLeafOriginal_locally_injective G T x.val a.val b.val ha hb (congrArg Subtype.val he)

omit [Fintype V] in
theorem deletedLeafBallOriginal_injective (G:SimpleGraph V)(T:Set V)
    (l:DeletedLeafIndex G T)(r:ℕ)(htree:(graphBall G l.2.val.val r).IsTree) :
    Function.Injective (deletedLeafBallOriginalHom G T l r) := by
  let F:=deletedLeafBallOriginalHom G T l r
  have hloc:GraphHomLocallyInjective F:=deletedLeafBallOriginal_locally_injective G T l r
  intro a b he
  obtain ⟨p,hp⟩:=(graphBall_connected
    (multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)) (.inr l) r).exists_isPath a b
  have hm:=map_path_into_forest F hloc htree.IsAcyclic p hp
  cases p with
  | nil=>rfl
  | @cons a c b h p=>
    change ((p.map F).cons (F.map_rel h)).IsPath at hm
    have hn:=((SimpleGraph.Walk.cons_isPath_iff _ _).mp hm).2
    apply False.elim
    apply hn
    rw [he]
    exact (p.map F).end_mem_support

omit [Fintype V] in
theorem deletedLeafGraph_leaf_separated (G:SimpleGraph V)(T:Set V)(selector:ℕ)
    (hsep:∀b c:T,b≠c → (selector:ℕ∞)<G.edist b.val c.val)
    (htree:∀b:T,(graphBall G b.val selector).IsTree)
    (l m:DeletedLeafIndex G T)(hne:l≠m) :
    (selector:ℕ∞)<(multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)).edist (.inr l) (.inr m) := by
  let H:=multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)
  by_cases hb:l.2.val=m.2.val
  · apply lt_of_not_ge
    intro hnear
    let a:graphBallVertices H (.inr l) selector:=⟨.inr l,by simp [graphBallVertices]⟩
    let b:graphBallVertices H (.inr l) selector:=⟨.inr m,hnear⟩
    have he:deletedLeafBallOriginalHom G T l selector a=deletedLeafBallOriginalHom G T l selector b:=by
      apply Subtype.ext
      exact congrArg (fun t:T=>t.val) hb
    have hab:=deletedLeafBallOriginal_injective G T l selector (htree l.2.val) he
    exact hne (Sum.inr.inj (congrArg Subtype.val hab))
  · exact (hsep l.2.val m.2.val hb).trans_le
      (graphHom_edist_le (deletedLeafOriginalHom G T) (.inr l) (.inr m))

namespace DeficientGraph
variable {d:ℕ}

theorem deletedLeafModel_ball_isTree (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(l:DeletedLeafIndex g.graph T)(r:ℕ)
    (htree:(graphBall g.graph l.2.val.val r).IsTree) :
    (graphBall (g.deletedLeafModel hd T).graph (.inr l) r).IsTree := by
  apply graphBall_tree_of_locally_injective_hom (deletedLeafOriginalHom g.graph T)
    (deletedLeafOriginal_locally_injective g.graph T) (.inr l) r r
  · intro v hv
    exact (graphHom_edist_le (deletedLeafOriginalHom g.graph T) (.inr l) v).trans hv
  · exact htree

theorem deletedLeafModel_ball_zero_deficit (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(l:DeletedLeafIndex g.graph T)(r:ℕ)
    (hzero:∀v∈graphBallVertices g.graph l.2.val.val r,g.deficit v=0) :
    ∀a∈graphBallVertices (g.deletedLeafModel hd T).graph (.inr l) r,
      (g.deletedLeafModel hd T).deficit a=0 := by
  intro a ha
  cases a with
  | inl v=>
    rw [g.deletedLeafModel_deficit_old]
    apply hzero
    exact (graphHom_edist_le (deletedLeafOriginalHom g.graph T) (.inr l) (.inl v)).trans ha
  | inr l'=>exact g.deletedLeafModel_deficit_leaf hd T l'

end DeficientGraph
end LocalLaw
