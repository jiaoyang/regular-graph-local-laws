import LocalLaw.FullPairCutNeighborhood
import LocalLaw.FullOldTwoTargetGeometry
import LocalLaw.CapturedStarPrecision

/-! # Literal inner and cut precision blocks in the near full-pair case

Radius-one capture of T preserves every T precision row and column.
Consequently the common model and the full pair have the same restored
inner block and the same couplings at every retained exterior index.
-/
noncomputable section
namespace LocalLaw
local instance fullCutPrecisionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type}

def cutInnerEmbedding (T S:Set V)(hTS:T⊆S):T↪S where
  toFun t:=⟨t.val,hTS t.property⟩
  inj':=fun _ _ h=>Subtype.ext (congrArg (fun v:S=>v.val) h)

def cutRetainedEmbedding (S:Set V)(e:I↪V)(he:∀i,e i∈S):I↪S where
  toFun i:=⟨e i,he i⟩
  inj':=fun _ _ h=>e.injective (congrArg Subtype.val h)

theorem cut_neighborhood_captures_neighbors (G:SimpleGraph V)(T S:Set V)
    (hcap:graphSetBall G T 1⊆S)(t:T)(v:V)(htv:G.Adj t.val v):v∈S:=
  hcap ⟨t.val,t.property,(SimpleGraph.edist_eq_one_iff_adj.mpr htv).le⟩

namespace DeficientGraph
variable [Fintype V][DecidableEq V]{d:ℕ}

theorem captured_cut_precision_blocks (g:DeficientGraph V d)(T S:Set V)
    (hcap:graphSetBall g.graph T 1⊆S)(e:I↪V)(he:∀i,e i∈S)(q z:ℂ):
    let hTS:=cut_neighborhood_captures_inner g.graph T S hcap
    let inner:=cutInnerEmbedding T S hTS
    let outer:=cutRetainedEmbedding S e he
    ((g.restrict S).extensionMatrix q z).submatrix inner inner=
      (g.extensionMatrix q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V) ∧
    ((g.restrict S).extensionMatrix q z).submatrix outer inner=
      (g.extensionMatrix q z).submatrix e (Subtype.val:T→V) ∧
    ((g.restrict S).extensionMatrix q z).submatrix inner outer=
      (g.extensionMatrix q z).submatrix (Subtype.val:T→V) e:=by
  dsimp only
  let hTS:=cut_neighborhood_captures_inner g.graph T S hcap
  let inner:=cutInnerEmbedding T S hTS
  let outer:=cutRetainedEmbedding S e he
  have hneighbors (t:T):∀w,g.graph.Adj (inner t).val w→w∈S:=
    fun w hw=>cut_neighborhood_captures_neighbors g.graph T S hcap t w hw
  refine ⟨?_,?_,?_⟩
  · ext t u
    exact g.restrict_extensionMatrix_captured_row S (inner t) (hneighbors t) q z (inner u)
  · ext i t
    exact g.restrict_extensionMatrix_captured_column S (inner t) (hneighbors t) q z (outer i)
  · ext t i
    exact g.restrict_extensionMatrix_captured_row S (inner t) (hneighbors t) q z (outer i)

theorem two_restrictions_captured_cut_precision_blocks (g:DeficientGraph V d)(T A B:Set V)
    (hA:graphSetBall g.graph T 1⊆A)(hB:graphSetBall g.graph T 1⊆B)
    (e:I↪V)(heA:∀i,e i∈A)(heB:∀i,e i∈B)(q z:ℂ):
    let innerA:=cutInnerEmbedding T A (cut_neighborhood_captures_inner g.graph T A hA)
    let innerB:=cutInnerEmbedding T B (cut_neighborhood_captures_inner g.graph T B hB)
    let outerA:=cutRetainedEmbedding A e heA
    let outerB:=cutRetainedEmbedding B e heB
    ((g.restrict A).extensionMatrix q z).submatrix innerA innerA=
      ((g.restrict B).extensionMatrix q z).submatrix innerB innerB ∧
    ((g.restrict A).extensionMatrix q z).submatrix outerA innerA=
      ((g.restrict B).extensionMatrix q z).submatrix outerB innerB ∧
    ((g.restrict A).extensionMatrix q z).submatrix innerA outerA=
      ((g.restrict B).extensionMatrix q z).submatrix innerB outerB:=by
  have ha:=g.captured_cut_precision_blocks T A hA e heA q z
  have hb:=g.captured_cut_precision_blocks T B hB e heB q z
  exact ⟨ha.1.trans hb.1.symm,ha.2.1.trans hb.2.1.symm,ha.2.2.trans hb.2.2.symm⟩

end DeficientGraph
namespace LabelledResamplingState
variable {T:Set V}{ι:Type}[Fintype ι]

theorem fullTwoTarget_captures_cut_neighborhood (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hr:1≤r)(x y:V):
    graphSetBall (s.fullResample selector).graph T 1⊆s.fullTwoTargetVertices selector r x y:=by
  rw[s.fullTwoTarget_new_setBall selector r x y]
  rintro v ⟨t,ht,htv⟩
  exact ⟨t,Or.inl (Or.inl ht),htv.trans (ENat.coe_le_coe.mpr hr)⟩

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem full_pair_near_same_cut_precision (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(hr:1≤r)(x y:Fin N)
    (hcap:graphSetBall (g.admissibleState T labels samples|>.fullResample selector).graph T 1⊆
      pairBallVertices (g.admissibleState T labels samples|>.fullResample selector).graph x y r)
    (e:I↪Fin N)(he:∀i,e i∈pairBallVertices
      (g.admissibleState T labels samples|>.fullResample selector).graph x y r)(q z:ℂ):
    let s:=g.admissibleState T labels samples
    let new:=g.labelledResampledGraph T labels samples selector
    let A:=s.fullTwoTargetVertices selector r x y
    let B:=pairBallVertices (s.fullResample selector).graph x y r
    let hA:=s.fullTwoTarget_captures_cut_neighborhood selector r hr x y
    let hsub:=s.switched_full_pair_subset_old_augmentation selector r x y
    let innerA:=cutInnerEmbedding T A (cut_neighborhood_captures_inner new.graph T A hA)
    let innerB:=cutInnerEmbedding T B (cut_neighborhood_captures_inner new.graph T B hcap)
    let outerA:=cutRetainedEmbedding A e (fun i=>hsub (he i))
    let outerB:=cutRetainedEmbedding B e he
    ((new.deficient.restrict A).extensionMatrix q z).submatrix innerA innerA=
      ((new.deficient.restrict B).extensionMatrix q z).submatrix innerB innerB ∧
    ((new.deficient.restrict A).extensionMatrix q z).submatrix outerA innerA=
      ((new.deficient.restrict B).extensionMatrix q z).submatrix outerB innerB ∧
    ((new.deficient.restrict A).extensionMatrix q z).submatrix innerA outerA=
      ((new.deficient.restrict B).extensionMatrix q z).submatrix innerB outerB:=by
  dsimp only
  let s:=g.admissibleState T labels samples
  exact (g.labelledResampledGraph T labels samples selector).deficient.two_restrictions_captured_cut_precision_blocks
    T (s.fullTwoTargetVertices selector r x y) (pairBallVertices (s.fullResample selector).graph x y r)
    (s.fullTwoTarget_captures_cut_neighborhood selector r hr x y) hcap e
    (fun i=>s.switched_full_pair_subset_old_augmentation selector r x y (he i)) he q z

end RegularGraph
end LocalLaw
