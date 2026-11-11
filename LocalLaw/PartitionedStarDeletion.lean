import LocalLaw.RestrictedDeletedStars

/-! # Exact flattening of outer deletion followed by inner-star deletion

Deleting the complementary sampled families is literal total deletion,
including the full physical deficit. The equivalence keeps the underlying
vertex unchanged and transports the genuine Green inverse.
-/

noncomputable section
namespace LocalLaw
local instance partitionedStarDeletionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}
local instance (priority := 2000) partitionedStarDeletionRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def partitionedStarDeletionEquiv (S O J B:Set V)(hJS:J⊆S)(hJO:∀v∈J,v∉O)(hpart:J∪O=B) :
    ((Set.range (restrictedStarInner S O J hJS hJO))ᶜ:Set ({v:S|v.val∈O}ᶜ:Set S))≃
      ({v:S|v.val∈B}ᶜ:Set S) := by
  have hJB:J⊆B:=by rw [←hpart];exact Set.subset_union_left
  have hOB:O⊆B:=by rw [←hpart];exact Set.subset_union_right
  have hB:B⊆J∪O:=by rw [hpart]
  exact
    {toFun:=fun u=>⟨u.val.val,by
       intro hu
       rcases hB hu with hj|ho
       · exact u.property ⟨⟨u.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
       · exact u.val.property ho⟩
     invFun:=fun u=>⟨⟨u.val,fun ho=>u.property (hOB ho)⟩,by
       rintro ⟨j,hj⟩
       have he:j.val=u.val.val:=congrArg (fun v:({v:S|v.val∈O}ᶜ:Set S)=>v.val.val) hj
       exact u.property (hJB (he ▸ j.property))⟩
     left_inv:=fun _=>rfl
     right_inv:=fun _=>rfl}

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d:ℕ}

theorem partitionedStar_total_extensionMatrix (g:DeficientGraph V d)
    (S O J B:Set V)(hJS:J⊆S)(hJO:∀v∈J,v∉O)(hpart:J∪O=B)(q z:ℂ) :
    (((g.restrict S).delete {v:S|v.val∈B}).extensionMatrix q z).submatrix
      (partitionedStarDeletionEquiv S O J B hJS hJO hpart)
      (partitionedStarDeletionEquiv S O J B hJS hJO hpart)=
    (((g.restrict S).delete {v:S|v.val∈O}).delete
      (Set.range (restrictedStarInner S O J hJS hJO))).extensionMatrix q z := by
  rw [(g.restrict S).extensionMatrix_delete,
    ((g.restrict S).delete {v:S|v.val∈O}).extensionMatrix_delete,
    (g.restrict S).extensionMatrix_delete]
  ext u v
  rfl

theorem partitionedStar_total_extensionGreen (g:DeficientGraph V d)
    (S O J B:Set V)(hJS:J⊆S)(hJO:∀v∈J,v∉O)(hpart:J∪O=B)(q z:ℂ) :
    (((g.restrict S).delete {v:S|v.val∈B}).extensionGreen q z).submatrix
      (partitionedStarDeletionEquiv S O J B hJS hJO hpart)
      (partitionedStarDeletionEquiv S O J B hJS hJO hpart)=
    (((g.restrict S).delete {v:S|v.val∈O}).delete
      (Set.range (restrictedStarInner S O J hJS hJO))).extensionGreen q z := by
  let φ:=partitionedStarDeletionEquiv S O J B hJS hJO hpart
  have hh:=Matrix.inv_submatrix_equiv (((g.restrict S).delete {v:S|v.val∈B}).extensionMatrix q z) φ φ
  rw [g.partitionedStar_total_extensionMatrix S O J B hJS hJO hpart q z] at hh
  exact hh.symm

theorem partitionedStar_core_extensionGreen {I:Type}
    (g:DeficientGraph V d)(S O J B:Set V)(hJS:J⊆S)(hJO:∀v∈J,v∉O)(hpart:J∪O=B)
    (e:I↪((Set.range (restrictedStarInner S O J hJS hJO))ᶜ:Set ({v:S|v.val∈O}ᶜ:Set S)))
    (q z:ℂ) :
    ((((g.restrict S).delete {v:S|v.val∈O}).delete
      (Set.range (restrictedStarInner S O J hJS hJO))).extensionGreen q z).submatrix e e=
    (((g.restrict S).delete {v:S|v.val∈B}).extensionGreen q z).submatrix
      (fun i=>partitionedStarDeletionEquiv S O J B hJS hJO hpart (e i))
      (fun i=>partitionedStarDeletionEquiv S O J B hJS hJO hpart (e i)) := by
  rw [←g.partitionedStar_total_extensionGreen S O J B hJS hJO hpart q z]
  rfl

end DeficientGraph
end LocalLaw
