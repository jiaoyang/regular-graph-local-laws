import LocalLaw.PartitionedStarDeletion
import LocalLaw.DeficientGraphInstanceTransport

/-! # Canonical target-core deciders in the exact total-deletion identity -/

noncomputable section
namespace LocalLaw
local instance partitionedStarDeletionCanonicalDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) partitionedStarDeletionCanonicalRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V I:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem partitionedStar_core_extensionGreen_canonical
    (g:DeficientGraph V d)(S O J B:Set V)(hJS:J⊆S)(hJO:∀v∈J,v∉O)(hpart:J∪O=B)
    (e:I↪((Set.range (restrictedStarInner S O J hJS hJO))ᶜ:Set ({v:S|v.val∈O}ᶜ:Set S)))
    (q z:ℂ) :
    letI:DecidableEq ({v:S|v.val∈B}ᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
    ((((g.restrict S).delete {v:S|v.val∈O}).delete
      (Set.range (restrictedStarInner S O J hJS hJO))).extensionGreen q z).submatrix e e=
    (((g.restrict S).delete {v:S|v.val∈B}).extensionGreen q z).submatrix
      (fun i=>partitionedStarDeletionEquiv S O J B hJS hJO hpart (e i))
      (fun i=>partitionedStarDeletionEquiv S O J B hJS hJO hpart (e i)) := by
  letI:DecidableEq ({v:S|v.val∈B}ᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
  have hh:=g.partitionedStar_core_extensionGreen S O J B hJS hJO hpart e q z
  have he:=extensionGreen_decidableEq_eq ((g.restrict S).delete {v:S|v.val∈B})
    (Subtype.instDecidableEq) (fun a b=>Classical.propDecidable (a=b)) q z
  rw [he] at hh
  exact hh

end DeficientGraph
end LocalLaw
