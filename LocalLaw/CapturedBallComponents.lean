import LocalLaw.ComponentPairGeometry

/-! # Captured balls remain in the component of their center -/

noncomputable section
namespace LocalLaw
local instance capturedBallComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} (G : SimpleGraph V)

def inducedComponentVertices (S : Set V) (C : (G.induce S).ConnectedComponent) : Set V :=
  (Subtype.val:S→V) '' C.supp

def inducedComponentIso (S : Set V) (C : (G.induce S).ConnectedComponent) :
    (G.induce S).induce C.supp ≃g G.induce (inducedComponentVertices G S C) where
  toEquiv:=Equiv.Set.image (Subtype.val:S→V) C.supp Subtype.val_injective
  map_rel_iff':=Iff.rfl

theorem captured_ball_in_component (S : Set V) (C : (G.induce S).ConnectedComponent)
    (i : S) (hi : i∈C.supp) (r : ℕ) (hcapture : graphBallVertices G i.val r⊆S) :
    graphBallVertices G i.val r⊆inducedComponentVertices G S C := by
  intro v hv
  let f : graphBall G i.val r →g G.induce S :=
    { toFun:=fun a=>⟨a.val,hcapture a.property⟩
      map_rel':=fun h=>h }
  let root : graphBallVertices G i.val r:=⟨i.val,center_mem_graphBall G i.val r⟩
  have hr:=((graphBall_connected G i.val r).preconnected root ⟨v,hv⟩).map f
  change (G.induce S).Reachable i ⟨v,hcapture hv⟩ at hr
  have hm : (⟨v,hcapture hv⟩:S)∈C.supp :=
    (SimpleGraph.ConnectedComponent.sound hr).symm.trans hi
  exact ⟨⟨v,hcapture hv⟩,hm,rfl⟩

theorem walk_support_asymmetric_balls (i j : V) (ri rj : ℕ)
    (p : G.Walk i j) (hlen : p.length≤ri+rj+1) :
    ∀ v∈p.support,v∈graphBallVertices G i ri ∪graphBallVertices G j rj := by
  intro v hv
  let left:=p.takeUntil v hv
  let right:=p.dropUntil v hv
  have hsum:left.length+right.length=p.length := by
    rw [←SimpleGraph.Walk.length_append]
    exact congrArg SimpleGraph.Walk.length (p.take_spec hv)
  by_cases hl:left.length≤ri
  · exact Or.inl ((SimpleGraph.edist_le left).trans (ENat.coe_le_coe.mpr hl))
  · have hr:right.length≤rj := by omega
    exact Or.inr ((SimpleGraph.edist_le right.reverse).trans (by
      simpa only [SimpleGraph.Walk.length_reverse] using ENat.coe_le_coe.mpr hr))

theorem captured_balls_disconnected_distance (hG : G.Connected) (S : Set V) (i j : S) (ri rj : ℕ)
    (hI : graphBallVertices G i.val ri⊆S) (hJ : graphBallVertices G j.val rj⊆S)
    (hnot : ¬(G.induce S).Reachable i j) : ri+rj+1<G.dist i.val j.val := by
  by_contra hn
  obtain ⟨p,hp,hlen⟩:=(hG i.val j.val).exists_path_of_dist
  have hlen':p.length≤ri+rj+1 := by omega
  have hs : ∀ v∈p.support,v∈S := by
    intro v hv
    exact (walk_support_asymmetric_balls G i.val j.val ri rj p hlen' v hv).elim (fun h=>hI h) (fun h=>hJ h)
  obtain ⟨q,_⟩:=walk_lift_induced_of_support G S p hs i.property j.property
  exact hnot q.reachable

end LocalLaw
