import LocalLaw.SourceBoundaryGuard
import LocalLaw.GraphMetricLocality

/-! # An outside boundary guard controls the ambient graph metric

A short ambient walk cannot enter the deleted set: its first entering
edge would exhibit an outside boundary endpoint within the forbidden range.
This also transfers the literal guarded balls and their tree property.
-/

noncomputable section
namespace LocalLaw
local instance boundaryGuardAmbientDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}

theorem boundaryFarOutside_neighbor_outside (G:SimpleGraph V) (T:Set V) (h:ℕ)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h) {c:V} (hbc:G.Adj b.val c) : c∉T := by
  intro hc
  let α:BoundaryOrientedEdge G T:=⟨(c,b.val),hbc.symm,hc,b.property⟩
  have hh:=hb α
  have he:boundaryOuterEndpoint G T α=b:=rfl
  rw [he,SimpleGraph.edist_self] at hh
  exact not_lt_of_ge (bot_le:(0:ℕ∞)≤h) hh

theorem boundaryFarOutside_short_walk_avoids (G:SimpleGraph V) (T:Set V) (h:ℕ)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h) {y:V}
    (p:G.Walk b.val y) (hlen:p.length≤h+1) : ∀x∈p.support,x∉T := by
  induction h generalizing b y with
  | zero =>
    cases p with
    | nil =>
      intro x hx
      have hx':x=b.val:=by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hx
      rw [hx']
      exact b.property
    | @cons a c y hac p =>
      have hc:c∉T:=boundaryFarOutside_neighbor_outside G T 0 b hb hac
      cases p with
      | nil =>
        intro x hx
        simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl
        · exact b.property
        · exact hc
      | cons hcd p => simp only [SimpleGraph.Walk.length_cons] at hlen;omega
  | succ h ih =>
    cases p with
    | nil =>
      intro x hx
      have hx':x=b.val:=by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hx
      exact hx' ▸ b.property
    | @cons a c y hac p =>
      have hc:c∉T:=boundaryFarOutside_neighbor_outside G T (h+1) b hb hac
      let c0:(Tᶜ:Set V):=⟨c,hc⟩
      have hcFar:c0∈boundaryFarOutside G T h:=boundaryFarOutside_step G T h
        (show (outsideGraph G T).Adj b c0 from hac) hb
      have htail:p.length≤h+1:=by simpa only [SimpleGraph.Walk.length_cons] using Nat.le_of_succ_le_succ hlen
      have ht:=ih c0 hcFar p htail
      intro x hx
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact b.property
      · exact ht x hx

theorem boundaryFarOutside_ambient_far_set (G:SimpleGraph V) (T:Set V) (h:ℕ)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h) (x:V) (hx:x∈T) :
    ((h+1:ℕ):ℕ∞)<G.edist b.val x := by
  apply lt_of_not_ge
  intro hnear
  have hfinite:=ne_top_of_le_ne_top (ENat.coe_ne_top (h+1)) hnear
  obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen:p.length≤h+1:=ENat.coe_le_coe.mp (hp.trans_le hnear)
  exact boundaryFarOutside_short_walk_avoids G T h b hb p hlen x p.end_mem_support hx

theorem boundaryFarOutside_ambient_far_boundary (G:SimpleGraph V) (T:Set V) (h:ℕ)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h) (α:BoundaryOrientedEdge G T) :
    (h:ℕ∞)<G.edist b.val (boundaryOuterEndpoint G T α).val := by
  apply lt_of_not_ge
  intro hnear
  have hfinite:=ne_top_of_le_ne_top (ENat.coe_ne_top h) hnear
  obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen:p.length≤h:=ENat.coe_le_coe.mp (hp.trans_le hnear)
  have hsupp:=boundaryFarOutside_short_walk_avoids G T h b hb p (by omega)
  obtain ⟨q,hq⟩:=walk_lift_induced_of_support G Tᶜ p hsupp b.property (boundaryOuterEndpoint G T α).property
  have hshort:(outsideGraph G T).edist b (boundaryOuterEndpoint G T α)≤(h:ℕ∞):=
    (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (by simpa only [hq] using hlen))
  exact not_lt_of_ge hshort (hb α)

theorem boundaryFarOutside_ball_image (G:SimpleGraph V) (T:Set V) (h r:ℕ) (hr:r≤h+1)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h) :
    graphBallVertices G b.val r=Subtype.val '' graphBallVertices (outsideGraph G T) b r := by
  ext x
  constructor
  · intro hx
    have hfinite:=ne_top_of_le_ne_top (ENat.coe_ne_top r) hx
    obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top hfinite
    have hlen:p.length≤r:=ENat.coe_le_coe.mp (hp.trans_le hx)
    have hsupp:=boundaryFarOutside_short_walk_avoids G T h b hb p (hlen.trans hr)
    have hxT:x∉T:=hsupp x p.end_mem_support
    let x0:(Tᶜ:Set V):=⟨x,hxT⟩
    obtain ⟨q,hq⟩:=walk_lift_induced_of_support G Tᶜ p hsupp b.property hxT
    refine ⟨x0,?_,rfl⟩
    exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (by simpa only [hq] using hlen))
  · rintro ⟨x,hx,rfl⟩
    exact (ambient_edist_le_induced_edist G Tᶜ b x).trans hx

theorem boundaryFarOutside_ambient_ball_isTree (G:SimpleGraph V) (T:Set V) (h r:ℕ) (hr:r≤h+1)
    (b:(Tᶜ:Set V)) (hb:b∈boundaryFarOutside G T h)
    (hTree:(graphBall (outsideGraph G T) b r).IsTree) : (graphBall G b.val r).IsTree := by
  have himage:=boundaryFarOutside_ball_image G T h r hr b hb
  have hmem (v:graphBallVertices G b.val r) :
      ∃w:graphBallVertices (outsideGraph G T) b r,w.val.val=v.val := by
    have hv:v.val∈Subtype.val '' graphBallVertices (outsideGraph G T) b r:=by
      rw [←himage]
      exact v.property
    obtain ⟨w,hw,heq⟩:=hv
    exact ⟨⟨w,hw⟩,heq⟩
  let f:graphBall G b.val r→g graphBall (outsideGraph G T) b r:=
    { toFun:=fun v=>Classical.choose (hmem v)
      map_rel':=by
        intro u v huv
        change G.Adj (Classical.choose (hmem u)).val.val (Classical.choose (hmem v)).val.val
        rw [Classical.choose_spec (hmem u),Classical.choose_spec (hmem v)]
        exact huv }
  have hf:Function.Injective f:=by
    intro u v huv
    apply Subtype.ext
    exact (Classical.choose_spec (hmem u)).symm.trans
      ((congrArg (fun x:graphBallVertices (outsideGraph G T) b r=>x.val.val) huv).trans
        (Classical.choose_spec (hmem v)))
  refine ⟨graphBall_connected G b.val r,?_⟩
  intro v p hp
  exact hTree.IsAcyclic (p.map f) (hp.map hf)

end LocalLaw
