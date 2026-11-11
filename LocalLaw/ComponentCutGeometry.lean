import LocalLaw.ComponentDeletionBudget
import LocalLaw.CutComponentDiameter

/-! # Genuine disconnected cut multiplicities and deleted intrinsic diameter -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance componentCutGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) componentCutGeometryMemDecidable {V : Type*}
    (G : SimpleGraph V) (C : G.ConnectedComponent) : DecidablePred (fun x => x∈C.supp) :=
  fun _ => Classical.propDecidable _
variable {V : Type} [Fintype V] [DecidableEq V]

namespace DeficientGraph
variable {d : ℕ}
omit [DecidableEq V] in
theorem componentwise_cutMultiplicity_bound (g : DeficientGraph V d)
    (hzero : ∀v,g.deficit v=0) (hbase : g.ComponentReferenceBudget)
    (T : Set V) (hT : (g.graph.induce T).Connected) (C : CutComponent g.graph T) :
    cutMultiplicity g.graph T C≤finiteOmega d+1 := by
  have hh := ((g.componentwise_connected_deletion_budget hzero hbase T hT) C).complexity_le
  simp only [g.deleted_component_deficit_eq_cutDeficit hzero T C] at hh
  have hsum := cutMultiplicity_eq_sum_deficit g.graph T C
  simp only [←finsum_eq_sum_of_fintype] at hh hsum
  omega
end DeficientGraph

omit [Fintype V] [DecidableEq V] in
theorem cut_component_root_cover_of_boundary (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) (e0 : CutBoundaryEdge G T C) (R : ℕ)
    (hR : ∀x y,G.dist x y≤R) (y : C.supp) :
    ∃ e : CutBoundaryEdge G T C,(cutComponentGraph G T C).dist (cutAttachmentRoot G T C e) y≤R := by
  let x := cutAttachmentRoot G T C e0
  obtain ⟨p0⟩ := C.connected_induce_supp.preconnected x y
  let inc : cutComponentGraph G T C →g G := ⟨fun v => v.val.val,fun h => h⟩
  have hr : G.Reachable e0.val.val.1 y.val.val := ((p0.map inc).cons e0.val.property.1).reachable
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  let A := cutComponentVertices G T C
  let φ := cutComponentFlatIso G T C
  have hyA : y.val.val∈A := ⟨y.val.property,y.property⟩
  have htA : e0.val.val.1∉A := by rintro ⟨hn,_⟩; exact hn e0.val.property.2.1
  obtain ⟨u,hu,v,hv,huv,q,hq⟩ : ∃(u:V)(_hu:u∉A)(v:V)(hv:v∈A)(_huv:G.Adj u v),
      ∃q:(G.induce A).Walk ⟨v,hv⟩ ⟨y.val.val,hyA⟩,q.length+1≤p.length := by
    rcases walk_last_set_entry G A p hyA with ⟨ht,_,_⟩ | h
    · exact False.elim (htA ht)
    · exact h
  have huT : u∈T := by
    by_contra hn
    exact hu (cutComponentVertices_adj_closed G T C hn hv huv)
  let e : CutBoundaryEdge G T C := ⟨⟨(u,v),huv,huT,hv.1⟩,hv.2⟩
  refine ⟨e,?_⟩
  have hd := SimpleGraph.dist_le (q.map φ.symm.toHom)
  change (cutComponentGraph G T C).dist (cutAttachmentRoot G T C e) y≤_ at hd
  rw [SimpleGraph.Walk.length_map] at hd
  have hb := hR e0.val.val.1 y.val.val
  omega

omit [DecidableEq V] in
theorem cut_component_diameter_of_boundary (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) (e0 : CutBoundaryEdge G T C) (R : ℕ)
    (hR : ∀x y,G.dist x y≤R) (a b : C.supp) :
    (cutComponentGraph G T C).dist a b≤2*R+(cutMultiplicity G T C-1)*(2*R+1) := by
  let H := cutComponentGraph G T C
  let center : CutBoundaryEdge G T C → C.supp := cutAttachmentRoot G T C
  let radius : CutBoundaryEdge G T C → ℕ := fun _ => R
  have hcover : ∀y:C.supp,y∈ballCoverVertices H center radius := by
    intro y
    obtain ⟨e,he⟩ := cut_component_root_cover_of_boundary G T C e0 R hR y
    obtain ⟨p,hp⟩ := C.connected_induce_supp.exists_walk_length_eq_dist (center e) y
    exact ⟨e,(SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr (hp.trans_le he))⟩
  let aa : ballCoverVertices H center radius := ⟨a,hcover a⟩
  let bb : ballCoverVertices H center radius := ⟨b,hcover b⟩
  have hd := ballCover_distance_bound H center radius R (fun _ => le_rfl) aa bb
  have hcut : ∀x∈ballCoverVertices H center radius,∀y∉ballCoverVertices H center radius,¬H.Adj x y := by
    intro x hx y hy
    exact False.elim (hy (hcover y))
  rw [isolated_induce_distance H (ballCoverVertices H center radius) hcut aa bb] at hd
  simpa only [cutMultiplicity,←Nat.card_eq_fintype_card] using hd

omit [DecidableEq V] in
theorem cut_component_diameter_zero_boundary (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) (hzero : cutMultiplicity G T C=0) (R : ℕ)
    (hR : ∀x y,G.dist x y≤R) (a b : C.supp) : (cutComponentGraph G T C).dist a b≤R := by
  let A := cutComponentVertices G T C
  let e := cutComponentFlatIso G T C
  have hcut : ∀u∈A,∀v∉A,¬G.Adj u v := by
    intro u hu v hv huv
    by_cases hvT : v∈T
    · let edge : CutBoundaryEdge G T C := ⟨⟨(v,u),huv.symm,hvT,hu.1⟩,hu.2⟩
      have hp : 0<cutMultiplicity G T C := Nat.card_pos_iff.mpr ⟨⟨edge⟩,inferInstance⟩
      omega
    · exact hv (cutComponentVertices_adj_closed G T C hvT hu huv.symm)
  rw [←graphIso_dist e a b,isolated_induce_distance G A hcut (e a) (e b)]
  exact hR _ _

theorem outside_graph_diameter_of_cut_bound (G : SimpleGraph V) (T : Set V) (R κ : ℕ)
    (hκ : 1≤κ) (hR : ∀x y,G.dist x y≤R)
    (hcut : ∀C:CutComponent G T,cutMultiplicity G T C≤κ) (a b:(Tᶜ:Set V)) :
    (outsideGraph G T).dist a b≤κ*(2*R+1) := by
  by_cases hr : (outsideGraph G T).Reachable a b
  · let C := (outsideGraph G T).connectedComponentMk a
    let aa : C.supp := ⟨a,rfl⟩
    let bb : C.supp := ⟨b,(SimpleGraph.ConnectedComponent.sound hr).symm⟩
    have hd : (cutComponentGraph G T C).dist aa bb≤κ*(2*R+1) := by
      by_cases hz : cutMultiplicity G T C=0
      · exact (cut_component_diameter_zero_boundary G T C hz R hR aa bb).trans (by nlinarith)
      · have hp : 0<cutMultiplicity G T C := by omega
        let e0 : CutBoundaryEdge G T C := Classical.choice (Nat.card_pos_iff.mp hp).1
        have hh := cut_component_diameter_of_boundary G T C e0 R hR aa bb
        have hsub : cutMultiplicity G T C-1+1=cutMultiplicity G T C := by omega
        have hmul := Nat.mul_le_mul_right (2*R+1) (hcut C)
        nlinarith
    change ((outsideGraph G T).induce C.supp).dist aa bb≤_ at hd
    have hclosed : ∀x∈C.supp,∀y∉C.supp,¬(outsideGraph G T).Adj x y := by
      intro x hx y hy hxy
      exact hy ((C.mem_supp_congr_adj hxy).mp hx)
    rw [isolated_induce_distance (outsideGraph G T) C.supp hclosed aa bb] at hd
    exact hd
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

namespace DeficientGraph
variable {d:ℕ}
theorem componentwise_connected_deletion_diameter (g:DeficientGraph V d)
    (hzero:∀v,g.deficit v=0) (hbase:g.ComponentReferenceBudget)
    (T:Set V) (hT:(g.graph.induce T).Connected) (R:ℕ) (hR:∀x y,g.graph.dist x y≤R) :
    ∀a b,(g.delete T).graph.dist a b≤(finiteOmega d+1)*(2*R+1) :=
  outside_graph_diameter_of_cut_bound g.graph T R (finiteOmega d+1) (by omega) hR
    (g.componentwise_cutMultiplicity_bound hzero hbase T hT)
end DeficientGraph
end LocalLaw
