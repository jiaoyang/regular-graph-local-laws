import LocalLaw.LeafDeficitAugmentation
import LocalLaw.RestrictionDeletionIdentity

/-! # Restoring any finite family of lost deficit units by distinct leaves

Every new leaf has its own label, even when several are attached to one
core vertex. The core deficit decreases by exactly its attachment count.
Deleting all new leaves restores the original precision matrix exactly.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance multiLeafAugmentationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V L:Type*}

def multiLeafGraph (G:SimpleGraph V)(mate:L→V) : SimpleGraph (V⊕L) where
  Adj
    | .inl a,.inl b=>G.Adj a b
    | .inl a,.inr l=>a=mate l
    | .inr l,.inl b=>b=mate l
    | .inr _,.inr _=>False
  symm:=by intro a b h;cases a <;> cases b <;> first | exact h.symm | exact h
  loopless:=by intro a;cases a;exact G.loopless _;exact id

def multiLeafProjection (mate:L→V) : V⊕L→V := Sum.elim id mate

theorem multiLeafGraph_project_edge (G:SimpleGraph V)(mate:L→V)
    {a b:V⊕L}(h:(multiLeafGraph G mate).Adj a b) :
    G.Reachable (multiLeafProjection mate a) (multiLeafProjection mate b) := by
  cases a with
  | inl a=>
    cases b with
    | inl b=>exact (show G.Adj a b from h).reachable
    | inr b=>exact h ▸ SimpleGraph.Reachable.refl _
  | inr a=>
    cases b with
    | inl b=>exact h.symm ▸ SimpleGraph.Reachable.refl _
    | inr b=>exact False.elim h

theorem multiLeafGraph_project_reachable (G:SimpleGraph V)(mate:L→V)
    {a b:V⊕L}(h:(multiLeafGraph G mate).Reachable a b) :
    G.Reachable (multiLeafProjection mate a) (multiLeafProjection mate b) := by
  obtain ⟨p⟩:=h
  induction p with
  | nil=>exact SimpleGraph.Reachable.refl _
  | cons h p ih=>exact (multiLeafGraph_project_edge G mate h).trans ih

theorem multiLeafGraph_reachable_old (G:SimpleGraph V)(mate:L→V)(a b:V) :
    (multiLeafGraph G mate).Reachable (.inl a) (.inl b) ↔ G.Reachable a b := by
  constructor
  · exact multiLeafGraph_project_reachable G mate
  · intro h
    exact h.map (show G→g multiLeafGraph G mate from ⟨Sum.inl,fun h=>h⟩)

theorem multiLeafGraph_anchor_reachable (G:SimpleGraph V)(mate:L→V)(a:V⊕L) :
    (multiLeafGraph G mate).Reachable (.inl (multiLeafProjection mate a)) a := by
  cases a with
  | inl a=>exact SimpleGraph.Reachable.refl _
  | inr l=>exact (show (multiLeafGraph G mate).Adj (.inl (mate l)) (.inr l) from rfl).reachable

def multiLeafComponentEquiv (G:SimpleGraph V)(mate:L→V) :
    (multiLeafGraph G mate).ConnectedComponent≃G.ConnectedComponent where
  toFun:=Quot.map (multiLeafProjection mate) (fun _ _ h=>multiLeafGraph_project_reachable G mate h)
  invFun:=Quot.map Sum.inl (fun _ _ h=>(multiLeafGraph_reachable_old G mate _ _).mpr h)
  left_inv:=by
    intro c
    induction c using Quot.inductionOn with
    | h a=>exact SimpleGraph.ConnectedComponent.sound (multiLeafGraph_anchor_reachable G mate a)
  right_inv:=by
    intro c
    induction c using Quot.inductionOn with
    | h a=>rfl

theorem multiLeafComponent_mem_iff (G:SimpleGraph V)(mate:L→V)
    (C:(multiLeafGraph G mate).ConnectedComponent)(a:V⊕L) :
    a∈C.supp ↔ multiLeafProjection mate a∈((multiLeafComponentEquiv G mate) C).supp := by
  change (multiLeafGraph G mate).connectedComponentMk a=C ↔
    G.connectedComponentMk (multiLeafProjection mate a)=(multiLeafComponentEquiv G mate) C
  exact (multiLeafComponentEquiv G mate).injective.eq_iff.symm

def multiLeafComponentMate (G:SimpleGraph V)(mate:L→V)
    (C:(multiLeafGraph G mate).ConnectedComponent) :
    {l:L //mate l∈((multiLeafComponentEquiv G mate) C).supp}→
      ((multiLeafComponentEquiv G mate) C).supp := fun l=>⟨mate l.val,l.property⟩

/-- Each actual augmented component is a pendant augmentation of its
literal projected core component. -/
def multiLeafComponentGraphIso (G:SimpleGraph V)(mate:L→V)
    (C:(multiLeafGraph G mate).ConnectedComponent) :
    multiLeafGraph (G.induce ((multiLeafComponentEquiv G mate) C).supp)
      (multiLeafComponentMate G mate C) ≃g (multiLeafGraph G mate).induce C.supp where
  toFun a:=match a with
    | .inl v=>⟨.inl v.val,(multiLeafComponent_mem_iff G mate C _).mpr v.property⟩
    | .inr l=>⟨.inr l.val,(multiLeafComponent_mem_iff G mate C _).mpr l.property⟩
  invFun a:=match h:a.val with
    | .inl v=>.inl ⟨v,(multiLeafComponent_mem_iff G mate C (.inl v)).mp (h ▸ a.property)⟩
    | .inr l=>.inr ⟨l,(multiLeafComponent_mem_iff G mate C (.inr l)).mp (h ▸ a.property)⟩
  left_inv a:=by cases a <;> rfl
  right_inv a:=by rcases a with ⟨a,ha⟩;cases a <;> rfl
  map_rel_iff':=by
    intro a b
    cases a with
    | inl a=>
      cases b with
      | inl b=>rfl
      | inr b=>
        change a.val=mate b.val ↔ a=⟨mate b.val,b.property⟩
        exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    | inr a=>
      cases b with
      | inl b=>
        change b.val=mate a.val ↔ b=⟨mate a.val,a.property⟩
        exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
      | inr b=>rfl

theorem multiLeafGraph_project_walk (G:SimpleGraph V)(mate:L→V)
    {a b:V⊕L}(p:(multiLeafGraph G mate).Walk a b) :
    ∃q:G.Walk (multiLeafProjection mate a) (multiLeafProjection mate b),q.length≤p.length := by
  induction p with
  | nil=>exact ⟨.nil,Nat.le_refl _⟩
  | @cons a b c h p ih=>
    obtain ⟨q,hq⟩:=ih
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        refine ⟨.cons (show G.Adj a b from h) q,?_⟩
        simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hq
      | inr l=>
        change a=mate l at h
        subst a
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
    | inr l=>
      cases b with
      | inl b=>
        change b=mate l at h
        subst b
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
      | inr l'=>exact False.elim h

theorem multiLeafGraph_edist_projection (G:SimpleGraph V)(mate:L→V)(a b:V⊕L) :
    G.edist (multiLeafProjection mate a) (multiLeafProjection mate b)≤
      (multiLeafGraph G mate).edist a b := by
  by_cases ht:(multiLeafGraph G mate).edist a b=⊤
  · simp only [ht,le_top]
  · obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top ht
    obtain ⟨q,hq⟩:=multiLeafGraph_project_walk G mate p
    exact (G.edist_le q).trans ((ENat.coe_le_coe.mpr hq).trans_eq hp)

def multiLeafLift (mate:L→V)(S:Set V):Set (V⊕L):={a |multiLeafProjection mate a∈S}

theorem multiLeafLift_pair_capture (G:SimpleGraph V)(mate:L→V)(S:Set V)
    (x y:V)(r:ℕ)(hcapture:pairBallVertices G x y r⊆S) :
    pairBallVertices (multiLeafGraph G mate) (.inl x) (.inl y) r⊆multiLeafLift mate S := by
  intro a ha
  apply hcapture
  rcases ha with hx | hy
  · exact Or.inl ((multiLeafGraph_edist_projection G mate (.inl x) a).trans hx)
  · exact Or.inr ((multiLeafGraph_edist_projection G mate (.inl y) a).trans hy)

/-- Added leaves cannot shortcut any pair of old vertices, even across
different connected components. -/
theorem multiLeafGraph_edist_old (G:SimpleGraph V)(mate:L→V)(a b:V) :
    (multiLeafGraph G mate).edist (.inl a) (.inl b)=G.edist a b := by
  apply le_antisymm
  · exact graphHom_edist_le (show G→g multiLeafGraph G mate from ⟨Sum.inl,fun h=>h⟩) a b
  · by_cases ht:(multiLeafGraph G mate).edist (.inl a) (.inl b)=⊤
    · simp only [ht,le_top]
    · obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top ht
      obtain ⟨q,hq⟩:=multiLeafGraph_project_walk G mate p
      exact (G.edist_le q).trans ((ENat.coe_le_coe.mpr hq).trans_eq hp)

theorem multiLeafGraph_dist_old (G:SimpleGraph V)(mate:L→V)(a b:V) :
    (multiLeafGraph G mate).dist (.inl a) (.inl b)=G.dist a b := by
  simp only [SimpleGraph.dist,multiLeafGraph_edist_old]

theorem multiLeafGraph_anchor_edist (G:SimpleGraph V)(mate:L→V)(a:V⊕L) :
    (multiLeafGraph G mate).edist a (.inl (multiLeafProjection mate a))≤1 := by
  cases a with
  | inl a=>simp only [multiLeafProjection,Sum.elim_inl,id_eq,SimpleGraph.edist_self,zero_le]
  | inr l=>exact (SimpleGraph.edist_eq_one_iff_adj.mpr
      (show (multiLeafGraph G mate).Adj (.inr l) (.inl (mate l)) from rfl)).le

theorem multiLeafGraph_edist_upper (G:SimpleGraph V)(mate:L→V)(a b:V⊕L) :
    (multiLeafGraph G mate).edist a b≤
      G.edist (multiLeafProjection mate a) (multiLeafProjection mate b)+2 := by
  let H:=multiLeafGraph G mate
  calc
    _≤H.edist a (.inl (multiLeafProjection mate a))+
        H.edist (.inl (multiLeafProjection mate a)) b:=H.edist_triangle
    _≤H.edist a (.inl (multiLeafProjection mate a))+
        (H.edist (.inl (multiLeafProjection mate a)) (.inl (multiLeafProjection mate b))+
          H.edist (.inl (multiLeafProjection mate b)) b):=
      add_le_add_left H.edist_triangle _
    _≤1+(G.edist (multiLeafProjection mate a) (multiLeafProjection mate b)+1):=by
      apply add_le_add (multiLeafGraph_anchor_edist G mate a)
      apply add_le_add
      · exact (multiLeafGraph_edist_old G mate _ _).le
      · simpa only [SimpleGraph.edist_comm] using multiLeafGraph_anchor_edist G mate b
    _=G.edist (multiLeafProjection mate a) (multiLeafProjection mate b)+((1:ℕ∞)+(1:ℕ∞)):=by
      rw [add_left_comm]
    _=_:=by norm_num

theorem multiLeafGraph_diameter_bound (G:SimpleGraph V)(mate:L→V)(D:ℕ)
    (hD:∀u v,G.dist u v≤D)(a b:V⊕L) : (multiLeafGraph G mate).dist a b≤D+2 := by
  let H:=multiLeafGraph G mate
  by_cases hr:H.Reachable a b
  · have hproj:=multiLeafGraph_project_reachable G mate hr
    have hg:(G.dist (multiLeafProjection mate a) (multiLeafProjection mate b):ℕ∞)=
        G.edist (multiLeafProjection mate a) (multiLeafProjection mate b):=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hproj)
    have hh:(H.dist a b:ℕ∞)=H.edist a b:=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
    apply ENat.coe_le_coe.mp
    rw [hh]
    exact (multiLeafGraph_edist_upper G mate a b).trans
      (by rw [←hg];exact_mod_cast Nat.add_le_add_right (hD _ _) 2)
  · rw [H.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

theorem multiLeafGraph_connected (G:SimpleGraph V)(mate:L→V)(hG:G.Connected) :
    (multiLeafGraph G mate).Connected := by
  obtain ⟨v⟩:=hG.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl v,?_⟩
  intro a
  cases a with
  | inl a=>exact (multiLeafGraph_reachable_old G mate v a).mpr (hG.preconnected v a)
  | inr l=>
    exact ((multiLeafGraph_reachable_old G mate v (mate l)).mpr (hG.preconnected v (mate l))).trans
      (show (multiLeafGraph G mate).Adj (.inl (mate l)) (.inr l) from rfl).reachable

section Finite
variable [Fintype V] [Fintype L]

def multiLeafMultiplicity (mate:L→V)(v:V):ℕ:=Nat.card {l:L //mate l=v}

theorem multiLeafGraph_degree_old (G:SimpleGraph V)(mate:L→V)(v:V) :
    (multiLeafGraph G mate).degree (.inl v)=G.degree v+multiLeafMultiplicity mate v := by
  have hh:=(multiLeafGraph G mate).degree_eq_sum_if_adj (R:=ℕ) (.inl v)
  rw [Fintype.sum_sum_type] at hh
  simp only [Nat.cast_id] at hh
  conv_rhs at hh=>simp only [multiLeafGraph]
  rw [←G.degree_eq_sum_if_adj (R:=ℕ) v] at hh
  have hc : (∑l:L,if v=mate l then (1:ℕ) else 0)=multiLeafMultiplicity mate v := by
    simp only [multiLeafMultiplicity,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simpa only [Nat.cast_id,eq_comm] using
      (Finset.sum_boole (α:=ℕ) (fun l:L=>v=mate l) Finset.univ)
  change (multiLeafGraph G mate).degree (.inl v)=G.degree v+(∑l:L,if v=mate l then (1:ℕ) else 0) at hh
  rw [hc] at hh
  exact hh

theorem multiLeafGraph_degree_leaf (G:SimpleGraph V)(mate:L→V)(l:L) :
    (multiLeafGraph G mate).degree (.inr l)=1 := by
  have hh:=(multiLeafGraph G mate).degree_eq_sum_if_adj (R:=ℕ) (.inr l)
  rw [Fintype.sum_sum_type] at hh
  have hh' : (multiLeafGraph G mate).degree (.inr l)=∑v:V,if v=mate l then (1:ℕ) else 0 := by
    simpa only [Nat.cast_id,multiLeafGraph,if_false,Finset.sum_const_zero,add_zero] using hh
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh'

theorem multiLeafMultiplicity_sum (mate:L→V) :
    (∑v:V,multiLeafMultiplicity mate v)=Fintype.card L := by
  have hh:=Nat.card_congr (Equiv.sigmaFiberEquiv mate)
  simpa only [Nat.card_sigma,Nat.card_eq_fintype_card,Fintype.card_sigma,multiLeafMultiplicity] using hh

theorem multiLeafGraph_edge_card (G:SimpleGraph V)(mate:L→V) :
    (multiLeafGraph G mate).edgeFinset.card=G.edgeFinset.card+Fintype.card L := by
  have hh:=(multiLeafGraph G mate).sum_degrees_eq_twice_card_edges
  have hG:=G.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hh
  simp_rw [multiLeafGraph_degree_old,multiLeafGraph_degree_leaf] at hh
  rw [Finset.sum_add_distrib,multiLeafMultiplicity_sum] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hh
  omega

theorem multiLeafGraph_excess_of_connected (G:SimpleGraph V)(mate:L→V)(hG:G.Connected) :
    graphExcess (multiLeafGraph G mate)=graphExcess G := by
  have hnew:=connected_graph_excess_euler _ (multiLeafGraph_connected G mate hG)
  have hold:=connected_graph_excess_euler G hG
  have hcard:=multiLeafGraph_edge_card G mate
  simp only [graphEdgeCount,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,
    Fintype.card_sum] at hnew hold
  omega

/-- Pendant augmentation preserves Euler excess without a connectivity
assumption, because the actual component quotient is unchanged. -/
theorem multiLeafGraph_excess (G:SimpleGraph V)(mate:L→V) :
    graphExcess (multiLeafGraph G mate)=graphExcess G := by
  have he:=multiLeafGraph_edge_card G mate
  have hc:=Nat.card_congr (multiLeafComponentEquiv G mate)
  simp only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at he ⊢
  rw [hc,Nat.card_sum]
  simp only [Nat.card_eq_fintype_card] at he ⊢
  omega

namespace DeficientGraph
variable {d:ℕ}

def attachLeaves (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v) : DeficientGraph (V⊕L) d where
  graph:=multiLeafGraph g.graph mate
  deficit:=Sum.elim (fun v=>g.deficit v-multiLeafMultiplicity mate v) (fun _=>0)
  degree_deficit_le:=by
    intro a
    cases a with
    | inl v=>
      rw [multiLeafGraph_degree_old]
      simp only [Sum.elim_inl]
      have hh:=g.degree_deficit_le v
      have hr:=hrestore v
      omega
    | inr l=>simpa only [multiLeafGraph_degree_leaf,Sum.elim_inr,add_zero] using hd

theorem attachLeaves_degree_deficit (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(v:V) :
    (g.attachLeaves hd mate hrestore).graph.degree (.inl v)+
      (g.attachLeaves hd mate hrestore).deficit (.inl v)=g.graph.degree v+g.deficit v := by
  change (multiLeafGraph g.graph mate).degree (.inl v)+
    (g.deficit v-multiLeafMultiplicity mate v)=_
  rw [multiLeafGraph_degree_old]
  have hr:=hrestore v
  omega

theorem attachLeaves_deficit_sum (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v) :
    (∑a,(g.attachLeaves hd mate hrestore).deficit a)+Fintype.card L=∑v,g.deficit v := by
  rw [Fintype.sum_sum_type]
  simp only [attachLeaves,Sum.elim_inl,Sum.elim_inr,Finset.sum_const_zero,add_zero]
  rw [←multiLeafMultiplicity_sum mate,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _=>Nat.sub_add_cancel (hrestore v))

theorem attachLeaves_complexity (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v) :
    ((∑a,(g.attachLeaves hd mate hrestore).deficit a)+
      graphExcess (g.attachLeaves hd mate hrestore).graph)+Fintype.card L=
        (∑v,g.deficit v)+graphExcess g.graph := by
  have hsum:=g.attachLeaves_deficit_sum hd mate hrestore
  have hex:=multiLeafGraph_excess g.graph mate
  change _+graphExcess (multiLeafGraph g.graph mate)+_=_
  rw [hex]
  omega

theorem attachLeaves_boundaryCoefficient (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(v:V) :
    (g.attachLeaves hd mate hrestore).boundaryCoefficient (.inl v)=g.boundaryCoefficient v := by
  have hh:=g.attachLeaves_degree_deficit hd mate hrestore v
  have hreal : ((g.attachLeaves hd mate hrestore).graph.degree (.inl v):ℝ)+
      ((g.attachLeaves hd mate hrestore).deficit (.inl v):ℝ)=
      (g.graph.degree v:ℝ)+(g.deficit v:ℝ):=by exact_mod_cast hh
  unfold boundaryCoefficient
  congr 1
  linarith

theorem attachLeaves_extensionMatrix_principal (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ) :
    ((g.attachLeaves hd mate hrestore).extensionMatrix q z).submatrix Sum.inl Sum.inl=
      g.extensionMatrix q z := by
  ext i j
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,boundaryDiagonal,
    Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal_apply,Sum.inl.injEq]
  rw [g.attachLeaves_boundaryCoefficient hd mate hrestore i]
  simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
    attachLeaves,multiLeafGraph]

end DeficientGraph
end Finite
end LocalLaw
