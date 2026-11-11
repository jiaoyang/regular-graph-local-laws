import LocalLaw.LocalExcessGeometry

/-! # Connected finite ball exhaustions of a locally finite graph

The ambient vertex type is arbitrary. No `Fintype V` or countability
assumption is used: finite breadth-first expansion follows from actual local
finiteness, and connectedness makes these finite induced balls cover V.
-/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance allCoreExhaustionDecidable (p:Prop):Decidable p:=Classical.propDecidable p

variable {V:Type*} [DecidableEq V] (G:SimpleGraph V) [G.LocallyFinite]

instance allCoreInducedLocallyFinite (S:Set V):(G.induce S).LocallyFinite:=fun v=>
  Fintype.ofInjective (fun w:(G.induce S).neighborSet v=>(⟨w.val.val,w.property⟩:G.neighborSet v.val))
    (fun _ _ h=>Subtype.ext (Subtype.ext (congrArg (fun w:G.neighborSet v.val=>w.val) h)))

/-- Literal finite breadth-first search, retaining all preceding vertices. -/
def allCoreBallFinset (root:V):ℕ→Finset V
  | 0=>{root}
  | n+1=>allCoreBallFinset root n ∪
      (allCoreBallFinset root n).biUnion (fun v=>G.neighborFinset v)

@[simp] theorem allCoreBallFinset_zero (root:V):allCoreBallFinset G root 0={root}:=rfl

@[simp] theorem allCoreBallFinset_succ (root:V)(n:ℕ):
    allCoreBallFinset G root (n+1)=allCoreBallFinset G root n ∪
      (allCoreBallFinset G root n).biUnion (fun v=>G.neighborFinset v):=rfl

theorem mem_allCoreBallFinset_iff (root v:V)(n:ℕ):
    v∈allCoreBallFinset G root n ↔ G.edist root v ≤ (n:ℕ∞):=by
  induction n generalizing v with
  | zero =>
    simp only [allCoreBallFinset_zero,Finset.mem_singleton,Nat.cast_zero]
    constructor
    · intro h;subst v;simp
    · intro h
      exact (SimpleGraph.edist_eq_zero_iff.mp (le_antisymm h bot_le)).symm
  | succ n ih =>
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv|hv
      · exact ((ih v).mp hv).trans (ENat.coe_le_coe.mpr (Nat.le_succ n))
      · obtain ⟨u,hu,huv⟩:=Finset.mem_biUnion.mp hv
        have ha:G.Adj u v:=(SimpleGraph.mem_neighborFinset G u v).mp huv
        have hu':G.edist root u ≤ (n:ℕ∞):=(ih u).mp hu
        calc
          G.edist root v ≤ G.edist root u+G.edist u v:=G.edist_triangle
          _ ≤ (n:ℕ∞)+1:=add_le_add hu' (SimpleGraph.edist_eq_one_iff_adj.mpr ha).le
          _=((n+1:ℕ):ℕ∞):=by norm_cast
    · intro hv
      have hb:v∈graphSetBall G {root} (n+1):=⟨root,by simp,hv⟩
      rcases graphSetBall_succ_subset G {root} n hb with hv|⟨u,hu,huv⟩
      · obtain ⟨s,hs,hsv⟩:=hv
        have hs':s=root:=Set.mem_singleton_iff.mp hs
        subst s
        exact Finset.mem_union_left _ ((ih v).mpr hsv)
      · obtain ⟨s,hs,hsu⟩:=hu
        have hs':s=root:=Set.mem_singleton_iff.mp hs
        subst s
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨u,(ih u).mpr hsu,
          (SimpleGraph.mem_neighborFinset G u v).mpr huv⟩

/-- The finite BFS set is the exact metric ball, not a larger exhaustion. -/
theorem allCoreBallFinset_set (root:V)(n:ℕ):
    (↑(allCoreBallFinset G root n):Set V)=graphBallVertices G root n:=by
  ext v
  exact mem_allCoreBallFinset_iff G root v n

theorem allCoreBallFinset_monotone (root:V):Monotone (allCoreBallFinset G root):=by
  intro n m hnm v hv
  exact (mem_allCoreBallFinset_iff G root v m).mpr
    (((mem_allCoreBallFinset_iff G root v n).mp hv).trans (ENat.coe_le_coe.mpr hnm))

theorem allCoreBallFinset_root_mem (root:V)(n:ℕ):root∈allCoreBallFinset G root n:=
  (mem_allCoreBallFinset_iff G root root n).mpr (by simp)

/-- Every finite approximant is connected even if the ambient graph is not. -/
theorem allCoreBallFinset_induce_connected (root:V)(n:ℕ):
    (G.induce (↑(allCoreBallFinset G root n):Set V)).Connected:=by
  rw [allCoreBallFinset_set]
  exact graphBall_connected G root n

theorem allCoreBallFinset_neighbor_mem (root:V)(n:ℕ){v w:V}
    (hv:v∈allCoreBallFinset G root n)(hvw:G.Adj v w):
    w∈allCoreBallFinset G root (n+1):=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨v,hv,(SimpleGraph.mem_neighborFinset G v w).mpr hvw⟩)

/-- Connectedness supplies a finite stage for every ambient vertex. -/
theorem allCoreBallFinset_covers (hconn:G.Connected)(root v:V):
    ∃n:ℕ,v∈allCoreBallFinset G root n:=by
  obtain ⟨p⟩:=hconn root v
  exact ⟨p.length,(mem_allCoreBallFinset_iff G root v p.length).mpr (SimpleGraph.edist_le p)⟩

theorem allCoreBallFinset_eventually_mem (hconn:G.Connected)(root v:V):
    ∀ᶠ n:ℕ in atTop,v∈allCoreBallFinset G root n:=by
  obtain ⟨n,hn⟩:=allCoreBallFinset_covers G hconn root v
  exact eventually_atTop.mpr ⟨n,fun m hm=>allCoreBallFinset_monotone G root hm hn⟩

/-- Eventually a vertex and all of its ambient neighbors are retained. -/
theorem allCoreBallFinset_eventually_star (hconn:G.Connected)(root v:V):
    ∀ᶠ n:ℕ in atTop,v∈allCoreBallFinset G root n ∧
      ∀w,G.Adj v w→w∈allCoreBallFinset G root n:=by
  obtain ⟨n,hn⟩:=allCoreBallFinset_covers G hconn root v
  apply eventually_atTop.mpr
  refine ⟨n+1,fun m hm=>⟨allCoreBallFinset_monotone G root (by omega) hn,?_⟩⟩
  intro w hw
  exact allCoreBallFinset_monotone G root hm (allCoreBallFinset_neighbor_mem G root n hn hw)

theorem allCoreBallFinset_eventually_finset (hconn:G.Connected)(root:V)(F:Finset V):
    ∀ᶠ n:ℕ in atTop,F⊆allCoreBallFinset G root n:=by
  induction F using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (fun _=>Finset.empty_subset _)
  | @insert v F hv ih =>
    filter_upwards [ih,allCoreBallFinset_eventually_mem G hconn root v] with n hF hv
    exact Finset.insert_subset_iff.mpr ⟨hv,hF⟩

/-- Finite-support tests and every incident edge eventually lie inside one
connected finite approximant. -/
theorem allCoreBallFinset_eventually_closed_finset (hconn:G.Connected)(root:V)(F:Finset V):
    ∀ᶠ n:ℕ in atTop,F⊆allCoreBallFinset G root n ∧
      ∀v∈F,∀w,G.Adj v w→w∈allCoreBallFinset G root n:=by
  filter_upwards [allCoreBallFinset_eventually_finset G hconn root
    (F∪F.biUnion (fun v=>G.neighborFinset v))] with n hN
  constructor
  · intro v hv
    exact hN (Finset.mem_union_left _ hv)
  · intro v hv w hvw
    exact hN (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨v,hv,(SimpleGraph.mem_neighborFinset G v w).mpr hvw⟩))

/-- Retaining an entire ambient star preserves its actual degree. -/
def retainedNeighborEquiv (S:Set V)(v:S)(hall:∀w,G.Adj v.val w→w∈S):
    (G.induce S).neighborSet v ≃ G.neighborSet v.val where
  toFun w:=⟨w.val.val,w.property⟩
  invFun w:=⟨⟨w.val,hall w.val w.property⟩,w.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [DecidableEq V] in
theorem induce_degree_eq_of_star (S:Set V)(v:S)(hall:∀w,G.Adj v.val w→w∈S):
    (G.induce S).degree v=G.degree v.val:=by
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
  exact Nat.card_congr (retainedNeighborEquiv G S v hall)

theorem allCoreBallFinset_eventually_degree (hconn:G.Connected)(root v:V):
    ∀ᶠ n:ℕ in atTop,∀hv:v∈allCoreBallFinset G root n,
      (G.induce (↑(allCoreBallFinset G root n):Set V)).degree ⟨v,hv⟩=G.degree v:=by
  filter_upwards [allCoreBallFinset_eventually_star G hconn root v] with n hn
  intro hv
  exact induce_degree_eq_of_star G (↑(allCoreBallFinset G root n):Set V) ⟨v,hv⟩ hn.2

/-- A root-free existence form for approximation arguments. The sequence
covers every finite support together with all its incident edges. -/
theorem exists_connected_finite_exhaustion (hconn:G.Connected):
    ∃ S:ℕ→Finset V,Monotone S ∧
      (∀n,(G.induce (↑(S n):Set V)).Connected) ∧
      (∀F:Finset V,∀ᶠ n:ℕ in atTop,F⊆S n ∧∀v∈F,∀w,G.Adj v w→w∈S n):=by
  obtain ⟨root⟩:=hconn.nonempty
  exact ⟨allCoreBallFinset G root,allCoreBallFinset_monotone G root,
    allCoreBallFinset_induce_connected G root,allCoreBallFinset_eventually_closed_finset G hconn root⟩

end SpectralConsequences
