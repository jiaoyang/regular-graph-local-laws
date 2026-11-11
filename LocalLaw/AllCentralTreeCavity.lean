import LocalLaw.EligibleBoundaryCavity
import LocalLaw.CentralUniqueAttachment

/-! # Every central boundary branch is a cavity tree in a genuine tree ball -/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance allCentralTreeCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem central_reachable_from_root_ball (G : SimpleGraph V) (T : Set V) (r : ℕ)
    (a : BoundaryOrientedEdge G T) (v : (Tᶜ : Set V))
    (hv : v ∈ graphBallVertices (outsideGraph G T) (boundaryOuterEndpoint G T a) r) :
    (centralBoundaryGraph G T r).Reachable (centralBoundaryCenter G T r a)
      ⟨v, ⟨boundaryOuterEndpoint G T a, ⟨a, rfl⟩, hv⟩⟩ := by
  let H := outsideGraph G T
  let f : graphBall H (boundaryOuterEndpoint G T a) r →g centralBoundaryGraph G T r :=
    { toFun := fun x => ⟨x.val, ⟨boundaryOuterEndpoint G T a, ⟨a, rfl⟩, x.property⟩⟩
      map_rel' := fun h => h }
  exact ((graphBall_connected H _ r).preconnected
    (cavityBallRoot H (boundaryOuterEndpoint G T a) r) ⟨v, hv⟩).map f

theorem central_ball_isTree_of_original_ball (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall G o R).IsTree)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    (graphBall (outsideGraph G (graphBallVertices G o ell))
      (boundaryOuterEndpoint G (graphBallVertices G o ell) a) r).IsTree := by
  let T := graphBallVertices G o ell
  let H := outsideGraph G T
  let f : graphBall H (boundaryOuterEndpoint G T a) r →g graphBall G o R :=
    { toFun := fun x => ⟨x.val.val, centralBoundaryVertices_subset_original_ball G o ell r R hmargin
        x.val ⟨boundaryOuterEndpoint G T a, ⟨a, rfl⟩, x.property⟩⟩
      map_rel' := fun h => h }
  constructor
  · exact graphBall_connected _ _ _
  · intro v p hp
    exact hTree.IsAcyclic (p.map f) (hp.map (fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : graphBallVertices G o R => x.val) h))))

theorem tree_central_boundary_label_unique [Fintype V] (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall G o R).IsTree)
    (a b : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (hreach : (centralBoundaryGraph G (graphBallVertices G o ell) r).Reachable
      (centralBoundaryCenter G (graphBallVertices G o ell) r a)
      (centralBoundaryCenter G (graphBallVertices G o ell) r b)) : b = a := by
  let T := graphBallVertices G o ell
  let c := (centralBoundaryGraph G T r).connectedComponentMk (centralBoundaryCenter G T r a)
  have hbudget : graphBallExcess G o R ≤ 0 := (tree_graphExcess_zero _ hTree).le
  have hcard := central_boundary_fiber_card_bound G o ell r R 0 hmargin hbudget c
  change Nat.card (CentralBoundaryFiber G T r c) ≤ 0 + 1 at hcard
  have hnonempty : Nonempty (CentralBoundaryFiber G T r c) := ⟨⟨a, rfl⟩⟩
  have hfinite : Finite (CentralBoundaryFiber G T r c) :=
    Finite.of_injective (fun x : CentralBoundaryFiber G T r c => x.val) Subtype.val_injective
  have hpos := Nat.card_pos_iff.mpr ⟨hnonempty, hfinite⟩
  have hone : Nat.card (CentralBoundaryFiber G T r c) = 1 := by omega
  have hsub := (Nat.card_eq_one_iff_unique.mp hone).1
  have hb : centralBoundaryCenter G T r b ∈ c.supp := (SimpleGraph.ConnectedComponent.sound hreach).symm
  exact congrArg (fun x : CentralBoundaryFiber G T r c => x.val) (hsub.elim ⟨b, hb⟩ ⟨a, rfl⟩)

theorem tree_boundary_label_unique_in_ball [Fintype V] (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall G o R).IsTree)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (v : ((graphBallVertices G o ell)ᶜ : Set V))
    (hv : v ∈ graphBallVertices (outsideGraph G (graphBallVertices G o ell))
      (boundaryOuterEndpoint G (graphBallVertices G o ell) a) r)
    (b : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (hb : boundaryOuterEndpoint G (graphBallVertices G o ell) b = v) : b = a := by
  have hr := central_reachable_from_root_ball G (graphBallVertices G o ell) r a v hv
  have he : (⟨v, ⟨boundaryOuterEndpoint G (graphBallVertices G o ell) a, ⟨a, rfl⟩, hv⟩⟩ :
      centralBoundaryVertices G (graphBallVertices G o ell) r) =
      centralBoundaryCenter G (graphBallVertices G o ell) r b := Subtype.ext hb.symm
  rw [he] at hr
  exact tree_central_boundary_label_unique G o ell r R hmargin hTree a b hr

theorem tree_central_component_subset_ball [Fintype V] (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall G o R).IsTree)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (v : centralBoundaryVertices G (graphBallVertices G o ell) r)
    (hv : v ∈ ((centralBoundaryGraph G (graphBallVertices G o ell) r).connectedComponentMk
      (centralBoundaryCenter G (graphBallVertices G o ell) r a)).supp) :
    v.val ∈ graphBallVertices (outsideGraph G (graphBallVertices G o ell))
      (boundaryOuterEndpoint G (graphBallVertices G o ell) a) r := by
  obtain ⟨u, ⟨b, rfl⟩, hb⟩ := v.property
  have hba := central_reachable_from_root_ball G (graphBallVertices G o ell) r b v.val hb
  have haa : (centralBoundaryGraph G (graphBallVertices G o ell) r).Reachable
      (centralBoundaryCenter G (graphBallVertices G o ell) r a) v :=
    SimpleGraph.ConnectedComponent.exact hv.symm
  have he := tree_central_boundary_label_unique G o ell r R hmargin hTree a b (haa.trans hba.symm)
  simpa only [he] using hb

theorem tree_central_ball_cut [Fintype V] (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall G o R).IsTree)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    ∀ x : centralBoundaryVertices G (graphBallVertices G o ell) r,
      x.val ∈ graphBallVertices (outsideGraph G (graphBallVertices G o ell))
        (boundaryOuterEndpoint G (graphBallVertices G o ell) a) r →
      ∀ y : centralBoundaryVertices G (graphBallVertices G o ell) r,
        y.val ∉ graphBallVertices (outsideGraph G (graphBallVertices G o ell))
          (boundaryOuterEndpoint G (graphBallVertices G o ell) a) r →
        ¬(centralBoundaryGraph G (graphBallVertices G o ell) r).Adj x y := by
  intro x hx y hy hxy
  have hxreach := central_reachable_from_root_ball G (graphBallVertices G o ell) r a x.val hx
  have hreach : (centralBoundaryGraph G (graphBallVertices G o ell) r).Reachable
      (centralBoundaryCenter G (graphBallVertices G o ell) r a) y := hxreach.trans hxy.reachable
  exact hy (tree_central_component_subset_ball G o ell r R hmargin hTree a y
    (SimpleGraph.ConnectedComponent.sound hreach).symm)

namespace RegularGraph
variable {N d : ℕ}

theorem tree_boundary_one_root_deficit (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (v : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hv : v ∈ graphBallVertices (outsideGraph g.graph (graphBallVertices g.graph o ell))
      (boundaryOuterEndpoint g.graph (graphBallVertices g.graph o ell) a) r) :
    (g.deficient.delete (graphBallVertices g.graph o ell)).deficit v =
      if v = boundaryOuterEndpoint g.graph (graphBallVertices g.graph o ell) a then 1 else 0 := by
  let T := graphBallVertices g.graph o ell
  have hlabel (t : {t : T // g.graph.Adj t.val v.val}) :
      (⟨(t.val.val, v.val), t.property, t.val.property, v.property⟩ : BoundaryOrientedEdge g.graph T) = a :=
    tree_boundary_label_unique_in_ball g.graph o ell r R hmargin hTree a v hv _ rfl
  rw [g.deficient.delete_deficit_eq_removed_neighbors]
  change 0 + Nat.card {t : T // g.graph.Adj t.val v.val} = _
  rw [zero_add]
  by_cases he : v = boundaryOuterEndpoint g.graph T a
  · rw [if_pos he]
    subst v
    let canonical : {t : T // g.graph.Adj t.val (boundaryOuterEndpoint g.graph T a).val} :=
      ⟨⟨a.val.1, a.property.2.1⟩, a.property.1⟩
    letI : Unique {t : T // g.graph.Adj t.val (boundaryOuterEndpoint g.graph T a).val} :=
      ⟨⟨canonical⟩, fun t => Subtype.ext (Subtype.ext
        (congrArg (fun b : BoundaryOrientedEdge g.graph T => b.val.1) (hlabel t)))⟩
    exact Nat.card_unique
  · rw [if_neg he]
    letI : IsEmpty {t : T // g.graph.Adj t.val v.val} := ⟨fun t =>
      he (congrArg (boundaryOuterEndpoint g.graph T) (hlabel t))⟩
    exact Nat.card_of_isEmpty

theorem tree_boundary_ball_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    let H := outsideGraph g.graph T
    ((g.deficient.delete T).restrict (graphBallVertices H (boundaryOuterEndpoint g.graph T a) r)).extensionGreen q z
      (cavityBallRoot H (boundaryOuterEndpoint g.graph T a) r)
      (cavityBallRoot H (boundaryOuterEndpoint g.graph T a) r) = cavityIterate z q (r + 1) := by
  dsimp only
  exact (g.deficient.delete (graphBallVertices g.graph o ell)).homogeneous_cavity_ball_diagonal hd _ r
    (central_ball_isTree_of_original_ball g.graph o ell r R hmargin hTree a)
    (fun v hv => g.tree_boundary_one_root_deficit o ell r R hmargin hTree a v hv)
    (fun v _ => g.deleted_degree_deficit_saturated _ v) q z hz hq

theorem tree_central_boundary_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    ((g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)).extensionGreen q z
      (centralBoundaryCenter g.graph T r a) (centralBoundaryCenter g.graph T r a) = cavityIterate z q (r + 1) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let B := graphBallVertices H (boundaryOuterEndpoint g.graph T a) r
  let K := centralBoundaryVertices g.graph T r
  let F : Set K := {v | v.val ∈ B}
  let M := (g.deficient.delete T).restrict K
  let MB := (g.deficient.delete T).restrict B
  have hBK : B ⊆ K := fun v hv => ⟨boundaryOuterEndpoint g.graph T a, ⟨a, rfl⟩, hv⟩
  let e : (M.restrict F).graph ≃g MB.graph := inducePreimageIso H K B hBK
  let root : F := ⟨centralBoundaryCenter g.graph T r a, by
    change H.edist (boundaryOuterEndpoint g.graph T a) (boundaryOuterEndpoint g.graph T a) ≤ (r : ℕ∞)
    simp⟩
  have hcut : ∀ x ∈ F, ∀ y ∉ F, ¬M.graph.Adj x y := by
    intro x hx y hy
    exact tree_central_ball_cut g.graph o ell r R hmargin hTree a x hx y hy
  have hblock := M.restrict_extensionGreen_of_isolated hd F hcut q z hz hq
  have hiso := MB.extensionGreen_iso (M.restrict F) e (fun _ => rfl) q z
  have h₁ := congrFun (congrFun hblock root) root
  have h₂ := congrFun (congrFun hiso root) root
  exact h₁.symm.trans (h₂.symm.trans (g.tree_boundary_ball_diagonal hd o ell r R hmargin hTree a q z hz hq))

/-- Literal diagonal scalar boundary block, with every tree-model input
derived from the actual original root ball. -/
theorem tree_central_boundary_block (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (a b : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    ((g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)).extensionGreen q z
      (centralBoundaryCenter g.graph T r a) (centralBoundaryCenter g.graph T r b) =
      if a = b then cavityIterate z q (r + 1) else 0 := by
  dsimp only
  by_cases hab : a = b
  · rw [if_pos hab, ← hab]
    exact g.tree_central_boundary_diagonal hd o ell r R hmargin hTree a q z hz hq
  · rw [if_neg hab]
    let T := graphBallVertices g.graph o ell
    let M := (g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)
    let F : Set (centralBoundaryVertices g.graph T r) := {v | v.val ∈
      graphBallVertices (outsideGraph g.graph T) (boundaryOuterEndpoint g.graph T a) r}
    have hcut : ∀ x ∈ F, ∀ y ∉ F, ¬M.graph.Adj x y := by
      intro x hx y hy
      exact tree_central_ball_cut g.graph o ell r R hmargin hTree a x hx y hy
    have ha : centralBoundaryCenter g.graph T r a ∈ F := by
      change (outsideGraph g.graph T).edist (boundaryOuterEndpoint g.graph T a)
        (boundaryOuterEndpoint g.graph T a) ≤ (r : ℕ∞)
      simp
    have hb : centralBoundaryCenter g.graph T r b ∉ F := fun h =>
      hab (tree_boundary_label_unique_in_ball g.graph o ell r R hmargin hTree a
        (boundaryOuterEndpoint g.graph T b) h b rfl).symm
    exact M.extensionGreen_zero_across_cut hd F hcut q z hz hq _ ha _ hb

end RegularGraph
end LocalLaw
