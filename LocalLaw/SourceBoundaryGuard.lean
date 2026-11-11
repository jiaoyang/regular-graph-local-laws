import LocalLaw.SourceSingletonObservation
import LocalLaw.ResamplingGeometricGood

/-! # The actual far-boundary guard used by the source singleton mask

The source mask at radius R/4 places both sampled edge endpoints in the
guard at radius R/4-1. Failed masks are counted by actual endpoint fibers
over a union of original boundary-root balls, yielding a deterministic
near-boundary edge cost rather than an assumed exceptional-set bound.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance sourceBoundaryGuardDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def boundaryFarOutside (G : SimpleGraph V) (T : Set V) (h : ℕ) : Set (Tᶜ : Set V) :=
  {v | ∀ α : BoundaryOrientedEdge G T,
    (h : ℕ∞) < (outsideGraph G T).edist v (boundaryOuterEndpoint G T α)}

def boundaryFarGuard (G : SimpleGraph V) (T : Set V) (h : ℕ) : Set V :=
  Subtype.val '' boundaryFarOutside G T h

omit [Fintype V] in
theorem boundaryFarGuard_subset_complement (G : SimpleGraph V) (T : Set V) (h : ℕ) :
    boundaryFarGuard G T h ⊆ Tᶜ := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

omit [Fintype V] in
theorem mem_boundaryFarGuard (G : SimpleGraph V) (T : Set V) (h : ℕ)
    (v : (Tᶜ : Set V)) : v.val ∈ boundaryFarGuard G T h ↔ v ∈ boundaryFarOutside G T h := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact Subtype.ext heq ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

omit [Fintype V] in
theorem boundaryFarOutside_step (G : SimpleGraph V) (T : Set V) (h : ℕ)
    {b c : (Tᶜ : Set V)} (hbc : (outsideGraph G T).Adj b c)
    (hfar : b ∈ boundaryFarOutside G T (h + 1)) : c ∈ boundaryFarOutside G T h := by
  intro α
  apply lt_of_not_ge
  intro hnear
  have hdist : (outsideGraph G T).edist b (boundaryOuterEndpoint G T α) ≤ ((h + 1 : ℕ) : ℕ∞) := by
    apply (SimpleGraph.edist_triangle (G := outsideGraph G T) (u := b) (v := c)).trans
    exact (add_le_add (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hbc)) hnear).trans_eq
      (by exact_mod_cast (show 1 + h = h + 1 by omega))
  exact (not_lt_of_ge hdist) (hfar α)

omit [Fintype V] in
theorem source_far_edge_guard (G : SimpleGraph V) (T : Set V) (R : ℕ) (hR : 1 ≤ R / 4)
    (e : OutsideOrientedEdge G T)
    (hfar : ∀ α : BoundaryOrientedEdge G T,
      ((R / 4 : ℕ) : ℕ∞) < (outsideGraph G T).edist
        ⟨e.val.1, e.property.2.1⟩ (boundaryOuterEndpoint G T α)) :
    e.val.1 ∈ boundaryFarGuard G T (R / 4 - 1) ∧
      e.val.2 ∈ boundaryFarGuard G T (R / 4 - 1) := by
  let b : (Tᶜ : Set V) := ⟨e.val.1, e.property.2.1⟩
  let c : (Tᶜ : Set V) := ⟨e.val.2, e.property.2.2⟩
  have hb : b ∈ boundaryFarOutside G T (R / 4) := hfar
  constructor
  · exact (mem_boundaryFarGuard G T _ b).mpr (fun α =>
      (ENat.coe_le_coe.mpr (Nat.sub_le _ _)).trans_lt (hb α))
  · apply (mem_boundaryFarGuard G T _ c).mpr
    apply boundaryFarOutside_step G T (R / 4 - 1) (show (outsideGraph G T).Adj b c from e.property.1)
    simpa only [Nat.sub_add_cancel hR] using hb

theorem not_boundaryFarOutside_mem_root_balls (G : SimpleGraph V) (T : Set V) (h : ℕ)
    (v : (Tᶜ : Set V)) (hnear : v ∉ boundaryFarOutside G T h) :
    v.val ∈ graphSetBall G (boundaryExteriorRoots G T) h := by
  classical
  have hex : ∃ α : BoundaryOrientedEdge G T,
      (outsideGraph G T).edist v (boundaryOuterEndpoint G T α) ≤ (h : ℕ∞) := by
    by_contra hnone
    apply hnear
    intro α
    exact lt_of_not_ge (fun h => hnone ⟨α, h⟩)
  obtain ⟨α, hα⟩ := hex
  exact boundary_near_mem_boundary_root_ball G T h α v (by rwa [SimpleGraph.edist_comm])

namespace RegularGraph
variable {N d : ℕ}

theorem boundary_root_balls_card_bound (g : RegularGraph N d) (T : Set (Fin N)) (h : ℕ) (hd : 3 ≤ d) :
    (graphSetBall g.graph (boundaryExteriorRoots g.graph T) h).toFinset.card ≤
      Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ h) := by
  have hroots : Nat.card (boundaryExteriorRoots g.graph T : Set (Fin N)) ≤
      Nat.card (BoundaryOrientedEdge g.graph T) := by
    have hcard : Nat.card (boundaryExteriorRoots g.graph T : Set (Fin N)) =
        (boundaryExteriorRoots g.graph T).card := by
      simpa only [Finset.toFinset_coe, Nat.card_eq_fintype_card] using
        (Set.toFinset_card (s := (boundaryExteriorRoots g.graph T : Set (Fin N)))).symm
    rw [hcard]
    exact boundaryExteriorRoots_card g.graph T
  have hh := graphSetBall_card_sharp g.graph (boundaryExteriorRoots g.graph T) d h hd
    (fun v => (g.regular.degree_eq v).le)
  have hcard : (graphSetBall g.graph (boundaryExteriorRoots g.graph T) h).toFinset.card =
      Nat.card (graphSetBall g.graph (boundaryExteriorRoots g.graph T) h) := by
    simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [hcard]
  exact hh.trans (Nat.mul_le_mul_right _ hroots)

theorem outside_edges_failing_boundary_mask_count (g : RegularGraph N d) (T : Set (Fin N))
    (h : ℕ) (hd : 3 ≤ d) :
    Nat.card {e : OutsideOrientedEdge g.graph T //
      (⟨e.val.1, e.property.2.1⟩ : (Tᶜ : Set (Fin N))) ∉ boundaryFarOutside g.graph T h} ≤
      Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ h) * d := by
  let B := (graphSetBall g.graph (boundaryExteriorRoots g.graph T) h).toFinset
  let f : {e : OutsideOrientedEdge g.graph T //
      (⟨e.val.1, e.property.2.1⟩ : (Tᶜ : Set (Fin N))) ∉ boundaryFarOutside g.graph T h} →
      {e : OutsideOrientedEdge g.graph T // outsideEdgeFirst g.graph T e ∈ B} :=
    fun e => ⟨e.val, Set.mem_toFinset.mpr (not_boundaryFarOutside_mem_root_balls g.graph T h _ e.property)⟩
  have hf : Function.Injective f := by
    intro a b he
    have hraw : a.val = b.val := congrArg
      (fun z : {e : OutsideOrientedEdge g.graph T // outsideEdgeFirst g.graph T e ∈ B} => z.val) he
    exact Subtype.ext hraw
  apply (Nat.card_le_card_of_injective f hf).trans
  apply (endpoint_preimage_card_bound (outsideEdgeFirst g.graph T) B d
    (fun v => (outsideEdgeFirst_fiber_card g.graph T v).trans (by rw [g.regular.degree_eq v]))).trans
  exact Nat.mul_le_mul_right d (g.boundary_root_balls_card_bound T h hd)

end RegularGraph
end LocalLaw
