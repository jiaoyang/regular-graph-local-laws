import LocalLaw.FiniteBallCover
import LocalLaw.LocalizationComponents

/-!
# Intrinsic diameter of actual deleted components

A shortest ambient walk from the cut to a component vertex supplies a short
suffix from an actual boundary root. The component is therefore covered by
one intrinsic radius-R ball per attachment edge. The proved finite-ball
cover theorem and Euler attachment bound give an excess-dependent cap.
-/

noncomputable section
namespace LocalLaw
local instance cutDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) cutDiameterComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

section Walks
variable {V : Type*} (G : SimpleGraph V)

theorem walk_last_set_entry (A : Set V) {x y : V} (p : G.Walk x y) (hy : y ∈ A) :
    (∃ hx : x ∈ A, ∃ q : (G.induce A).Walk ⟨x, hx⟩ ⟨y, hy⟩, q.length ≤ p.length) ∨
      ∃ (u : V) (_hu : u ∉ A) (v : V) (hv : v ∈ A) (_h : G.Adj u v),
        ∃ q : (G.induce A).Walk ⟨v, hv⟩ ⟨y, hy⟩, q.length + 1 ≤ p.length := by
  induction p with
  | nil => exact Or.inl ⟨hy, SimpleGraph.Walk.nil, le_rfl⟩
  | @cons x z y hxz p ih =>
    rcases ih hy with ⟨hz, q, hq⟩ | ⟨u, hu, v, hv, h, q, hq⟩
    · by_cases hx : x ∈ A
      · refine Or.inl ⟨hx, q.cons (show (G.induce A).Adj ⟨x, hx⟩ ⟨z, hz⟩ from hxz), ?_⟩
        simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hq
      · exact Or.inr ⟨x, hx, z, hz, hxz, q, by simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hq⟩
    · exact Or.inr ⟨u, hu, v, hv, h, q, hq.trans (by simp only [SimpleGraph.Walk.length_cons]; omega)⟩

end Walks

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_component_boundary_root_cover (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hS : S.Nonempty) (c : CutComponent G S)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (y : c.supp) :
    ∃ e : CutBoundaryEdge G S c, (cutComponentGraph G S c).dist (cutAttachmentRoot G S c e) y ≤ R := by
  obtain ⟨t, ht⟩ := hS
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist t y.val.val
  let A := cutComponentVertices G S c
  let φ := cutComponentFlatIso G S c
  have hyA : y.val.val ∈ A := ⟨y.val.property, y.property⟩
  have htA : t ∉ A := by rintro ⟨hn, _⟩; exact hn ht
  obtain ⟨u, hu, v, hv, huv, q, hq⟩ : ∃ (u : V) (_hu : u ∉ A) (v : V) (hv : v ∈ A) (_h : G.Adj u v),
      ∃ q : (G.induce A).Walk ⟨v, hv⟩ ⟨y.val.val, hyA⟩, q.length + 1 ≤ p.length := by
    rcases walk_last_set_entry G A p hyA with ⟨ht', q, hq⟩ | h
    · exact False.elim (htA ht')
    · exact h
  have huS : u ∈ S := by
    by_contra hn
    exact hu (cutComponentVertices_adj_closed G S c hn hv huv)
  let e : CutBoundaryEdge G S c := ⟨⟨(u, v), huv, huS, hv.1⟩, hv.2⟩
  refine ⟨e, ?_⟩
  have hdist := SimpleGraph.dist_le (q.map φ.symm.toHom)
  change (cutComponentGraph G S c).dist (cutAttachmentRoot G S c e) y ≤ _ at hdist
  rw [SimpleGraph.Walk.length_map] at hdist
  have hcap := hR t y.val.val
  omega

theorem cut_component_diameter_by_attachments (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hS : S.Nonempty) (c : CutComponent G S)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (a b : c.supp) :
    (cutComponentGraph G S c).dist a b ≤
      2 * R + (cutMultiplicity G S c - 1) * (2 * R + 1) := by
  let H := cutComponentGraph G S c
  let center : CutBoundaryEdge G S c → c.supp := cutAttachmentRoot G S c
  let radius : CutBoundaryEdge G S c → ℕ := fun _ => R
  have hcover : ∀ y : c.supp, y ∈ ballCoverVertices H center radius := by
    intro y
    obtain ⟨e, he⟩ := cut_component_boundary_root_cover G hG S hS c R hR y
    obtain ⟨p, hp⟩ := c.connected_induce_supp.exists_walk_length_eq_dist (center e) y
    exact ⟨e, (SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr (hp.trans_le he))⟩
  let aa : ballCoverVertices H center radius := ⟨a, hcover a⟩
  let bb : ballCoverVertices H center radius := ⟨b, hcover b⟩
  have hdist := ballCover_distance_bound H center radius R (fun _ => le_rfl) aa bb
  have hcut : ∀ x ∈ ballCoverVertices H center radius, ∀ y ∉ ballCoverVertices H center radius, ¬H.Adj x y := by
    intro x hx y hy
    exact False.elim (hy (hcover y))
  rw [isolated_induce_distance H (ballCoverVertices H center radius) hcut aa bb] at hdist
  simpa only [cutMultiplicity, ← Nat.card_eq_fintype_card] using hdist

theorem cut_component_diameter_bound (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hS : (G.induce S).Connected) (ω : ℕ) (hω : graphExcess G ≤ ω)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (c : CutComponent G S) (a b : c.supp) :
    (cutComponentGraph G S c).dist a b ≤ (ω + 1) * (2 * R + 1) := by
  have hSne : S.Nonempty := by obtain ⟨x⟩ := hS.nonempty; exact ⟨x.val, x.property⟩
  have hMultiplicity := component_cut_multiplicity_bound G S hG hS ω hω c
  have hdist := cut_component_diameter_by_attachments G hG S hSne c R hR a b
  have hsub : cutMultiplicity G S c - 1 ≤ ω := by omega
  have hmul := Nat.mul_le_mul_right (2 * R + 1) hsub
  exact hdist.trans (by nlinarith)

/-- All actual deleted components inherit an intrinsic diameter cap from
the ambient diameter and excess, including exceptional components. -/
theorem outside_graph_diameter_bound (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hS : (G.induce S).Connected) (ω : ℕ) (hω : graphExcess G ≤ ω)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (a b : (Sᶜ : Set V)) :
    (outsideGraph G S).dist a b ≤ (ω + 1) * (2 * R + 1) := by
  by_cases hab : (outsideGraph G S).connectedComponentMk a = (outsideGraph G S).connectedComponentMk b
  · let c := (outsideGraph G S).connectedComponentMk a
    let aa : c.supp := ⟨a, rfl⟩
    let bb : c.supp := ⟨b, hab.symm⟩
    have hh := cut_component_diameter_bound G hG S hS ω hω R hR c aa bb
    have hcut : ∀ x ∈ c.supp, ∀ y ∉ c.supp, ¬(outsideGraph G S).Adj x y := by
      intro x hx y hy hxy
      exact hy ((c.mem_supp_congr_adj hxy).mp hx)
    change ((outsideGraph G S).induce c.supp).dist aa bb ≤ _ at hh
    rw [isolated_induce_distance (outsideGraph G S) c.supp hcut aa bb] at hh
    exact hh
  · have hnot : ¬(outsideGraph G S).Reachable a b := fun h => hab (SimpleGraph.ConnectedComponent.sound h)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hnot]
    exact Nat.zero_le _

end LocalLaw
