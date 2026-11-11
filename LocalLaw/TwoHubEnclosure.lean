import LocalLaw.TwoHubMetric

/-! A component of an old set with two hubs has a genuine ambient center. -/
noncomputable section
namespace LocalLaw
local instance twoHubEnclosureDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V W : Type}

theorem twoHub_any_center_enclosure (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (hl : l.val ∈ L) (hm : m.val ∈ M) (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c → H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L →
      H.edist (f l) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u l)
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M →
      H.edist (f m) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u m)
    (a b : twoHubVertices K L M) (ha : a = l ∨ a = m)
    (hr : (G.induce (twoHubVertices K L M)).Reachable a b) :
    H.edist (f a) (f b) ≤ ((3*r+2*D+3 : ℕ) : ℕ∞) := by
  have haHub : a.val ∈ L ∪ M := ha.elim (fun h => Or.inl (h ▸ hl)) (fun h => Or.inr (h ▸ hm))
  obtain ⟨center,hc,hd,hreach⟩ := twoHub_entry_center G K L M H f l m D r hK hL hM b a haHub hr.symm
  have hrcc := hr.trans hreach
  have hcent : H.edist (f a) (f center) ≤ ((2*r+D+2 : ℕ) : ℕ∞) := by
    rcases ha with ha | ha <;> rcases hc with hc | hc
    · rw [ha,hc]; simp
    · rw [ha,hc]
      exact twoHub_centers_edist G K L M H f l m hl hm D r hK
        (fun u hu => (hL u hu).1) (fun u hu => (hM u hu).1) (by simpa only [ha,hc] using hrcc)
    · rw [ha,hc]
      simpa only [SimpleGraph.edist_comm] using twoHub_centers_edist G K L M H f l m hl hm D r hK
        (fun u hu => (hL u hu).1) (fun u hu => (hM u hu).1) (by simpa only [ha,hc] using hrcc.symm)
    · rw [ha,hc]; simp
  have hd' : H.edist (f center) (f b) ≤ ((D+r+1 : ℕ) : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using hd
  exact ((SimpleGraph.edist_triangle (G := H) (u := f a) (v := f center) (w := f b)).trans
    (add_le_add hcent hd')).trans_eq (by push_cast; ring)

/-- Each actual augmented component has a center and an ambient enclosure.
Old components not meeting a hub retain their old enclosure. -/
theorem twoHub_component_enclosure (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (hl : l.val ∈ L) (hm : m.val ∈ M) (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c → H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L →
      H.edist (f l) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u l)
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M →
      H.edist (f m) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u m)
    (c : (G.induce (twoHubVertices K L M)).ConnectedComponent) :
    ∃ a : twoHubVertices K L M, a ∈ c.supp ∧
      ∀ b ∈ c.supp, H.edist (f a) (f b) ≤ ((3*r+2*D+3 : ℕ) : ℕ∞) := by
  by_cases hlc : l ∈ c.supp
  · refine ⟨l,hlc,fun b hb => ?_⟩
    exact twoHub_any_center_enclosure G K L M H f l m hl hm D r hK hL hM l b (Or.inl rfl)
      (SimpleGraph.ConnectedComponent.exact (hlc.trans hb.symm))
  by_cases hmc : m ∈ c.supp
  · refine ⟨m,hmc,fun b hb => ?_⟩
    exact twoHub_any_center_enclosure G K L M H f l m hl hm D r hK hL hM m b (Or.inr rfl)
      (SimpleGraph.ConnectedComponent.exact (hmc.trans hb.symm))
  let a : c.supp := Classical.choice c.connected_induce_supp.nonempty
  refine ⟨a.val,a.property,fun b hb => ?_⟩
  have hr : (G.induce (twoHubVertices K L M)).Reachable a.val b :=
    SimpleGraph.ConnectedComponent.exact (a.property.trans hb.symm)
  have hn : ¬∃ v : twoHubVertices K L M, v.val ∈ L ∪ M ∧
      (G.induce (twoHubVertices K L M)).Reachable a.val v := by
    rintro ⟨v,hv,hrv⟩
    rcases hv with hv | hv
    · have hrl := hrv.trans (hL v hv).2
      exact hlc ((SimpleGraph.ConnectedComponent.sound hrl).symm.trans a.property)
    · have hrm := hrv.trans (hM v hv).2
      exact hmc ((SimpleGraph.ConnectedComponent.sound hrm).symm.trans a.property)
  obtain ⟨cc,hac,hbc⟩ := twoHub_no_hub_same_component G K L M a.val b hr hn
  exact (hK cc a.val b hac hbc).trans (ENat.coe_le_coe.mpr (by omega))

end LocalLaw
