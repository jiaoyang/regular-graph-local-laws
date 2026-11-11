import LocalLaw.SampleTreeNeighborhood
import LocalLaw.ResamplingEdgeAgreement

/-!
# The actual full resampling equals one switch on an isolated neighborhood

All other switching footprints miss a good sampled-edge neighborhood.
The full original-data schedule is without repetitions, so its adjacency
rows there equal exactly the selected coordinate's single switch. This
provides the actual local edge identities for the large tree-gadget proof.
-/

noncomputable section
namespace LocalLaw

local instance isolatedSwitchNeighborhoodDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem SwitchingQuad.apply_adj_congr (q : SwitchingQuad V) (G H : SimpleGraph V)
    {x y : V} (h : G.Adj x y ↔ H.Adj x y) :
    (q.apply G).Adj x y ↔ (q.apply H).Adj x y := by
  simp only [SwitchingQuad.apply, simpleSwitch, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  exact or_congr (and_congr h Iff.rfl) Iff.rfl

theorem applySwitches_adj_outside_footprints (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    {x y : V} (hout : ∀ q ∈ L, ¬ q.footprint.Adj x y) :
    (applySwitches L G).Adj x y ↔ G.Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
    exact (ih (q.apply G) (fun p hp => hout p (List.mem_cons_of_mem _ hp))).trans
      (q.adj_outside_footprint G (hout q List.mem_cons_self))

theorem applySwitches_adj_single_footprint (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (p : SwitchingQuad V) (hL : L.Nodup) (hp : p ∈ L) {x y : V}
    (hout : ∀ q ∈ L, q ≠ p → ¬ q.footprint.Adj x y) :
    (applySwitches L G).Adj x y ↔ (p.apply G).Adj x y := by
  induction L generalizing G with
  | nil => simp at hp
  | cons q L ih =>
    obtain ⟨hqnot, htail⟩ := List.nodup_cons.mp hL
    by_cases hqp : q = p
    · subst q
      apply applySwitches_adj_outside_footprints L (p.apply G)
      intro q hq
      apply hout q (List.mem_cons_of_mem _ hq)
      intro h
      exact hqnot (h ▸ hq)
    · have hpTail : p ∈ L := (List.mem_cons.mp hp).resolve_left (fun h => hqp h.symm)
      have hq := q.adj_outside_footprint G (hout q List.mem_cons_self hqp)
      exact (ih (q.apply G) htail hpTail
        (fun v hv hne => hout v (List.mem_cons_of_mem _ hv) hne)).trans
        (p.apply_adj_congr (q.apply G) G hq)

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

theorem quad_injective (s : LabelledResamplingState V T ι) : Function.Injective s.quad := by
  intro i j h
  apply s.boundary.injective
  apply Subtype.ext
  exact Prod.ext (congrArg SwitchingQuad.a h) (congrArg SwitchingQuad.b h)

theorem selectedQuads_nodup (s : LabelledResamplingState V T ι) (selector : ℕ)
    (L : List ι) (hL : L.Nodup) : (s.selectedQuads selector L).Nodup := by
  unfold selectedQuads
  exact (hL.filter _).map s.quad_injective

variable [Fintype ι]

theorem fullResample_incident_eq_single (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : ι) (hi : s.Eligible selector i) (W : Set V)
    (hWT : Disjoint W T) (hother : ∀ j, j ≠ i → Disjoint W (s.quad j).exterior)
    {x y : V} (hx : x ∈ W) :
    (s.fullResample selector).graph.Adj x y ↔ ((s.quad i).apply s.graph).Adj x y := by
  let L := s.selectedQuads selector (Finset.univ : Finset ι).toList
  have hgraph := congrArg (fun G : SimpleGraph V => G.Adj x y) (s.fullResample_graph_eq_applySwitches selector)
  apply hgraph.to_iff.trans
  have hnodup : L.Nodup := s.selectedQuads_nodup selector _ (Finset.nodup_toList _)
  have hmem : s.quad i ∈ L := (s.mem_selectedQuads selector _ _).mpr
    ⟨i, by simp, hi, rfl⟩
  apply applySwitches_adj_single_footprint L s.graph (s.quad i) hnodup hmem
  intro q hq hqi hfoot
  obtain ⟨j, _, hj, hqj⟩ := (s.mem_selectedQuads selector _ q).mp hq
  have hji : j ≠ i := fun h => hqi (h ▸ hqj.symm)
  have hsupport := q.footprint_left_mem_support hfoot
  rw [← hqj] at hsupport
  change x = (s.quad j).a ∨ x ∈ (s.quad j).exterior at hsupport
  rcases hsupport with hroot | hext
  · exact Set.disjoint_left.mp hWT hx (hroot ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary j))
  · exact Set.disjoint_left.mp (hother j hji) hx hext

variable [Fintype V]

/-- Good sampled pair neighborhoods are affected by exactly their own
actual accepted switching, including all incident edges. -/
theorem fullResample_good_sample_neighborhood_incident (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    {x y : V} (hx : x ∈ pairBallVertices s.graph
      (s.samples (s.boundary i)).val.1 (s.samples (s.boundary i)).val.2 R) :
    (s.fullResample selector).graph.Adj x y ↔ ((s.quad i).apply s.graph).Adj x y := by
  let W := pairBallVertices s.graph (s.samples (s.boundary i)).val.1 (s.samples (s.boundary i)).val.2 R
  have hWT : Disjoint W T := Set.disjoint_left.mpr
    (sampled_ambient_pair_ball_avoids_interior s.graph T R s.samples (s.boundary i) hmark)
  have hothers : ∀ j, j ≠ i → Disjoint W (s.quad j).exterior := by
    intro j hji
    apply Set.disjoint_left.mpr
    intro v hv hext
    have hout : v ∉ T := fun ht => Set.disjoint_left.mp
      (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary j)) hext ht
    exact sampled_ambient_pair_ball_avoids_other_triples s.graph T R s.samples (s.boundary i)
      hmark hother (s.boundary j) (fun h => hji (s.boundary.injective h)) ⟨v, hout⟩ hext hv
  exact s.fullResample_incident_eq_single selector i hi W hWT hothers hx

end LabelledResamplingState
end LocalLaw
