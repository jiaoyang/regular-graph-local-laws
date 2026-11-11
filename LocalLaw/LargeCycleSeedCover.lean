import LocalLaw.LastChangedEdge
import LocalLaw.GoodSamplePathSeeds
import LocalLaw.GoodSampleCycleBranches
import LocalLaw.BadSampleAddedEdges

/-! # An actual finite seed cover for switched half-radius cycles

The seeds are the center and the original switching vertices at exceptional
sample labels or labels whose actual switched outside triple is near the
center. A last-changed-edge decomposition, not an assumed localization,
places every short-cycle vertex in an original ball around one of these
seeds. A good sampleward last edge is ruled out by its split tree patch.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
namespace LabelledResamplingState

local instance largeCycleSeedCoverDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

def exceptionalSeedLabels (s : LabelledResamplingState V T ι) (R : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => s.boundary i ∈ sampleExceptionalIndices s.graph T R s.samples)

def nearbySeedLabels (s : LabelledResamplingState V T ι) (selector r : ℕ) (center : V) : Finset ι :=
  if hx : center ∉ T then
    (s.fullResample selector).labelledTripleNearIndices r ⟨center, hx⟩ else ∅

def largeCycleSeedLabels (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (center : V) : Finset ι :=
  s.exceptionalSeedLabels R ∪ s.nearbySeedLabels selector r center

def largeCycleSeeds (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (center : V) : Finset V :=
  insert center ((s.largeCycleSeedLabels selector R r center).biUnion
    (fun i => (s.quad i).support.toFinset))

theorem mem_largeCycleSeeds_of_label (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (center : V) (i : ι)
    (hi : i ∈ s.largeCycleSeedLabels selector R r center) {v : V}
    (hv : v ∈ (s.quad i).support) : v ∈ s.largeCycleSeeds selector R r center := by
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, hi, Set.mem_toFinset.mpr hv⟩)

theorem fullResample_short_cycle_base_in_old_seed_balls
    (s : LabelledResamplingState V T ι) (selector R r : ℕ) (hr : 2 * r ≤ R)
    (center z : V) (hz : z ∈ graphBallVertices (s.fullResample selector).graph center r)
    (cycle : (s.fullResample selector).graph.Walk z z) (hcycle : cycle.IsCycle)
    (hcycleLen : cycle.length ≤ 2 * r + 1) :
    z ∈ graphSetBall s.graph (s.largeCycleSeeds selector R r center : Set V) r := by
  classical
  let H := (s.fullResample selector).graph
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top r) hz
  obtain ⟨p₀, hp₀⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  let p := p₀.bypass
  have hp : p.IsPath := p₀.bypass_isPath
  have hlen : p.length ≤ r := p₀.length_bypass_le.trans (ENat.coe_le_coe.mp (hp₀.trans_le hz))
  rcases simple_walk_common_suffix s.graph H p hp with ⟨q, hq⟩ |
      ⟨u, v, pre, hnew, hnot, hpre, suffix, hlength⟩
  · refine ⟨center, Finset.mem_insert_self _ _, ?_⟩
    exact (s.graph.edist_le (q.mapLe (show s.graph ⊓ H ≤ s.graph from inf_le_left))).trans
      (ENat.coe_le_coe.mpr (by simpa only [SimpleGraph.Walk.mapLe,
        SimpleGraph.Walk.length_map, hq] using hlen))
  · have hpreLen : pre.length ≤ r := by omega
    have hsuffixLen : suffix.length ≤ r := by omega
    have hschedule := congrArg (fun G : SimpleGraph V => G.Adj u v)
      (s.fullResample_graph_eq_applySwitches selector)
    have hactual := hschedule.to_iff.mp hnew
    rcases applySwitches_edge_provenance _ s.graph hactual with hold | ⟨q, hq, hadded⟩
    · exact False.elim (hnot hold)
    · obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
      subst q
      have seed_of_label : i ∈ s.largeCycleSeedLabels selector R r center →
          z ∈ graphSetBall s.graph (s.largeCycleSeeds selector R r center : Set V) r := by
        intro hlabel
        refine ⟨v, s.mem_largeCycleSeeds_of_label selector R r center i hlabel
          ((s.quad i).added_left_mem hadded.symm), ?_⟩
        exact (s.graph.edist_le (suffix.mapLe (show s.graph ⊓ H ≤ s.graph from inf_le_left))).trans
          (ENat.coe_le_coe.mpr (by simpa only [SimpleGraph.Walk.mapLe,
            SimpleGraph.Walk.length_map] using hsuffixLen))
      by_cases hbad : s.boundary i ∈ sampleExceptionalIndices s.graph T R s.samples
      · apply seed_of_label
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
      · have hgood := hbad
        simp only [sampleExceptionalIndices, Finset.mem_union, not_or] at hgood
        have hcases :
            ((u = (s.quad i).c ∧ v = (s.quad i).b) ∨
              (u = (s.quad i).d ∧ v = (s.quad i).a)) ∨
            ((u = (s.quad i).b ∧ v = (s.quad i).c) ∨
              (u = (s.quad i).a ∧ v = (s.quad i).d)) := by
          simp only [switchingAdded, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hadded
          rcases hadded with h | h
          · rcases h.1 with h | h
            · exact Or.inr (Or.inr h)
            · exact Or.inl (Or.inr h)
          · rcases h.1 with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inl h)
        rcases hcases with hcore | hbranch
        · obtain ⟨hx, hnear⟩ := s.fullResample_good_coreward_path_near selector R r (by omega)
            i hi hgood.1 hgood.2.1 hgood.2.2 pre hnew hpre hpreLen hcore
          apply seed_of_label
          apply Finset.mem_union_right
          simpa only [nearbySeedLabels, dif_pos hx] using hnear
        · exact False.elim (s.fullResample_good_sampleward_cycle_impossible selector R r hr i hi
            hgood.1 hgood.2.1 hgood.2.2 hnot hbranch suffix hsuffixLen cycle hcycle hcycleLen)

theorem fullResample_short_cycle_support_in_old_seed_balls
    (s : LabelledResamplingState V T ι) (selector R r : ℕ) (hr : 2 * r ≤ R)
    (center : V) {z : graphBallVertices (s.fullResample selector).graph center r}
    (cycle : (graphBall (s.fullResample selector).graph center r).Walk z z)
    (hcycle : cycle.IsCycle) (hcycleLen : cycle.length ≤ 2 * r + 1) :
    ∀ w ∈ cycle.support,
      w.val ∈ graphSetBall s.graph (s.largeCycleSeeds selector R r center : Set V) r := by
  intro w hw
  let f : graphBall (s.fullResample selector).graph center r →g (s.fullResample selector).graph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let c := cycle.rotate hw
  have hc : c.IsCycle := hcycle.rotate hw
  have hlen : c.length = cycle.length := by
    have h := congrArg SimpleGraph.Walk.length (cycle.take_spec hw)
    simp only [SimpleGraph.Walk.length_append] at h
    simp only [c, SimpleGraph.Walk.rotate, SimpleGraph.Walk.length_append]
    omega
  exact s.fullResample_short_cycle_base_in_old_seed_balls selector R r hr center w.val w.property
    (c.map f) (hc.map Subtype.val_injective)
    (by simpa only [SimpleGraph.Walk.length_map, hlen] using hcycleLen)

end LabelledResamplingState
end LocalLaw
