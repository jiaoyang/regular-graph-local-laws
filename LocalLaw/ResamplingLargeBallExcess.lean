import LocalLaw.LargeCycleSeedCounts
import LocalLaw.ShortCycleEvenLocalization
import LocalLaw.DisconnectedEvenTransfer
import LocalLaw.HalfRadiusUnionExcess
import LocalLaw.GeneralExcessSurgery

/-! # The actual switched half-radius ball has bounded excess

The short-cycle seed cover is lifted to all even patterns by actual BFS
cycle generation. Their edges lie in the old graph plus the proved bounded
exceptional added graph. Restriction and the finite cycle-space cardinal
bound transfer excess into the literal union of old half-radius balls.
The old radius-R budget bounds that union, and actual added-edge counting
pays for the exceptional switchings.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance resamplingLargeBallExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem graphEdgeCount_induce_le (G : SimpleGraph V) (S : Set V) :
    graphEdgeCount (G.induce S) ≤ graphEdgeCount G := by
  let f : G.induce S →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  exact Nat.card_le_card_of_injective f.mapEdgeSet (SimpleGraph.Hom.mapEdgeSet.injective f Subtype.val_injective)

def resamplingLargeExcessConstant (d ω k j C t : ℕ) : ℕ :=
  halfRadiusUnionExcessConstant d (largeCycleSeedCount ω k j C t) ω + 2 * (2 * j + C + t)

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_half_ball_excess_seed_bound (s : LabelledResamplingState V T ι)
    (selector R d ω : ℕ) (hR : 2 ≤ R) (hdegree : ∀ v, s.graph.degree v ≤ d)
    (hbudget : ∀ v, graphBallExcess s.graph v R ≤ ω) (center : V) :
    graphBallExcess (s.fullResample selector).graph center (R / 2) ≤
      halfRadiusUnionExcessConstant d (s.largeCycleSeeds selector R (R / 2) center).card ω +
        2 * (sampleExceptionalIndices s.graph T R s.samples).card := by
  classical
  let H := (s.fullResample selector).graph
  let B := graphBall H center (R / 2)
  let roots := s.largeCycleSeeds selector R (R / 2) center
  let S := graphSetBall s.graph (roots : Set V) (R / 2)
  let D := badSampleAddedGraph s.graph T R s.samples
  let emb : graphBallVertices H center (R / 2) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hlocal : ∀ C : EvenEdgeSubgraph B, ∀ v ∈ C.val.support, v.val ∈ S := by
    apply fun C => ball_even_pattern_support_of_short_cycles H center (R / 2) S ?_ C
    intro v p hp hlen
    exact s.fullResample_short_cycle_support_in_old_seed_balls selector R (R / 2) (by omega)
      center p hp hlen
  have hsupport : ∀ C : EvenEdgeSubgraph B, (C.val.map emb).support ⊆ S := by
    intro C x hx
    obtain ⟨y, hxy⟩ := ((C.val.map emb).mem_support).mp hx
    obtain ⟨a, b, hab, rfl, _⟩ := (SimpleGraph.map_adj emb C.val x y).mp hxy
    exact hlocal C a ((C.val.mem_support).mpr ⟨b, hab⟩)
  have hedges : ∀ C : EvenEdgeSubgraph B, C.val.map emb ≤ s.graph ⊔ D :=
    fun C => s.fullResample_half_ball_even_map_le_old_add_bad selector R center C
  have htransfer := graphExcess_le_of_even_pattern_localization_general B (s.graph ⊔ D) emb S
    (graphBall_connected H center (R / 2)) hedges hsupport
  have hsplit : graphExcess ((s.graph ⊔ D).induce S) ≤
      graphExcess (s.graph.induce S) + graphEdgeCount (D.induce S) := by
    exact graphExcess_sup_le (s.graph.induce S) (D.induce S)
  have hadded : graphEdgeCount (D.induce S) ≤
      2 * (sampleExceptionalIndices s.graph T R s.samples).card :=
    (graphEdgeCount_induce_le D S).trans (badSampleAddedGraph_edgeCount s.graph T R s.samples)
  have hroots : Nat.card (roots : Set V) = roots.card := by
    simpa only [Finset.toFinset_coe, Nat.card_eq_fintype_card] using
      (Set.toFinset_card (s := (roots : Set V))).symm
  have hunion := graphSetBall_halfRadius_excess_bound s.graph (roots : Set V) d R ω hR hdegree hbudget
  rw [hroots] at hunion
  have hfinal := htransfer.trans (hsplit.trans (Nat.add_le_add hunion hadded))
  simp only [B, H, roots, graphBallExcess, graphBall, graphExcess,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hfinal ⊢
  exact hfinal

end LabelledResamplingState

/-- Source Prop. 5.12's large-ball conclusion with a fully explicit constant.
All geometric conclusions are derived; the input is the proved sampling
event and the original graph's degree/excess budgets. -/
theorem sourceFullGood_fullResample_half_ball_excess {ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (o : V) (ell selector R d ω k j C t : ℕ)
    (boundary : ι ≃ BoundaryOrientedEdge G (graphBallVertices G o ell))
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hR : 2 ≤ R) (hdegree : ∀ v, G.degree v ≤ d)
    (hbudget : ∀ v, graphBallExcess G v R ≤ ω)
    (hgood : SourceFullGeometricGood G o ell R ω k j C t S) (center : V) :
    let s : LabelledResamplingState V (graphBallVertices G o ell) ι := ⟨G, boundary, S⟩
    graphBallExcess (s.fullResample selector).graph center (R / 2) ≤
      resamplingLargeExcessConstant d ω k j C t := by
  let s : LabelledResamplingState V (graphBallVertices G o ell) ι := ⟨G, boundary, S⟩
  have h := s.fullResample_half_ball_excess_seed_bound selector R d ω hR hdegree hbudget center
  have hseed := sourceFullGood_largeCycleSeeds_card G o ell selector R ω k j C t boundary S hgood center
  have hbad := sampleExceptionalIndices_card_of_sourceFullGood G o ell R ω k j C t S hgood
  apply h.trans
  unfold resamplingLargeExcessConstant halfRadiusUnionExcessConstant
  gcongr

end LocalLaw
