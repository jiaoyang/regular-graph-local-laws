import LocalLaw.SourceBoundaryGuard
import LocalLaw.ResamplingStructuralCost
import LocalLaw.EffectiveModelRadius
import LocalLaw.SourceSpectralEvents
import LocalLaw.OffsetStructuralEvent

/-! # Actual exceptional edges for the masked source cavity mean

An edge is exceptional if its first endpoint fails the literal source mask
or its second endpoint has a non-tree original local ball. Endpoint fibers
count both alternatives. The actual plus event contributes its doubled
bad-center budget, giving the explicit harmless constant 3d.
-/

noncomputable section
namespace LocalLaw

local instance sourceBiasBadEdgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def sourceBiasBadEdges (G : SimpleGraph V) (T : Set V) (r h : ℕ) :
    Finset (OutsideOrientedEdge G T) :=
  Finset.univ.filter (fun e =>
    (⟨e.val.1, e.property.2.1⟩ : (Tᶜ : Set V)) ∉ boundaryFarOutside G T h ∨
      ¬ (graphBall G e.val.2 (r + 1)).IsTree)

theorem not_mem_sourceBiasBadEdges (G : SimpleGraph V) (T : Set V) (r h : ℕ)
    (e : OutsideOrientedEdge G T) (he : e ∉ sourceBiasBadEdges G T r h) :
    (⟨e.val.1, e.property.2.1⟩ : (Tᶜ : Set V)) ∈ boundaryFarOutside G T h ∧
      (graphBall G e.val.2 (r + 1)).IsTree := by
  simpa only [sourceBiasBadEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] using he

namespace RegularGraph
variable {N d : ℕ}

theorem outside_edges_second_nonTree_count (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ) :
    Nat.card {e : OutsideOrientedEdge g.graph T // ¬ (graphBall g.graph e.val.2 r).IsTree} ≤
      (nonTreeCenters g.graph r).card * d := by
  have hh := endpoint_preimage_card_bound (outsideEdgeSecond g.graph T) (nonTreeCenters g.graph r) d
    (fun v => (outsideEdgeSecond_fiber_card g.graph T v).trans (by rw [g.regular.degree_eq v]))
  simpa only [outsideEdgeSecond, nonTreeCenters_membership] using hh

theorem sourceBiasBadEdges_card_bound (g : RegularGraph N d) (T : Set (Fin N)) (r h : ℕ) (hd : 3 ≤ d) :
    (sourceBiasBadEdges g.graph T r h).card ≤
      (Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ h) +
        (nonTreeCenters g.graph (r + 1)).card) * d := by
  let A : Finset (OutsideOrientedEdge g.graph T) := Finset.univ.filter (fun e =>
    (⟨e.val.1, e.property.2.1⟩ : (Tᶜ : Set (Fin N))) ∉ boundaryFarOutside g.graph T h)
  let B : Finset (OutsideOrientedEdge g.graph T) := Finset.univ.filter (fun e =>
    ¬ (graphBall g.graph e.val.2 (r + 1)).IsTree)
  have hsub : sourceBiasBadEdges g.graph T r h ⊆ A ∪ B := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  have hA : A.card ≤ Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ h) * d := by
    simpa only [A, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      g.outside_edges_failing_boundary_mask_count T h hd
  have hB : B.card ≤ (nonTreeCenters g.graph (r + 1)).card * d := by
    simpa only [B, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      g.outside_edges_second_nonTree_count T (r + 1)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  nlinarith

end RegularGraph

theorem eventually_sourceBiasBadEdges_count (a d : ℕ) (c β γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c / 32)
    (hγ : c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ) (ω Cq badCount : ℕ),
      badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceStructuralPlus (logarithmicRadius (c / 4) d N) ω Cq badCount →
      (sourceBiasBadEdges g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
        (effectiveModelRadius a d N β) (logarithmicRadius (c / 4) d N / 4)).card ≤
          3 * d * ⌊(N : ℝ) ^ γ⌋₊ := by
  have hdepth := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [RegularGraph.eventually_resampling_badCenter_cost a d c γ hd hc.le hγ,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc, hdepth] with
      N hcost hradii hdepth
  intro g o z ω Cq badCount hbadCount hplus
  let R := logarithmicRadius (c / 4) d N
  let r := effectiveModelRadius a d N β
  let ell := actualCavityDepth a d N z - 1
  let T := graphBallVertices g.graph o ell
  let b : ℕ := ⌊(N : ℝ) ^ γ⌋₊
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hmask : Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ (R / 4)) ≤ b := by
    have hraw := hcost g o ell hell
    have hraw' : 4 * (Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ R)) ≤ b := by
      simpa only [Nat.mul_assoc] using hraw
    have hp : (d - 1) ^ (R / 4) ≤ (d - 1) ^ R := Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ _)
    have hh := Nat.mul_le_mul_left (Nat.card (BoundaryOrientedEdge g.graph T)) (Nat.mul_le_mul_left (d + 1) hp)
    change _ ≤ b
    omega
  have hfit : r + 1 ≤ R := by
    have h₁ := hradii.1
    have h₂ := hradii.2.1
    have hr : r ≤ logarithmicRadius β d N := Nat.sub_le _ _
    dsimp only [R] at *
    omega
  have hbad : (nonTreeCenters g.graph (r + 1)).card ≤ 2 * b :=
    (Finset.card_le_card (nonTreeCenters_mono g.graph hfit)).trans
      (hplus.2.2.trans (Nat.mul_le_mul_left 2 hbadCount))
  have hh := g.sourceBiasBadEdges_card_bound T r (R / 4) hd
  nlinarith

end LocalLaw
