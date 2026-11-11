import LocalLaw.ResamplingTripleGeometry
import LocalLaw.SourceBoundaryGuard
import LocalLaw.ComponentFiniteLocalization
import LocalLaw.TripleTreeTest

/-! # Actual geometry of admissible sampled vertices

The I-test forces the sampled root away from its own boundary root: an old
short path plus the inserted edge would be a cycle in the tested tree. The
J-test separates it from every other triple. Hence admissible first sampled
vertices are injectively labelled, mutually separated, and pass the literal
source far-boundary mask. Separated two-root models are truly disconnected.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw

local instance admissibleSampleGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem tree_test_boundary_sample_far (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) :
    (radius : ℕ∞) < (outsideGraph G T).edist
      (boundaryOutsideVertex G T α) (sampledFirstOutsideVertex G T S α) := by
  classical
  let H := outsideGraph G T
  let a := boundaryOutsideVertex G T α
  let b := sampledFirstOutsideVertex G T S α
  let X := outsideTripleNeighborhood G T radius S α
  have ha : a ∈ X := ⟨a, (outsideTriple_mem_iff G T S α a).mpr (Or.inl rfl), by simp⟩
  have hb : b ∈ X := ⟨b, (outsideTriple_mem_iff G T S α b).mpr (Or.inr (Or.inl rfl)), by simp⟩
  let A := (H ⊔ SimpleGraph.edge a b).induce X
  have hadj : A.Adj (⟨a, ha⟩ : X) (⟨b, hb⟩ : X) :=
    Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hI.distinct⟩)
  have hbridge : A.IsBridge s((⟨a, ha⟩ : X), (⟨b, hb⟩ : X)) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hI.tree.IsAcyclic) hadj
  let D := A \ SimpleGraph.edge (⟨a, ha⟩ : X) (⟨b, hb⟩ : X)
  have hNoReach : ¬D.Reachable (⟨a, ha⟩ : X) (⟨b, hb⟩ : X) :=
    (SimpleGraph.isBridge_iff.mp hbridge).2
  have hle : H.induce X ≤ D := by
    intro u v huv
    refine ⟨Or.inl huv, ?_⟩
    intro he
    rcases (SimpleGraph.edge_adj (⟨a, ha⟩ : X) (⟨b, hb⟩ : X) u v).mp he with ⟨he, _⟩
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hI.new_edge huv
    · exact hI.new_edge huv.symm
  apply lt_of_not_ge
  intro hnear
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top radius) hnear
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ radius := ENat.coe_le_coe.mp (hp.trans_le hnear)
  have hsupp : ∀ v ∈ p.support, v ∈ X := by
    intro v hv
    refine ⟨a, (outsideTriple_mem_iff G T S α a).mpr (Or.inl rfl), ?_⟩
    exact (H.edist_le (p.takeUntil v hv)).trans
      (ENat.coe_le_coe.mpr ((p.length_takeUntil_le hv).trans hlen))
  obtain ⟨q, _⟩ := walk_lift_induced_of_support H X p hsupp ha hb
  exact hNoReach (q.mapLe hle).reachable

theorem pairBall_not_connected_of_edist_gt (G : SimpleGraph V) (i j : V) (r : ℕ)
    (hfar : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist i j) : ¬(pairBallGraph G i j r).Connected := by
  intro hconn
  let a := pairBallLeft G i j r
  let b := pairBallRight G i j r
  obtain ⟨p⟩ := hconn.preconnected a b
  have hb : ¬G.edist i b.val ≤ (r : ℕ∞) := by
    intro h
    exact (not_lt_of_ge (h.trans (ENat.coe_le_coe.mpr (by omega)))) hfar
  obtain ⟨x, hx, y, hy, hxy⟩ := walk_crosses_cut (pairBallGraph G i j r) p
    {v | G.edist i v.val ≤ (r : ℕ∞)} (by change G.edist i i ≤ _; simp) hb
  have hyr : G.edist j y.val ≤ (r : ℕ∞) := y.property.resolve_left hy
  exact graphBalls_no_edge_of_edist_gt G i j r hfar x.val hx y.val hyr hxy

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

def AdmissibleSampleIndex (s : LabelledResamplingState V T ι) (radius : ℕ) :=
  {i : ι // s.Eligible radius i}

instance admissibleSampleIndexFintype [Fintype ι] (s : LabelledResamplingState V T ι) (radius : ℕ) :
    Fintype (s.AdmissibleSampleIndex radius) := by
  unfold AdmissibleSampleIndex
  infer_instance

def admissibleSampleVertex (s : LabelledResamplingState V T ι) (radius : ℕ)
    (i : s.AdmissibleSampleIndex radius) : (Tᶜ : Set V) :=
  sampledFirstOutsideVertex s.graph T s.samples (s.boundary i.val)

def admissibleSampleSet (s : LabelledResamplingState V T ι) (radius : ℕ) : Set (Tᶜ : Set V) :=
  Set.range (s.admissibleSampleVertex radius)

def admissibleSampleAmbientSet (s : LabelledResamplingState V T ι) (radius : ℕ) : Set V :=
  Set.range (fun i : s.AdmissibleSampleIndex radius => (s.admissibleSampleVertex radius i).val)

theorem admissibleSampleVertex_separated (s : LabelledResamplingState V T ι) (radius : ℕ)
    (i j : s.AdmissibleSampleIndex radius) (hij : i ≠ j) :
    (radius : ℕ∞) < (outsideGraph s.graph T).edist
      (s.admissibleSampleVertex radius i) (s.admissibleSampleVertex radius j) := by
  have hlabel : s.boundary j.val ≠ s.boundary i.val := by
    intro h
    exact hij (Subtype.ext (s.boundary.injective h).symm)
  exact i.property.2 (s.boundary j.val) hlabel
    (s.admissibleSampleVertex radius i)
    ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inl rfl)))
    (s.admissibleSampleVertex radius j)
    ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inl rfl)))

theorem admissibleSampleVertex_injective (s : LabelledResamplingState V T ι) (radius : ℕ) :
    Function.Injective (s.admissibleSampleVertex radius) := by
  intro i j heq
  by_contra hij
  have h := s.admissibleSampleVertex_separated radius i j hij
  rw [heq, SimpleGraph.edist_self] at h
  exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ radius)) h

theorem admissibleSampleVertex_far_boundary (s : LabelledResamplingState V T ι) (radius : ℕ)
    (i : s.AdmissibleSampleIndex radius) :
    s.admissibleSampleVertex radius i ∈ boundaryFarOutside s.graph T radius := by
  intro α
  by_cases hα : α = s.boundary i.val
  · subst α
    change (radius : ℕ∞) < (outsideGraph s.graph T).edist
      (sampledFirstOutsideVertex s.graph T s.samples (s.boundary i.val))
      (boundaryOutsideVertex s.graph T (s.boundary i.val))
    rw [SimpleGraph.edist_comm]
    exact tree_test_boundary_sample_far s.graph T radius s.samples (s.boundary i.val) i.property.1
  · exact i.property.2 α hα (s.admissibleSampleVertex radius i)
      ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inl rfl)))
      (boundaryOuterEndpoint s.graph T α)
      ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inl rfl))

theorem admissibleSamplePair_disconnected (s : LabelledResamplingState V T ι)
    (radius r : ℕ) (hr : 2 * r + 1 ≤ radius)
    (i j : s.AdmissibleSampleIndex radius) (hij : i ≠ j) :
    ¬(pairBallGraph (outsideGraph s.graph T)
      (s.admissibleSampleVertex radius i) (s.admissibleSampleVertex radius j) r).Connected :=
  pairBall_not_connected_of_edist_gt _ _ _ _
    ((ENat.coe_le_coe.mpr hr).trans_lt (s.admissibleSampleVertex_separated radius i j hij))

end LabelledResamplingState
end LocalLaw
