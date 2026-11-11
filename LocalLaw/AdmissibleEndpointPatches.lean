import LocalLaw.AdmissibleSampleGeometry

/-! # The endpoint-only common model has separated genuine tree patches

The central patch contains all original outside boundary roots. Each selected
sample contributes its two-root patch. Actual I/J tests make these sample
patches trees, disjoint from the central patch and from one another, with no
old cross edges. No arbitrary target neighborhoods are included.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance admissibleEndpointPatchesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

def outerBoundaryRoots (G : SimpleGraph V) (T : Set V) : Set (Tᶜ : Set V) :=
  Set.range (boundaryOuterEndpoint G T)

theorem graphSetBalls_disjoint_no_edge (G : SimpleGraph V) (A B : Set V) (r : ℕ)
    (hfar : ∀ a ∈ A, ∀ b ∈ B, ((2 * r + 1 : ℕ) : ℕ∞) < G.edist a b) :
    Disjoint (graphSetBall G A r) (graphSetBall G B r) ∧
      ∀ x ∈ graphSetBall G A r, ∀ y ∈ graphSetBall G B r, ¬G.Adj x y := by
  constructor
  · apply Set.disjoint_left.mpr
    rintro v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
    exact Set.disjoint_left.mp (graphBalls_disjoint_of_edist_gt G a b r
      ((ENat.coe_le_coe.mpr (by omega : 2 * r ≤ 2 * r + 1)).trans_lt (hfar a ha b hb))) hav hbv
  · rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hby⟩ hxy
    exact graphBalls_no_edge_of_edist_gt G a b r (hfar a ha b hb) x hax y hby hxy

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

def admissibleSecondVertex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : (Tᶜ : Set V) :=
  sampledSecondOutsideVertex s.graph T s.samples (s.boundary i.val)

def admissiblePairRoots (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Set (Tᶜ : Set V) :=
  {s.admissibleSampleVertex selector i, s.admissibleSecondVertex selector i}

def centralEndpointPatch (s : LabelledResamplingState V T ι) (r : ℕ) : Set (Tᶜ : Set V) :=
  graphSetBall (outsideGraph s.graph T) (outerBoundaryRoots s.graph T) r

def sampledEndpointPatch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Set (Tᶜ : Set V) :=
  graphSetBall (outsideGraph s.graph T) (s.admissiblePairRoots selector i) r

def endpointModelRoots (s : LabelledResamplingState V T ι) (selector : ℕ) : Set (Tᶜ : Set V) :=
  outerBoundaryRoots s.graph T ∪ ⋃ i : s.AdmissibleSampleIndex selector, s.admissiblePairRoots selector i

def endpointModelVertices (s : LabelledResamplingState V T ι) (selector r : ℕ) : Set (Tᶜ : Set V) :=
  graphSetBall (outsideGraph s.graph T) (s.endpointModelRoots selector) r

theorem admissiblePairRoots_subset_triple (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.admissiblePairRoots selector i ⊆ s.triple i.val := by
  intro v hv
  simp only [admissiblePairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact (outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inl rfl))
  · exact (outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inr rfl))

theorem sampledEndpointPatch_eq_pairBall (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.sampledEndpointPatch selector r i = pairBallVertices (outsideGraph s.graph T)
      (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i) r := by
  ext v
  simp only [sampledEndpointPatch, graphSetBall, admissiblePairRoots, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, pairBallVertices]
  aesop

theorem admissiblePairRoots_far_boundary (s : LabelledResamplingState V T ι) (selector : ℕ)
    (hselector : 1 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    s.admissiblePairRoots selector i ⊆ boundaryFarOutside s.graph T (selector - 1) := by
  intro v hv
  simp only [admissiblePairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact fun α => (ENat.coe_le_coe.mpr (Nat.sub_le _ _)).trans_lt
      (s.admissibleSampleVertex_far_boundary selector i α)
  · apply boundaryFarOutside_step s.graph T (selector - 1)
      (show (outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i)
        (s.admissibleSecondVertex selector i) from (s.samples (s.boundary i.val)).property.1)
    simpa only [Nat.sub_add_cancel hselector] using s.admissibleSampleVertex_far_boundary selector i

theorem sampledEndpointPatch_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    ((outsideGraph s.graph T).induce (s.sampledEndpointPatch selector r i)).IsTree := by
  let H := outsideGraph s.graph T
  let X := outsideTripleNeighborhood s.graph T selector s.samples (s.boundary i.val)
  have hsubset : s.sampledEndpointPatch selector r i ⊆ X := by
    rintro v ⟨u, hu, hd⟩
    exact ⟨u, s.admissiblePairRoots_subset_triple selector i hu,
      hd.trans (ENat.coe_le_coe.mpr hr)⟩
  let f : H.induce (s.sampledEndpointPatch selector r i) →g
      ((H ⊔ SimpleGraph.edge (boundaryOutsideVertex s.graph T (s.boundary i.val))
        (s.admissibleSampleVertex selector i)).induce X) :=
    { toFun := fun v => ⟨v.val, hsubset v.property⟩
      map_rel' := fun h => Or.inl h }
  have hf : Function.Injective f := by
    intro v w heq
    have hraw : v.val = w.val := congrArg (fun x : X => x.val) heq
    exact Subtype.ext hraw
  constructor
  · rw [s.sampledEndpointPatch_eq_pairBall selector r i]
    exact pairBall_connected_of_adj H (show H.Adj (s.admissibleSampleVertex selector i)
      (s.admissibleSecondVertex selector i) from (s.samples (s.boundary i.val)).property.1) r
  · intro v p hp
    exact i.property.1.tree.IsAcyclic (p.map f) (hp.map hf)

theorem sampledEndpointPatches_disjoint_no_edge (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 1 ≤ selector)
    (i j : s.AdmissibleSampleIndex selector) (hij : i ≠ j) :
    Disjoint (s.sampledEndpointPatch selector r i) (s.sampledEndpointPatch selector r j) ∧
      ∀ x ∈ s.sampledEndpointPatch selector r i, ∀ y ∈ s.sampledEndpointPatch selector r j,
        ¬(outsideGraph s.graph T).Adj x y := by
  apply graphSetBalls_disjoint_no_edge
  intro a ha b hb
  have hlabel : s.boundary j.val ≠ s.boundary i.val := fun h =>
    hij (Subtype.ext (s.boundary.injective h).symm)
  exact (ENat.coe_le_coe.mpr hsep).trans_lt (i.property.2 (s.boundary j.val) hlabel a
    (s.admissiblePairRoots_subset_triple selector i ha) b (s.admissiblePairRoots_subset_triple selector j hb))

theorem central_sampledEndpointPatch_disjoint_no_edge (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    Disjoint (s.centralEndpointPatch r) (s.sampledEndpointPatch selector r i) ∧
      ∀ x ∈ s.centralEndpointPatch r, ∀ y ∈ s.sampledEndpointPatch selector r i,
        ¬(outsideGraph s.graph T).Adj x y := by
  apply graphSetBalls_disjoint_no_edge
  rintro a ⟨α, rfl⟩ b hb
  rw [SimpleGraph.edist_comm]
  exact (ENat.coe_le_coe.mpr (by omega : 2 * r + 1 ≤ selector - 1)).trans_lt
    (s.admissiblePairRoots_far_boundary selector (by omega) i hb α)

theorem eligible_exterior_mem_endpointModelRoots (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : ι) (hi : s.Eligible selector i) (x : (Tᶜ : Set V))
    (hx : x.val ∈ (s.quad i).exterior) : x ∈ s.endpointModelRoots selector := by
  simp only [SwitchingQuad.exterior, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · apply Or.inl
    exact ⟨s.boundary i, Subtype.ext hx.symm⟩
  · apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, Or.inl ?_⟩
    exact Subtype.ext hx
  · apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, Or.inr ?_⟩
    exact Subtype.ext hx

end LabelledResamplingState
end LocalLaw
