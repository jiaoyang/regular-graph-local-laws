import LocalLaw.EdgeDisjointSwitching
import LocalLaw.FiniteResampling

/-!
# The finite local-resampling data of Section 3

Boundary edges are oriented from T to its complement. For every boundary edge,
one independently samples an oriented edge entirely outside T. The sampling
fiber is the full function type, so repetitions are allowed. We use a
simple-graph sampler whose I-type tree test includes explicit insertion
validity, since simple-graph union alone discards loops and repeated edges.
`LocalResamplingInvolution` proves selector invariance and reversibility for
this sampler; `BallResamplingMeasure` constructs its uniform-graph reversible
kernel. No equivalence with a separate multigraph selector convention is
asserted.
-/

open scoped BigOperators

namespace LocalLaw

variable {V : Type*}

/-- Oriented edges leaving the fixed vertex set T. -/
def BoundaryOrientedEdge (G : SimpleGraph V) (T : Set V) :=
  {e : V × V // G.Adj e.1 e.2 ∧ e.1 ∈ T ∧ e.2 ∉ T}

/-- Oriented edges of G(T), with both endpoints outside T. -/
def OutsideOrientedEdge (G : SimpleGraph V) (T : Set V) :=
  {e : V × V // G.Adj e.1 e.2 ∧ e.1 ∉ T ∧ e.2 ∉ T}

/-- Independent assignments of an outside oriented edge to every boundary
edge. No injectivity condition is imposed: repetitions are permitted. -/
def LocalSamplingFiber (G : SimpleGraph V) (T : Set V) :=
  BoundaryOrientedEdge G T → OutsideOrientedEdge G T

/-- The graph remaining after removal of T, on its actual remaining vertices. -/
def outsideGraph (G : SimpleGraph V) (T : Set V) : SimpleGraph {v : V // v ∉ T} :=
  G.induce {v | v ∉ T}

def sampledSwitchingQuad (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) : SwitchingQuad V :=
  ⟨α.val.1, α.val.2, (S α).val.1, (S α).val.2⟩

theorem sampledSwitching_root_mem (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) :
    (sampledSwitchingQuad G T S α).a ∈ T := α.property.2.1

theorem sampledSwitching_exterior_disjoint (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) :
    Disjoint (sampledSwitchingQuad G T S α).exterior T := by
  apply Set.disjoint_left.mpr
  intro x hx hT
  simp only [sampledSwitchingQuad, SwitchingQuad.exterior, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact α.property.2.2 hT
  · exact (S α).property.2.1 hT
  · exact (S α).property.2.2 hT

/-- The exterior triple as actual vertices of G(T). -/
def outsideTriple (G : SimpleGraph V) (T : Set V) (S : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) : Set {v : V // v ∉ T} :=
  {v | v.val ∈ (sampledSwitchingQuad G T S α).exterior}

/-- The J isolation criterion, with an integer radius fixed explicitly.
Extended graph distance gives disconnected pairs infinite distance. -/
def resamplingIsolation (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) : Prop :=
  ∀ β : BoundaryOrientedEdge G T, β ≠ α →
    ∀ x ∈ outsideTriple G T S α, ∀ y ∈ outsideTriple G T S β,
      (radius : ℕ∞) < (outsideGraph G T).edist x y

/-- J forces disjoint exterior triples, since a common vertex would have
extended graph distance zero from itself. -/
theorem isolation_exterior_disjoint (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hJ : resamplingIsolation G T radius S α) (hβα : β ≠ α) :
    Disjoint (sampledSwitchingQuad G T S α).exterior
      (sampledSwitchingQuad G T S β).exterior := by
  apply Set.disjoint_left.mpr
  intro x hxα hxβ
  have hxT : x ∉ T := fun hx =>
    (Set.disjoint_left.mp (sampledSwitching_exterior_disjoint G T S α)) hxα hx
  have hdist := hJ β hβα ⟨x, hxT⟩ hxα ⟨x, hxT⟩ hxβ
  rw [SimpleGraph.edist_self] at hdist
  exact not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ radius) hdist

/-- Radius-neighborhood of an exterior triple inside the deleted graph. -/
def outsideTripleNeighborhood (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) : Set {v : V // v ∉ T} :=
  {v | ∃ u ∈ outsideTriple G T S α, (outsideGraph G T).edist u v ≤ radius}

def boundaryOutsideVertex (G : SimpleGraph V) (T : Set V) (α : BoundaryOrientedEdge G T) :
    {v : V // v ∉ T} := ⟨α.val.2, α.property.2.2⟩

def sampledFirstOutsideVertex (G : SimpleGraph V) (T : Set V) (S : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) : {v : V // v ∉ T} := ⟨(S α).val.1, (S α).property.2.1⟩

/-- I-type tree test with explicit validity of the inserted outside edge.
Adding first and then inducing on the original neighborhood is exactly adding
that edge to the neighborhood, because both endpoints belong to the triple. -/
structure ResamplingTreeTest (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) : Prop where
  distinct : boundaryOutsideVertex G T α ≠ sampledFirstOutsideVertex G T S α
  new_edge : ¬(outsideGraph G T).Adj (boundaryOutsideVertex G T α)
    (sampledFirstOutsideVertex G T S α)
  tree : ((outsideGraph G T ⊔ SimpleGraph.edge (boundaryOutsideVertex G T α)
      (sampledFirstOutsideVertex G T S α)).induce
      (outsideTripleNeighborhood G T radius S α)).IsTree

/-- Guarded I and J imply the actual quadruple is an admissible simple
switching. The new interior-to-exterior edge is absent because otherwise it
would supply another boundary index contradicting J-isolation. -/
theorem sampledSwitching_admissible (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    (sampledSwitchingQuad G T S α).Admissible G := by
  have hlT := α.property.2.1
  have haT := α.property.2.2
  have hbT := (S α).property.2.1
  have hcT := (S α).property.2.2
  have hab : α.val.2 ≠ (S α).val.1 := by
    intro heq
    apply hI.distinct
    exact Subtype.ext heq
  have hnewAB : ¬G.Adj α.val.2 (S α).val.1 := hI.new_edge
  have hac : α.val.2 ≠ (S α).val.2 := by
    intro heq
    apply hnewAB
    rw [heq]
    exact (S α).property.1.symm
  have hlb : α.val.1 ≠ (S α).val.1 := by
    intro heq
    exact hbT (heq ▸ hlT)
  have hlc : α.val.1 ≠ (S α).val.2 := by
    intro heq
    exact hcT (heq ▸ hlT)
  have hnewLC : ¬G.Adj α.val.1 (S α).val.2 := by
    intro hadj
    let β : BoundaryOrientedEdge G T := ⟨(α.val.1, (S α).val.2), hadj, hlT, hcT⟩
    have hβα : β ≠ α := by
      intro heq
      have hout := congrArg (fun e : BoundaryOrientedEdge G T => e.val.2) heq
      exact hac hout.symm
    have hdis := isolation_exterior_disjoint G T radius S α β hJ hβα
    apply (Set.disjoint_left.mp hdis) (a := (S α).val.2)
    · simp [sampledSwitchingQuad, SwitchingQuad.exterior]
    · simp [sampledSwitchingQuad, SwitchingQuad.exterior, β]
  exact ⟨α.property.1.ne, hlb, hlc, hab, hac, (S α).property.1.ne,
    α.property.1, (S α).property.1, hnewLC, hnewAB⟩

section Finite
variable [Fintype V]
noncomputable local instance samplingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable instance boundaryOrientedEdgeFintype (G : SimpleGraph V) (T : Set V) :
    Fintype (BoundaryOrientedEdge G T) := by
  unfold BoundaryOrientedEdge
  infer_instance

noncomputable instance outsideOrientedEdgeFintype (G : SimpleGraph V) (T : Set V) :
    Fintype (OutsideOrientedEdge G T) := by
  unfold OutsideOrientedEdge
  infer_instance

noncomputable instance localSamplingFiberFintype (G : SimpleGraph V) (T : Set V) :
    Fintype (LocalSamplingFiber G T) := by
  unfold LocalSamplingFiber
  infer_instance

/-- The exact product-fiber cardinality for independent outside-edge choices. -/
theorem localSamplingFiber_card (G : SimpleGraph V) (T : Set V) :
    Fintype.card (LocalSamplingFiber G T) =
      Fintype.card (OutsideOrientedEdge G T) ^ Fintype.card (BoundaryOrientedEdge G T) :=
  Fintype.card_fun

omit [Fintype V] in
theorem localSamplingFiber_nonempty (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T)) : Nonempty (LocalSamplingFiber G T) := by
  letI := hout
  exact inferInstanceAs (Nonempty (BoundaryOrientedEdge G T → OutsideOrientedEdge G T))

/-- The uniform measure on the full function fiber. -/
noncomputable def localSamplingWeight (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) : ℝ := finiteUniformWeight (LocalSamplingFiber G T) S

/-- Its constant weight is the product of the uniform coordinate weights. -/
theorem localSamplingWeight_product (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) :
    localSamplingWeight G T S = ∏ _α : BoundaryOrientedEdge G T,
      (Fintype.card (OutsideOrientedEdge G T) : ℝ)⁻¹ := by
  simp [localSamplingWeight, finiteUniformWeight, localSamplingFiber_card, one_div]

/-- Uniform local sampling is normalized whenever an outside oriented edge
exists; no lower bound for its count is assumed implicitly. -/
theorem localSamplingWeight_total (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T)) :
    (∑ S : LocalSamplingFiber G T, localSamplingWeight G T S) = 1 := by
  letI := localSamplingFiber_nonempty G T hout
  exact finiteUniformWeight_total

/-- Enumerate an arbitrary accepted subset of boundary indices. -/
noncomputable def sampledSwitchingFamily (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (accepted : Finset (BoundaryOrientedEdge G T)) :
    List (SwitchingQuad V) := accepted.toList.map (sampledSwitchingQuad G T S)

omit [Fintype V] in
/-- J on all accepted indices gives edge-disjoint modifications, even when
multiple accepted boundary edges share an interior leaf. -/
theorem sampledSwitchingFamily_edge_disjoint (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (accepted : Finset (BoundaryOrientedEdge G T))
    (hJ : ∀ α ∈ accepted, resamplingIsolation G T radius S α) :
    EdgeDisjointSwitchingFootprints (sampledSwitchingFamily G T S accepted) := by
  apply boundary_family_edge_disjoint _ T
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hq
    exact sampledSwitching_root_mem G T S α
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hq
    exact sampledSwitching_exterior_disjoint G T S α
  · rw [sampledSwitchingFamily, List.pairwise_map]
    apply accepted.nodup_toList.pairwise_of_forall_ne
    intro α hα β hβ hαβ
    exact isolation_exterior_disjoint G T radius S α β
      (hJ α (Finset.mem_toList.mp hα)) hαβ.symm

/-- The accepted boundary indices under the guarded I-test and the J-test. -/
noncomputable def acceptedResamplingIndices (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ.filter (fun α => ResamplingTreeTest G T radius S α ∧ resamplingIsolation G T radius S α)

omit [Fintype V] in
/-- Every member of an arbitrary accepted family is a valid simple switching
when its I- and J-tests pass in the original graph. -/
theorem sampledSwitchingFamily_admissible (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (accepted : Finset (BoundaryOrientedEdge G T))
    (hI : ∀ α ∈ accepted, ResamplingTreeTest G T radius S α)
    (hJ : ∀ α ∈ accepted, resamplingIsolation G T radius S α) :
    SwitchingFamilyAdmissible (sampledSwitchingFamily G T S accepted) G := by
  intro q hq
  obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hq
  exact sampledSwitching_admissible G T radius S α
    (hI α (Finset.mem_toList.mp hα)) (hJ α (Finset.mem_toList.mp hα))

/-- The selected family's two deterministic certificates needed to compose
all accepted switchings, including repetitions of interior leaf vertices. -/
theorem acceptedSwitchingFamily_valid (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) :
    EdgeDisjointSwitchingFootprints
        (sampledSwitchingFamily G T S (acceptedResamplingIndices G T radius S)) ∧
      SwitchingFamilyAdmissible
        (sampledSwitchingFamily G T S (acceptedResamplingIndices G T radius S)) G := by
  have htests : ∀ α ∈ acceptedResamplingIndices G T radius S,
      ResamplingTreeTest G T radius S α ∧ resamplingIsolation G T radius S α := by
    intro α hα
    exact (Finset.mem_filter.mp hα).2
  exact ⟨sampledSwitchingFamily_edge_disjoint G T radius S _ (fun α hα => (htests α hα).2),
    sampledSwitchingFamily_admissible G T radius S _ (fun α hα => (htests α hα).1)
      (fun α hα => (htests α hα).2)⟩

/-- The actual finite simultaneous switching map for these guarded selectors. -/
noncomputable def localResampledGraph (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) : SimpleGraph V :=
  applySwitches (sampledSwitchingFamily G T S (acceptedResamplingIndices G T radius S)) G

theorem localResampledGraph_degree (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (x : V) :
    (localResampledGraph G T radius S).degree x = G.degree x := by
  obtain ⟨hd, ha⟩ := acceptedSwitchingFamily_valid G T radius S
  exact edge_applySwitches_degree _ G hd ha x

theorem localResampledGraph_regular (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) {d : ℕ} (hG : G.IsRegularOfDegree d) :
    (localResampledGraph G T radius S).IsRegularOfDegree d := by
  intro x
  rw [localResampledGraph_degree G T radius S x]
  exact hG.degree_eq x

end Finite

end LocalLaw
