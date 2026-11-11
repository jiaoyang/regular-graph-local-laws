import LocalLaw.TreeEdgeBranches

/-! # Actual two branches of each accepted sample patch

The ambient branches are literal images of the two components after the
sampled edge is removed from its genuine induced tree patch.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw

local instance admissibleTreeBranchesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

def inducedTreeBranch (G : SimpleGraph V) (W : Set V) (a b root : W) : Set V :=
  Set.range (fun x : treeEdgeBranch (G.induce W) a b root => x.val.val)

theorem inducedTreeBranch_subset (G : SimpleGraph V) (W : Set V) (a b root : W) :
    inducedTreeBranch G W a b root ⊆ W := by
  rintro _ ⟨x, rfl⟩
  exact x.val.property

theorem mem_inducedTreeBranch_iff (G : SimpleGraph V) (W : Set V) (a b root : W)
    (x : W) : x.val ∈ inducedTreeBranch G W a b root ↔
      x ∈ treeEdgeBranch (G.induce W) a b root := by
  constructor
  · rintro ⟨y, h⟩
    have he : y.val = x := Subtype.ext h
    exact Eq.mp (congrArg (fun z => z ∈ treeEdgeBranch (G.induce W) a b root) he) y.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem inducedTreeBranch_root_mem (G : SimpleGraph V) (W : Set V) (a b root : W) :
    root.val ∈ inducedTreeBranch G W a b root :=
  (mem_inducedTreeBranch_iff G W a b root root).mpr rfl

theorem inducedTreeBranch_cover (G : SimpleGraph V) (W : Set V) (a b : W)
    (hconn : (G.induce W).Connected) :
    inducedTreeBranch G W a b a ∪ inducedTreeBranch G W a b b = W := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (inducedTreeBranch_subset G W a b a) (inducedTreeBranch_subset G W a b b)
  · intro v hv
    have h : (⟨v, hv⟩ : W) ∈ treeEdgeBranch (G.induce W) a b a ∪
        treeEdgeBranch (G.induce W) a b b := by
      rw [treeEdgeBranch_cover _ _ _ hconn]
      trivial
    exact h.imp ((mem_inducedTreeBranch_iff G W a b a ⟨v, hv⟩).mpr)
      ((mem_inducedTreeBranch_iff G W a b b ⟨v, hv⟩).mpr)

theorem inducedTreeBranch_disjoint (G : SimpleGraph V) (W : Set V) (a b : W)
    (htree : (G.induce W).IsTree) (hab : G.Adj a.val b.val) :
    Disjoint (inducedTreeBranch G W a b a) (inducedTreeBranch G W a b b) := by
  apply Set.disjoint_left.mpr
  intro v ha hb
  let x : W := ⟨v, inducedTreeBranch_subset G W a b a ha⟩
  exact Set.disjoint_left.mp (treeEdgeBranch_disjoint _ a b htree hab)
    ((mem_inducedTreeBranch_iff G W a b a x).mp ha)
    ((mem_inducedTreeBranch_iff G W a b b x).mp hb)

theorem inducedTreeBranch_isTree (G : SimpleGraph V) (W : Set V) (a b root : W)
    (htree : (G.induce W).IsTree) (hab : G.Adj a.val b.val)
    (hroot : root = a ∨ root = b) :
    (G.induce (inducedTreeBranch G W a b root)).IsTree := by
  let f : treeEdgeBranch (G.induce W) a b root → V := fun x => x.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  let e : ((G.induce W).induce (treeEdgeBranch (G.induce W) a b root)) ≃g
      G.induce (inducedTreeBranch G W a b root) :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have h := treeEdgeBranch_isTree (G.induce W) a b htree hab root hroot
  constructor
  · exact e.connected_iff.mp h.isConnected
  · intro v p hp
    exact h.IsAcyclic (p.map e.symm.toHom) (hp.map e.symm.injective)

theorem inducedTreeBranch_old_cross_iff (G : SimpleGraph V) (W : Set V) (a b : W)
    (htree : (G.induce W).IsTree) (hab : G.Adj a.val b.val)
    {x y : V} (hx : x ∈ inducedTreeBranch G W a b a)
    (hy : y ∈ inducedTreeBranch G W a b b) :
    G.Adj x y ↔ (SimpleGraph.edge a.val b.val).Adj x y := by
  let u : W := ⟨x, inducedTreeBranch_subset G W a b a hx⟩
  let v : W := ⟨y, inducedTreeBranch_subset G W a b b hy⟩
  have h := treeEdgeBranch_old_cross_iff (G.induce W) a b htree hab
    ((mem_inducedTreeBranch_iff G W a b a u).mp hx)
    ((mem_inducedTreeBranch_iff G W a b b v).mp hy)
  change G.Adj x y ↔ (SimpleGraph.edge a b).Adj u v at h
  simpa [SimpleGraph.edge_adj, Subtype.ext_iff, u, v] using h

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

def sampledPatchFirst (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.sampledEndpointPatch selector r i :=
  ⟨s.admissibleSampleVertex selector i, ⟨_, Or.inl rfl, by simp⟩⟩

def sampledPatchSecond (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.sampledEndpointPatch selector r i :=
  ⟨s.admissibleSecondVertex selector i, ⟨_, Or.inr rfl, by simp⟩⟩

def sampledFirstBranch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Set (Tᶜ : Set V) :=
  inducedTreeBranch (outsideGraph s.graph T) (s.sampledEndpointPatch selector r i)
    (s.sampledPatchFirst selector r i) (s.sampledPatchSecond selector r i) (s.sampledPatchFirst selector r i)

def sampledSecondBranch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Set (Tᶜ : Set V) :=
  inducedTreeBranch (outsideGraph s.graph T) (s.sampledEndpointPatch selector r i)
    (s.sampledPatchFirst selector r i) (s.sampledPatchSecond selector r i) (s.sampledPatchSecond selector r i)

theorem sampledBranch_cover (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    s.sampledFirstBranch selector r i ∪ s.sampledSecondBranch selector r i =
      s.sampledEndpointPatch selector r i :=
  inducedTreeBranch_cover _ _ _ _ (s.sampledEndpointPatch_isTree selector r hr i).isConnected

theorem sampledBranch_disjoint (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    Disjoint (s.sampledFirstBranch selector r i) (s.sampledSecondBranch selector r i) :=
  inducedTreeBranch_disjoint _ _ _ _ (s.sampledEndpointPatch_isTree selector r hr i)
    (s.samples (s.boundary i.val)).property.1

theorem sampledFirstBranch_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    ((outsideGraph s.graph T).induce (s.sampledFirstBranch selector r i)).IsTree :=
  inducedTreeBranch_isTree _ _ _ _ _ (s.sampledEndpointPatch_isTree selector r hr i)
    (s.samples (s.boundary i.val)).property.1 (Or.inl rfl)

theorem sampledSecondBranch_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    ((outsideGraph s.graph T).induce (s.sampledSecondBranch selector r i)).IsTree :=
  inducedTreeBranch_isTree _ _ _ _ _ (s.sampledEndpointPatch_isTree selector r hr i)
    (s.samples (s.boundary i.val)).property.1 (Or.inr rfl)

theorem sampledBranch_old_cross_iff (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector)
    {x y : (Tᶜ : Set V)} (hx : x ∈ s.sampledFirstBranch selector r i)
    (hy : y ∈ s.sampledSecondBranch selector r i) :
    (outsideGraph s.graph T).Adj x y ↔
      (SimpleGraph.edge (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i)).Adj x y :=
  inducedTreeBranch_old_cross_iff (outsideGraph s.graph T) (s.sampledEndpointPatch selector r i)
    (s.sampledPatchFirst selector r i) (s.sampledPatchSecond selector r i)
    (s.sampledEndpointPatch_isTree selector r hr i)
    (s.samples (s.boundary i.val)).property.1 hx hy

end LabelledResamplingState
end LocalLaw
