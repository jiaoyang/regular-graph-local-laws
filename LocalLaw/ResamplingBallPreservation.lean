import LocalLaw.LocalResamplingInvolution
import LocalLaw.GraphBallCounting

/-!
# Preservation of the resampling ball

Agreement on edges incident to radius r already preserves radius r+1. A
boundary leaf at distance ell from the center cannot belong to radius ell-1;
all sampled exterior vertices also lie outside that smaller ball. Therefore
every elementary boundary switching preserves the original radius-ell ball.
The property then survives a finite schedule and the full labelled resampling.
-/

namespace LocalLaw
variable {V : Type*}

/-- Root balls increase with their radius. -/
theorem graphSetBall_mono_radius (G : SimpleGraph V) (S : Set V) {r R : ℕ} (h : r ≤ R) :
    graphSetBall G S r ⊆ graphSetBall G S R := by
  rintro v ⟨s, hs, hd⟩
  exact ⟨s, hs, hd.trans (ENat.coe_le_coe.mpr h)⟩

/-- Exact one-step neighborhood expansion, not just an upper cardinality bound. -/
theorem graphSetBall_succ_eq (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    graphSetBall G S (r + 1) = graphSetBall G S r ∪
      {v | ∃ u ∈ graphSetBall G S r, G.Adj u v} := by
  apply Set.Subset.antisymm (graphSetBall_succ_subset G S r)
  intro v hv
  rcases hv with hv | ⟨u, hu, huv⟩
  · exact graphSetBall_mono_radius G S (Nat.le_succ r) hv
  · obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk G S r u).mp hu
    apply (mem_graphSetBall_iff_walk G S (r + 1) v).mpr
    exact ⟨s, hs, p.concat huv, by simpa only [SimpleGraph.Walk.length_concat] using Nat.succ_le_succ hp⟩

/-- The sharper locality principle needed at a boundary: agreement on all
edges incident to radius r preserves radius r+1 as well. -/
theorem graphSetBall_succ_eq_of_incident_agreement (G H : SimpleGraph V) (S : Set V)
    (r : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S r ∨ y ∈ graphSetBall G S r →
      (G.Adj x y ↔ H.Adj x y)) :
    graphSetBall G S (r + 1) = graphSetBall H S (r + 1) := by
  have hball := graphSetBall_eq_of_incident_agreement G H S r hagree
  rw [graphSetBall_succ_eq G, graphSetBall_succ_eq H, ← hball]
  ext v
  constructor
  · rintro (hv | ⟨u, hu, huv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨u, hu, (hagree u v (Or.inl hu)).mp huv⟩
  · rintro (hv | ⟨u, hu, huv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨u, hu, (hagree u v (Or.inl hu)).mpr huv⟩

/-- A vertex with an edge leaving radius r+1 cannot lie in radius r. -/
theorem boundary_leaf_not_inner (G : SimpleGraph V) (S : Set V) (r : ℕ) {l a : V}
    (hla : G.Adj l a) (ha : a ∉ graphSetBall G S (r + 1)) : l ∉ graphSetBall G S r := by
  intro hl
  apply ha
  rw [graphSetBall_succ_eq]
  exact Or.inr ⟨l, hl, hla⟩

/-- Every actual boundary switching preserves the radius-ell root ball. This
metric statement needs only boundary placement, not any selector assumption. -/
theorem sampledSwitching_ball_preserved (G : SimpleGraph V) (T roots : Set V) (ell : ℕ)
    (hT : T = graphSetBall G roots ell) (S : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) :
    graphSetBall ((sampledSwitchingQuad G T S α).apply G) roots ell = T := by
  cases ell with
  | zero =>
      rw [graphSetBall_zero] at hT ⊢
      exact hT.symm
  | succ r =>
      let q := sampledSwitchingQuad G T S α
      have hroot : q.a ∉ graphSetBall G roots r := by
        apply boundary_leaf_not_inner G roots r α.property.1
        simpa only [← hT] using α.property.2.2
      have hinner : graphSetBall G roots r ⊆ T := by
        rw [hT]
        exact graphSetBall_mono_radius G roots (Nat.le_succ r)
      have hext := sampledSwitching_exterior_disjoint G T S α
      have hout : ∀ x ∈ graphSetBall G roots r, x ∉ q.support := by
        intro x hx hsupport
        change x = q.a ∨ x ∈ q.exterior at hsupport
        rcases hsupport with rfl | hex
        · exact hroot hx
        · exact Set.disjoint_left.mp hext hex (hinner hx)
      have hball : graphSetBall G roots (r + 1) = graphSetBall (q.apply G) roots (r + 1) := by
        apply graphSetBall_succ_eq_of_incident_agreement
        intro x y hxy
        rcases hxy with hx | hy
        · exact (q.adj_away G (hout x hx)).symm
        · rw [G.adj_comm, (q.apply G).adj_comm]
          exact (q.adj_away G (hout y hy)).symm
      exact hball.symm.trans hT.symm

noncomputable section
local instance ballPreservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

theorem perform_ball (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i)
    (roots : Set V) (ell : ℕ) (hT : T = graphSetBall s.graph roots ell) :
    graphSetBall (s.perform radius i hI hJ).graph roots ell = T :=
  sampledSwitching_ball_preserved s.graph T roots ell hT s.samples (s.boundary i)

theorem flip_ball (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (roots : Set V) (ell : ℕ) (hT : T = graphSetBall s.graph roots ell) :
    graphSetBall (s.flip radius i).graph roots ell = T := by
  by_cases h : s.Eligible radius i
  · rw [s.flip_eq_perform radius i h]
    exact s.perform_ball radius i h.1 h.2 roots ell hT
  · rw [s.flip_eq_self radius i h]
    exact hT.symm

theorem flips_ball (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι)
    (roots : Set V) (ell : ℕ) (hT : T = graphSetBall s.graph roots ell) :
    graphSetBall (s.flips radius L).graph roots ell = T := by
  induction L generalizing s with
  | nil => exact hT.symm
  | cons i L ih =>
      exact ih (s.flip radius i) (s.flip_ball radius i roots ell hT).symm

variable [Fintype ι]

/-- The original dynamically chosen ball is exactly the new ball after full
resampling. Together with fullResample_induce this proves its graph is unchanged. -/
theorem fullResample_ball (s : LabelledResamplingState V T ι) (radius : ℕ)
    (roots : Set V) (ell : ℕ) (hT : T = graphSetBall s.graph roots ell) :
    graphSetBall (s.fullResample radius).graph roots ell = T := s.flips_ball radius _ roots ell hT

theorem fullResample_neighborhood (s : LabelledResamplingState V T ι) (radius : ℕ)
    (roots : Set V) (ell : ℕ) (hT : T = graphSetBall s.graph roots ell) :
    graphSetBall (s.fullResample radius).graph roots ell = T ∧
      (s.fullResample radius).graph.induce T = s.graph.induce T :=
  ⟨s.fullResample_ball radius roots ell hT, s.fullResample_induce radius⟩

end LabelledResamplingState
end

end LocalLaw
