import LocalLaw.OmittedOldCompletion
import LocalLaw.MultiLeafBallStability

/-! # Actual extra A slots preserve every old fake-leaf tree patch

I/J places every extra attachment mate beyond the selector from every old
sampled B vertex. The artificial old lost-neighbor ball therefore contains
no extra leaf. Its tree and zero inherited-deficit properties are retained.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance omittedAllLeafGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

omit [Fintype ι] in
theorem omittedOld_leaf_extra_mate_far (g : RegularGraph N d)(hd : 1 ≤ d)
    (T : Set (Fin N))(labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T)(selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))
    (l : (g.admissibleState T labels samples).OmittedOldLeaves selector S)
    (j : (g.admissibleState T labels samples).OmittedExtraLeaves selector S) :
    (selector:ℕ∞) < (g.omittedOldCompletion hd T labels samples selector S).graph.edist
      (.inr l) (.inl ((g.admissibleState T labels samples).omittedExtraRoot selector S j)) := by
  let s := g.admissibleState T labels samples
  obtain ⟨i,hi⟩ := l.2.val.property
  have hfar := s.admissibleSampleVertex_far_boundary selector i (labels j.val.val)
  have hf := graphHom_edist_le (s.omittedOldOriginalHom selector S) (.inr l)
    (.inl (s.omittedExtraRoot selector S j))
  change (selector:ℕ∞) < (outsideGraph g.graph T).edist (s.admissibleSampleVertex selector i)
    (s.admissibleBoundaryVertex selector j.val) at hfar
  change s.admissibleSampleVertex selector i=l.2.val.val at hi
  rw [hi] at hfar
  exact hfar.trans_le hf

theorem omittedAllCompletion_old_leaf_geometry (g : RegularGraph N d)(hd : 1 ≤ d)
    (T : Set (Fin N))(labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T)(selector r : ℕ)(hr : r+1 ≤ selector)
    (S : Set (Tᶜ : Set (Fin N)))
    (l : (g.admissibleState T labels samples).OmittedOldLeaves selector S) :
    let H := g.omittedAllCompletion hd T labels samples selector S
    (graphBall H.graph (.inr (.inl l)) r).IsTree ∧
      ∀v ∈ graphBallVertices H.graph (.inr (.inl l)) r,H.deficit v=0 := by
  dsimp only
  let s := g.admissibleState T labels samples
  let C := g.omittedCommonModel T labels samples selector S
  let H0 := g.omittedOldCompletion hd T labels samples selector S
  let H := g.omittedAllCompletion hd T labels samples selector S
  let a : s.OmittedOldLeaves selector S → s.OmittedCore selector S := Sigma.fst
  let b : s.OmittedExtraLeaves selector S → s.OmittedCore selector S := s.omittedExtraRoot selector S
  let e := multiLeafGraph_sum_iso C.graph a b
  let J := multiLeafGraph H0.graph (Sum.inl ∘ b)
  have hfar : ∀j,(r:ℕ∞) < H0.graph.edist (.inr l) (.inl (b j)) := by
    intro j
    exact (ENat.coe_le_coe.mpr (by omega : r ≤ selector)).trans_lt
      (g.omittedOld_leaf_extra_mate_far hd T labels samples selector S l j)
  have hold := g.omittedOldCompletion_leaf_tree_zero hd T labels samples selector r hr S l
  have ht : (graphBall J (.inl (.inr l)) r).IsTree :=
    multiLeafGraph_ball_tree_of_remote_mates H0.graph (Sum.inl ∘ b) (.inr l) r hfar hold.1
  have himage : ∀v ∈ graphBallVertices H.graph (.inr (.inl l)) r,
      e v ∈ graphBallVertices J (.inl (.inr l)) r := by
    intro v hv
    exact (graphIso_edist e (.inr (.inl l)) v).le.trans hv
  have hloc : GraphHomLocallyInjective e.toHom := by
    intro x y z _ _ h
    exact e.injective h
  constructor
  · exact graphBall_tree_of_locally_injective_hom e.toHom hloc (.inr (.inl l)) r r himage ht
  · intro v hv
    have hv' := himage v hv
    obtain ⟨w,hw⟩ := multiLeafGraph_ball_excludes_leaves H0.graph (Sum.inl ∘ b)
      (.inr l) r hfar (e v) hv'
    have hwball : w ∈ graphBallVertices H0.graph (.inr l) r := by
      have hh := (multiLeafGraph_edist_projection H0.graph (Sum.inl ∘ b)
        (.inl (.inr l)) (e v)).trans hv'
      simpa only [hw,multiLeafProjection,Sum.elim_inl,id_eq] using hh
    cases v with
    | inl v =>
      have hwv : w = .inl v := Sum.inl.inj hw.symm
      have hz := hold.2 (.inl v) (hwv ▸ hwball)
      change C.deficit v-multiLeafMultiplicity (s.omittedAllMate selector S) v=0
      have hle : multiLeafMultiplicity a v ≤ multiLeafMultiplicity (s.omittedAllMate selector S) v := by
        change Nat.card {l:s.OmittedOldLeaves selector S //l.1=v} ≤ _
        rw [Nat.card_congr (s.omittedOldFiberEquiv selector S v),s.omittedAllMultiplicity]
        exact Nat.le_add_right _ _
      exact Nat.eq_zero_of_le_zero ((Nat.sub_le_sub_left hle (C.deficit v)).trans_eq hz)
    | inr v =>
      cases v with
      | inl v => rfl
      | inr j => exact False.elim (Sum.noConfusion hw)

end RegularGraph
end LocalLaw
