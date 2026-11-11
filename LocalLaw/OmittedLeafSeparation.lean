import LocalLaw.OmittedAllLeafGeometry
import LocalLaw.ImmersedBallInjection
import LocalLaw.EligibleCentralIsolation

/-! # All actual completion slots are separated

Old fake slots at the same sampled vertex are separated by the actual I
forest test and local injectivity. Distinct sampled endpoints, distinct A
roots, and mixed old/A slots are separated by the literal J/I tests.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance omittedLeafSeparationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

omit [Fintype ι] in
theorem omittedOldCompletion_leaf_separated (g : RegularGraph N d)(hd : 1≤d)
    (T : Set (Fin N))(labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T)(selector h : ℕ)(hh : h+1≤selector)
    (S : Set (Tᶜ : Set (Fin N)))
    (l m : (g.admissibleState T labels samples).OmittedOldLeaves selector S)(hne : l≠m) :
    (h:ℕ∞) < (g.omittedOldCompletion hd T labels samples selector S).graph.edist (.inr l) (.inr m) := by
  let s := g.admissibleState T labels samples
  let H := g.omittedOldCompletion hd T labels samples selector S
  let f := s.omittedOldOriginalHom selector S
  by_cases hb : l.2.val=m.2.val
  · apply lt_of_not_ge
    intro hnear
    obtain ⟨i,hi⟩ := l.2.val.property
    have hp := g.eligible_sample_root_tree_zero_ball T labels samples selector h hh i
      l.2.val.val (Or.inl hi.symm)
    have hmap : ∀v ∈ graphBallVertices H.graph (.inr l) h,
        f v ∈ graphBallVertices (outsideGraph g.graph T) (f (.inr l)) h := by
      intro v hv
      exact (graphHom_edist_le f (.inr l) v).trans hv
    let a : graphBallVertices H.graph (.inr l) h := ⟨.inr l,by simp [graphBallVertices]⟩
    let b : graphBallVertices H.graph (.inr l) h := ⟨.inr m,hnear⟩
    have he : f a.val=f b.val := congrArg Subtype.val hb
    have hab := immersed_ball_injective f (s.omittedOldOriginal_locally_injective selector S)
      (.inr l) h h hmap hp.1 he
    exact hne (Sum.inr.inj (congrArg Subtype.val hab))
  · have hs := s.selectedFirstSet_separated selector l.2.val.val l.2.val.property
      m.2.val.val m.2.val.property (fun h => hb (Subtype.ext h))
    exact ((ENat.coe_le_coe.mpr (by omega : h≤selector)).trans_lt hs).trans_le
      (graphHom_edist_le f (.inr l) (.inr m))

theorem omittedAllCompletion_leaves_separated (g : RegularGraph N d)(hd : 1≤d)
    (T : Set (Fin N))(labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T)(selector h : ℕ)(hh : h+1≤selector)
    (S : Set (Tᶜ : Set (Fin N)))
    (l m : (g.admissibleState T labels samples).OmittedOldLeaves selector S ⊕
      (g.admissibleState T labels samples).OmittedExtraLeaves selector S)(hne : l≠m) :
    (h:ℕ∞) < (g.omittedAllCompletion hd T labels samples selector S).graph.edist (.inr l) (.inr m) := by
  let s := g.admissibleState T labels samples
  let C := g.omittedCommonModel T labels samples selector S
  let H0 := g.omittedOldCompletion hd T labels samples selector S
  let H := g.omittedAllCompletion hd T labels samples selector S
  let a : s.OmittedOldLeaves selector S → s.OmittedCore selector S := Sigma.fst
  let b : s.OmittedExtraLeaves selector S → s.OmittedCore selector S := s.omittedExtraRoot selector S
  let e := multiLeafGraph_sum_iso C.graph a b
  have hmixed (l : s.OmittedOldLeaves selector S)(j : s.OmittedExtraLeaves selector S) :
      (h:ℕ∞) < H.graph.edist (.inr (.inl l)) (.inr (.inr j)) := by
    have hp := multiLeafGraph_edist_projection H0.graph (Sum.inl ∘ b) (.inl (.inr l)) (.inr j)
    have hf := g.omittedOld_leaf_extra_mate_far hd T labels samples selector S l j
    have hh' := ((ENat.coe_le_coe.mpr (by omega : h≤selector)).trans_lt hf).trans_le hp
    exact hh'.trans_eq (graphIso_edist e (.inr (.inl l)) (.inr (.inr j)))
  cases l with
  | inl l =>
    cases m with
    | inl m =>
      have hs := g.omittedOldCompletion_leaf_separated hd T labels samples selector h hh S l m
        (fun h => hne (congrArg Sum.inl h))
      have he := graphIso_edist e (.inr (.inl l)) (.inr (.inl m))
      change (multiLeafGraph H0.graph (Sum.inl ∘ b)).edist (.inl (.inr l)) (.inl (.inr m)) = _ at he
      rw [multiLeafGraph_edist_old] at he
      exact hs.trans_eq he
    | inr j => exact hmixed l j
  | inr i =>
    cases m with
    | inl l => simpa only [SimpleGraph.edist_comm] using hmixed l i
    | inr j =>
      have hij : i.val≠j.val := fun h => hne (congrArg Sum.inr (Subtype.ext h))
      have hlabels : labels j.val.val≠labels i.val.val := fun h =>
        hij (Subtype.ext (labels.injective h).symm)
      have hf := s.eligible_boundary_root_far selector i.val (labels j.val.val) hlabels
      let f : C.graph →g outsideGraph g.graph T := ⟨fun v => v.val.val,fun h => h⟩
      have hp := (graphHom_edist_le f (b i) (b j)).trans
        (multiLeafGraph_edist_projection C.graph (s.omittedAllMate selector S) (.inr (.inr i)) (.inr (.inr j)))
      exact ((ENat.coe_le_coe.mpr (by omega : h≤selector)).trans_lt hf).trans_le hp

end RegularGraph
end LocalLaw
