import LocalLaw.OmittedLeafBudget
import LocalLaw.HereditaryReferenceBounds

/-! # Intrinsic diameter of the actual all-slot completion

The common core is an induced old restriction. Its possibly disconnected
intrinsic diameter is controlled by the old finite excess budget. Pendant
slots increase this diameter by at most two, including the extra A slots.
-/

noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance omittedLeafDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem omittedCommonModel_diameter (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ : Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (D : ℕ) (hD : ∀u v,((g.deficient.delete T).restrict S).graph.dist u v ≤ D)
    (u v : (g.admissibleState T labels samples).OmittedCore selector S) :
    (g.omittedCommonModel T labels samples selector S).graph.dist u v ≤
      hereditaryReferenceRadius d D := by
  let s := g.admissibleState T labels samples
  let K : Set S := {w | w.val ∉ s.selectedFirstSet selector}
  letI : DecidablePred (fun w : S => w ∈ K) := fun _ => Classical.propDecidable _
  let old := (g.deficient.delete T).restrict S
  let e : (g.omittedCommonModel T labels samples selector S).graph ≃g (old.restrict K).graph :=
    { toEquiv :=
        { toFun := fun w => ⟨⟨w.val.val,w.property⟩,w.val.property⟩
          invFun := fun w => ⟨⟨w.val.val,w.property⟩,w.val.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hh := old.finite_class_restriction_intrinsic_diameter hb D hD K (e u) (e v)
  exact (graphIso_dist e u v).symm.le.trans hh

theorem omittedAllCompletion_diameter (g : RegularGraph N d) (hd : 1 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (S : Set (Tᶜ : Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (D : ℕ) (hD : ∀u v,((g.deficient.delete T).restrict S).graph.dist u v ≤ D)
    (u v : (g.admissibleState T labels samples).OmittedCore selector S ⊕
      ((g.admissibleState T labels samples).OmittedOldLeaves selector S ⊕
        (g.admissibleState T labels samples).OmittedExtraLeaves selector S)) :
    (g.omittedAllCompletion hd T labels samples selector S).graph.dist u v ≤
      hereditaryReferenceRadius d D + 2 := by
  exact multiLeafGraph_diameter_bound _ _ _
    (g.omittedCommonModel_diameter T labels samples selector S hb D hD) u v

end RegularGraph
end LocalLaw
