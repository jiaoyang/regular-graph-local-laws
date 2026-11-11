import LocalLaw.DeficitReduction
import LocalLaw.EligibleBoundaryCavity
import LocalLaw.SourceResamplingStructural

/-! # Deficit restoration on every included accepted old boundary root

The outside vertex set is arbitrary. Eligibility gives exactly one old
boundary deficit at each included attachment root, so restoring its unit
is an actual finite model with the inherited reference class.
-/

noncomputable section
namespace LocalLaw
local instance partialDeficitRestorationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type*}

def includedEligibleBoundary (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ:Set V)) : Set S :=
  {x | ∃ i : s.AdmissibleSampleIndex selector,x.val=boundaryOuterEndpoint s.graph T (s.boundary i.val)}

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type}

theorem includedEligibleBoundary_deficit_one (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ:Set (Fin N)))
    (x : S) (hx : x∈(g.admissibleState T labels samples).includedEligibleBoundary selector S) :
    ((g.deficient.delete T).restrict S).deficit x=1 := by
  obtain ⟨i,hi⟩ := hx
  have hh := g.eligible_boundary_one_root_deficit T labels samples selector 0 (Nat.zero_le _) i
    (boundaryOuterEndpoint g.graph T (labels i.val)) (center_mem_graphBall _ _ 0)
  change (g.deficient.delete T).deficit x.val=1
  rw [hi]
  simpa only [if_pos rfl] using hh

def partialRestoredModel (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ:Set (Fin N))) : DeficientGraph S d :=
  ((g.deficient.delete T).restrict S).restoreOneDeficit
    ((g.admissibleState T labels samples).includedEligibleBoundary selector S)
    (fun x hx => by rw [g.includedEligibleBoundary_deficit_one T labels samples selector S x hx]; norm_num)

theorem partialRestoredModel_component_budget (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ:Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget) :
    (g.partialRestoredModel T labels samples selector S).ComponentFiniteReferenceBudget :=
  ((g.deficient.delete T).restrict S).restoreOneDeficit_componentFiniteReferenceBudget _ _ hb

theorem partialRestoredModel_extensionMatrix (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ:Set (Fin N))) (q z : ℂ) :
    (g.partialRestoredModel T labels samples selector S).extensionMatrix q z=
      ((g.deficient.delete T).restrict S).extensionMatrix q z-
        q • Matrix.diagonal (fun v => if v∈(g.admissibleState T labels samples).includedEligibleBoundary selector S
          then ((1/((d:ℝ)-1):ℝ):ℂ) else 0) :=
  ((g.deficient.delete T).restrict S).restoreOneDeficit_extensionMatrix _ _ q z

end RegularGraph
end LocalLaw
