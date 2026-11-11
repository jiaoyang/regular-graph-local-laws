import LocalLaw.LabelledResamplingMeasure

/-!
# Global uniform graph law under labelled local resampling

Every regular graph belongs to exactly one finite boundary-size block. Summing
the proved fixed-block identities gives an actual reversible extension of the
original uniform regular-graph law, with no assumed marginality, involution,
or weight preservation. The removed vertex set T is fixed in this module.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000
noncomputable section

namespace LocalLaw

local instance globalLabelledDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Boundary sizes range over a finite set, since every boundary edge is an
oriented edge and the total number of oriented edges is Nd. -/
theorem regular_boundary_size_le {N d : ℕ} (g : RegularGraph N d) (T : Set (Fin N)) :
    Nat.card (BoundaryOrientedEdge g.graph T) ≤ N * d := by
  have h := g.outside_count_identity T
  omega

/-- The finite disjoint decomposition of the actual graph ensemble by its
boundary size, not merely a counting assumption. -/
def regularBoundaryDecomposition (N d : ℕ) (T : Set (Fin N)) :
    (Σ μ : Fin (N * d + 1), RegularBoundaryBlock N d μ.val T) ≃ RegularGraph N d where
  toFun ω := ω.2.val
  invFun g := ⟨⟨Nat.card (BoundaryOrientedEdge g.graph T),
    Nat.lt_succ_of_le (regular_boundary_size_le g T)⟩, g, rfl⟩
  left_inv ω := by
    rcases ω with ⟨⟨μ, hμ⟩, ⟨g, hg⟩⟩
    cases hg
    rfl
  right_inv _ := rfl

/-- All actual labelled sample states, with the boundary size retained only
as a finite auxiliary index. -/
def GlobalLabelledSpace (N d : ℕ) (T : Set (Fin N)) : Type :=
  Σ μ : Fin (N * d + 1), Σ g : RegularBoundaryBlock N d μ.val T, LabelledBoundaryFiber g

instance globalLabelledSpaceFintype (N d : ℕ) (T : Set (Fin N)) :
    Fintype (GlobalLabelledSpace N d T) := by
  unfold GlobalLabelledSpace
  infer_instance

/-- Projection to the original regular graph. -/
def globalLabelledProject {N d : ℕ} {T : Set (Fin N)} (ω : GlobalLabelledSpace N d T) :
    RegularGraph N d := ω.2.1.val

/-- Original uniform graph weight divided by its full labelled sample-fiber
cardinality. Different graphs may have different sample-fiber cardinalities. -/
def globalLabelledWeight (N d : ℕ) (T : Set (Fin N)) (ω : GlobalLabelledSpace N d T) : ℝ :=
  finiteFiberWeight (fun g : RegularBoundaryBlock N d ω.1.val T => LabelledBoundaryFiber g)
    (fun _ => (1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ)) ω.2

theorem globalLabelledWeight_nonnegative (N d : ℕ) (T : Set (Fin N))
    (ω : GlobalLabelledSpace N d T) : 0 ≤ globalLabelledWeight N d T ω :=
  finiteFiberWeight_nonneg _ _ (fun _ => by positivity) ω.2

/-- The actual source resampling, preserving each boundary-size component. -/
def globalLabelledResample (N d : ℕ) (T : Set (Fin N)) (radius : ℕ)
    (ω : GlobalLabelledSpace N d T) : GlobalLabelledSpace N d T :=
  ⟨ω.1, labelledBlockPermutation N d ω.1.val T radius ω.2⟩

theorem globalLabelledResample_involutive (N d : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    Function.Involutive (globalLabelledResample N d T radius) := by
  rintro ⟨μ, ω⟩
  exact congrArg (fun s : Σ g : RegularBoundaryBlock N d μ.val T, LabelledBoundaryFiber g =>
    (⟨μ, s⟩ : GlobalLabelledSpace N d T))
      (labelledBlockPermutation_involutive N d μ.val T radius ω)

def globalLabelledPermutation (N d : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    Equiv.Perm (GlobalLabelledSpace N d T) :=
  Function.Involutive.toPerm (globalLabelledResample N d T radius)
    (globalLabelledResample_involutive N d T radius)

/-- The actual global permutation preserves the constructed weights, by the
proved fixed-block weight theorem. -/
theorem globalLabelledWeight_preserved (N d : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    ∀ ω, globalLabelledWeight N d T (globalLabelledPermutation N d T radius ω) =
      globalLabelledWeight N d T ω := by
  rintro ⟨μ, ω⟩
  exact labelledBlockWeight_preserved N d μ.val T radius
    ((1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ)) ω

/-- Summing the boundary blocks recovers the original uniform graph event
mass exactly. -/
theorem regularBoundaryDecomposition_mass (N d : ℕ) (T : Set (Fin N))
    (P : RegularGraph N d → Prop) :
    (∑ μ : Fin (N * d + 1), eventMass
      (fun _g : RegularBoundaryBlock N d μ.val T =>
        (1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ)) (fun g => P g.val)) =
      eventMass (finiteUniformWeight (RegularGraph N d)) P := by
  unfold eventMass finiteUniformWeight
  calc
    _ = ∑ ω : Σ μ : Fin (N * d + 1), RegularBoundaryBlock N d μ.val T,
        (if P ω.2.val then (1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ) else 0) :=
      (Fintype.sum_sigma _).symm
    _ = _ := by
      apply Fintype.sum_equiv (regularBoundaryDecomposition N d T)
      intro ω
      rfl

/-- Marginality for the entire original graph ensemble. Nonempty sample
fibers are derived from regularity and the deterministic small-set bound. -/
theorem globalLabelledWeight_projection (N d : ℕ) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (P : RegularGraph N d → Prop) :
    eventMass (globalLabelledWeight N d T) (fun ω => P (globalLabelledProject ω)) =
      eventMass (finiteUniformWeight (RegularGraph N d)) P := by
  calc
    eventMass (globalLabelledWeight N d T) (fun ω => P (globalLabelledProject ω)) =
        ∑ μ : Fin (N * d + 1), eventMass
          (finiteFiberWeight (fun g : RegularBoundaryBlock N d μ.val T => LabelledBoundaryFiber g)
            (fun _ => (1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ))) (fun ω => P ω.1.val) := by
      unfold eventMass
      exact Fintype.sum_sigma (fun ω : GlobalLabelledSpace N d T =>
        if P (globalLabelledProject ω) then globalLabelledWeight N d T ω else 0)
    _ = ∑ μ : Fin (N * d + 1), eventMass
        (fun _g : RegularBoundaryBlock N d μ.val T =>
          (1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ)) (fun g => P g.val) := by
      apply Finset.sum_congr rfl
      intro μ _
      exact labelledBlockWeight_projection (N := N) (d := d) (μ := μ.val) (T := T)
        hN hd hT ((1 : ℝ) / (Fintype.card (RegularGraph N d) : ℝ)) (fun g => P g.val)
    _ = _ := regularBoundaryDecomposition_mass N d T P

/-- The enlarged graph-plus-label-plus-samples weights are a genuine
probability distribution whenever the original graph ensemble is nonempty. -/
theorem globalLabelledWeight_normalized (N d : ℕ) (T : Set (Fin N))
    [Nonempty (RegularGraph N d)] (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) :
    (∑ ω : GlobalLabelledSpace N d T, globalLabelledWeight N d T ω) = 1 := by
  have h := globalLabelledWeight_projection N d T hN hd hT (fun _ => True)
  have hbase := finiteUniformWeight_total (Γ := RegularGraph N d)
  simpa only [eventMass, if_true, hbase] using h

/-- Source Proposition 3.5 for the actual labelled finite local-resampling
kernel and the full original uniform regular-graph ensemble, for fixed T. -/
theorem global_labelled_resampling_stationary (N d : ℕ) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) (radius : ℕ)
    (P : RegularGraph N d → Prop) :
    eventMass (globalLabelledWeight N d T)
      (fun ω => P (globalLabelledProject (globalLabelledPermutation N d T radius ω))) =
      eventMass (finiteUniformWeight (RegularGraph N d)) P := by
  calc
    _ = eventMass (globalLabelledWeight N d T) (fun ω => P (globalLabelledProject ω)) :=
      eventMass_pullback _ (globalLabelledPermutation N d T radius)
        (globalLabelledWeight_preserved N d T radius) (fun ω => P (globalLabelledProject ω))
    _ = _ := globalLabelledWeight_projection N d T hN hd hT P

/-- Actual reversible extension of the original uniform graph law. All
combinatorial and probability fields are proved from the finite source data. -/
def globalLabelledReversibleExtension (N d : ℕ) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) (radius : ℕ) :
    ReversibleExtension (RegularGraph N d) (finiteUniformWeight (RegularGraph N d)) where
  space := GlobalLabelledSpace N d T
  finite := inferInstance
  weight := globalLabelledWeight N d T
  nonnegative := globalLabelledWeight_nonnegative N d T
  project := globalLabelledProject
  marginal := globalLabelledWeight_projection N d T hN hd hT
  switching := globalLabelledPermutation N d T radius
  preserve := globalLabelledWeight_preserved N d T radius
  involution := globalLabelledResample_involutive N d T radius

end LocalLaw
