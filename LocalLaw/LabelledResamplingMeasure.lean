import LocalLaw.LocalResamplingInvolution
import LocalLaw.OutsideEdgeCounting
import LocalLaw.Assembly

/-!
# The actual labelled local-resampling probability space

On a fixed boundary-size block, retain a uniformly random boundary labeling
as auxiliary data. The actual graph-plus-data involution is transported to the
finite dependent sample space. Fiber counts and induced-T preservation prove
weight preservation; it is not an additional resampling hypothesis.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance labelledMeasureDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual regular graphs whose fixed T boundary has exactly μ labels. -/
def RegularBoundaryBlock (N d μ : ℕ) (T : Set (Fin N)) : Type :=
  {g : RegularGraph N d // Nat.card (BoundaryOrientedEdge g.graph T) = μ}

instance regularBoundaryBlockFintype (N d μ : ℕ) (T : Set (Fin N)) :
    Fintype (RegularBoundaryBlock N d μ T) := by
  unfold RegularBoundaryBlock
  infer_instance

/-- Retaining the label equivalence makes the combinatorial inverse literal. -/
def LabelledBoundaryFiber {N d μ : ℕ} {T : Set (Fin N)} (g : RegularBoundaryBlock N d μ T) : Type :=
  (Fin μ ≃ BoundaryOrientedEdge g.val.graph T) × LocalSamplingFiber g.val.graph T

instance labelledBoundaryFiberFintype {N d μ : ℕ} {T : Set (Fin N)}
    (g : RegularBoundaryBlock N d μ T) : Fintype (LabelledBoundaryFiber g) := by
  unfold LabelledBoundaryFiber
  infer_instance

/-- There is an actual boundary labeling for each graph in the boundary block. -/
def boundaryBlockLabel {N d μ : ℕ} {T : Set (Fin N)} (g : RegularBoundaryBlock N d μ T) :
    Fin μ ≃ BoundaryOrientedEdge g.val.graph T :=
  Fintype.equivOfCardEq (by
    have h : Fintype.card (BoundaryOrientedEdge g.val.graph T) = μ := by
      simpa only [Nat.card_eq_fintype_card] using g.property
    simpa only [Fintype.card_fin] using h.symm)

/-- Exact label-times-sampling count: μ! labelings and O^μ sample assignments. -/
theorem labelledBoundaryFiber_card {N d μ : ℕ} {T : Set (Fin N)}
    (g : RegularBoundaryBlock N d μ T) :
    Fintype.card (LabelledBoundaryFiber g) =
      μ.factorial * (Fintype.card (OutsideOrientedEdge g.val.graph T)) ^ μ := by
  have hlabel : Fintype.card (Fin μ ≃ BoundaryOrientedEdge g.val.graph T) = μ.factorial := by
    simpa only [Fintype.card_fin] using Fintype.card_equiv (boundaryBlockLabel g)
  have hboundary : Fintype.card (BoundaryOrientedEdge g.val.graph T) = μ := by
    simpa only [Nat.card_eq_fintype_card] using g.property
  simp only [LabelledBoundaryFiber, Fintype.card_prod, hlabel,
    LocalSamplingFiber, Fintype.card_fun, hboundary]

/-- Nonempty outside samples imply nonempty labelled fibers. -/
theorem labelledBoundaryFiber_nonempty {N d μ : ℕ} {T : Set (Fin N)}
    (g : RegularBoundaryBlock N d μ T) (hout : Nonempty (OutsideOrientedEdge g.val.graph T)) :
    Nonempty (LabelledBoundaryFiber g) := by
  obtain ⟨S⟩ := localSamplingFiber_nonempty g.val.graph T hout
  exact ⟨boundaryBlockLabel g, S⟩

/-- The actual labelled state with regularity retained as a proved property. -/
def RegularLabelledState (N d μ : ℕ) (T : Set (Fin N)) : Type :=
  {s : LabelledResamplingState (Fin N) T (Fin μ) // s.graph.IsRegularOfDegree d}

/-- Exact identification of the dependent graph/fiber space with the actual
labelled state used by the proved switching involution. -/
def labelledBlockStateEquiv (N d μ : ℕ) (T : Set (Fin N)) :
    (Σ g : RegularBoundaryBlock N d μ T, LabelledBoundaryFiber g) ≃ RegularLabelledState N d μ T where
  toFun ω := ⟨⟨ω.1.val.graph, ω.2.1, ω.2.2⟩, ω.1.val.regular⟩
  invFun s := ⟨⟨⟨s.val.graph, s.property⟩, by
      have h := Nat.card_congr s.val.boundary
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm⟩,
    s.val.boundary, s.val.samples⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance regularLabelledStateFintype (N d μ : ℕ) (T : Set (Fin N)) :
    Fintype (RegularLabelledState N d μ T) :=
  Fintype.ofEquiv _ (labelledBlockStateEquiv N d μ T)

/-- The real local switching map preserves regularity by its actual degree
preservation theorem. -/
def regularLabelledResample {N d μ : ℕ} {T : Set (Fin N)}
    (s : RegularLabelledState N d μ T) (radius : ℕ) : RegularLabelledState N d μ T :=
  ⟨s.val.fullResample radius, s.val.fullResample_regular radius s.property⟩

theorem regularLabelledResample_twice {N d μ : ℕ} {T : Set (Fin N)}
    (s : RegularLabelledState N d μ T) (radius : ℕ) :
    regularLabelledResample (regularLabelledResample s radius) radius = s := by
  apply Subtype.ext
  exact s.val.fullResample_twice radius

def regularLabelledPermutation (N d μ : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    Equiv.Perm (RegularLabelledState N d μ T) :=
  Function.Involutive.toPerm (fun s => regularLabelledResample s radius)
    (fun s => regularLabelledResample_twice s radius)

/-- The actual finite dependent-space resampling permutation. -/
def labelledBlockPermutation (N d μ : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    Equiv.Perm (Σ g : RegularBoundaryBlock N d μ T, LabelledBoundaryFiber g) :=
  (labelledBlockStateEquiv N d μ T).trans
    ((regularLabelledPermutation N d μ T radius).trans (labelledBlockStateEquiv N d μ T).symm)

theorem labelledBlockPermutation_involutive (N d μ : ℕ) (T : Set (Fin N)) (radius : ℕ) :
    Function.Involutive (labelledBlockPermutation N d μ T radius) := by
  intro ω
  apply (labelledBlockStateEquiv N d μ T).injective
  simp only [labelledBlockPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact regularLabelledResample_twice _ radius

/-- The induced T graph is preserved by the actual resampling, not assumed. -/
theorem labelledBlockPermutation_induce (N d μ : ℕ) (T : Set (Fin N)) (radius : ℕ)
    (ω : Σ g : RegularBoundaryBlock N d μ T, LabelledBoundaryFiber g) :
    ((labelledBlockPermutation N d μ T radius ω).1.val.graph).induce T =
      (ω.1.val.graph).induce T := by
  exact (labelledBlockStateEquiv N d μ T ω).val.fullResample_induce radius

/-- Equal induced T graphs imply equal full labelled-fiber cardinalities. -/
theorem labelledBoundaryFiber_card_invariant {N d μ : ℕ} {T : Set (Fin N)}
    (g h : RegularBoundaryBlock N d μ T) (hinduced : g.val.graph.induce T = h.val.graph.induce T) :
    Fintype.card (LabelledBoundaryFiber g) = Fintype.card (LabelledBoundaryFiber h) := by
  rw [labelledBoundaryFiber_card, labelledBoundaryFiber_card]
  have hout := (g.val.boundary_outside_count_invariant h.val T hinduced).2
  simpa only [Nat.card_eq_fintype_card] using congrArg (fun n => μ.factorial * n ^ μ) hout

/-- The actual involution preserves enlarged weights for every constant base
weight, including original uniform graph weights restricted to this block. -/
theorem labelledBlockWeight_preserved (N d μ : ℕ) (T : Set (Fin N)) (radius : ℕ) (c : ℝ) :
    ∀ ω, finiteFiberWeight (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g)
      (fun _ => c) (labelledBlockPermutation N d μ T radius ω) =
      finiteFiberWeight (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g)
        (fun _ => c) ω := by
  apply finiteFiberWeight_preserved_of_block _ (fun _ => c)
    (fun g : RegularBoundaryBlock N d μ T => g.val.graph.induce T)
    (fun _ _ _ => rfl)
  · intro g h heq
    exact labelledBoundaryFiber_card_invariant g h heq
  · exact labelledBlockPermutation_induce N d μ T radius

section Marginals

variable {N d μ : ℕ} {T : Set (Fin N)}

/-- Marginality of the actual labelled enlarged space under the paper's
small removed-set condition. -/
theorem labelledBlockWeight_projection (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (c : ℝ) (P : RegularBoundaryBlock N d μ T → Prop) :
    eventMass (finiteFiberWeight (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g)
      (fun _ => c)) (fun ω => P ω.1) = eventMass (fun _ : RegularBoundaryBlock N d μ T => c) P := by
  letI : ∀ g : RegularBoundaryBlock N d μ T, Nonempty (LabelledBoundaryFiber g) :=
    fun g => labelledBoundaryFiber_nonempty g (g.val.outside_edge_nonempty T hN hd hT)
  exact finiteFiberWeight_projection _ _ _

/-- Exact stationarity under actual labelled local resampling on a fixed
boundary-size block. The weights may be the original uniform graph weights,
restricted to the block; global normalization is not needed for the identity. -/
theorem labelledBlock_resampling_stationary (hN : 0 < N) (hd : 0 < d)
    (hT : 4 * Nat.card T ≤ N) (radius : ℕ) (c : ℝ)
    (P : RegularBoundaryBlock N d μ T → Prop) :
    eventMass (finiteFiberWeight (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g)
      (fun _ => c)) (fun ω => P (labelledBlockPermutation N d μ T radius ω).1) =
      eventMass (fun _ : RegularBoundaryBlock N d μ T => c) P := by
  calc
    _ = eventMass (finiteFiberWeight
        (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g) (fun _ => c))
          (fun ω => P ω.1) :=
      eventMass_pullback _ (labelledBlockPermutation N d μ T radius)
        (labelledBlockWeight_preserved N d μ T radius c) (fun ω => P ω.1)
    _ = _ := labelledBlockWeight_projection hN hd hT c P

/-- A real reversible extension on each boundary-size block, built from the
actual source involution. No involution, marginality, or weight-preservation
field remains an assumption for this extension. -/
def labelledBlockReversibleExtension (hN : 0 < N) (hd : 0 < d)
    (hT : 4 * Nat.card T ≤ N) (radius : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ReversibleExtension (RegularBoundaryBlock N d μ T) (fun _ => c) := by
  letI : ∀ g : RegularBoundaryBlock N d μ T, Nonempty (LabelledBoundaryFiber g) :=
    fun g => labelledBoundaryFiber_nonempty g (g.val.outside_edge_nonempty T hN hd hT)
  exact finiteFiberExtension
    (fun g : RegularBoundaryBlock N d μ T => LabelledBoundaryFiber g)
    (fun _ => c) (fun _ => hc) (fun g => g.val.graph.induce T)
    (fun _ _ _ => rfl) (fun g h heq => labelledBoundaryFiber_card_invariant g h heq)
    (labelledBlockPermutation N d μ T radius) (labelledBlockPermutation_induce N d μ T radius)
    (labelledBlockPermutation_involutive N d μ T radius)

end Marginals

end LocalLaw
