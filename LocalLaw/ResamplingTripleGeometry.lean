import LocalLaw.ResamplingSchedule
import LocalLaw.LocalExcessGeometry
import LocalLaw.CycleSpaceCounting

/-!
# Actual tree geometry around accepted resampling triples

Every labelled exterior triple and each of its neighborhoods below the
selector radius are invariant through the full resampling. An accepted final
augmented neighborhood is a tree, so its actual outside induced neighborhood
is acyclic. Small outside balls near an accepted triple are consequently
trees. Attaching such outside pieces through the interior ball is a separate
global excess-counting step.
-/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState

local instance resamplingTripleGeometryDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} {T : Set V} {ι : Type*}

def triple (s : LabelledResamplingState V T ι) (i : ι) : Set {v : V // v ∉ T} :=
  outsideTriple s.graph T s.samples (s.boundary i)

def tripleBall (s : LabelledResamplingState V T ι) (r : ℕ) (i : ι) : Set {v : V // v ∉ T} :=
  graphSetBall (outsideGraph s.graph T) (s.triple i) r

theorem perform_triple (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).triple j = s.triple j :=
  elementaryOutsideTriple_at_map s.graph T radius s.samples (s.boundary i) hI hJ (s.boundary j)

theorem flip_triple (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι) :
    (s.flip radius i).triple j = s.triple j := by
  by_cases hi : s.Eligible radius i
  · rw [s.flip_eq_perform radius i hi]
    exact s.perform_triple radius i j hi.1 hi.2
  · rw [s.flip_eq_self radius i hi]

theorem flips_triple (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) (j : ι) :
    (s.flips radius L).triple j = s.triple j := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_triple radius i j)

theorem perform_tripleBall (s : LabelledResamplingState V T ι) (radius r : ℕ)
    (hr : r ≤ radius) (i j : ι) (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).tripleBall r j = s.tripleBall r j := by
  have hJr : resamplingIsolation s.graph T r s.samples (s.boundary i) := by
    intro β hβ x hx y hy
    exact (ENat.coe_le_coe.mpr hr).trans_lt (hJ β hβ x hx y hy)
  unfold tripleBall
  rw [s.perform_triple radius i j hI hJ]
  exact (elementaryTripleBall_preserved s.graph T r s.samples (s.boundary i) hJr (s.boundary j)).symm

theorem flip_tripleBall (s : LabelledResamplingState V T ι) (radius r : ℕ)
    (hr : r ≤ radius) (i j : ι) : (s.flip radius i).tripleBall r j = s.tripleBall r j := by
  by_cases hi : s.Eligible radius i
  · rw [s.flip_eq_perform radius i hi]
    exact s.perform_tripleBall radius r hr i j hi.1 hi.2
  · rw [s.flip_eq_self radius i hi]

theorem flips_tripleBall (s : LabelledResamplingState V T ι) (radius r : ℕ)
    (hr : r ≤ radius) (L : List ι) (j : ι) :
    (s.flips radius L).tripleBall r j = s.tripleBall r j := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_tripleBall radius r hr i j)

theorem flip_ITest (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι) :
    (s.flip radius i).ITest radius j ↔ s.ITest radius j := by
  by_cases hi : s.Eligible radius i
  · rw [s.flip_eq_perform radius i hi]
    exact s.perform_ITest radius i j hi.1 hi.2
  · rw [s.flip_eq_self radius i hi]

theorem flips_ITest (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) (j : ι) :
    (s.flips radius L).ITest radius j ↔ s.ITest radius j := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_ITest radius i j)

variable [Fintype ι]

theorem fullResample_triple (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) :
    (s.fullResample radius).triple i = s.triple i := s.flips_triple radius _ i

theorem fullResample_tripleBall (s : LabelledResamplingState V T ι) (radius r : ℕ)
    (hr : r ≤ radius) (i : ι) :
    (s.fullResample radius).tripleBall r i = s.tripleBall r i := s.flips_tripleBall radius r hr _ i

theorem fullResample_ITest (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) :
    (s.fullResample radius).ITest radius i ↔ s.ITest radius i := s.flips_ITest radius _ i

/-- Every accepted final triple neighborhood is a genuine forest in the
actual deleted switched graph, by deleting the extra I-test edge from a tree. -/
theorem fullResample_tripleBall_acyclic (s : LabelledResamplingState V T ι)
    (radius : ℕ) (i : ι) (hi : s.Eligible radius i) :
    ((outsideGraph (s.fullResample radius).graph T).induce
      ((s.fullResample radius).tripleBall radius i)).IsAcyclic := by
  have hI := (s.fullResample_ITest radius i).mpr hi.1
  exact graph_acyclic_of_le (fun _ _ h => Or.inl h) hI.tree.IsAcyclic

/-- Actual small outside balls near an accepted triple are trees. The center
is specified in the original metric; exact neighborhood invariance transfers
it to the switched graph. The inequality 2r≤radius is the source R/8 vs R/4
scale separation in literal integer form. -/
theorem fullResample_local_outside_ball_isTree (s : LabelledResamplingState V T ι)
    (radius r : ℕ) (i : ι) (hi : s.Eligible radius i) (hsmall : 2 * r ≤ radius)
    (x : {v : V // v ∉ T}) (hx : x ∈ s.tripleBall r i) :
    (graphBall (outsideGraph (s.fullResample radius).graph T) x r).IsTree := by
  let t := s.fullResample radius
  let H := outsideGraph t.graph T
  have hr : r ≤ radius := by omega
  have hx' : x ∈ t.tripleBall r i := by rwa [s.fullResample_tripleBall radius r hr i]
  have hsub : ∀ v : graphBallVertices H x r, v.val ∈ t.tripleBall radius i := by
    intro v
    obtain ⟨a, ha, had⟩ := hx'
    refine ⟨a, ha, ?_⟩
    calc
      H.edist a v.val ≤ H.edist a x + H.edist x v.val := H.edist_triangle
      _ ≤ (r : ℕ∞) + (r : ℕ∞) := add_le_add had v.property
      _ ≤ (radius : ℕ∞) := by exact_mod_cast (show r + r ≤ radius by omega)
  let f : graphBall H x r →g H.induce (t.tripleBall radius i) :=
    { toFun := fun v => ⟨v.val, hsub v⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun z : t.tripleBall radius i => z.val) h
  refine ⟨graphBall_connected H x r, ?_⟩
  intro v p hp
  exact s.fullResample_tripleBall_acyclic radius i hi (p.map f) (hp.map hf)

end LabelledResamplingState
end LocalLaw
