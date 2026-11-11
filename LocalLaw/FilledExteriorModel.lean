import LocalLaw.RestrictionDeletionIdentity
import LocalLaw.SourceBoundarySchur
import LocalLaw.EmbeddedCutIncidence

/-!
# Fill an actual exterior model by the complete retained set

For an arbitrary exterior vertex set K, the full vertex set is T union K.
Deleting its literal copy of T gives exactly the original deficient exterior
restriction, including its actual lost-neighbor deficit. This lets Schur
expansion use the same endpoint kernel as the switching estimates.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filledExteriorModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def filledExteriorVertices (T : Set V) (K : Set (Tᶜ : Set V)) : Set V :=
  T ∪ Subtype.val '' K

def filledExteriorInner (T : Set V) (K : Set (Tᶜ : Set V)) : Set (filledExteriorVertices T K) :=
  {x | x.val ∈ T}

theorem filledExterior_contains_inner (T : Set V) (K : Set (Tᶜ : Set V)) :
    T ⊆ filledExteriorVertices T K := Set.subset_union_left

theorem filledExterior_outside_mem (T : Set V) (K : Set (Tᶜ : Set V)) (x : (Tᶜ : Set V)) :
    x.val ∈ filledExteriorVertices T K ↔ x ∈ K := by
  constructor
  · rintro (h | ⟨y, hy, heq⟩)
    · exact False.elim (x.property h)
    · exact Subtype.val_injective heq ▸ hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

def filledExteriorInnerEquiv (T : Set V) (K : Set (Tᶜ : Set V)) :
    filledExteriorInner T K ≃ T where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def filledExteriorOutsideEquiv (T : Set V) (K : Set (Tᶜ : Set V)) :
    ((filledExteriorInner T K)ᶜ : Set (filledExteriorVertices T K)) ≃ K where
  toFun x := ⟨⟨x.val.val, x.property⟩,
    (filledExterior_outside_mem T K ⟨x.val.val, x.property⟩).mp x.val.property⟩
  invFun x := ⟨⟨x.val.val, Or.inr ⟨x.val, x.property, rfl⟩⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def filledExteriorOutsideIso (G : SimpleGraph V) (T : Set V) (K : Set (Tᶜ : Set V)) :
    outsideGraph (G.induce (filledExteriorVertices T K)) (filledExteriorInner T K) ≃g
      (outsideGraph G T).induce K where
  toEquiv := filledExteriorOutsideEquiv T K
  map_rel_iff' := Iff.rfl

section Finite
variable [Fintype V] [DecidableEq V]
namespace DeficientGraph
variable {d : ℕ}

omit [DecidableEq V] in
theorem filledExterior_deleted_deficit (g : DeficientGraph V d)
    (T : Set V) (K : Set (Tᶜ : Set V))
    (x : ((filledExteriorInner T K)ᶜ : Set (filledExteriorVertices T K))) :
    ((g.restrict (filledExteriorVertices T K)).delete (filledExteriorInner T K)).deficit x =
      ((g.delete T).restrict K).deficit (filledExteriorOutsideIso g.graph T K x) := by
  exact g.restrictionDeletion_deficit (filledExteriorVertices T K) T (filledExteriorInner T K)
    (fun _ => Iff.rfl) (filledExterior_contains_inner T K) x

/-- Exact equality of the genuine deleted inverse with the exterior model.
It holds for every q,z, because the actual deficits and graph are identical. -/
theorem filledExterior_deleted_extensionGreen (g : DeficientGraph V d)
    (T : Set V) (K : Set (Tᶜ : Set V)) (q z : ℂ) :
    (((g.delete T).restrict K).extensionGreen q z).submatrix
      (filledExteriorOutsideIso g.graph T K) (filledExteriorOutsideIso g.graph T K) =
      ((g.restrict (filledExteriorVertices T K)).delete (filledExteriorInner T K)).extensionGreen q z :=
  ((g.delete T).restrict K).extensionGreen_iso
    ((g.restrict (filledExteriorVertices T K)).delete (filledExteriorInner T K))
    (filledExteriorOutsideIso g.graph T K) (g.filledExterior_deleted_deficit T K) q z

end DeficientGraph
namespace RegularGraph
variable {N d : ℕ}

def filledExteriorModel (g : RegularGraph N d) (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N))) :=
  g.deficient.restrict (filledExteriorVertices T K)

def filledRetainedGreen (g : RegularGraph N d) (T : Set (Fin N))
    (K : Set (Tᶜ : Set (Fin N))) (q z : ℂ) : Matrix T T ℂ :=
  (g.filledExteriorModel T K).extensionGreen q z |>.submatrix
    (fun x => (filledExteriorInnerEquiv T K).symm x |>.val)
    (fun x => (filledExteriorInnerEquiv T K).symm x |>.val)

def filledCutCoupling (g : RegularGraph N d) (T : Set (Fin N))
    (K : Set (Tᶜ : Set (Fin N))) : Matrix T K ℂ :=
  g.H.submatrix Subtype.val (fun x => x.val.val)

/-- Literal capture of every boundary edge gives zero retained charge. -/
theorem filledExterior_retained_boundary_zero (g : RegularGraph N d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (x : filledExteriorInner T K) :
    (g.filledExteriorModel T K).boundaryCoefficient x.val = 0 := by
  have hneighbors : ∀ y, g.graph.Adj x.val.val y → y ∈ filledExteriorVertices T K := by
    intro y hxy
    by_cases hy : y ∈ T
    · exact Or.inl hy
    · exact Or.inr ⟨⟨y, hy⟩, hK ⟨(x.val.val, y), hxy, x.property, hy⟩, rfl⟩
  have hdeg := induce_degree_eq_of_neighbors g.graph (filledExteriorVertices T K) x.val hneighbors
  have hdegree : (g.filledExteriorModel T K).graph.degree x.val = d := hdeg.trans (g.regular _)
  change ((d : ℝ) - (0 : ℕ) - ((g.filledExteriorModel T K).graph.degree x.val : ℝ)) / _ = 0
  rw [hdegree]
  simp

/-- The genuine retained finite inverse, now indexed by the original T,
uses exactly the exterior restriction K. -/
theorem filledRetainedGreen_inverse (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (g.filledRetainedGreen T K q z)⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) Subtype.val) z -
        g.filledCutCoupling T K * ((g.deficient.delete T).restrict K).extensionGreen q z *
          (g.filledCutCoupling T K).transpose := by
  let M := g.filledExteriorModel T K
  let I := filledExteriorInner T K
  let φ := (filledExteriorInnerEquiv T K).symm
  let ψ := (filledExteriorOutsideIso g.graph T K).symm
  have hboundary : M.boundaryDiagonal.submatrix (Subtype.val : I → _) (Subtype.val : I → _) = 0 := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp only [DeficientGraph.boundaryDiagonal, Matrix.submatrix_apply, Matrix.diagonal_apply_eq,
        Matrix.zero_apply]
      exact congrArg Complex.ofReal (g.filledExterior_retained_boundary_zero T K hK x)
    · have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      simp [DeficientGraph.boundaryDiagonal, hval]
  have hschur := M.retained_extensionGreen_schur hd I q z hz hq
  rw [hboundary, smul_zero, sub_zero] at hschur
  have hInv := congrArg (fun A : Matrix I I ℂ => A.submatrix φ φ) hschur
  dsimp only at hInv
  rw [← Matrix.inv_submatrix_equiv] at hInv
  have hself : (M.retainedSelfEnergy I q z).submatrix φ φ =
      g.filledCutCoupling T K * ((g.deficient.delete T).restrict K).extensionGreen q z *
        (g.filledCutCoupling T K).transpose := by
    unfold DeficientGraph.retainedSelfEnergy
    rw [Matrix.submatrix_mul _ _ φ ψ φ ψ.bijective,
      Matrix.submatrix_mul _ _ φ ψ ψ ψ.bijective]
    have hdel := g.deficient.filledExterior_deleted_extensionGreen T K q z
    have hdel' : ((M.delete I).extensionGreen q z).submatrix ψ ψ =
        ((g.deficient.delete T).restrict K).extensionGreen q z := by
      change (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix
        (filledExteriorOutsideIso g.graph T K) (filledExteriorOutsideIso g.graph T K) =
          (M.delete I).extensionGreen q z at hdel
      rw [← hdel]
      ext x y
      simp only [Matrix.submatrix_apply]
      rfl
    rw [hdel']
    have hleft : (M.H.submatrix (Subtype.val : I → _) (Subtype.val : (Iᶜ : Set _) → _)).submatrix φ ψ =
        g.filledCutCoupling T K := rfl
    have hright : (M.H.submatrix (Subtype.val : (Iᶜ : Set _) → _) (Subtype.val : I → _)).submatrix ψ φ =
        (g.filledCutCoupling T K).transpose := by
      ext x y
      change g.H x.val.val y.val = g.H y.val x.val.val
      simp only [H, normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
      rw [g.graph.adj_comm]
    rw [hleft, hright]
  change (g.filledRetainedGreen T K q z)⁻¹ = _ at hInv
  change (g.filledRetainedGreen T K q z)⁻¹ =
    (spectralMatrix (M.H.submatrix (Subtype.val : I → _) (Subtype.val : I → _)) z).submatrix φ φ -
      (M.retainedSelfEnergy I q z).submatrix φ φ at hInv
  rw [hself, ← spectralMatrix_principal _ z φ φ.injective] at hInv
  exact hInv


/-- A retained finite Green block is nonsingular in the upper half-plane. -/
theorem filledRetainedGreen_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    IsUnit (g.filledRetainedGreen T K q z) := by
  let M := g.filledExteriorModel T K
  let I := filledExteriorInner T K
  have hdel := (M.delete I).extensionMatrix_isUnit hd q z hz hq
  rw [M.extensionMatrix_delete] at hdel
  have hh := retained_principal_inverse_isUnit I (M.extensionMatrix q z)
    (M.extensionMatrix_isUnit hd q z hz hq) hdel
  exact (Matrix.isUnit_submatrix_equiv (filledExteriorInnerEquiv T K).symm
    (filledExteriorInnerEquiv T K).symm).mpr hh

/-- Equality of the genuine exterior self-energies determines the retained
finite kernels, rather than merely their inverse equations. -/
theorem filledRetainedGreen_eq_of_selfEnergy (g h : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K L : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (hL : ∀ e : BoundaryOrientedEdge h.graph T, boundaryOutsideVertex h.graph T e ∈ L)
    (hinner : g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N) =
      h.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (hself : g.filledCutCoupling T K * ((g.deficient.delete T).restrict K).extensionGreen q z *
        (g.filledCutCoupling T K).transpose =
      h.filledCutCoupling T L * ((h.deficient.delete T).restrict L).extensionGreen q z *
        (h.filledCutCoupling T L).transpose) :
    g.filledRetainedGreen T K q z = h.filledRetainedGreen T L q z := by
  have hInv : (g.filledRetainedGreen T K q z)⁻¹ = (h.filledRetainedGreen T L q z)⁻¹ := by
    rw [g.filledRetainedGreen_inverse hd T K hK q z hz hq,
      h.filledRetainedGreen_inverse hd T L hL q z hz hq, hinner, hself]
  have hh := congrArg (fun A : Matrix T T ℂ => A⁻¹) hInv
  dsimp only at hh
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (g.filledRetainedGreen_isUnit hd T K q z hz hq)),
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (h.filledRetainedGreen_isUnit hd T L q z hz hq))] at hh
  exact hh

end RegularGraph
end Finite
end LocalLaw
