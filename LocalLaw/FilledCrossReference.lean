import LocalLaw.FilledCrossRows

/-! # The filled finite reference has the actual cut-labelled cross formula -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filledCrossReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def filledCrossGreen (g : RegularGraph N d) (T : Set (Fin N))
    (K : Set (Tᶜ:Set (Fin N))) (q z : ℂ) : Matrix T K ℂ :=
  (g.filledExteriorModel T K).extensionGreen q z |>.submatrix
    (fun x => (filledExteriorInnerEquiv T K).symm x |>.val)
    (fun x => (filledExteriorOutsideIso g.graph T K).symm x |>.val)

theorem filledCrossGreen_formula (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (K : Set (Tᶜ:Set (Fin N)))
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    g.filledCrossGreen T K q z= -(g.filledRetainedGreen T K q z*g.filledCutCoupling T K*
      ((g.deficient.delete T).restrict K).extensionGreen q z) := by
  let M := g.filledExteriorModel T K
  let I := filledExteriorInner T K
  let φ := (filledExteriorInnerEquiv T K).symm
  let ψ := (filledExteriorOutsideIso g.graph T K).symm
  have hh := M.extensionGreen_principal_cross hd I q z hz hq
  have he := congrArg (fun A : Matrix I (Iᶜ:Set (filledExteriorVertices T K)) ℂ => A.submatrix φ ψ) hh
  dsimp only at he
  change ((M.extensionGreen q z).submatrix (Subtype.val:I→_) (Subtype.val:(Iᶜ:Set _)→_)).submatrix φ ψ=
    -(((M.extensionGreen q z).submatrix (Subtype.val:I→_) (Subtype.val:I→_)*
      M.H.submatrix (Subtype.val:I→_) (Subtype.val:(Iᶜ:Set _)→_)*
        (M.delete I).extensionGreen q z).submatrix φ ψ) at he
  rw [Matrix.submatrix_mul _ _ φ ψ ψ ψ.bijective,
    Matrix.submatrix_mul _ _ φ φ ψ φ.bijective] at he
  have hdel := g.deficient.filledExterior_deleted_extensionGreen T K q z
  change (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix
    (filledExteriorOutsideIso g.graph T K) (filledExteriorOutsideIso g.graph T K)=
      (M.delete I).extensionGreen q z at hdel
  have hdel' : ((M.delete I).extensionGreen q z).submatrix ψ ψ=
      ((g.deficient.delete T).restrict K).extensionGreen q z := by
    rw [←hdel]
    ext x y
    rfl
  rw [hdel'] at he
  exact he

theorem filledCrossGreen_row (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (K : Set (Tᶜ:Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T,boundaryOutsideVertex g.graph T e∈K)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (i : T) (j : K) :
    g.filledCrossGreen T K q z i j= -(↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)*
      ∑ a,g.filledRetainedGreen T K q z i (cutInsideVertex g.graph T a)*
        ((g.deficient.delete T).restrict K).extensionGreen q z (g.filledBoundaryVertex T K hK a) j := by
  rw [g.filledCrossGreen_formula hd T K q z hz hq,g.filledCutCoupling_factor T K hK]
  change -((g.filledRetainedGreen T K q z*(cutInnerCoupling g.graph d T*
    endpointProjection (g.filledBoundaryVertex T K hK)))*
      ((g.deficient.delete T).restrict K).extensionGreen q z) i j=_
  have hselect (a : BoundaryOrientedEdge g.graph T) :
      (endpointProjection (g.filledBoundaryVertex T K hK)*
        ((g.deficient.delete T).restrict K).extensionGreen q z) a j=
      ((g.deficient.delete T).restrict K).extensionGreen q z (g.filledBoundaryVertex T K hK a) j := by
    simp [Matrix.mul_apply,endpointProjection,ite_mul]
  have hassoc : g.filledRetainedGreen T K q z*(cutInnerCoupling g.graph d T*
      endpointProjection (g.filledBoundaryVertex T K hK))*((g.deficient.delete T).restrict K).extensionGreen q z=
      (g.filledRetainedGreen T K q z*cutInnerCoupling g.graph d T)*
        (endpointProjection (g.filledBoundaryVertex T K hK)*((g.deficient.delete T).restrict K).extensionGreen q z) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  change -(∑ a,(g.filledRetainedGreen T K q z*cutInnerCoupling g.graph d T) i a*
    (endpointProjection (g.filledBoundaryVertex T K hK)*
      ((g.deficient.delete T).restrict K).extensionGreen q z) a j)=_
  simp only [mul_cutInnerCoupling,hselect,neg_mul,Finset.mul_sum]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end RegularGraph
end LocalLaw
