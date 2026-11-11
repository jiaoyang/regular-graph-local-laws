import LocalLaw.TargetModelDeletionComparison
import LocalLaw.DeletedNeighborhoodDiameter

/-!
# Actual original-graph comparison after neighborhood deletion

The finite model is the concrete union of three graph balls. Its reference
budgets, full and deleted diameter caps, removed-set identity and Schur sums
are all derived. Only the four full Green approximation blocks and the
literal finite numerical absorption conditions remain as inputs.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance neighborhoodDeletionComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section SetCongruence
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem green_reindex_equiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (H : Matrix J J ℂ) (e : I ≃ J) (z : ℂ) :
    green (H.submatrix e e) z = (green H z).submatrix e e := by
  unfold green
  rw [spectralMatrix_principal H z e e.injective, Matrix.inv_submatrix_equiv]

omit [Fintype A] in
theorem green_principal_entry_set_congr (H : Matrix A A ℂ) (z : ℂ) (S T : Set A) (hST : S = T)
    [Fintype S] [Fintype T]
    (i j : A) (hiS : i ∈ S) (hjS : j ∈ S) (hiT : i ∈ T) (hjT : j ∈ T) :
    green (H.submatrix (Subtype.val : S → A) (Subtype.val : S → A)) z ⟨i, hiS⟩ ⟨j, hjS⟩ =
      green (H.submatrix (Subtype.val : T → A) (Subtype.val : T → A)) z ⟨i, hiT⟩ ⟨j, hjT⟩ := by
  let φ := Equiv.setCongr hST
  have hmatrix : H.submatrix (Subtype.val : S → A) (Subtype.val : S → A) =
      (H.submatrix (Subtype.val : T → A) (Subtype.val : T → A)).submatrix φ φ := by
    ext x y
    rfl
  have hh := green_reindex_equiv (H.submatrix (Subtype.val : T → A) (Subtype.val : T → A)) φ z
  rw [← hmatrix] at hh
  exact congrFun (congrFun hh ⟨i, hiS⟩) ⟨j, hjS⟩

end SetCongruence

variable {V : Type*}

def deletionNeighborhoodOutsideLeft (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hi : i ∉ graphBallVertices G o ell) :
    ((deletionNeighborhoodInnerSet G o i j ell r)ᶜ : Set (deletionNeighborhoodVertices G o i j ell r)) :=
  ⟨deletionNeighborhoodLeft G o i j ell r, fun hh => hi
    ((deletionNeighborhood_inner_mem G o i j ell r _).mp hh)⟩

def deletionNeighborhoodOutsideRight (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hj : j ∉ graphBallVertices G o ell) :
    ((deletionNeighborhoodInnerSet G o i j ell r)ᶜ : Set (deletionNeighborhoodVertices G o i j ell r)) :=
  ⟨deletionNeighborhoodRight G o i j ell r, fun hh => hj
    ((deletionNeighborhood_inner_mem G o i j ell r _).mp hh)⟩

namespace RegularGraph
variable {N d : ℕ}

theorem deficient_deleted_G_eq_principal (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) :
    (g.deficient.delete T).G z =
      green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z := by
  change green (g.deficient.delete T).H z = _
  rw [g.deficient.H_delete]
  rfl

/-- The physical original-graph deletion comparison with all finite-model
geometry and cross-sum estimates discharged from the structural ball bound.
The four approximation blocks are precisely those supplied by localization
around the removed set and the two targets. -/
theorem neighborhood_deleted_comparison (g : RegularGraph N d) (hd : 3 ≤ d)
    (o i j : Fin N) (ell r R : ℕ) (hr : 1 ≤ r)
    (hi : i ∉ graphBallVertices g.graph o ell) (hj : j ∉ graphBallVertices g.graph o ell)
    (hmargin : 6 * (ell + r) + 2 ≤ R)
    (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (hqnear : ‖q - semicircleRoot z‖ ≤ 1)
    (smallRef : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((6 * (ell + r) + 2 : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallDel : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) *
        ((2 * r + (finiteOmega d + 2) * (2 * r + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hTT : ∀ x y : deletionNeighborhoodInnerSet g.graph o i j ell r,
      ‖g.G z x.val.val y.val.val -
        (g.deletionNeighborhoodModel o i j ell r).extensionGreen q z x.val y.val‖ ≤ δ)
    (hrowError : ∀ x : deletionNeighborhoodInnerSet g.graph o i j ell r,
      ‖g.G z i x.val.val - (g.deletionNeighborhoodModel o i j ell r).extensionGreen q z
        (deletionNeighborhoodLeft g.graph o i j ell r) x.val‖ ≤ δ)
    (hcolumnError : ∀ y : deletionNeighborhoodInnerSet g.graph o i j ell r,
      ‖g.G z y.val.val j - (g.deletionNeighborhoodModel o i j ell r).extensionGreen q z
        y.val (deletionNeighborhoodRight g.graph o i j ell r)‖ ≤ δ)
    (htarget : ‖g.G z i j - (g.deletionNeighborhoodModel o i j ell r).extensionGreen q z
      (deletionNeighborhoodLeft g.graph o i j ell r) (deletionNeighborhoodRight g.graph o i j ell r)‖ ≤ δ)
    (smallCut : (Nat.card (graphBallVertices g.graph o ell) : ℝ) *
      DeficientGraph.boundarySchurConstant d B * δ ≤ 1 / 2) :
    ‖(g.deficient.delete (graphBallVertices g.graph o ell)).G z ⟨i, hi⟩ ⟨j, hj⟩ -
        ((g.deletionNeighborhoodModel o i j ell r).delete
          (deletionNeighborhoodInnerSet g.graph o i j ell r)).extensionGreen q z
          (deletionNeighborhoodOutsideLeft g.graph o i j ell r hi)
          (deletionNeighborhoodOutsideRight g.graph o i j ell r hj)‖ ≤
      modelDeletionErrorConstant d ell (Nat.card (graphBallVertices g.graph o ell)) B δ * δ := by
  let M := g.deletionNeighborhoodModel o i j ell r
  let T := deletionNeighborhoodInnerSet g.graph o i j ell r
  let root := deletionNeighborhoodRoot g.graph o i j ell r
  let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
  let ii := deletionNeighborhoodOutsideLeft g.graph o i j ell r hi
  let jj := deletionNeighborhoodOutsideRight g.graph o i j ell r hj
  have hMbudget := g.deletionNeighborhoodModel_component_budget o i j ell r R hmargin hballs
  have himage : e '' T = graphBallVertices g.graph o ell :=
    deletionNeighborhood_inner_ball_image g.graph o i j ell r
  have hcard : Nat.card T = Nat.card (graphBallVertices g.graph o ell) := by
    exact Nat.card_congr ((Equiv.Set.image (e : _ → Fin N) T e.injective).trans (Equiv.setCongr himage))
  have hsmall : (Nat.card T : ℝ) * DeficientGraph.boundarySchurConstant d B * δ ≤ 1 / 2 := by
    rw [hcard]
    exact smallCut
  have hcomp := componentwise_embedded_target_deletion_comparison M hd
    (g.deletionNeighborhoodModel_zero_deficit o i j ell r) hMbudget
    g.H (normalizedAdjacency_isHermitian g.graph d) e root ell T rfl q z hz hq B hB hqnear
    (6 * (ell + r) + 2) (deletionNeighborhood_distance_bound g.graph o i j ell r) smallRef
    (2 * r + (finiteOmega d + 2) * (2 * r + 1))
    (deletedNeighborhood_distance_bound g.graph o i j ell r R (finiteOmega d) hr hi hj hmargin (hballs o))
    smallDel δ hδ ii jj hTT hrowError hcolumnError htarget hsmall
  have hphysical : green (g.H.submatrix (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)) z
        (embeddingOutsideImage e T ii) (embeddingOutsideImage e T jj) =
      (g.deficient.delete (graphBallVertices g.graph o ell)).G z ⟨i, hi⟩ ⟨j, hj⟩ := by
    rw [g.deficient_deleted_G_eq_principal]
    exact green_principal_entry_set_congr g.H z ((e '' T)ᶜ) ((graphBallVertices g.graph o ell)ᶜ)
      (congrArg HasCompl.compl himage) i j (embeddingOutsideImage e T ii).property
        (embeddingOutsideImage e T jj).property hi hj
  rw [hphysical, hcard] at hcomp
  exact hcomp

end RegularGraph
end LocalLaw
