import LocalLaw.DeletedDiagonalBudget
import LocalLaw.FiniteReferenceModelBounds

/-! # Derived reference-imaginary and boundary bounds for deleted diagonals

The local finite-reference class is a proved consequence of the original
radius budget and common-ball geometry. It supplies both analytic model
inputs in the source variance cap, with a degree-dependent constant.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance deletedDiagonalReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def deletedSensitivityConstant (d : ℕ) : ℝ :=
  8 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1)

theorem deletedSensitivityConstant_nonnegative (d : ℕ) : 0 ≤ deletedSensitivityConstant d := by
  unfold deletedSensitivityConstant coreConvolutionConstant
  positivity

namespace RegularGraph
variable {N d : ℕ}

def deletedDiagonalModel (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ)
    (u : (Tᶜ : Set (Fin N))) :=
  (g.deficient.delete T).restrict (pairBallVertices (outsideGraph g.graph T) u u r)

theorem deletedDiagonalModel_connected (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ)
    (u : (Tᶜ : Set (Fin N))) : (g.deletedDiagonalModel T r u).graph.Connected := by
  have hK : pairBallVertices (outsideGraph g.graph T) u u r =
      graphBallVertices (outsideGraph g.graph T) u r := by
    ext v
    simp only [pairBallVertices, graphBallVertices, Set.mem_setOf_eq, or_self]
  change ((outsideGraph g.graph T).induce (pairBallVertices (outsideGraph g.graph T) u u r)).Connected
  rw [hK]
  exact graphBall_connected _ _ _

theorem deletedP_diagonal_reference_im_bound (g : RegularGraph N d) (hd : 3 ≤ d)
    (o : Fin N) (ell r R : ℕ) (hmargin : r + 2 * ell + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im)
    (u : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    |(g.deletedP (graphBallVertices g.graph o ell) r z (semicircleRoot z) u u).im| ≤
      finiteExtraReferenceConstant d * (graphKestenMcKayReference d z).im := by
  let T := graphBallVertices g.graph o ell
  let M := g.deletedDiagonalModel T r u
  exact (M.finite_class_reference_bounds hd (g.deletedDiagonalModel_connected T r u)
    (g.deleted_diagonal_finiteReferenceBudget o ell r R hmargin hballs u) z hz).2
      (pairBallLeft (outsideGraph g.graph T) u u r) (pairBallRight (outsideGraph g.graph T) u u r)

theorem deletedP_diagonal_boundary_uniform_stability (g : RegularGraph N d) (hd : 3 ≤ d)
    (o : Fin N) (ell r R : ℕ) (hmargin : r + 2 * ell + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (4 * (r : ℝ) + 2) ≤ 1 / 2)
    (u : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    ‖g.deletedP (graphBallVertices g.graph o ell) r z q u u -
      g.deletedP (graphBallVertices g.graph o ell) r z (semicircleRoot z) u u‖ ≤
        deletedSensitivityConstant d * ‖q - semicircleRoot z‖ := by
  let T := graphBallVertices g.graph o ell
  let M := g.deletedDiagonalModel T r u
  have hM : M.graph.Connected := g.deletedDiagonalModel_connected T r u
  have hbudget : M.FiniteReferenceBudget :=
    g.deleted_diagonal_finiteReferenceBudget o ell r R hmargin hballs u
  have hexcess : graphExcess M.graph ≤ finiteOmega d + 1 := by
    have hh := hbudget.complexity_le
    omega
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hdiam : ∀ i j, M.graph.dist i j ≤ 4 * r + 1 :=
    pairBall_distance_bound (outsideGraph g.graph T) u u r
  have hsmall : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((4 * r + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    convert small using 1
    push_cast
    ring
  exact M.reference_boundary_uniform_stability hd hM (finiteOmega d + 1) hexcess z q hz hq
    (finiteExtraReferenceConstant d) hC (4 * r + 1) hdiam
    (M.finite_class_reference_bounds hd hM hbudget z hz).1 hsmall
    (pairBallLeft (outsideGraph g.graph T) u u r) (pairBallRight (outsideGraph g.graph T) u u r)

end RegularGraph
end LocalLaw
