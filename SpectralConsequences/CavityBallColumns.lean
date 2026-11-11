import SpectralConsequences.RegularBoundaryCounts

/-! Actual cavity-ball radial columns, including the deleted-neighbor model. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance cavityBallColumnsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type*}[Fintype V][DecidableEq V]{d:ℕ}

theorem homogeneous_tree_cavity_column (g : DeficientGraph V d) (hd : 3 ≤ d)
    (root : V) (r : ℕ) (hG : g.graph.IsTree) (hheight : ∀ v, g.graph.dist v root ≤ r)
    (hdeficit : ∀ v, g.deficit v = if v = root then 1 else 0)
    (hdegree : ∀ v, g.graph.degree v = if g.graph.dist v root < r then
      (if v = root then d - 1 else d) else (if v = root then 0 else 1))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (v:V) :
    g.extensionGreen q z v root = radialCavityColumn z q (treeEdgeWeight d) r (g.graph.dist v root) := by
  have hmatrix : g.extensionMatrix q z = radialCavityMatrix g.graph d root r q z := by
    rw [g.extensionMatrix_one_root_deficit root hdeficit q z]
    unfold forestReferenceMatrix radialCavityMatrix
    have hD : (Matrix.diagonal (fun v => (forestBoundaryCoefficient g.graph d root 1 v : ℂ))) =
        Matrix.diagonal (fun v => if g.graph.dist v root = r then 1 else 0) := by
      apply congrArg (fun f : V → ℂ => Matrix.diagonal f)
      funext v
      rw [homogeneous_forest_boundary_coefficient g.graph d hd root r hheight hdegree v]
      split_ifs <;> rfl
    rw [hD]
  change (g.extensionMatrix q z)⁻¹ v root = _
  rw [hmatrix]
  have hu:IsUnit (radialCavityMatrix g.graph d root r q z):=by
    rw [←hmatrix]
    exact g.extensionMatrix_isUnit hd q z hz hq
  exact inverse_column_of_mulVec _ hu _ root
    (radialCavityMatrix_column g.graph d hd root r hG hheight hdegree q z hz hq) v

theorem homogeneous_cavity_ball_column (g : DeficientGraph V d) (hd : 3 ≤ d)
    (root : V) (r : ℕ) (hTree : (graphBall g.graph root r).IsTree)
    (hdeficit : ∀ v ∈ graphBallVertices g.graph root r,
      g.deficit v = if v = root then 1 else 0)
    (hsaturated : ∀ v ∈ graphBallVertices g.graph root r, g.graph.degree v + g.deficit v = d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (v:graphBallVertices g.graph root r) :
    (g.restrict (graphBallVertices g.graph root r)).extensionGreen q z
      v (cavityBallRoot g.graph root r)=
        radialCavityColumn z q (treeEdgeWeight d) r (g.graph.dist v.val root) := by
  let M := g.restrict (graphBallVertices g.graph root r)
  let o := cavityBallRoot g.graph root r
  have hdef : ∀ v, M.deficit v = if v = o then 1 else 0 := by
    intro v
    change g.deficit v.val = _
    rw [hdeficit v.val v.property]
    simp only [o, cavityBallRoot, Subtype.ext_iff]
  have hdegree : ∀ v, M.graph.degree v = if M.graph.dist v o < r then
      (if v = o then d - 1 else d) else (if v = o then 0 else 1) := by
    intro v
    by_cases hint : M.graph.dist v o < r
    · rw [if_pos hint]
      change (graphBall g.graph root r).degree v = _
      rw [graphBall_interior_degree g.graph root r v hint]
      have hh := hsaturated v.val v.property
      have hδ := hdef v
      change g.deficit v.val = _ at hδ
      by_cases hv : v = o
      · rw [if_pos hv] at hδ ⊢
        omega
      · rw [if_neg hv] at hδ ⊢
        omega
    · rw [if_neg hint]
      exact tree_ball_boundary_degree g.graph root r hTree v
        (by
          have hh := graphBall_center_distance_le g.graph root r v
          change M.graph.dist v o ≤ r at hh
          change M.graph.dist v o = r
          omega)
  have hh:=homogeneous_tree_cavity_column M hd o r hTree
    (graphBall_center_distance_le g.graph root r) hdef hdegree q z hz hq v
  have he:M.graph.dist v o=g.graph.dist v.val root:=graphBall_center_distance g.graph root r v
  rw [he] at hh
  exact hh

end DeficientGraph

 theorem radialCavityColumn_fixed (m z α:ℂ)(hm:m^2+z*m+1=0)(ell h:ℕ):
    radialCavityColumn z m α ell h=m*(-m*α)^h:=by
  induction h with
  | zero=>simp only [radialCavityColumn,cavityIterate_fixed_point hm,pow_zero,mul_one]
  | succ h ih=>rw [radialCavityColumn,cavityIterate_fixed_point hm,ih,pow_succ];ring

namespace RegularGraph
variable {N d:ℕ}

theorem deleted_root_ball_cavity_column (g:LocalLaw.RegularGraph N d)(hd:3≤d)
    (j o:Fin N)(ell:ℕ)(hjo:g.graph.Adj j o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (v:graphBallVertices (g.deficient.deleteVertex j).graph ⟨o,hjo.ne.symm⟩ ell):
    ((g.deficient.deleteVertex j).restrict
      (graphBallVertices (g.deficient.deleteVertex j).graph ⟨o,hjo.ne.symm⟩ ell)).extensionGreen q z
      v (cavityBallRoot (g.deficient.deleteVertex j).graph ⟨o,hjo.ne.symm⟩ ell)=
      radialCavityColumn z q (treeEdgeWeight d) ell
        ((g.deficient.deleteVertex j).graph.dist v.val ⟨o,hjo.ne.symm⟩):=by
  let root:{v:Fin N//v≠j}:=⟨o,hjo.ne.symm⟩
  have ht:=deleted_ball_isTree g.graph j root ell hTree
  have hδ:=g.deficient.deleted_tree_ball_one_root_deficit j root hjo ell hTree (fun _ _=>rfl)
  have hsat:∀v∈graphBallVertices (g.deficient.deleteVertex j).graph root ell,
      (g.deficient.deleteVertex j).graph.degree v+(g.deficient.deleteVertex j).deficit v=d:=by
    intro v _
    have hh:=g.deficient.deleteVertex_degree_deficit_sum j v
    change _=g.graph.degree v.val+0 at hh
    simpa only [g.regular v.val,add_zero] using hh
  exact DeficientGraph.homogeneous_cavity_ball_column (g.deficient.deleteVertex j) hd root ell ht
    (fun v hv=>hδ ⟨v,hv⟩) hsat q z hz hq v

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.deleted_root_ball_cavity_column
