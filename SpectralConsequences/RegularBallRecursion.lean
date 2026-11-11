import SpectralConsequences.RegularRootRecursion
import LocalLaw.HomogeneousCavityBall
import LocalLaw.ZeroDeficitForestReference

/-! Exact source X_ell on an actual homogeneous full tree ball. -/
open scoped BigOperators Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance regularBallRecursionDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def radialRegularColumn (d:ℕ)(z q α:ℂ)(r:ℕ):ℕ→ℂ
  | 0=>regularRootValue d r q z
  | h+1=>-α*cavityIterate z q (r-h)*radialRegularColumn d z q α r h

theorem radialRegularColumn_parent (d:ℕ)(z q α:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (r n:ℕ)(hn:n+1≤r):
    (z+cavityIterate z q (r-(n+1)))*radialRegularColumn d z q α r (n+1)=
      α*radialRegularColumn d z q α r n:=by
  have heq:r-n=(r-(n+1))+1:=by omega
  rw [radialRegularColumn,heq]
  linear_combination -(α*radialRegularColumn d z q α r n)*
    cavityIterate_step_product z q hz hq (r-(n+1))

section FiniteTree
variable {V:Type*}[Fintype V][DecidableEq V](G:SimpleGraph V)

theorem radialRegularMatrix_column (d : ℕ) (hd : 3 ≤ d) (root : V) (r : ℕ) (hr : 1≤r)
    (hG : G.IsTree) (hheight : ∀ v, G.dist v root ≤ r)
    (hdegree : ∀ v, G.degree v = if G.dist v root < r then
      d else (if v = root then 0 else 1))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    radialCavityMatrix G d root r q z *ᵥ
      (fun v => radialRegularColumn d z q (treeEdgeWeight d) r (G.dist v root)) = Pi.single root 1 := by
  let α := treeEdgeWeight d
  let F := radialRegularColumn d z q α r
  have hnorm : ((d : ℂ) - 1) * α ^ 2 = 1 := by
    dsimp only [α]
    rw [treeEdgeWeight_sq d hd]
    have hk : (d : ℂ) - 1 ≠ 0 := by
      have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
      exact_mod_cast (show (d : ℝ) - 1 ≠ 0 by linarith)
    field_simp
  funext v
  rw [radialCavityMatrix_mulVec]
  change α * (∑ w ∈ G.neighborFinset v, F (G.dist w root)) - z * F (G.dist v root) -
    q * (if G.dist v root = r then 1 else 0) * F (G.dist v root) = (Pi.single root (1 : ℂ) : V → ℂ) v
  by_cases hv : v = root
  · subst v
    rw [radial_root_neighbor_sum, G.dist_self]
    simp only [Pi.single_apply, if_pos rfl, ite_true]
    have hdeg : G.degree root = d := by
      simpa only [G.dist_self, if_pos (show 0<r by omega)] using hdegree root
    rw [hdeg]
    simp only [if_neg (show ¬(0:ℕ)=r by omega)]
    have hsq : α^2=1/((d:ℂ)-1) := treeEdgeWeight_sq d hd
    have hprod : (-z-(d:ℂ)/((d:ℂ)-1)*cavityIterate z q r)*regularRootValue d r q z=1 := by
      have hden:=regularRootValue_denominator_nonzero d r q z hz hq
      have hkcast:((d-1:ℕ):ℂ)=(d:ℂ)-1:=by rw [Nat.cast_sub (by omega : 1≤d),Nat.cast_one]
      rw [hkcast] at hden
      unfold regularRootValue kestenMcKayTransform
      rw [hkcast]
      exact mul_inv_cancel₀ hden
    change α*((d:ℂ)*(-α*cavityIterate z q r*regularRootValue d r q z))-
      z*regularRootValue d r q z-q*0*regularRootValue d r q z=1
    linear_combination -(d:ℂ)*cavityIterate z q r*regularRootValue d r q z*hsq+hprod

  · rw [Pi.single_apply, if_neg hv]
    obtain ⟨parent, hvp, hp, hfar⟩ := forest_parent_distance hG.IsAcyclic root v (hG.isConnected.preconnected v root) hv
    rw [radial_nonroot_neighbor_sum G root v parent F hvp hfar]
    have hparent := radialRegularColumn_parent d z q α hz hq r (G.dist parent root)
      (by rw [hp]; exact hheight v)
    change (z + cavityIterate z q (r - (G.dist parent root + 1))) * F (G.dist parent root + 1) =
      α * F (G.dist parent root) at hparent
    rw [hp] at hparent
    by_cases hboundary : G.dist v root = r
    · have hdeg : G.degree v = 1 := by
        simpa only [hboundary, lt_self_iff_false, if_false, if_neg hv] using hdegree v
      rw [hdeg]
      simp only [Nat.cast_one, sub_self, zero_mul, zero_add, if_pos hboundary, mul_one]
      rw [hboundary, Nat.sub_self] at hparent
      change (z + q) * F r = α * F (G.dist parent root) at hparent
      rw [hboundary]
      linear_combination -hparent
    · have hinterior : G.dist v root < r := lt_of_le_of_ne (hheight v) hboundary
      have hdeg : G.degree v = d := by simpa only [if_pos hinterior, if_neg hv] using hdegree v
      rw [hdeg, if_neg hboundary]
      have hchild : α * (((d : ℂ) - 1) * F (G.dist v root + 1)) =
          -cavityIterate z q (r - G.dist v root) * F (G.dist v root) := by
        change α * (((d : ℂ) - 1) * (-α * cavityIterate z q (r - G.dist v root) * F (G.dist v root))) = _
        linear_combination -(cavityIterate z q (r - G.dist v root) * F (G.dist v root)) * hnorm
      linear_combination -hparent + hchild

theorem homogeneous_full_boundary_coefficient (d:ℕ)(hd:3≤d)(root:V)(r:ℕ)(hr:1≤r)
    (hheight:∀v,G.dist v root≤r)
    (hdegree:∀v,G.degree v=if G.dist v root<r then d else if v=root then 0 else 1)(v:V):
    forestBoundaryCoefficient G d root 0 v=if G.dist v root=r then 1 else 0:=by
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hk:(d:ℝ)-1≠0:=by linarith
  by_cases hb:G.dist v root=r
  · have hv:v≠root:=by intro he;subst v;rw [G.dist_self] at hb;omega
    have hdeg:G.degree v=1:=by rw [hdegree v,if_neg (by omega),if_neg hv]
    simp only [forestBoundaryCoefficient,ite_self,Nat.cast_zero,sub_zero,hdeg,Nat.cast_one,if_pos hb]
    exact div_self hk
  · have hi:G.dist v root<r:=lt_of_le_of_ne (hheight v) hb
    have hdeg:G.degree v=d:=by rw [hdegree v,if_pos hi]
    simp only [forestBoundaryCoefficient,ite_self,Nat.cast_zero,sub_zero,hdeg,sub_self,zero_div,if_neg hb]

theorem homogeneous_full_inverse_column (d:ℕ)(hd:3≤d)(root:V)(r:ℕ)(hr:1≤r)
    (hG:G.IsTree)(hheight:∀v,G.dist v root≤r)
    (hdegree:∀v,G.degree v=if G.dist v root<r then d else if v=root then 0 else 1)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(v:V):
    (forestReferenceMatrix G d root 0 q z)⁻¹ v root=
      radialRegularColumn d z q (treeEdgeWeight d) r (G.dist v root):=by
  have hm:forestReferenceMatrix G d root 0 q z=radialCavityMatrix G d root r q z:=by
    unfold forestReferenceMatrix radialCavityMatrix
    have hdiag:(Matrix.diagonal (fun v=>(forestBoundaryCoefficient G d root 0 v:ℂ)))=
        Matrix.diagonal (fun v=>if G.dist v root=r then (1:ℂ) else 0):=by
      apply congrArg Matrix.diagonal
      funext w
      rw [homogeneous_full_boundary_coefficient G d hd root r hr hheight hdegree w]
      split_ifs <;> rfl
    rw [hdiag]
  rw [hm]
  have hu:IsUnit (radialCavityMatrix G d root r q z):=by
    have hh:=boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
      (fun v=>if G.dist v root=r then (1:ℝ) else 0)
      (fun v=>by dsimp only;split_ifs <;> norm_num) q z hz hq
    simpa only [radialCavityMatrix,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using hh
  exact inverse_column_of_mulVec _ hu _ root
    (radialRegularMatrix_column G d hd root r hr hG hheight hdegree q z hz hq) v

end FiniteTree

namespace RegularGraph
variable {N d:ℕ}

/-- Actual finite graph model, on its literal induced radius-ell tree ball. -/
theorem full_ball_extension_column (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(v:graphBallVertices g.graph o ell):
    (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z
      v (cavityBallRoot g.graph o ell)=
        radialRegularColumn d z q (treeEdgeWeight d) ell (g.graph.dist v.val o):=by
  let M:=g.deficient.restrict (graphBallVertices g.graph o ell)
  let root:=cavityBallRoot g.graph o ell
  have hzero:∀v,M.deficit v=0:=by intro v;rfl
  have hheight:∀v,M.graph.dist v root≤ell:=graphBall_center_distance_le g.graph o ell
  have hdegree:∀v,M.graph.degree v=if M.graph.dist v root<ell then d else if v=root then 0 else 1:=by
    intro v
    change (graphBall g.graph o ell).degree v=
      if (graphBall g.graph o ell).dist v (cavityBallRoot g.graph o ell)<ell then d
        else if v=cavityBallRoot g.graph o ell then 0 else 1
    by_cases hi:(graphBall g.graph o ell).dist v (cavityBallRoot g.graph o ell)<ell
    · rw [if_pos hi]
      exact (graphBall_interior_degree g.graph o ell v hi).trans (g.regular v.val)
    · rw [if_neg hi]
      exact tree_ball_boundary_degree g.graph o ell hTree v
        (by have hh:=graphBall_center_distance_le g.graph o ell v;omega)
  change (M.extensionMatrix q z)⁻¹ v root=_
  rw [M.extensionMatrix_zero_deficit_forest_form hzero root q z,
    homogeneous_full_inverse_column M.graph d hd root ell hell hTree hheight hdegree q z hz hq v]
  congr 1
  exact graphBall_center_distance g.graph o ell v

theorem full_ball_extension_diagonal (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im):
    (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z
      (cavityBallRoot g.graph o ell) (cavityBallRoot g.graph o ell)=regularRootValue d ell q z:=by
  rw [full_ball_extension_column g hd o ell hell hTree q z hz hq]
  simp only [cavityBallRoot,SimpleGraph.dist_self,radialRegularColumn]

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.full_ball_extension_column
