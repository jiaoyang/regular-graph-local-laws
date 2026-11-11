import SpectralConsequences.RegularBallRecursion
import LocalLaw.TreeBoundaryMass

/-! Exact regular-tree columns and root-to-boundary response weights. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance regularTreeWeightsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

/-- Product formula for every radial column, including its actual q dependence. -/
theorem radialRegularColumn_product (d:ℕ)(z q α:ℂ)(ell h:ℕ):
    radialRegularColumn d z q α ell h=regularRootValue d ell q z*(-α)^h*
      ∏j∈Finset.range h,cavityIterate z q (ell-j):=by
  induction h with
  | zero=>simp [radialRegularColumn]
  | succ h ih=>
    rw [radialRegularColumn,ih,Finset.prod_range_succ,pow_succ]
    ring

namespace RegularGraph
variable {N d:ℕ}

theorem full_ball_neighbor_entry (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(v:graphBallVertices g.graph o ell)
    (hvo:g.graph.Adj v.val o):
    (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z v
      (cavityBallRoot g.graph o ell)=
      -treeEdgeWeight d*cavityIterate z q ell*regularRootValue d ell q z:=by
  rw [full_ball_extension_column g hd o ell hell hTree q z hz hq,
    SimpleGraph.dist_eq_one_iff_adj.mpr hvo]
  simp only [radialRegularColumn,Nat.sub_zero]

theorem full_ball_neighbor_ratio (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(v:graphBallVertices g.graph o ell)
    (hvo:g.graph.Adj v.val o):
    (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z v
      (cavityBallRoot g.graph o ell)/
      (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z
        (cavityBallRoot g.graph o ell) (cavityBallRoot g.graph o ell)=
      -treeEdgeWeight d*cavityIterate z q ell:=by
  rw [full_ball_neighbor_entry g hd o ell hell hTree q z hz hq v hvo,
    full_ball_extension_diagonal g hd o ell hell hTree q z hz hq]
  exact mul_div_cancel_right₀ _ (inv_ne_zero (regularRootValue_denominator_nonzero d ell q z hz hq))

end RegularGraph

section BoundaryWeights
variable {V:Type*}[Fintype V][DecidableEq V](G:SimpleGraph V)

/-- The exact full-tree boundary derivative. The radius support and the total
boundary count are derived from the actual tree and homogeneous degrees. -/
theorem regular_tree_boundary_response_sum (d:ℕ)(hd:3≤d)(root:V)(ell:ℕ)(hell:1≤ell)
    (hTree:G.IsTree)(hheight:∀v,G.dist v root≤ell)
    (hdegree:∀v,G.degree v=if G.dist v root<ell then d else if v=root then 0 else 1)
    (m md:ℂ):
    (∑v,(forestBoundaryCoefficient G d root 0 v:ℂ)*md^2*(-m*treeEdgeWeight d)^(2*G.dist v root))=
      regularRootLinearCoefficient d ell m md:=by
  let β:V→ℝ:=forestBoundaryCoefficient G d root 0
  have hβ:∀v,β v=if G.dist v root=ell then 1 else 0:=
    homogeneous_full_boundary_coefficient G d hd root ell hell hheight hdegree
  have hflow:∀v,(treeEdgeWeight d)^(2*G.dist v root)=
      (treeFlowWeight G root ((d:ℝ)-1) v:ℂ):=by
    intro v
    rw [pow_mul,treeEdgeWeight_sq d hd]
    simp only [treeFlowWeight,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_sub,
      Complex.ofReal_natCast,Complex.ofReal_one,one_div]
  have hmass:(∑v,(β v:ℂ)*(treeFlowWeight G root ((d:ℝ)-1) v:ℂ))=
      (d:ℂ)/((d-1:ℕ):ℂ):=by
    have hh:=congrArg (fun x:ℝ=>(x:ℂ)) (tree_boundary_mass G hTree d hd root 0)
    dsimp only [β]
    simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_sub,
      Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_zero,sub_zero,
      Nat.cast_sub (by omega:1≤d),Nat.cast_one] using hh

  calc
    _=md^2*m^(2*ell)*(∑v,(β v:ℂ)*(treeFlowWeight G root ((d:ℝ)-1) v:ℂ)):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      change (β v:ℂ)*md^2*(-m*treeEdgeWeight d)^(2*G.dist v root)=_
      by_cases hv:G.dist v root=ell
      · have hhflow:=hflow v
        rw [hv] at hhflow
        rw [hv,mul_pow,show (-m)^(2*ell)=m^(2*ell) by rw [pow_mul,neg_sq,←pow_mul],←hhflow]
        ring
      · rw [hβ v,if_neg hv]
        simp
    _=regularRootLinearCoefficient d ell m md:=by rw [hmass];unfold regularRootLinearCoefficient;ring

end BoundaryWeights
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.full_ball_neighbor_ratio
#print axioms SpectralConsequences.regular_tree_boundary_response_sum
