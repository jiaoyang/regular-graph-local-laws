import SpectralConsequences.RegularBoundaryCounts
import LocalLaw.BoundarySchurRows
import LocalLaw.BoundaryDepthAndIncidence

/-! Constant full-root boundary weights and their exact off-diagonal total. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance fullBoundaryWeightsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem finite_constant_offdiag_sum {I:Type*}[Fintype I](w k:ℂ):
    (∑i:I,∑j:I,if i=j then 0 else w*w/k)=
      (Fintype.card I:ℂ)*((Fintype.card I:ℂ)-1)*w^2/k:=by
  classical
  have hin:∀i:I,(∑j:I,if i=j then 0 else w*w/k)=((Fintype.card I:ℂ)-1)*(w*w/k):=by
    intro i
    calc
      _=∑j:I,((w*w/k)-(if i=j then w*w/k else 0)):=by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _=((Fintype.card I:ℂ)-1)*(w*w/k):=by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq,
          Finset.mem_univ,ite_true]
        ring
  simp_rw [hin]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

namespace RegularGraph
variable {N d:ℕ}

def fullBoundaryWeight (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(q z:ℂ)
    (e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℂ:=
  (g.deficient.restrict (graphBallVertices g.graph o ell)).extensionGreen q z
    (cavityBallRoot g.graph o ell) ⟨e.val.1,e.property.2.1⟩

theorem fullBoundaryWeight_eq_radial (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):
    fullBoundaryWeight g o ell q z e=radialRegularColumn d z q (treeEdgeWeight d) ell ell:=by
  have he:g.graph.dist e.val.1 o=ell:=by
    change (g.graph.edist e.val.1 o).toNat=ell
    rw [SimpleGraph.edist_comm,ball_boundary_inner_edist g.graph o ell e,ENat.toNat_coe]
  unfold fullBoundaryWeight
  rw [((g.deficient.restrict _).extensionGreen_isSymm q z).apply,
    full_ball_extension_column g hd o ell hell hTree q z hz hq,he]

theorem fullBoundaryWeight_physical (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hTree:(graphBall g.graph o ell).IsTree)(z:ℂ)(hz:0<z.im)
    (e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):
    fullBoundaryWeight g o ell (semicircleRoot z) z e=
      kestenMcKayTransform d (semicircleRoot z) z*(-semicircleRoot z*treeEdgeWeight d)^ell:=by
  let M:=g.deficient.restrict (graphBallVertices g.graph o ell)
  let root:=cavityBallRoot g.graph o ell
  let leaf:graphBallVertices g.graph o ell:=⟨e.val.1,e.property.2.1⟩
  have he:M.graph.dist leaf root=ell:=by
    change (graphBall g.graph o ell).dist leaf (cavityBallRoot g.graph o ell)=ell
    rw [graphBall_center_distance]
    change (g.graph.edist e.val.1 o).toNat=ell
    rw [SimpleGraph.edist_comm,ball_boundary_inner_edist g.graph o ell e,ENat.toNat_coe]
  change M.extensionGreen (semicircleRoot z) z root leaf=_
  rw [(M.extensionGreen_isSymm _ _).apply,
    M.extensionGreen_zero_deficit_forest_column hd (fun _=>rfl) hTree.IsAcyclic root
      _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le leaf]
  have hr:M.graph.Reachable leaf root:=hTree.isConnected.preconnected leaf root
  simp only [forestKernelColumn,if_pos hr,he]

/-- The source trace correction coefficient is the literal off-diagonal
boundary-weight sum, including all labels and their exact multiplicities. -/
theorem full_boundary_offdiag_correction (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)(z:ℂ)(hz:0<z.im):
    ((∑e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑f:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if e=f then 0 else fullBoundaryWeight g o ell (semicircleRoot z) z e*
          fullBoundaryWeight g o ell (semicircleRoot z) z f/((d-1:ℕ):ℂ))*
      (1+semicircleRoot z*treeEdgeWeight d)^2)=
      traceCorrectionCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z):=by
  let m:=semicircleRoot z
  let md:=kestenMcKayTransform d m z
  let α:=treeEdgeWeight d
  let k:ℂ:=((d-1:ℕ):ℂ)
  have hk:k≠0:=Nat.cast_ne_zero.mpr (by omega)
  have hK:k^ell≠0:=pow_ne_zero ell hk
  have hα:α^2=1/k:=by dsimp only [α,k];rw [treeEdgeWeight_sq d hd,Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  simp_rw [fullBoundaryWeight_physical g hd o ell hTree z hz]
  rw [finite_constant_offdiag_sum]
  have hcard:(Fintype.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℂ)=
      (d:ℂ)*k^ell:=by
    have hh:=full_tree_ball_boundary_card g hd o ell hell hTree
    rw [Nat.card_eq_fintype_card] at hh
    dsimp only [k]
    exact_mod_cast hh
  rw [hcard]
  change ((d:ℂ)*k^ell*((d:ℂ)*k^ell-1)*(md*(-m*α)^ell)^2/k)*(1+m*α)^2=_
  have hpow:(-m*α)^(2*ell)=m^(2*ell)/k^ell:=by
    calc
      _=((-m*α)^2)^ell:=by rw [←pow_mul]
      _=(m^2*α^2)^ell:=by rw [mul_pow,neg_sq]
      _=m^(2*ell)/k^ell:=by rw [hα,mul_pow,div_pow,one_pow,←pow_mul];ring

  rw [mul_pow,←pow_mul,show ell*2=2*ell by omega,hpow]
  unfold traceCorrectionCoefficient
  change ((d:ℂ)*k^ell*((d:ℂ)*k^ell-1)*(md^2*(m^(2*ell)/k^ell))/k)*(1+m*α)^2=
    (d:ℂ)/k*((d:ℂ)*k^ell-1)*md^2*m^(2*ell)*(1+m*α)^2
  field_simp [hk,hK]
  ring

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.full_boundary_offdiag_correction
