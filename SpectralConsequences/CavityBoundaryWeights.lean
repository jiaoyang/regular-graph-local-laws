import SpectralConsequences.CavityBoundaryActive
import SpectralConsequences.FullBoundaryWeights

/-! Literal truncated-minor boundary columns, zero on the removed branch,
and exact off-diagonal cavity correction weights. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance cavityBoundaryWeightsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

def cavityBoundaryWeight (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)(q z:ℂ)
    (e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℂ:=
  ((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).extensionGreen q z
    (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityBoundaryInner o ell hell j hjo e)

theorem cavityBoundaryWeight_eq_radial (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:2≤ell)(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (e0:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):
    cavityBoundaryWeight g o ell hell j hjo q z e0=
      if cavityBoundaryInnerDeleted g o ell hell j hjo e0∈
        graphBallVertices (g.deficient.deleteVertex j.val).graph ⟨o,hjo.ne.symm⟩ ell
      then radialCavityColumn z q (treeEdgeWeight d) ell ell else 0:=by
  let T:=graphBallVertices g.graph o ell
  let D:=g.deficient.deleteVertex j.val
  let A:Set {v:Fin N//v≠j.val}:={v|v.val∈T}
  let rootD:{v:Fin N//v≠j.val}:=⟨o,hjo.ne.symm⟩
  let B:=graphBallVertices D.graph rootD ell
  let L:=(g.deficient.restrict T).deleteVertex j
  let M:=D.restrict A
  let rootL:=g.truncatedCavityRoot o ell j hjo
  let leafL:=g.truncatedCavityBoundaryInner o ell hell j hjo e0
  let φ:=g.deficient.restrictDeleteVertexIso T j
  have hBA:B⊆A:=by
    intro v hv
    exact (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) {v|v≠j.val}).toHom rootD v).trans hv
  let F:Set A:={v|v.val∈B}
  let rootF:F:=⟨φ rootL,center_mem_graphBall _ _ _⟩
  let φB:(M.restrict F).graph≃g(D.restrict B).graph:=inducePreimageIso D.graph A B hBA
  have hcut:∀x∈F,∀y∉F,¬M.graph.Adj x y:=by
    intro x hx y hy hxy
    exact hy (tree_deleted_ball_closed_in_root_ball g.graph j.val o ell hjo hTree hx y.property hxy)
  have hmodel:=M.extensionGreen_iso L φ (g.deficient.restrictDeleteVertex_deficit T j) q z
  have hmodelEntry:M.extensionGreen q z (φ rootL) (φ leafL)=L.extensionGreen q z rootL leafL:=
    congrFun (congrFun hmodel rootL) leafL
  change L.extensionGreen q z rootL leafL=_
  rw [←hmodelEntry]
  by_cases hactive:cavityBoundaryInnerDeleted g o ell hell j hjo e0∈B
  · rw [if_pos hactive]
    let leafF:F:=⟨φ leafL,hactive⟩
    let leafB:B:=⟨cavityBoundaryInnerDeleted g o ell hell j hjo e0,hactive⟩
    have hblock:=M.restrict_extensionGreen_of_isolated hd F hcut q z hz hq
    have hblockEntry:(M.restrict F).extensionGreen q z rootF leafF=M.extensionGreen q z (φ rootL) (φ leafL):=
      congrFun (congrFun hblock rootF) leafF
    have hball:=(D.restrict B).extensionGreen_iso (M.restrict F) φB (fun _=>rfl) q z
    have hballEntry:=(congrFun (congrFun hball rootF) leafF)
    rw [←hblockEntry,←hballEntry]
    change (D.restrict B).extensionGreen q z (cavityBallRoot D.graph rootD ell) leafB=_
    rw [((D.restrict B).extensionGreen_isSymm q z).apply]
    rw [deleted_root_ball_cavity_column g hd j.val o ell hjo hTree q z hz hq leafB]
    have hlo:(ell:ℕ∞)≤D.graph.edist rootD leafB.val:=by
      have hh:=graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) {v|v≠j.val}).toHom rootD leafB.val
      change g.graph.edist o e0.val.1≤_ at hh
      rwa [ball_boundary_inner_edist g.graph o ell e0] at hh
    have heq:D.graph.edist rootD leafB.val=(ell:ℕ∞):=le_antisymm hactive hlo
    have hdist:D.graph.dist leafB.val rootD=ell:=by
      change (D.graph.edist leafB.val rootD).toNat=ell
      rw [SimpleGraph.edist_comm,heq,ENat.toNat_coe]
    rw [hdist]
  · rw [if_neg hactive]
    exact M.extensionGreen_zero_across_cut hd F hcut q z hz hq (φ rootL) rootF.property (φ leafL) hactive

theorem cavityBoundaryWeight_active_physical (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:2≤ell)(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(z:ℂ)(hz:0<z.im)
    (e:ActiveCavityBoundary g o ell hell j hjo):
    cavityBoundaryWeight g o ell hell j hjo (semicircleRoot z) z e.val=
      semicircleRoot z*(-semicircleRoot z*treeEdgeWeight d)^ell:=by
  rw [cavityBoundaryWeight_eq_radial g hd o ell hell j hjo hTree _ z hz (semicircleRoot_im_pos hz).le,
    if_pos e.property,radialCavityColumn_fixed _ _ _ (semicircleRoot_equation z)]

/-- The physical cavity correction is the exact active off-diagonal weight
sum; the branch removed by j contributes identically zero. -/
theorem cavity_boundary_offdiag_correction (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:2≤ell)(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(z:ℂ)(hz:0<z.im):
    ((∑e:ActiveCavityBoundary g o ell hell j hjo,∑f:ActiveCavityBoundary g o ell hell j hjo,
      if e=f then 0 else cavityBoundaryWeight g o ell hell j hjo (semicircleRoot z) z e.val*
        cavityBoundaryWeight g o ell hell j hjo (semicircleRoot z) z f.val/((d-1:ℕ):ℂ))*
      (1+semicircleRoot z*treeEdgeWeight d)^2)=cavityCorrectionCoefficient d ell (semicircleRoot z):=by
  let m:=semicircleRoot z
  let α:=treeEdgeWeight d
  let k:ℂ:=((d-1:ℕ):ℂ)
  have hk:k≠0:=Nat.cast_ne_zero.mpr (by omega)
  have hK:k^ell≠0:=pow_ne_zero ell hk
  have hα:α^2=1/k:=by dsimp only [α,k];rw [treeEdgeWeight_sq d hd,Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  simp_rw [cavityBoundaryWeight_active_physical g hd o ell hell j hjo hTree z hz]
  rw [finite_constant_offdiag_sum]
  have hcard:(Fintype.card (ActiveCavityBoundary g o ell hell j hjo):ℂ)=k^(ell+1):=by
    have hh:=activeCavityBoundary_card g hd o ell hell j hjo hTree
    rw [Nat.card_eq_fintype_card] at hh
    dsimp only [k]
    exact_mod_cast hh
  rw [hcard]
  change (k^(ell+1)*(k^(ell+1)-1)*(m*(-m*α)^ell)^2/k)*(1+m*α)^2=_
  have hpow:(-m*α)^(2*ell)=m^(2*ell)/k^ell:=by
    calc
      _=((-m*α)^2)^ell:=by rw [←pow_mul]
      _=(m^2*α^2)^ell:=by rw [mul_pow,neg_sq]
      _=m^(2*ell)/k^ell:=by rw [hα,mul_pow,div_pow,one_pow,←pow_mul];ring
  rw [mul_pow,←pow_mul,show ell*2=2*ell by omega,hpow]
  unfold cavityCorrectionCoefficient
  change (k^(ell+1)*(k^(ell+1)-1)*(m^2*(m^(2*ell)/k^ell))/k)*(1+m*α)^2=
    (k^(ell+1)-1)*m^(2*ell+2)*(1+m*α)^2
  rw [pow_succ,pow_add]
  field_simp [hk,hK]
  ring

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.cavity_boundary_offdiag_correction
