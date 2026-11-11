import SpectralConsequences.RegularTreeWeights
import LocalLaw.OutsideEdgeCounting
import LocalLaw.TruncatedTreeCavity

/-! Exact cut counts of actual homogeneous full and one-deficit tree balls. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance regularBoundaryCountsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

section Counts
variable {V:Type*}[Fintype V][DecidableEq V]

omit [DecidableEq V] in
theorem boundary_card_degree_difference (G:SimpleGraph V)(T:Set V)
    (hle:∀v:T,(G.induce T).degree v≤G.degree v.val):
    Nat.card (BoundaryOrientedEdge G T)=∑v:T,(G.degree v.val-(G.induce T).degree v):=by
  have hfirst:Nat.card (FirstInsideOrientedEdge G T)=∑v:T,G.degree v.val:=by
    rw [Nat.card_congr (firstInside_neighbor_equiv G T),Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  have hinterior:Nat.card (InteriorOrientedEdge G T)=∑v:T,(G.induce T).degree v:=by
    rw [interior_count_induced,Nat.card_eq_fintype_card,SimpleGraph.dart_card_eq_sum_degrees]
  have hsum:(∑v:T,(G.degree v.val-(G.induce T).degree v))+(∑v:T,(G.induce T).degree v)=∑v:T,G.degree v.val:=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact Nat.sub_add_cancel (hle v)
  have hh:=firstInside_count G T
  rw [hfirst,hinterior] at hh
  omega

/-- A weighted tree identity fixes the exact number of missing slots at the
last layer. It works for both root deficits b=0 and b=1. -/
theorem homogeneous_missing_degree_sum (H:SimpleGraph V)(d b:ℕ)(hd:3≤d)(hb:b≤d)
    (root:V)(ell:ℕ)(_hell:1≤ell)(hTree:H.IsTree)(hheight:∀v,H.dist v root≤ell)
    (hdegree:∀v,H.degree v=if H.dist v root<ell then
      (if v=root then d-b else d) else (if v=root then 0 else 1)):
    (∑v,((d:ℝ)-(if v=root then (b:ℝ) else 0)-(H.degree v:ℝ)))=
      ((d:ℝ)-(b:ℝ))*((d:ℝ)-1)^ell:=by
  let F:=fun v:V=>(d:ℝ)-(if v=root then (b:ℝ) else 0)-(H.degree v:ℝ)
  let k:ℝ:=(d:ℝ)-1
  have hk:0<k:=by dsimp only [k];have hh:(3:ℝ)≤d:=Nat.cast_le.mpr hd;linarith
  have hf:∀v,F v*(k⁻¹)^ell=F v*treeFlowWeight H root k v:=by
    intro v
    by_cases hv:H.dist v root=ell
    · rw [treeFlowWeight,hv]
    · have hi:H.dist v root<ell:=lt_of_le_of_ne (hheight v) hv
      have hz:F v=0:=by
        dsimp only [F]
        rw [hdegree v,if_pos hi]
        by_cases he:v=root
        · simp only [if_pos he,Nat.cast_sub hb]
          ring
        · simp only [if_neg he]
          ring
      rw [hz,zero_mul,zero_mul]
  have hh:(∑v,F v)*(k⁻¹)^ell=(d:ℝ)-(b:ℝ):=by
    rw [Finset.sum_mul]
    simp_rw [hf]
    exact tree_missing_degree_mass H hTree d hd root b
  have hh':=((congrArg (fun x:ℝ=>x*k^ell) hh))
  dsimp only at hh'
  rw [mul_assoc,←mul_pow,inv_mul_cancel₀ hk.ne',one_pow,mul_one] at hh'
  exact hh'

/-- Exact cut size for a literal ball with saturated forward degrees. -/
theorem saturated_tree_ball_boundary_card (G:SimpleGraph V)(d b:ℕ)(hd:3≤d)(hb:b≤d)
    (o:V)(ell:ℕ)(hell:1≤ell)(hTree:(graphBall G o ell).IsTree)
    (hambient:∀v∈graphBallVertices G o ell,G.degree v=if v=o then d-b else d):
    Nat.card (BoundaryOrientedEdge G (graphBallVertices G o ell))=(d-b)*(d-1)^ell:=by
  let T:=graphBallVertices G o ell
  let H:=graphBall G o ell
  let root:=cavityBallRoot G o ell
  have hAmb:∀v:T,G.degree v.val=if v=root then d-b else d:=by
    intro v
    rw [hambient v.val v.property]
    simp only [root,cavityBallRoot,Subtype.ext_iff]
  have hheight:∀v:T,H.dist v root≤ell:=graphBall_center_distance_le G o ell
  have hdegree:∀v:T,H.degree v=if H.dist v root<ell then
      (if v=root then d-b else d) else (if v=root then 0 else 1):=by
    intro v
    by_cases hi:H.dist v root<ell
    · rw [if_pos hi]
      exact (graphBall_interior_degree G o ell v hi).trans (hAmb v)
    · rw [if_neg hi]
      exact tree_ball_boundary_degree G o ell hTree v (by have hh:=hheight v;change H.dist v root=ell;omega)
  have hle:∀v:T,H.degree v≤G.degree v.val:=by
    intro v
    simp only [hdegree v,hAmb v]
    split_ifs <;> omega

  have hcount:=boundary_card_degree_difference G T hle
  have hreal:(Nat.card (BoundaryOrientedEdge G T):ℝ)=
      ∑v:T,((d:ℝ)-(if v=root then (b:ℝ) else 0)-(H.degree v:ℝ)):=by
    rw [hcount,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro v _
    change ((G.degree v.val-H.degree v:ℕ):ℝ)=_
    rw [Nat.cast_sub (hle v),hAmb v]
    by_cases he:v=root
    · simp only [if_pos he,Nat.cast_sub hb]
    · simp only [if_neg he,sub_zero]
  have hmass:=homogeneous_missing_degree_sum H d b hd hb root ell hell hTree hheight hdegree
  have hh:=hreal.trans hmass
  have hc:((d-1:ℕ):ℝ)=(d:ℝ)-1:=by rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  have htarget:(Nat.card (BoundaryOrientedEdge G T):ℝ)=((d-b:ℕ):ℝ)*((d-1:ℕ):ℝ)^ell:=by
    rw [Nat.cast_sub hb,hc]
    exact hh
  exact_mod_cast htarget

end Counts
namespace RegularGraph
variable {N d:ℕ}

theorem full_tree_ball_boundary_card (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree):
    Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))=d*(d-1)^ell:=by
  simpa only [Nat.sub_zero,ite_self] using saturated_tree_ball_boundary_card g.graph d 0 hd (Nat.zero_le d)
    o ell hell hTree (fun v _=>by simp only [ite_self,Nat.sub_zero];exact g.regular v)

theorem deleted_tree_ball_boundary_card (g:LocalLaw.RegularGraph N d)(hd:3≤d)(j o:Fin N)
    (ell:ℕ)(hell:1≤ell)(hjo:g.graph.Adj j o)(hTree:(graphBall g.graph o (ell+1)).IsTree):
    let D:=g.deficient.deleteVertex j
    let root:{v:Fin N//v≠j}:=⟨o,hjo.ne.symm⟩
    Nat.card (BoundaryOrientedEdge D.graph (graphBallVertices D.graph root ell))=(d-1)^(ell+1):=by
  dsimp only
  let D:=g.deficient.deleteVertex j
  let root:{v:Fin N//v≠j}:=⟨o,hjo.ne.symm⟩
  have hTreeD:(graphBall D.graph root ell).IsTree:=deleted_ball_isTree g.graph j root ell hTree
  have hδ:=g.deficient.deleted_tree_ball_one_root_deficit j root hjo ell hTree (fun _ _=>rfl)
  have hamb:∀v∈graphBallVertices D.graph root ell,D.graph.degree v=if v=root then d-1 else d:=by
    intro v hv
    have hdef:=hδ ⟨v,hv⟩
    have hsat:=g.deficient.deleteVertex_degree_deficit_sum j v
    change D.graph.degree v+D.deficit v=g.graph.degree v.val+0 at hsat
    rw [g.regular v.val,Nat.add_zero,hdef] at hsat
    by_cases he:v=root
    · rw [if_pos he] at hsat ⊢
      omega
    · rw [if_neg he] at hsat ⊢
      omega
  have hh:=saturated_tree_ball_boundary_card D.graph d 1 hd (by omega) root ell hell hTreeD hamb
  exact hh.trans (by rw [pow_succ];ring)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.full_tree_ball_boundary_card
#print axioms SpectralConsequences.RegularGraph.deleted_tree_ball_boundary_card
