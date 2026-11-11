import SpectralConsequences.CavityBoundaryWeights

/-! The q-dependent cavity correction summed over ALL original cut labels. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance cavityBoundaryTotalWeightsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem finite_offdiag_weight_sum {I:Type*}[Fintype I] (w:I→ℂ):
    (∑i:I,∑j:I,if i=j then 0 else w i*w j)=(∑i:I,w i)^2-∑i:I,(w i)^2:=by
  have hin:∀i:I,(∑j:I,if i=j then 0 else w i*w j)=w i*(∑j:I,w j)-(w i)^2:=by
    intro i
    calc
      _=∑j:I,(w i*w j-(if i=j then (w i)^2 else 0)):=by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h:i=j
        · subst j;simp [pow_two]
        · simp only [h,if_false,sub_zero]
      _=w i*(∑j:I,w j)-(w i)^2:=by
        rw [Finset.sum_sub_distrib,←Finset.mul_sum]
        simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [hin]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,pow_two]

theorem finite_supported_constant_offdiag_sum {I:Type*}[Fintype I] (A:I→Prop) [Fintype {i:I//A i}]
    (w0:ℂ):
    (∑i:I,∑j:I,if i=j then 0 else (if A i then w0 else 0)*(if A j then w0 else 0))=
      (Fintype.card {i:I//A i}:ℂ)*((Fintype.card {i:I//A i}:ℂ)-1)*w0^2:=by
  have hsum:(∑i:I,if A i then w0 else 0)=(Fintype.card {i:I//A i}:ℂ)*w0:=by
    rw [←Finset.sum_filter]
    rw [Finset.sum_subtype (p:=A) (F:=inferInstance) _ (fun i=>by simp)]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hsum2:(∑i:I,(if A i then w0 else 0)^2)=(Fintype.card {i:I//A i}:ℂ)*w0^2:=by
    have heq:∀i:I,(if A i then w0 else 0)^2=(if A i then w0^2 else 0):=by intro i;split_ifs <;>simp
    simp_rw [heq]
    rw [←Finset.sum_filter]
    rw [Finset.sum_subtype (p:=A) (F:=inferInstance) _ (fun i=>by simp)]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [finite_offdiag_weight_sum,hsum,hsum2]
  ring

namespace RegularGraph
variable {N d:ℕ}

theorem cavity_boundary_all_label_weights (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)
    (ell:ℕ)(hell:2≤ell)(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im):
    (∑e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑f:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if e=f then 0 else cavityBoundaryWeight g o ell hell j hjo q z e*
          cavityBoundaryWeight g o ell hell j hjo q z f)=
      (((d-1:ℕ):ℂ)^(ell+1))*((((d-1:ℕ):ℂ)^(ell+1))-1)*
        (radialCavityColumn z q (treeEdgeWeight d) ell ell)^2:=by
  letI:Fintype {e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)//
    cavityBoundaryInnerDeleted g o ell hell j hjo e∈
      graphBallVertices (g.deficient.deleteVertex j.val).graph ⟨o,hjo.ne.symm⟩ ell}:=
    activeCavityBoundaryFintype g o ell hell j hjo
  simp_rw [cavityBoundaryWeight_eq_radial g hd o ell hell j hjo hTree q z hz hq]
  rw [finite_supported_constant_offdiag_sum]
  have hcard:(Fintype.card (ActiveCavityBoundary g o ell hell j hjo):ℂ)=((d-1:ℕ):ℂ)^(ell+1):=by
    have hh:=activeCavityBoundary_card g hd o ell hell j hjo hTree
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  dsimp only [ActiveCavityBoundary] at hcard
  rw [hcard]

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.cavity_boundary_all_label_weights
