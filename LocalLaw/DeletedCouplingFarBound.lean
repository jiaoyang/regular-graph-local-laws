import LocalLaw.BoundarySchurRows
import LocalLaw.PairBoundaryDepth

/-! # Far omitted sampled neighbors give a small true coupling column -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deletedCouplingFarDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem omitted_pair_neighbor_far (G:SimpleGraph V)(x y b v:V)(r:ℕ)
    (hb:b∉pairBallVertices G x y r)(hvb:G.Adj v b) :
    (r:ℕ∞)≤G.edist x v ∧ (r:ℕ∞)≤G.edist y v := by
  constructor
  · apply le_of_not_gt
    intro h
    exact pair_near_vertex_no_crossing_edge G x y r v b (Or.inl h) hb hvb
  · apply le_of_not_gt
    intro h
    exact pair_near_vertex_no_crossing_edge G x y r v b (Or.inr h) hb hvb

namespace DeficientGraph
variable {V:Type} [Fintype V] {d:ℕ}

theorem cut_coupling_far_column_bound (g:DeficientGraph V d)(T:Set V)
    (P:Matrix (Tᶜ:Set V) (Tᶜ:Set V) ℂ)(x:(Tᶜ:Set V))(b:T)(F:ℝ)(hF:0≤F)
    (hfar:∀v:(Tᶜ:Set V),g.graph.Adj v.val b.val→‖P x v‖≤F) :
    ‖(P*g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖≤
      F*((d:ℝ)/Real.sqrt ((d:ℝ)-1)) := by
  have hcol:(∑v:(Tᶜ:Set V),‖g.H v.val b.val‖)≤(d:ℝ)/Real.sqrt ((d:ℝ)-1):=by
    simpa only [H,normalizedAdjacency_norm,g.graph.adj_comm] using
      normalized_cut_left_row_bound g.graph d T g.degree_le b
  have hp (v:(Tᶜ:Set V)):‖P x v‖*‖g.H v.val b.val‖≤F*‖g.H v.val b.val‖:=by
    by_cases hv:g.graph.Adj v.val b.val
    · exact mul_le_mul_of_nonneg_right (hfar v hv) (norm_nonneg _)
    · have hz:g.H v.val b.val=0:=by
        simp [H,normalizedAdjacency,SimpleGraph.adjMatrix_apply,hv]
      simp only [hz,norm_zero,mul_zero,le_refl]
  calc
    _≤∑v:(Tᶜ:Set V),‖P x v‖*‖g.H v.val b.val‖:=by
      simpa only [Matrix.mul_apply,Matrix.submatrix_apply,norm_mul] using
        norm_sum_le Finset.univ (fun v:(Tᶜ:Set V)=>P x v*g.H v.val b.val)
    _≤∑v:(Tᶜ:Set V),F*‖g.H v.val b.val‖:=Finset.sum_le_sum (fun v _=>hp v)
    _=F*(∑v:(Tᶜ:Set V),‖g.H v.val b.val‖):=(Finset.mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left hcol hF

end DeficientGraph
end LocalLaw
