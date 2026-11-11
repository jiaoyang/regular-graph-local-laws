import LocalLaw.CavityMinorRowIdentity
import LocalLaw.CavityWeightFamily
import LocalLaw.SourceRetainedRowSplit

/-! # Exact diagonal, off-diagonal and nonlinear cavity terms -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cavityMinorRowSplitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem offdiag_add_scalar_identity {F : Type*} [Fintype F] [DecidableEq F]
    (A B : F → ℂ) (D : Matrix F F ℂ) (q : ℂ) :
    (∑ i,∑ j,if i=j then 0 else A i*(D+q • 1) i j*B j)=
      ∑ i,∑ j,if i=j then 0 else A i*D i j*B j := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · simp only [hij,if_true]
  · simp only [hij,if_false,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_zero,add_zero]

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem cavity_minor_diagonal_norm_split (g : RegularGraph N d) (hd : 3≤d) (o : Fin N)
    (ell : ℕ) (hell : 2≤ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector : ℕ)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let T := graphBallVertices g.graph o ell
    let R := (g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
    let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen q z
    let root := g.truncatedCavityRoot o ell j hjo
    let l := fun α => g.truncatedCavityBoundaryInner o ell hell j hjo (labels α)
    let D := g.sourceTruncatedBoundaryDefect T labels samples selector q z
    let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
    ‖R root root-P root root‖≤
      ‖∑ α,g.truncatedCavityWeight o ell hell j hjo q z (labels α)*D α α‖+
      ‖∑ α,∑ β,if α=β then 0 else P root (l α)*D α β*P (l β) root‖+
      ‖coeff*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) root)‖ := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let R := (g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
  let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen q z
  let root := g.truncatedCavityRoot o ell j hjo
  let l := fun α => g.truncatedCavityBoundaryInner o ell hell j hjo (labels α)
  let D := g.sourceTruncatedBoundaryDefect T labels samples selector q z
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  have hrow := g.cavity_minor_row_identity hd o ell hell j hjo labels samples selector q z hz hq root
  have hsym : P.IsSymm := ((g.deficient.restrict T).deleteVertex j).extensionGreen_isSymm q z
  have hsplit := weighted_double_sum_diagonal_split (fun α => P root (l α)) (fun β => P (l β) root) D
  have hdiag : (∑ α,P root (l α)*P (l α) root*D α α)=
      ∑ α,g.truncatedCavityWeight o ell hell j hjo q z (labels α)*D α α := by
    apply Finset.sum_congr rfl
    intro α _
    rw [hsym.apply root (l α)]
    unfold truncatedCavityWeight
    change P root (l α)*P root (l α)*D α α=P root (l α)^2*D α α
    rw [pow_two]
  rw [hsplit,hdiag,mul_add] at hrow
  rw [hrow]
  apply ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
  apply add_le_add_right
  apply add_le_add
  all_goals
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (cut_coefficient_norm_le_one d hd)

end RegularGraph
end LocalLaw
