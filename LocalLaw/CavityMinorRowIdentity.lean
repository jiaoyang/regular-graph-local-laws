import LocalLaw.MinorTruncatedBoundarySchur
import LocalLaw.TruncatedReferencePreservation
import LocalLaw.CavityMinorModelBounds
import LocalLaw.TreeCavityBoundaryDefect
import LocalLaw.SwitchedRetainedReference

/-! # Exact cavity minor row expansion with fixed old reference weights -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance cavityMinorRowIdentityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Indexed
variable {I F : Type*} [Fintype I] [Fintype F] [DecidableEq I]

def indexedBoundaryCoupling (l : F → I) (w : ℂ) : Matrix I F ℂ := fun i a => if i = l a then w else 0

omit [Fintype F] in
theorem mul_indexedBoundaryCoupling (l : F → I) (w : ℂ) (A : Matrix I I ℂ) (i : I) (a : F) :
    (A * indexedBoundaryCoupling l w) i a = w * A i (l a) := by
  simp only [Matrix.mul_apply, indexedBoundaryCoupling, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [Fintype F] in
theorem transpose_indexedBoundaryCoupling_mul (l : F → I) (w : ℂ) (A : Matrix I I ℂ) (a : F) (i : I) :
    ((indexedBoundaryCoupling l w).transpose * A) a i = w * A (l a) i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, indexedBoundaryCoupling, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem indexedBoundary_sandwich_row (l : F → I) (w : ℂ) (A B : Matrix I I ℂ) (D : Matrix F F ℂ)
    (i j : I) :
    ((A * indexedBoundaryCoupling l w) * D * ((indexedBoundaryCoupling l w).transpose * B)) i j =
      w ^ 2 * ∑ a, ∑ b, A i (l a) * D a b * B (l b) j := by
  calc
    _ = ∑ a, ∑ b, (A * indexedBoundaryCoupling l w) i a * D a b *
        ((indexedBoundaryCoupling l w).transpose * B) b j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      simp only [mul_indexedBoundaryCoupling, transpose_indexedBoundaryCoupling_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end Indexed

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem cavity_minor_new_coupling_reindex (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (hell : 2 ≤ ell)
    (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector : ℕ) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels samples
    let gnew := g.labelledResampledGraph T labels samples selector
    ((cutInnerCoupling gnew.graph d T).submatrix (Subtype.val : {v : T // v ≠ j} → T) id).submatrix
      id (s.fullResample selector).boundary =
      indexedBoundaryCoupling (fun a => g.truncatedCavityBoundaryInner o ell hell j hjo (labels a))
        (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  ext v a
  have hfirst := s.fullResample_boundary_inner_endpoint selector a
  have hfirst' : (((g.admissibleState (graphBallVertices g.graph o ell) labels samples).fullResample selector).boundary a).val.1 =
      (labels a).val.1 := hfirst
  have hpred : v.val.val = (labels a).val.1 ↔
      v = g.truncatedCavityBoundaryInner o ell hell j hjo (labels a) := by
    constructor
    · exact fun h => Subtype.ext (Subtype.ext h)
    · exact fun h => congrArg (fun v : {v : T // v ≠ j} => v.val.val) h
  simp only [Matrix.submatrix_apply, id_eq, cutInnerCoupling, indexedBoundaryCoupling]
  simp only [hfirst', hpred]

theorem cavity_minor_row_identity (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector : ℕ)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    let gnew := g.labelledResampledGraph T labels samples selector
    let R := gnew.retainedPhysicalMinor T j z
    let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen q z
    let root := g.truncatedCavityRoot o ell j hjo
    let l := fun a => g.truncatedCavityBoundaryInner o ell hell j hjo (labels a)
    let D := g.sourceTruncatedBoundaryDefect T labels samples selector q z
    let c : ℂ := (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2
    ∀ v, R root v - P root v =
      c * (∑ a, ∑ b, P root (l a) * D a b * P (l b) v) +
      c * (∑ a, ∑ b, (R root (l a) - P root (l a)) * D a b * P (l b) v) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let R := gnew.retainedPhysicalMinor T j z
  let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen q z
  let l := fun a => g.truncatedCavityBoundaryInner o ell hell j hjo (labels a)
  let U := indexedBoundaryCoupling l (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ)
  let Unew := (cutInnerCoupling gnew.graph d T).submatrix (Subtype.val : {v : T // v ≠ j} → T) id
  let Dnew := gnew.truncatedBoundaryDefect T q z
  let D := g.sourceTruncatedBoundaryDefect T labels samples selector q z
  let e := (s.fullResample selector).boundary
  have hU : Unew.submatrix id e = U := g.cavity_minor_new_coupling_reindex o ell hell j hjo labels samples selector
  have hUt : Unew.transpose.submatrix e id = U.transpose := by
    ext a v
    exact congrFun (congrFun hU v) a
  have hD : Dnew.submatrix e e = D := (g.sourceTruncatedBoundaryDefect_eq_actual T labels samples selector q z).symm
  have hmiddle : Unew * Dnew * Unew.transpose = U * D * U.transpose := by
    have h := sandwich_equiv_middle Unew Dnew Unew.transpose e
    exact h.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) hU hD) hUt)
  have h := gnew.truncated_minor_boundary_retained_expansion hd T j q z hz hq
  dsimp only at h
  rw [g.resampled_truncated_minor_extensionGreen_eq T labels samples selector j q z] at h
  change R - P = P * (Unew * Dnew * Unew.transpose) * P + (R - P) * (Unew * Dnew * Unew.transpose) * P at h
  rw [hmiddle] at h
  have hlead : P * (U * D * U.transpose) * P = (P * U) * D * (U.transpose * P) := by simp only [Matrix.mul_assoc]
  have hrem : (R - P) * (U * D * U.transpose) * P = ((R - P) * U) * D * (U.transpose * P) := by
    simp only [Matrix.mul_assoc]
  rw [hlead, hrem] at h
  intro v
  have he := congrFun (congrFun h (g.truncatedCavityRoot o ell j hjo)) v
  simp only [Matrix.sub_apply, Matrix.add_apply] at he
  rw [indexedBoundary_sandwich_row, indexedBoundary_sandwich_row] at he
  exact he

end RegularGraph
end LocalLaw
