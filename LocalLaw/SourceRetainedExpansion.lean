import LocalLaw.SwitchedRetainedReference
import LocalLaw.SourceBoundaryDefect
import LocalLaw.CutRowAlgebra

/-!
# Source row expansion with fixed weights and the literal surgery defect

The old deterministic central model and new physical matrix are on T. The
actual canonical endpoint defect is reindexed by the same original labels.
Every equality connecting these three objects is exact.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedExpansionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def sourceRetainedReference (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ) (q z : ℂ) : Matrix T T ℂ :=
  g.filledRetainedGreen T (centralBoundaryVertices g.graph T r) q z

def sourceCutCoupling (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) : Matrix T ι ℂ :=
  (cutInnerCoupling g.graph d T).submatrix id labels

theorem sourceBoundaryDefect_eq_filled (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) :
    let s := g.admissibleState T labels samples
    let gnew := g.labelledResampledGraph T labels samples selector
    let K := s.endpointModelVertices selector r
    let hK := s.endpointModel_contains_new_boundary selector r
    (gnew.filledBoundaryDefect T K hK q z).submatrix
      (s.fullResample selector).boundary (s.fullResample selector).boundary =
        g.sourceBoundaryDefect T labels samples selector r q z := by
  dsimp only
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := s.endpointModelVertices selector r
  let hK := s.endpointModel_contains_new_boundary selector r
  ext j k
  have hvertex (i : ι) : boundaryOutsideVertex gnew.graph T ((s.fullResample selector).boundary i) =
      (s.endpointFinalBoundaryRoot selector i).val := (s.endpointFinalBoundaryRoot_outer selector i).symm
  have hmodel (i : ι) : gnew.filledBoundaryVertex T K hK ((s.fullResample selector).boundary i) =
      s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector i) :=
    Subtype.ext (hvertex i)
  change (gnew.deficient.delete T).G z _ _ -
      ((gnew.deficient.delete T).restrict K).extensionGreen q z _ _ =
    (gnew.deficient.delete T).G z _ _ -
      ((gnew.deficient.delete T).restrict K).extensionGreen q z _ _
  exact congrArg₂ (fun a b : ℂ => a - b)
    (congrArg₂ ((gnew.deficient.delete T).G z) (hvertex j) (hvertex k))
    (congrArg₂ (((gnew.deficient.delete T).restrict K).extensionGreen q z) (hmodel j) (hmodel k))

/-- The exact source self-energy equation has a fixed old reference and
canonical actual boundary D, without an approximation bridge. -/
theorem sourceRetained_inverse_difference (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let gnew := g.labelledResampledGraph T labels samples selector
    (g.sourceRetainedReference T r q z)⁻¹ -
      ((gnew.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
      g.sourceCutCoupling T labels * g.sourceBoundaryDefect T labels samples selector r q z *
        (g.sourceCutCoupling T labels).transpose := by
  dsimp only
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := s.endpointModelVertices selector r
  let hK := s.endpointModel_contains_new_boundary selector r
  have hRef := g.switched_filled_reference_eq_old_central hd T labels samples selector r hsep hr q z hz hq
  have hInv := gnew.filledRetained_inverse_difference hd T K hK q z hz hq
  have hU : (cutInnerCoupling gnew.graph d T).submatrix id (s.fullResample selector).boundary =
      g.sourceCutCoupling T labels := by
    ext i a
    simp only [Matrix.submatrix_apply, sourceCutCoupling, id_eq, cutInnerCoupling,
      s.fullResample_boundary_inner_endpoint selector a]
    rfl
  have hUt : (cutInnerCoupling gnew.graph d T).transpose.submatrix (s.fullResample selector).boundary id =
      (g.sourceCutCoupling T labels).transpose := by
    ext a i
    exact congrFun (congrFun hU i) a
  have hD := g.sourceBoundaryDefect_eq_filled T labels samples selector r q z
  calc
    _ = (gnew.filledRetainedGreen T K q z)⁻¹ -
        ((gnew.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ := by
      exact congrArg (fun P : Matrix T T ℂ => P⁻¹ -
        ((gnew.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹) hRef.symm
    _ = _ := by
      rw [hInv, sandwich_equiv_middle _ _ _ (s.fullResample selector).boundary]
      rw [hU, hUt, hD]

/-- Source (6.24) with actual canonical D and deterministic pre-sampling
reference weights. All inverse and model-identification inputs are derived. -/
theorem sourceRetained_row_three_term (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (x y : T) :
    let gnew := g.labelledResampledGraph T labels samples selector
    let R := (gnew.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
    let P := g.sourceRetainedReference T r q z
    let U := g.sourceCutCoupling T labels
    let D := g.sourceBoundaryDefect T labels samples selector r q z
    ‖R x y - P x y‖ ≤
      ‖∑ a, (P * U) x a * (U.transpose * P) a y * D a a‖ +
      ‖∑ a, ∑ b ∈ (Finset.univ.erase a), (P * U) x a * D a b * (U.transpose * P) b y‖ +
      ‖((R - P) * U * D * U.transpose * P) x y‖ := by
  let gnew := g.labelledResampledGraph T labels samples selector
  apply retained_boundary_row_three_term _ _ _ _ _
    (green_retained_principal_inverse T gnew.H (normalizedAdjacency_isHermitian gnew.graph d) z hz).1
    (g.filledRetainedGreen_isUnit hd T (centralBoundaryVertices g.graph T r) q z hz hq)
    (g.sourceRetained_inverse_difference hd T labels samples selector r hsep hr q z hz hq)

end RegularGraph
end LocalLaw
