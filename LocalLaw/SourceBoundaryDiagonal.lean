import LocalLaw.SourceBoundaryDefect
import LocalLaw.SourceEndpointVertices
import LocalLaw.SourceGoodDiagonalComparison

/-! # The actual good boundary diagonal has its exact cavity-tree model -/

noncomputable section
namespace LocalLaw
local instance sourceBoundaryDiagonalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem sourceBoundaryDefect_eligible_diagonal (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (i : ι)
    (hi : (g.admissibleState T labels S).Eligible selector i) :
    let s := g.admissibleState T labels S
    let gnew := g.labelledResampledGraph T labels S selector
    g.sourceBoundaryDefect T labels S selector r q z i i =
      (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val -
        cavityIterate z q (r + 1) := by
  dsimp only
  let s := g.admissibleState T labels S
  let k : s.AdmissibleSampleIndex selector := ⟨i, hi⟩
  have htip : s.endpointFinalBoundaryRoot selector i = g.sourceEndpointTipIndex T labels S selector k := by
    have hi' : s.Eligible selector i := hi
    simp only [LabelledResamplingState.endpointFinalBoundaryRoot, dif_pos hi']
    rfl
  have hmodel : g.sourceEndpointQ T labels S selector r q z
      (s.endpointFinalBoundaryRoot selector i) (s.endpointFinalBoundaryRoot selector i) = cavityIterate z q (r + 1) := by
    rw [htip]
    exact g.sourceEndpointQ_tip_diagonal hd T labels S selector r hsep hr k q z hz hq
  change g.sourceEndpointT T labels S selector z _ _ - g.sourceEndpointQ T labels S selector r q z _ _ = _
  rw [hmodel]
  congr 1
  simp only [LabelledResamplingState.endpointFinalBoundaryRoot, dif_pos hi]
  rfl

end RegularGraph
end LocalLaw
