import LocalLaw.LeafMateRows
import LocalLaw.LeafSchurModelRows

/-! # Uniform lost-neighbor incidence rows after deleting all fake leaves

The common leaf-deleted core need not belong to the reference class. The
actual leaf column equation and exact Schur deletion provide its incidence
weights with no leaf-count loss.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance leafDeletedMateDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

theorem deleted_leaf_mate_rows (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z p:ℂ)(hz:0<z.im)(hq:0≤q.im)(hp:p≠0)
    (B W δ:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)(hW:0≤W)(hδ:0≤δ)
    (hleaf:∀x:V⊕I,(∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inr l)‖)≤W)
    (herror:∀l k:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inr k)-
      (if l=k then p else 0)‖≤δ)
    (hsmall:(Fintype.card I:ℝ)*‖p⁻¹‖*δ≤1/2) :
    let U:=‖(treeEdgeWeight d)⁻¹‖*(1+(B+2)*W)
    (∀v:V,(∑l:I,‖g.extensionGreen q z v (mate l)‖)≤U+2*W*‖p⁻¹‖*U) ∧
      (∀v:V,(∑l:I,‖g.extensionGreen q z (mate l) v‖)≤U+2*W*‖p⁻¹‖*U) := by
  dsimp only
  let U:=‖(treeEdgeWeight d)⁻¹‖*(1+(B+2)*W)
  have hB:0≤B:=(norm_nonneg z).trans hzB
  have hU:0≤U:=by dsimp only [U];positivity
  have hm:∀x:V⊕I,(∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inl (mate l))‖)≤U:=
    fun x=>g.attachLeaves_mate_row_bound hd mate hr q z hz hq B W hzB hqnorm hW x (hleaf x)
  exact g.attachLeaves_remaining_rows_cols hd mate hr mate q z p hz hq hp δ U W U hδ hU
    herror hsmall (fun v=>hm (.inl v)) (fun v=>hleaf (.inl v)) (fun l=>hm (.inr l))

end DeficientGraph
end LocalLaw
