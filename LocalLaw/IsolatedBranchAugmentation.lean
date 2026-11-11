import LocalLaw.DetachedEndpointModel
import LocalLaw.TwoBallAugmentation

/-! # A distant target ball preserves an isolated rooted branch -/

noncomputable section
namespace LocalLaw
local instance isolatedBranchAugmentationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem isolated_branch_augmented_cut (H : SimpleGraph V) (K C : Set V)
    (c j : V) (r : ℕ)
    (hcut : ∀ u∈C,∀ v∈K,v∉C → ¬H.Adj u v)
    (hradial : ∀ v∈C,H.edist c v≤(r:ℕ∞))
    (hfar : ((2*r+1:ℕ):ℕ∞)<H.edist c j) :
    ∀ u∈C,∀ v∈K∪graphBallVertices H j r,v∉C → ¬H.Adj u v := by
  intro u hu v hv hvC huv
  rcases hv with hv|hv
  · exact hcut u hu v hv hvC huv
  · have hpath : H.edist c j≤((2*r+1:ℕ):ℕ∞) := by
      calc
        _ ≤ H.edist c u+H.edist u j := H.edist_triangle
        _ ≤ H.edist c u+(H.edist u v+H.edist v j) := add_le_add_left H.edist_triangle _
        _ ≤ (r:ℕ∞)+(1+(r:ℕ∞)) := add_le_add (hradial u hu)
          (add_le_add (SimpleGraph.edist_eq_one_iff_adj.mpr huv).le (by simpa only [H.edist_comm] using hv))
        _ = _ := by exact_mod_cast (by omega : r+(1+r)=2*r+1)
    exact (not_le_of_gt hfar) hpath

theorem isolated_branch_target_not_mem (H : SimpleGraph V) (C : Set V) (c j : V) (r : ℕ)
    (hradial : ∀ v∈C,H.edist c v≤(r:ℕ∞))
    (hfar : ((2*r+1:ℕ):ℕ∞)<H.edist c j) : j∉C := by
  intro hj
  have hh := hradial j hj
  exact (not_le_of_gt hfar) (hh.trans (ENat.coe_le_coe.mpr (by omega)))

end LocalLaw
