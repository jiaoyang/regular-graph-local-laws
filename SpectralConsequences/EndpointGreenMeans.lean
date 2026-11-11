import SpectralConsequences.OutsideEdgeMeans
import SpectralConsequences.ExchangeableFinite

/-! # All four endpoint orientations in equation (7.26)

Reversing a directed edge is an actual finite permutation. Thus either
endpoint of either independent draw has the same pole mean, with the same
explicit outside-edge restriction error.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace SpectralConsequences
open LocalLaw
local instance endpointGreenMeansDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

def outsideEdgeReverse (G : SimpleGraph V) (T : Set V) :
    OutsideOrientedEdge G T ≃ OutsideOrientedEdge G T where
  toFun e := ⟨(e.val.2,e.val.1),e.property.1.symm,e.property.2.2,e.property.2.1⟩
  invFun e := ⟨(e.val.2,e.val.1),e.property.1.symm,e.property.2.2,e.property.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- true selects the first endpoint, false the second. -/
def outsideCoordinate {G : SimpleGraph V} {T : Set V}
    (first : Bool) (e : OutsideOrientedEdge G T) : V := if first then e.val.1 else e.val.2

def outsideCoordinatePermutation (G : SimpleGraph V) (T : Set V) (first : Bool) :
    OutsideOrientedEdge G T ≃ OutsideOrientedEdge G T :=
  if first then outsideEdgeReverse G T else Equiv.refl _

theorem outsideCoordinate_permutation (G : SimpleGraph V) (T : Set V) (first : Bool)
    (e : OutsideOrientedEdge G T) :
    outsideCoordinate first (outsideCoordinatePermutation G T first e) = e.val.2 := by
  cases first <;> rfl

namespace RegularGraph
variable {N d : ℕ}

theorem outside_endpoint_green_mean_eq_second (g : LocalLaw.RegularGraph N d)
    (T : Set (Fin N)) (z : ℂ) (first second : Bool) :
    finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
      finiteComplexMean (fun f : OutsideOrientedEdge g.graph T =>
        g.G z (outsideCoordinate first e) (outsideCoordinate second f))) =
    finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
      finiteComplexMean (fun f : OutsideOrientedEdge g.graph T => g.G z e.val.2 f.val.2)) := by
  calc
    _ = finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
        finiteComplexMean (fun f : OutsideOrientedEdge g.graph T =>
          g.G z e.val.2 (outsideCoordinate second f))) := by
      have h := finiteComplexMean_equiv (outsideCoordinatePermutation g.graph T first)
        (fun e : OutsideOrientedEdge g.graph T => finiteComplexMean
          (fun f : OutsideOrientedEdge g.graph T =>
            g.G z (outsideCoordinate first e) (outsideCoordinate second f)))
      simpa only [outsideCoordinate_permutation] using h.symm
    _ = _ := by
      congr 1
      funext e
      have h := finiteComplexMean_equiv (outsideCoordinatePermutation g.graph T second)
        (fun f : OutsideOrientedEdge g.graph T => g.G z e.val.2 (outsideCoordinate second f))
      simpa only [outsideCoordinate_permutation] using h.symm

/-- Equation (7.26), including all four choices of first/second endpoints.
In particular the last covariance is b_alpha,b_beta, not the adjacent pair
b_beta,c_beta printed in the source equation. -/
theorem outside_endpoint_green_mean (g : LocalLaw.RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4*Nat.card T ≤ N)
    (z : ℂ) (hz : 0 < z.im) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ i j, ‖g.G z i j‖ ≤ C) (first second : Bool) :
    ‖finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
      finiteComplexMean (fun f : OutsideOrientedEdge g.graph T =>
        g.G z (outsideCoordinate first e) (outsideCoordinate second f))) -
      (N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹‖ ≤
      8*C*(Nat.card T:ℝ)/(N:ℝ) := by
  rw [outside_endpoint_green_mean_eq_second g T z first second]
  exact outside_second_green_mean g T hN hd hT z hz C hC hG

end RegularGraph
end SpectralConsequences
