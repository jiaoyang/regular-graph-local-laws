import SpectralConsequences.BallConditionalTest
import SpectralConsequences.FiniteMeanAlgebra

/-! Uniform and masked bounds for the exact conditional ball kernel. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance ballConditionalMaskBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem finiteComplexMean_norm_bound_nonnegative {E:Type*}[Fintype E]
    (f:E→ℂ) (C:ℝ) (hC:0≤C) (hf:∀e,‖f e‖≤C):‖finiteComplexMean f‖≤C:=by
  by_cases h:Nonempty E
  · letI:=h
    exact finiteComplexMean_norm_bound f C hf
  · letI:IsEmpty E:=not_nonempty_iff.mp h
    simpa only [finiteComplexMean,Finset.univ_eq_empty,Finset.sum_empty,smul_zero,norm_zero] using hC

theorem finiteComplexMean_mask_norm {E:Type*}[Fintype E]
    (P:E→Prop) (f:E→ℂ) (C:ℝ) (hf:∀e,P e→‖f e‖≤C):
    ‖finiteComplexMean (fun e=>if P e then f e else 0)‖≤C*eventMass (finiteUniformWeight E) P:=by
  rw [finiteComplexMean_eq_expectation]
  apply (finiteExpectation_norm_le (finiteUniformWeight E) finiteUniformWeight_nonneg _).trans
  rw [eventMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he:P e
  · simp only [he,if_true]
    exact (mul_le_mul_of_nonneg_left (hf e he) (finiteUniformWeight_nonneg e)).trans_eq (by ring)
  · simp [he]

theorem ballLabelledConditionalMean_norm_bound (N d:ℕ)(o:Fin N)(ell:ℕ)
    (f:BallLabelledSpace N d→ℂ)(g:RegularGraph N d)(C:ℝ)(hC:0≤C)
    (hf:∀labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
      BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∀S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell),
        ‖f (canonicalBallLabelledState N d o ell g (labels,S))‖≤C):
    ‖ballLabelledConditionalMean N d o ell f g‖≤C:=by
  rw [ballLabelledConditionalMean_prod]
  apply finiteComplexMean_norm_bound_nonnegative _ C hC
  intro labels
  exact finiteComplexMean_norm_bound_nonnegative _ C hC (hf labels)

theorem ballLabelledConditionalMean_mask_bound (N d:ℕ)(o:Fin N)(ell:ℕ)
    (P:BallLabelledSpace N d→Prop)(f:BallLabelledSpace N d→ℂ)(g:RegularGraph N d)
    (C p:ℝ)(hC:0≤C)(hp:0≤p)
    (hf:∀labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
      BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∀S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell),
        P (canonicalBallLabelledState N d o ell g (labels,S))→
          ‖f (canonicalBallLabelledState N d o ell g (labels,S))‖≤C)
    (hprob:∀labels:Fin (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))≃
      BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S=>P (canonicalBallLabelledState N d o ell g (labels,S)))≤p):
    ‖ballLabelledConditionalMean N d o ell (fun ω=>if P ω then f ω else 0) g‖≤C*p:=by
  rw [ballLabelledConditionalMean_prod]
  apply finiteComplexMean_norm_bound_nonnegative _ (C*p) (mul_nonneg hC hp)
  intro labels
  exact (finiteComplexMean_mask_norm
    (fun S=>P (canonicalBallLabelledState N d o ell g (labels,S)))
    (fun S=>f (canonicalBallLabelledState N d o ell g (labels,S))) C (hf labels)).trans
      (mul_le_mul_of_nonneg_left (hprob labels) hC)

end SpectralConsequences
