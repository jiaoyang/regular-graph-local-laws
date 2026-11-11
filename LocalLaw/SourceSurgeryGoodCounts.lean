import LocalLaw.SourceBoundaryDefect
import LocalLaw.PairedBoundaryParameters

/-! # Actual quadratic-log exceptional index count after label transport -/

noncomputable section
namespace LocalLaw
local instance sourceSurgeryGoodCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem sourceSurgeryGoodIndices_bad_card_eq (g : RegularGraph N d) (o : Fin N)
    (ell R : ℕ) (hfit : ell+1≤R/8)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    (Finset.univ\g.sourceSurgeryGoodIndices o ell R hfit labels z φ S).card =
      (Finset.univ\g.sourceSurgeryGoodLabels o ell R hfit z φ S).card := by
  classical
  have hmem (i : ι) : i ∈ Finset.univ\g.sourceSurgeryGoodIndices o ell R hfit labels z φ S ↔
      labels i ∈ Finset.univ\g.sourceSurgeryGoodLabels o ell R hfit z φ S := by
    simp [sourceSurgeryGoodIndices]
  apply Finset.card_bij (fun i _ => labels i)
  · intro i hi
    exact (hmem i).mp hi
  · intro i _ j _ h
    exact labels.injective h
  · intro a ha
    refine ⟨labels.symm a,(hmem _).mpr (by simpa only [labels.apply_symm_apply] using ha),?_⟩
    exact labels.apply_symm_apply a

theorem sourceSurgeryGoodIndices_bad_card (g : RegularGraph N d) (o : Fin N)
    (ell R ω m J : ℕ) (hfit : ell+1≤R/8)
    (hbudget : graphBallExcess g.graph o (R/8)≤ω)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hisolation : ¬g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z φ (R/4) m S)
    (hrejected : (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S).card≤J) :
    (Finset.univ\g.sourceSurgeryGoodIndices o ell R hfit labels z φ S).card≤4*m^2+3*m+2*ω+J := by
  rw [g.sourceSurgeryGoodIndices_bad_card_eq o ell R hfit labels z φ S]
  exact g.sourceSurgeryGoodLabels_bad_card o ell R ω m J hfit hbudget z φ S hisolation hrejected

/-- The actual stronger F2 good-index set has a fixed log-squared complement
once the two proved rare events are excluded. -/
theorem sourceSurgeryGoodIndices_bad_log_bound (g : RegularGraph N d) (o : Fin N)
    (ell R ω J : ℕ) (hfit : ell+1≤R/8)
    (hbudget : graphBallExcess g.graph o (R/8)≤ω)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hlog : 1≤Real.log (N:ℝ))
    (hisolation : ¬g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z φ (R/4)
      (Nat.ceil (Real.log (N:ℝ))) S)
    (hrejected : (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S).card≤J) :
    ((Finset.univ\g.sourceSurgeryGoodIndices o ell R hfit labels z φ S).card:ℝ)≤
      (22+2*(ω:ℝ)+(J:ℝ))*Real.log (N:ℝ)^2 := by
  exact quadratic_log_exception_count (Real.log (N:ℝ)) ω J _ hlog
    (g.sourceSurgeryGoodIndices_bad_card o ell R ω (Nat.ceil (Real.log (N:ℝ))) J hfit hbudget
      labels z φ S hisolation hrejected)

end RegularGraph
end LocalLaw
