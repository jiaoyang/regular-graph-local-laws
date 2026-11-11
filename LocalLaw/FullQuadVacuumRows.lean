import LocalLaw.FullQuadVacuumBenchmark
import LocalLaw.VacuumLeafRows

/-! # Full switching benchmark bounds from the genuine edge-cut core -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullQuadVacuumRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {K L:Type} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

omit [Fintype K] [DecidableEq L] in
theorem fullQuadRetainedEdges_isSymm (inner outer:L→Option K) (α:ℂ) :
    (fullQuadRetainedEdges inner outer α).IsSymm := by
  ext k k'
  simp only [Matrix.transpose_apply,fullQuadRetainedEdges]
  apply Finset.sum_congr rfl
  intro i _
  simp only [and_comm,add_comm]

theorem fullQuadVacuum_inverse_rows (inner outer:L→Option K) (B C:Set L)
    (A₀:Matrix K K ℂ) (q p α:ℂ) (hq:q≠0) (hp:p≠0) (P R a:ℝ)
    (hP:0≤P) (hR:0≤R) (ha:0≤a) (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (hαq:‖α*q‖≤1)
    (hmultiplicity:∀k,(Nat.card {j:B⊕C//fullQuadLeafMate inner outer B C j=some k}:ℝ)≤a)
    (hcut:IsUnit (A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k)))
    (hrows:∀k,∑k',‖(A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k))⁻¹ k k'‖≤R) :
    ∀u,∑v,‖(fullQuadVacuumPrecision inner outer B C A₀ q p α)⁻¹ u v‖≤P+(1+a)*R :=
  vacuumLeaf_inverse_rows (fullQuadLeafMate inner outer B C)
    (A₀-fullQuadRetainedEdges inner outer α) (fullQuadRetainedDegree inner outer)
    q p α hq hp P R a hP hR ha hqnorm hpnorm hαq hmultiplicity hcut hrows

theorem fullQuadVacuum_inverse_columns (inner outer:L→Option K) (B C:Set L)
    (A₀:Matrix K K ℂ) (q p α:ℂ) (hA:A₀.IsSymm) (hq:q≠0) (hp:p≠0) (P R a:ℝ)
    (hP:0≤P) (hR:0≤R) (ha:0≤a) (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (hαq:‖α*q‖≤1)
    (hmultiplicity:∀k,(Nat.card {j:B⊕C//fullQuadLeafMate inner outer B C j=some k}:ℝ)≤a)
    (hcut:IsUnit (A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k)))
    (hrows:∀k,∑k',‖(A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k))⁻¹ k k'‖≤R) :
    ∀v,∑u,‖(fullQuadVacuumPrecision inner outer B C A₀ q p α)⁻¹ u v‖≤P+(1+a)*R :=
  vacuumLeaf_inverse_columns (fullQuadLeafMate inner outer B C)
    (A₀-fullQuadRetainedEdges inner outer α) (fullQuadRetainedDegree inner outer)
    q p α (hA.sub (fullQuadRetainedEdges_isSymm inner outer α)) hq hp P R a hP hR ha
    hqnorm hpnorm hαq hmultiplicity hcut hrows

end LocalLaw
