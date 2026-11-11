import LocalLaw.VacuumLeafSchur
import LocalLaw.PartialSampleBenchmark

/-! # Exact full switching benchmark with partial core retention

The optional interior mates may repeat. The optional outer mates and sampled
masks are independent. Eliminating the sampled vertices erases precisely
the retained old interior--outer edges and fills their degrees with q.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullQuadVacuumDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {K L:Type} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

def fullQuadLeafMate (inner outer:L→Option K) (B C:Set L):B⊕C→Option K
  | .inl b=>outer b.val
  | .inr c=>inner c.val

def fullQuadRetainedEdges (inner outer:L→Option K) (α:ℂ):Matrix K K ℂ:=
  fun k k'=>∑i,((if inner i=some k∧outer i=some k' then α else 0)+
    (if outer i=some k∧inner i=some k' then α else 0))

def fullQuadRetainedDegree (inner outer:L→Option K) (k:K):ℂ:=
  ∑i,((if inner i=some k∧outer i≠none then 1 else 0)+
    (if outer i=some k∧inner i≠none then 1 else 0))

def fullQuadVacuumPrecision (inner outer:L→Option K) (B C:Set L) (A₀:Matrix K K ℂ) (q p α:ℂ):
    Matrix (K⊕(B⊕C)) (K⊕(B⊕C)) ℂ:=
  vacuumLeafMatrix (fullQuadLeafMate inner outer B C)
    (A₀-fullQuadRetainedEdges inner outer α) (fullQuadRetainedDegree inner outer) q p α

def fullQuadOldPrecision (B C:Set L) (A₀:Matrix K K ℂ) (q p α:ℂ):
    Matrix (K⊕(B⊕C)) (K⊕(B⊕C)) ℂ:=
  Matrix.fromBlocks A₀ 0 0 (partialSamplePrecision B C q p α)

def fullQuadSampleCharge (inner outer:L→Option K) (B C:Set L) (q α:ℂ):Matrix (B⊕C) (B⊕C) ℂ:=
  Matrix.fromBlocks
    (Matrix.diagonal (fun b:B=>q*α^2*((if outer b.val=none then 0 else 1)-(if b.val∈C then 1 else 0))))
    (-(partialMatchingCoupling B C α)) (-(partialMatchingCoupling B C α).transpose)
    (Matrix.diagonal (fun c:C=>q*α^2*((if inner c.val=none then 0 else 1)-(if c.val∈B then 1 else 0))))

def fullQuadSurgeryCoupling (inner outer:L→Option K) (B C:Set L) (q α:ℂ):
    Matrix (K⊕(B⊕C)) (K⊕(B⊕C)) ℂ:=
  let mate:=fullQuadLeafMate inner outer B C
  let E:=vacuumLeafIncidence mate α
  Matrix.fromBlocks
    (-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*(fullQuadRetainedDegree inner outer k-vacuumLeafMultiplicity mate k)))
    E E.transpose (fullQuadSampleCharge inner outer B C q α)

omit [Fintype K] in
theorem fullQuadVacuum_precision_update (inner outer:L→Option K) (B C:Set L)
    (A₀:Matrix K K ℂ) (q p α:ℂ) (hrel:p⁻¹=q⁻¹-q*α^2) :
    fullQuadVacuumPrecision inner outer B C A₀ q p α=
      fullQuadOldPrecision B C A₀ q p α+fullQuadSurgeryCoupling inner outer B C q α := by
  ext u v
  rcases u with k | (b | c) <;> rcases v with k' | (b' | c')
  all_goals simp only [fullQuadVacuumPrecision,vacuumLeafMatrix,fullQuadOldPrecision,
    fullQuadSurgeryCoupling,fullQuadSampleCharge,partialSamplePrecision,
    vacuumLeafDiagonal,fullQuadLeafMate,partialVacuumDiagonal,Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.zero_apply,
    Matrix.diagonal_apply,Matrix.transpose_apply]
  all_goals first | rfl | (try split_ifs)
  all_goals (try simp_all [hrel]) <;> ring

theorem fullQuadVacuum_schur (inner outer:L→Option K) (B C:Set L)
    (A₀:Matrix K K ℂ) (q p α:ℂ) (hq:q≠0) (hp:p≠0)
    (hcut:IsUnit (A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k))) :
    IsUnit (fullQuadVacuumPrecision inner outer B C A₀ q p α)∧
      blockSchur (fullQuadVacuumPrecision inner outer B C A₀ q p α)=
        A₀-fullQuadRetainedEdges inner outer α-
          Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k)∧
      ((fullQuadVacuumPrecision inner outer B C A₀ q p α)⁻¹).toBlocks₁₁=
        (A₀-fullQuadRetainedEdges inner outer α-
          Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k))⁻¹ :=
  vacuumLeaf_schur (fullQuadLeafMate inner outer B C)
    (A₀-fullQuadRetainedEdges inner outer α) (fullQuadRetainedDegree inner outer) q p α hq hp hcut

end LocalLaw
