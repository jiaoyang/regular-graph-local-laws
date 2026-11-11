import LocalLaw.SourceFullTwoTargetGeometry

/-! # Hereditary geometry of every actual full partial restriction -/

noncomputable section
namespace LocalLaw
local instance sourceFullRestrictionGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def fullRestrictionLogCap (d : ℕ) (β : ℝ) : ℝ :=
  (((2*(finiteOmega d+2)+1:ℕ):ℝ)+1)^2 *
    (|fullTwoTargetLogCap d β|+|sourceObservationLogCap d β|+1)

theorem fullRestrictionLogCap_properties (d : ℕ) (β : ℝ) :
    0 ≤ fullRestrictionLogCap d β ∧ sourceObservationLogCap d β ≤ fullRestrictionLogCap d β ∧
    ((2*(finiteOmega d+2)+1:ℕ):ℝ)*fullTwoTargetLogCap d β ≤ fullRestrictionLogCap d β ∧
    ((2*(finiteOmega d+2)+1:ℕ):ℝ)^2*fullTwoTargetLogCap d β ≤ fullRestrictionLogCap d β := by
  let H : ℝ := ((2*(finiteOmega d+2)+1:ℕ):ℝ)
  let A := |fullTwoTargetLogCap d β|+|sourceObservationLogCap d β|+1
  have hH : 0 ≤ H := Nat.cast_nonneg _
  have hA : 1 ≤ A := by dsimp only [A]; nlinarith only [abs_nonneg (fullTwoTargetLogCap d β),abs_nonneg (sourceObservationLogCap d β)]
  have hobs : sourceObservationLogCap d β≤A := by dsimp only [A]; linarith [le_abs_self (sourceObservationLogCap d β),abs_nonneg (fullTwoTargetLogCap d β)]
  have haug : fullTwoTargetLogCap d β≤A := by dsimp only [A]; linarith [le_abs_self (fullTwoTargetLogCap d β),abs_nonneg (sourceObservationLogCap d β)]
  have hp1 : 1≤(H+1)^2 := by nlinarith [sq_nonneg H]
  have hpH : H≤(H+1)^2 := by nlinarith [sq_nonneg H]
  have hpH2 : H^2≤(H+1)^2 := by nlinarith
  change 0≤(H+1)^2*A ∧ sourceObservationLogCap d β≤(H+1)^2*A ∧
    H*fullTwoTargetLogCap d β≤(H+1)^2*A ∧ H^2*fullTwoTargetLogCap d β≤(H+1)^2*A
  refine ⟨by positivity, hobs.trans ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hp1 (by linarith : 0≤A)]
  · exact (mul_le_mul_of_nonneg_left haug hH).trans
      (mul_le_mul_of_nonneg_right hpH (by linarith))
  · exact (mul_le_mul_of_nonneg_left haug (sq_nonneg H)).trans
      (mul_le_mul_of_nonneg_right hpH2 (by linarith))

namespace RegularGraph

theorem eventually_source_fullRestriction_geometry (a b d : ℕ) (c β B : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N) (S : Set (Fin N)),
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState (graphBallVertices g.graph o ell) labels samples
      S⊆s.fullTwoTargetVertices (logarithmicRadius (c/4) d N/4) r x y →
      let R := hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
      (g.deficient.restrict S).ComponentFiniteReferenceBudget ∧
      (∀u v,(g.deficient.restrict S).graph.dist u v≤R) ∧
      (R:ℝ)+1≤fullRestrictionLogCap d β*Real.log (N:ℝ) ∧
      (hereditaryReferenceRadius d R:ℝ)+1≤fullRestrictionLogCap d β*Real.log (N:ℝ) := by
  filter_upwards [eventually_source_fullTwoTarget_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_log_ge_nat 1] with N hgeo hL
  intro g o z hz hfloor hballs ι _ labels samples x y S
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState (graphBallVertices g.graph o ell) labels samples
  let M := s.fullTwoTargetVertices (logarithmicRadius (c/4) d N/4) r x y
  let D := fullTwoTargetDiameter d ell r
  let R := hereditaryReferenceRadius d D
  let L := Real.log (N:ℝ)
  intro hSM
  have hg := (hgeo g o z hz hfloor hballs labels samples x y).1
  have hfinite := hg.base.to_componentFinite
  have hold := hereditaryReferenceRadius_log_bound d D (fullTwoTargetLogCap d β) L hg.diameter_log
  have hcut := hereditaryReferenceRadius_log_bound d R
    (((2*(finiteOmega d+2)+1:ℕ):ℝ)*fullTwoTargetLogCap d β) L hold
  have hcaps := fullRestrictionLogCap_properties d β
  have hL0 : 0≤L := by dsimp only [L]; linarith
  refine ⟨g.deficient.subset_restriction_component_budget M S hSM hfinite,
    g.deficient.subset_restriction_intrinsic_diameter M S hSM hfinite D hg.diameter, ?_, ?_⟩
  · exact hold.trans (mul_le_mul_of_nonneg_right hcaps.2.2.1 hL0)
  · have hh := mul_le_mul_of_nonneg_right hcaps.2.2.2 hL0
    nlinarith only [hcut,hh]

end RegularGraph
end LocalLaw
