import LocalLaw.SingleTargetOutsideModel
import LocalLaw.ComponentCutGeometry
import LocalLaw.DeficientBudgetIso

/-! # Actual deleted one-target geometry for outside Green comparisons -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourceOutsideDeletedGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideDeletedDiameter (d ell r : ℕ) : ℕ :=
  (finiteOmega d+1)*(2*singleTargetFilledDiameter d ell r+1)

def sourceOutsideDeletedLogCap (d : ℕ) (β : ℝ) : ℝ :=
  2*((finiteOmega d:ℝ)+1)*singleTargetFilledLogCap d β+1

namespace RegularGraph
variable {N d : ℕ}

theorem filledOutside_budget_diameter (g : RegularGraph N d)
    (T : Set (Fin N)) (K : Set (Tᶜ:Set (Fin N)))
    (hT : (g.graph.induce T).Connected)
    (hbase : (g.filledExteriorModel T K).ComponentReferenceBudget)
    (R : ℕ) (hR : ∀ x y,(g.filledExteriorModel T K).graph.dist x y≤R) :
    ((g.deficient.delete T).restrict K).ComponentFiniteReferenceBudget ∧
      ∀ x y,((g.deficient.delete T).restrict K).graph.dist x y≤(finiteOmega d+1)*(2*R+1) := by
  let M := g.filledExteriorModel T K
  let I := filledExteriorInner T K
  let ψ := filledExteriorOutsideIso g.graph T K
  let Q := (g.deficient.delete T).restrict K
  have hI : (M.graph.induce I).Connected := (filledInnerGraphIso g.graph T K).connected_iff.mpr hT
  have hzero : ∀ v,M.deficit v=0 := fun _ => rfl
  have hbudget := M.componentwise_connected_deletion_budget hzero hbase I hI
  have hdiam := M.componentwise_connected_deletion_diameter hzero hbase I hI R hR
  have hdef (x : K) : Q.deficit x=(M.delete I).deficit (ψ.symm x) := by
    have hh := g.deficient.filledExterior_deleted_deficit T K (ψ.symm x)
    change (M.delete I).deficit (ψ.symm x)=Q.deficit (ψ (ψ.symm x)) at hh
    rw [ψ.apply_symm_apply] at hh
    exact hh.symm
  constructor
  · exact (M.delete I).componentFiniteReferenceBudget_of_iso Q ψ.symm hdef hbudget
  · intro x y
    have hh := hdiam (ψ.symm x) (ψ.symm y)
    have he : Q.graph.dist x y=(M.delete I).graph.dist (ψ.symm x) (ψ.symm y) :=
      (graphIso_dist ψ.symm x y).symm
    rw [he]
    exact hh


theorem eventually_source_outside_deleted_geometry (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ∀ (y : Fin N) (hy : y∉T),
      let K := g.singleTargetOutsideVertices T labels samples (R/4) r y
      ((gnew.deficient.delete T).restrict K).ComponentFiniteReferenceBudget ∧
      (∀ u v,((gnew.deficient.delete T).restrict K).graph.dist u v≤sourceOutsideDeletedDiameter d ell r) ∧
      (sourceOutsideDeletedDiameter d ell r:ℝ)+1≤sourceOutsideDeletedLogCap d β*Real.log (N:ℝ) ∧
      (∀ α : BoundaryOrientedEdge gnew.graph T,
        graphBallVertices (outsideGraph gnew.graph T) (boundaryOutsideVertex gnew.graph T α) r⊆K) ∧
      graphBallVertices (outsideGraph gnew.graph T) ⟨y,hy⟩ r⊆K := by
  filter_upwards [eventually_singleTargetFilled_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat 1] with N hgeom hlog
  intro g o z hz hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let s := g.admissibleState T labels samples
  intro htarget y hy
  let K := g.singleTargetOutsideVertices T labels samples (R/4) r y
  let Rfull := singleTargetFilledDiameter d ell r
  have geom := g.singleTargetOutside_geometry T labels samples (R/4) r y Rfull
    (singleTargetFilledLogCap d β) (Real.log (N:ℝ))
      (hgeom g o z hz hfloor Cq badCount hplus labels samples htarget y)
  have hT : (gnew.graph.induce T).Connected := by
    rw [show gnew.graph.induce T=g.graph.induce T from s.fullResample_induce (R/4)]
    exact graphBall_connected g.graph o ell
  have hdg := gnew.filledOutside_budget_diameter T K hT geom.base Rfull geom.diameter
  refine ⟨hdg.1,hdg.2,?_,?_,?_⟩
  · have hh := geom.diameter_log
    have hΩ : (0:ℝ)≤(finiteOmega d:ℝ)+1 := by positivity
    have hm := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2*((finiteOmega d:ℝ)+1) by positivity)
    dsimp only [sourceOutsideDeletedDiameter,sourceOutsideDeletedLogCap,Rfull] at *
    push_cast at *
    nlinarith only [hm,hlog]
  · intro α v hv
    exact Or.inl (Or.inr ⟨v,s.endpointModel_contains_new_boundary_ball (R/4) r α hv,rfl⟩)
  · intro v hv
    exact Or.inr (Or.inl ((graphHom_edist_le
      (SimpleGraph.Embedding.induce (G:=gnew.graph) Tᶜ).toHom ⟨y,hy⟩ v).trans hv))

end RegularGraph
end LocalLaw
