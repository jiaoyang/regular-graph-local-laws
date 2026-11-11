import LocalLaw.FullEndpointBudget
import LocalLaw.FilledModelDiameter
import LocalLaw.SourceObservationParameters
import LocalLaw.EffectiveModelRadius

/-! # Actual source class and logarithmic diameter of the filled model -/

noncomputable section
namespace LocalLaw
local instance sourceFilledEndpointBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def filledEndpointDiameter (d ell r : ℕ) : ℕ :=
  2*ell+2*((2*(finiteOmega d+1))*(2*r+1)+1)

def filledEndpointLogCap (d : ℕ) (β : ℝ) : ℝ := 2*sourceObservationLogCap d β+3

theorem eventually_filledEndpoint_diameter_log (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      (filledEndpointDiameter d (actualCavityDepth a d N z-1) (effectiveModelRadius a d N β):ℝ)+1≤
        filledEndpointLogCap d β*Real.log (N:ℝ) := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actualCavityDepth_le_log a d hd] with N hnum hdepth
  intro z hz hscale
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  have num := hnum z hz hscale
  have hell : (ell:ℝ)≤L := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (hdepth z)
  have hRout : ((2*(finiteOmega d+1))*(2*r+1):ℝ)≤(singletonObservationDiameter d r:ℝ) := by
    exact_mod_cast endpoint_component_diameter_le_observation d r
  have hRlog := num.diameter_log
  have hL := num.log_one
  change (filledEndpointDiameter d ell r:ℝ)+1≤filledEndpointLogCap d β*L
  unfold filledEndpointDiameter filledEndpointLogCap
  push_cast
  nlinarith only [hell,hRout,hRlog,hL]


structure SourceFullEndpointGeometry {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}
    (M : DeficientGraph V d) (Rfull : ℕ) (A L : ℝ) : Prop where
  base : M.ComponentReferenceBudget
  diameter : ∀ x y,M.graph.dist x y≤Rfull
  diameter_log : (Rfull:ℝ)+1≤A*L

namespace SourceFullEndpointGeometry
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ} {M : DeficientGraph V d}
    {Rfull : ℕ} {A L : ℝ}
theorem finite_budget (h : SourceFullEndpointGeometry M Rfull A L) : M.ComponentFiniteReferenceBudget :=
  h.base.to_componentFinite
end SourceFullEndpointGeometry

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem source_filledEndpoint_component_budget (g : RegularGraph N d)
    (a rError R ell Cq badCount : ℕ) (r selector : ℕ) (C1 : ℝ) (o : Fin N) (z : ℂ)
    (hplus : g.SourceOmegaPlusWithRadii a r rError R ell (finiteOmega d) Cq badCount C1 o z)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R/8) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    let M := (g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
      (s.endpointModelVertices selector r)
    M.ComponentReferenceBudget ∧ (∀ x y,M.graph.dist x y≤filledEndpointDiameter d ell r) := by
  exact ⟨g.filledEndpoint_component_reference_budget o ell selector r (R/8) boundary samples hsep hmargin
      (hplus.structural.1 o),
    g.filledEndpoint_distance_bound o ell selector r (R/8) (finiteOmega d) boundary samples hsep hmargin
      (hplus.structural.1 o)⟩


theorem eventually_source_fullEndpoint_geometry (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let M := (g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
        (s.endpointModelVertices selector r)
      SourceFullEndpointGeometry M (filledEndpointDiameter d (actualCavityDepth a d N z-1) r)
        (filledEndpointLogCap d β) (Real.log (N:ℝ)) := by
  filter_upwards [eventually_filledEndpoint_diameter_log a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc] with N hlog hmargin
  intro g o z hz hscale Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  have hm : ell+r+1≤R/8 := by have hh := hmargin.2.2.2 z; dsimp only [ell,R,r]; omega
  have hs : 2*r+2≤R/4 := by omega
  have hgeom := g.source_filledEndpoint_component_budget a (logarithmicRadius β d N) R ell Cq badCount
    r (R/4) C1 o z hplus boundary samples hs hm
  exact ⟨hgeom.1,hgeom.2,hlog z hz hscale⟩

end RegularGraph
end LocalLaw
