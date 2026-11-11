import LocalLaw.SourceBoundaryDefect
import LocalLaw.SourcePairedSurgeryParameters
import LocalLaw.ActualSourceEndpointStability

/-!
# Actual sparse boundary-defect pattern and derived column sums

Every physical/model comparison and numerical smallness is derived from the
source enlarged event. Only the actual exceptional-label cardinality remains
as a count argument; the independent probability module controls that count.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualBoundaryColumnDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def pairedEndpointGoodError (C w δ n φ : ℝ) : ℝ :=
  (1+C*w)^2*φ+2*(1+C*w)^3*(2*δ+n*φ)*w*δ

namespace RegularGraph

theorem eventually_actual_boundary_defect_pattern (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let selector := R/4
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let s := g.admissibleState T labels S
      let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))
      let w := endpointSurgeryCouplingCap d
      let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z
      let δold := 2*C1*g.sourcePrime a (logarithmicRadius β d N) z
      let D := g.sourceBoundaryDefect T labels S selector r (g.Q z) z
      ∃ hfit : ell+1≤R/8, ∀ φ : ℝ, 0≤φ →
        let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ S
        let η := pairedEndpointGoodError C w δold (Fintype.card (s.endpointModelRoots selector)) φ
        (∀ u v, ‖D u v‖≤δ) ∧
        (∀ u v, u≠v → (u∈good ∨ v∈good) → ‖D u v‖≤η) ∧
        (∀ Bbad : ℕ, (Finset.univ\good).card≤Bbad → ∀ j,
          ∑ i, ‖D i j‖≤((Bbad:ℝ)+1)*δ+(Fintype.card ι:ℝ)*η) := by
  filter_upwards [eventually_actual_source_endpoint_stability a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_paired_endpoint_offdiagonal a b d c β B C1 ha hb hd hc hβ hβc hC1,
    Filter.eventually_ge_atTop 1] with N hglobal hpaired hN
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels S
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))
  let w := endpointSurgeryCouplingCap d
  let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z
  let δold := 2*C1*g.sourcePrime a (logarithmicRadius β d N) z
  let D := g.sourceBoundaryDefect T labels S selector r (g.Q z) z
  obtain ⟨hfit,hpairs⟩ := hpaired g o z hz hfloor hzB Cq badCount hplus labels S
  refine ⟨hfit,?_⟩
  intro φ hφ
  let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ S
  let η := pairedEndpointGoodError C w δold (Fintype.card (s.endpointModelRoots selector)) φ
  have hglobal' : ∀ u v, ‖D u v‖≤δ := by
    intro u v
    exact hglobal g o z hz hfloor hzB Cq badCount hplus labels S
      (s.endpointFinalBoundaryRoot selector u) (s.endpointFinalBoundaryRoot selector v)
  have hpattern : ∀ u v, u≠v → (u∈good ∨ v∈good) → ‖D u v‖≤η :=
    g.sourceBoundaryDefect_sparse_pattern o ell R r hfit labels S (g.Q z) z φ η
      (fun i j hji hnot hi => hpairs i j φ hφ hji hnot hi)
  have hC0 : 0≤C := by
    dsimp only [C,endpointSurgeryModelRowCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hprime : 0≤g.sourcePrime a (logarithmicRadius β d N) z := by
    have hh := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    unfold sourcePrime inflatedPrime
    positivity
  have hδ : 0≤δ := by dsimp only [δ,sourceEndpointErrorConstant]; positivity
  have hδold : 0≤δold := by dsimp only [δold]; positivity
  have hη : 0≤η := by dsimp only [η,pairedEndpointGoodError]; positivity
  refine ⟨hglobal',hpattern,?_⟩
  intro Bbad hcount j
  apply sparse_boundary_defect_column_sum D (Finset.univ\good) Bbad δ η hcount hδ hη hglobal' _ j
  intro u v huv hg
  apply hpattern u v huv
  rcases hg with hu | hv
  · exact Or.inl (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hu)
  · exact Or.inr (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hv)

end RegularGraph
end LocalLaw
