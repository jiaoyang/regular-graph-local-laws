import LocalLaw.SourceCavityEstimate
import LocalLaw.SourceCavityParameterTransport
import LocalLaw.ResamplingNeighborSet
import LocalLaw.SourceLocalCertificate

/-! # Actual target-Q average absolute cavity certificate

The graph's genuine neighbor average is used. The neighbor set is preserved
by boundary switching, and the finite iteration is transported from old Q
to target Q using the proved switching Ward estimate.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCavityAverageCertificateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceCavityAverageConstant (d J : ℕ) (β C1 : ℝ) : ℝ := sourceCavityEstimateConstant d J β C1+1

namespace RegularGraph

theorem eventually_source_cavity_average_certificate (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∀ badCount : ℕ, badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      g.SourceCavityWeightGood a c β C1 o z samples →
      (graphBall gnew.graph o R).IsTree →
      gnew.sourceCavityAbsoluteResidual ell o z≤sourceCavityAverageConstant d J β C1*(ε/L^4) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_neighbor_cavity_estimate a b d J c β γ B C1 Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_actual_selected_cavity_parameter_change a b d c β B C1 ha hb hd hc hβ hβc hC1 hB,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,hdepth]
    with N hestimate htransport hnum hdepth
  intro g o z hz hzB hfloor badCount hbadCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let Rstruct := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
  let K := sourceCavityAverageConstant d J β C1
  intro htarget hisolation hrejected hconcentration hTree
  have hpointOld := hestimate g o z hz hzB hfloor badCount hbadCount hplus labels samples htarget
    hisolation hrejected hconcentration hTree
  have hiterate := htransport g o z hz hzB hfloor Cq badCount hplus labels samples htarget
  have num := hnum z hz hfloor
  have hε : 0≤ε := num.error_nonnegative
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hell : 1≤ell := by
    have hh := (actualCavityDepth_radius_bounds a d N z hdepth).1
    have hh' : (1:ℝ)≤(ell:ℝ) := by dsimp only [ell]; linarith
    exact_mod_cast hh'
  have hdepthEq : ell+1=actualCavityDepth a d N z := by dsimp only [ell] at *; omega
  have hneighbors : gnew.graph.neighborSet o=g.graph.neighborSet o :=
    s.fullResample_neighborSet_eq (Rstruct/4) o ell hell rfl
  let e : g.graph.neighborSet o ≃ gnew.graph.neighborSet o := Equiv.setCongr hneighbors.symm
  have hiterate' : ‖cavityIterate z (g.Q z) (ell+1)-cavityIterate z (gnew.Q z) (ell+1)‖≤ε/L^4 := by
    rw [hdepthEq]
    exact hiterate.trans (div_le_div_of_nonneg_left hε (pow_pos hLp 4) (pow_le_pow_right₀ hL (by omega)))
  have hpoint (j : gnew.graph.neighborSet o) :
      ‖green (deletedMatrix gnew.H j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩-
        cavityIterate z (gnew.Q z) (ell+1)‖≤K*(ε/L^4) := by
    let jold := e.symm j
    have hjold : jold.val=j.val := rfl
    have hp := hpointOld jold
    change ‖green (deletedMatrix gnew.H jold.val) z ⟨o,jold.property.ne⟩ ⟨o,jold.property.ne⟩-
      cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖≤sourceCavityEstimateConstant d J β C1*(ε/L^4) at hp
    rw [←hdepthEq] at hp
    have hp' : ‖green (deletedMatrix gnew.H j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩-
        cavityIterate z (g.Q z) (ell+1)‖≤sourceCavityEstimateConstant d J β C1*(ε/L^4) := by
      simpa only [hjold] using hp
    have ht := (norm_sub_le_norm_sub_add_norm_sub (green (deletedMatrix gnew.H j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩)
      (cavityIterate z (g.Q z) (ell+1)) (cavityIterate z (gnew.Q z) (ell+1))).trans (add_le_add hp' hiterate')
    exact ht.trans_eq (by dsimp only [K,sourceCavityAverageConstant]; ring)
  have hcard : Fintype.card (gnew.graph.neighborSet o)=d :=
    (gnew.graph.card_neighborSet_eq_degree o).trans (gnew.regular o)
  change (d:ℝ)⁻¹*∑ j : gnew.graph.neighborSet o,‖green (deletedMatrix gnew.H j.val) z
    ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩-cavityIterate z (gnew.Q z) (ell+1)‖≤K*(ε/L^4)
  calc
    _ ≤ (d:ℝ)⁻¹*∑ _j : gnew.graph.neighborSet o,K*(ε/L^4) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hpoint j)) (by positivity)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
      have hd0 : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by omega)
      field_simp

end RegularGraph
end LocalLaw
