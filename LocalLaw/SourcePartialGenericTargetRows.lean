import LocalLaw.PartialOldTargetRows
import LocalLaw.SourceObservationGeneralCap
import LocalLaw.EndpointFarTailParameters

/-! # Realized arbitrary-q partial target weights on every admitted restriction -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePartialGenericTargetRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_generic_target_rows (a b d : ℕ) (c β B C1 A : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hA : sourceObservationLogCap d β≤A) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0 ≤ q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let R:=logarithmicRadius (c/4) d N
      let selector:=R/4
      let s:=g.admissibleState T labels samples
      ∀ (S : Set (Tᶜ:Set (Fin N))),((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget →
      ∀ D : ℕ,(∀ u v,((g.deficient.delete T).restrict S).graph.dist u v≤D) →
      (D:ℝ)+1≤A*Real.log (N:ℝ) → ∀ (Bnear : ℕ) (x : S),
      (tripleNearIndices g.graph T (R/2) samples x.val).card≤Bnear →
      (∑ i : s.PartialEndpointIndex selector S,
        ‖((g.deficient.delete T).restrict S).extensionGreen q z x (s.partialEndpointEmbedding selector S i)‖)≤
        2*finiteExtraReferenceConstant d*(3*(Bnear:ℝ)+1) := by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,hdepth]
    with N hnum htail hradii hdepthN
  intro g o z q hz hfloor hqim hpriorQ ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let R:=logarithmicRadius (c/4) d N
  let selector:=R/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  intro S hbudget D hdiam hDlog Bnear x hnear
  have num:=hnum z hz hfloor
  have hprior:=hpriorQ.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hsmall:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((D:ℝ)+1)≤1/2 :=
    (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B
      (C1^2*ε) L A (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative
      num.error_scaled hprior D (4*r+1) hDlog num.pair_log num.localization_large).1
  have hrows:=g.partial_old_endpoint_rows hd T labels samples selector S hbudget D hdiam
    q z hz hqim hsmall (R/2) Bnear x hnear
  have hell:ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have ht:=htail g o ell hell labels samples selector (logarithmicRadius β d N) (R/2)
    (by dsimp only [R]; have hh:=hradii.1; omega) z hz.le
  simp only [one_mul] at ht
  have hC1sq:1≤C1^2 := by nlinarith
  have hεone:ε≤1 := by
    have hh:ε≤(C1^2*ε)*L^4 :=
      (le_mul_of_one_le_left num.error_nonnegative hC1sq).trans
        (le_mul_of_one_le_right (mul_nonneg (sq_nonneg C1) num.error_nonnegative) (one_le_pow₀ num.log_one))
    exact hh.trans num.error_scaled
  have htailOne:(Nat.card (s.endpointModelRoots selector):ℝ)*physicalTransfer d z^(R/2)≤1 :=
    ht.trans ((div_le_self num.error_nonnegative (one_le_pow₀ num.log_one)).trans hεone)
  exact hrows.trans (mul_le_mul_of_nonneg_left (add_le_add_left htailOne _) (by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    positivity))

end RegularGraph
end LocalLaw
