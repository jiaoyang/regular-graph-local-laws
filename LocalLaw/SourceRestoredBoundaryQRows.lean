import LocalLaw.RestoredBoundaryQRows

/-! # Realized restored boundary rows on actual switched pair vertex sets -/
open Filter
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRestoredQRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

/-- The partial vacuum's restored A precision is genuinely nonsingular
and its inverse has fixed row and column bounds at q=Q(old graph). Every
geometric and numerical hypothesis of the finite row theorem is derived. -/
theorem eventually_source_restored_boundary_Q_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(Cq badCount:ℕ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let e:=s.partialBoundaryEmbedding selector S
      let P:=(((g.deficient.delete T).restrict S).extensionGreen (g.Q z) z).submatrix e e
      let K:=P⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>g.Q z*treeEdgeWeight d^2)
      IsUnit K ∧ (∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
        (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_old_switched_pair_reference_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_paperError_small a b d β ha hb hd hβ,eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,hdepth,eventually_ge_atTop 1]
    with N hmodels htail hsmall hrad hlog hdepthN hN
  intro g o z Cq badCount hz hfloor hplus hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hm:=hmodels g o z Cq badCount hz hfloor hplus hballs labels samples x y
  have hell:ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have ht:=htail g o ell hell labels samples selector (logarithmicRadius β d N) selector hrad.2.2.1 z hz.le
  simp only [one_mul] at ht
  have hεcap:ε≤1 := (hsmall z hz hfloor).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hlog))
  have hcap:ε/L^16≤1 :=
    (div_le_self (graphPaperError_nonnegative a d N _ z hN hz.le) (one_le_pow₀ hlog)).trans hεcap
  have hcard:=Nat.cast_le (α:=ℝ).mpr (s.partialBoundaryMask_card_le_roots selector S)
  have hmask:(Fintype.card (s.partialBoundaryMask selector S):ℝ)*physicalTransfer d z^selector≤1 := by
    have hh:=(mul_le_mul_of_nonneg_right hcard (pow_nonneg (physicalTransfer_pos d hd z).le _)).trans (ht.trans hcap)
    simpa only [Nat.card_eq_fintype_card] using hh
  exact g.partial_restored_boundary_q_rows hd T labels samples selector S hm.1 z (g.Q z) hz
    (g.Q_im_nonnegative z hz) (hereditaryReferenceRadius d (augmentedObservationDiameter d r))
    hm.2.1 hm.2.2.1 hmask

end RegularGraph
end LocalLaw
