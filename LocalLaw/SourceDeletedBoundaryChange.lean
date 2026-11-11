import LocalLaw.SourcePartialBoundaryContinuity

/-! # The actual deleted pair model absorbs the switching change in Q -/

open Filter
noncomputable section
namespace LocalLaw
local instance sourceDeletedBoundaryChangeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_deleted_boundary_change (a b d Bnear : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q v : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0 ≤ q.im → 0 ≤ v.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖v-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖q-v‖≤graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ)^16 →
      (∀ w,graphBallExcess g.graph w (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let h:=g.labelledResampledGraph T labels samples selector
      (∀ w : (Tᶜ:Set (Fin N)),
        (tripleNearIndices g.graph T (logarithmicRadius (c/4) d N/2) samples w).card≤Bnear) →
      ∀ x y : (Tᶜ:Set (Fin N)),
      ‖h.deletedP T r z q x y-h.deletedP T r z v x y‖≤g.sourcePrime a (logarithmicRadius β d N) z := by
  let K:=sourcePartialContinuityConstant d β Bnear
  have hobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hK : 0≤K := by
    dsimp only [K,sourcePartialContinuityConstant,sourcePartialObservationLogCap]
    positivity
  filter_upwards [eventually_source_partial_boundary_continuity a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat (|K|+1),eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hcontinuity hlarge hlog hN
  intro g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hchange hballs ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hLp : 0<L := by dsimp only [L]; linarith
  have hKL : K≤L := (le_abs_self K).trans ((by linarith : |K|≤|K|+1).trans hlarge)
  intro hnear x y
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let xl:=pairBallLeft (outsideGraph (s.fullResample selector).graph T) x y r
  let yl:=pairBallRight (outsideGraph (s.fullResample selector).graph T) x y r
  have hS : S⊆s.twoTargetEndpointVertices selector r x y := s.switched_pairBall_subset_old_augmentation selector r x y
  have hcomp:=hcontinuity g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hballs labels samples x y S hS
    Bnear xl yl (hnear x) (hnear y)
  change ‖M.extensionGreen q z xl yl-M.extensionGreen v z xl yl‖≤g.sourcePrime a (logarithmicRadius β d N) z
  apply hcomp.trans
  change K*L*‖q-v‖≤L^3*ε
  calc
    _≤K*L*(ε/L^16) := mul_le_mul_of_nonneg_left hchange (mul_nonneg hK hLp.le)
    _=(K*L*ε)/L^16 := by ring
    _≤L^3*ε := by
      apply (div_le_iff₀ (pow_pos hLp 16)).mpr
      have hkl : K*L≤L^2 := (mul_le_mul_of_nonneg_right hKL hLp.le).trans_eq (by ring)
      have hp : L^2≤L^(3+16) := pow_le_pow_right₀ hlog (by omega)
      have hh:=mul_le_mul_of_nonneg_right (hkl.trans hp) hε
      exact hh.trans_eq (by rw [pow_add]; ring)

end RegularGraph
end LocalLaw
