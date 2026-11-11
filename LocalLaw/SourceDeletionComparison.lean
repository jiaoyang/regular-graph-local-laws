import LocalLaw.SourceDeletionParameters
import LocalLaw.SourceSpectralEvents

/-!
# Actual source deletion comparison

The original weak event supplies the full pair-model approximation. Finite
localization gives every Schur block in the larger neighborhood; genuine
Schur deletion and a second localization identify the actual inherited-
deficit deleted pair model. All smallness fields are realized by
`eventually_sourceDeletionBounds`.
-/

set_option maxHeartbeats 1200000

noncomputable section
namespace LocalLaw
local instance sourceDeletionComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d a : ℕ} {β B : ℝ} {z : ℂ}

/-- Actual Proposition 5.1 at realized finite source parameters. Neither a
four-block approximation nor a deleted approximation is an input. -/
theorem source_deleted_comparison (g : RegularGraph N d)
    (S : SourceDeletionBounds a d N β B z) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (R : ℕ) (hr : 1 ≤ logarithmicRadius β d N)
    (hmargin : 6 * ((actualCavityDepth a d N z - 1) + logarithmicRadius β d N) + 2 ≤ R)
    (hballs : ∀ o, graphBallExcess g.graph o R ≤ finiteOmega d)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hB : ‖z‖ ≤ B)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (happrox : ∀ i j, ‖g.G z i j - g.P (logarithmicRadius β d N) z q i j‖ ≤
      graphPaperError a d N (logarithmicRadius β d N) z)
    (o : Fin N) (i j : ((graphBallVertices g.graph o (actualCavityDepth a d N z - 1))ᶜ : Set (Fin N))) :
    ‖(g.deficient.delete (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))).G z i j -
      g.deletedP (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
        (logarithmicRadius β d N) z q i j‖ ≤
      sourceDeletionConstant d β B * Real.log (N : ℝ) ^ 3 *
        graphPaperError a d N (logarithmicRadius β d N) z := by
  let r := logarithmicRadius β d N
  let ell := actualCavityDepth a d N z - 1
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N r z
  let A := sourceLocalizationLogCap d β
  let K := DeficientGraph.localizationWeakConstant d B A
  let δ := (K + 1) * L * ε
  let M := g.deletionNeighborhoodModel o i.val j.val ell r
  let Tm := deletionNeighborhoodInnerSet g.graph o i.val j.val ell r
  let ii := deletionNeighborhoodOutsideLeft g.graph o i.val j.val ell r i.property
  let jj := deletionNeighborhoodOutsideRight g.graph o i.val j.val ell r j.property
  have hL : 1 ≤ L := S.localization.log_one
  have hLp : 0 < L := by linarith
  have hε : 0 ≤ ε := S.localization.error_nonnegative
  have hA : 0 ≤ A := sourceLocalizationLogCap_nonnegative d hd β hβ
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DeficientGraph.localizationWeakConstant_ge_one d hd B A hA)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hB0 : 0 ≤ B := (norm_nonneg z).trans hB
  have hnear : ‖q - semicircleRoot z‖ ≤ 1 := by
    have hh := weak_prior_scaled_norm z q hz ε L hε S.localization.error_scaled hprior
    have hLsq : 1 ≤ L ^ 2 := by nlinarith only [hL]
    exact (le_mul_of_one_le_right (norm_nonneg _) hLsq).trans hh
  have hMbudget := g.deletionNeighborhoodModel_component_budget o i.val j.val ell r R hmargin hballs
  have hMclass := hMbudget.to_componentFinite
  have hMdiam : ∀ x y, M.graph.dist x y ≤ 6 * (ell + r) + 2 :=
    deletionNeighborhood_distance_bound g.graph o i.val j.val ell r
  have hlocal (x y : deletionNeighborhoodVertices g.graph o i.val j.val ell r) :
      ‖M.extensionGreen q z x y - M.P r z q x y‖ ≤ K * L * ε :=
    S.localization.full_model hd hβ M hMclass q hz hq hB hprior hMdiam x y
  have hblocks (x y : deletionNeighborhoodVertices g.graph o i.val j.val ell r)
      (hx : x.val ∈ graphBallVertices g.graph o ell ∨ x.val = i.val ∨ x.val = j.val)
      (hy : y.val ∈ graphBallVertices g.graph o ell ∨ y.val = i.val ∨ y.val = j.val) :
      ‖g.G z x.val y.val - M.extensionGreen q z x y‖ ≤ δ := by
    have hid := g.deletionNeighborhoodModel_P_schur o i.val j.val ell r x y hx hy q z
    have hsecond : ‖g.P r z q x.val y.val - M.extensionGreen q z x y‖ ≤ K * L * ε := by
      rw [← hid]
      simpa only [norm_sub_rev] using hlocal x y
    have htri := (norm_sub_le_norm_sub_add_norm_sub (g.G z x.val y.val) (g.P r z q x.val y.val)
      (M.extensionGreen q z x y)).trans (add_le_add (happrox x.val y.val) hsecond)
    apply htri.trans
    have hεL := le_mul_of_one_le_left hε hL
    dsimp only [δ]
    nlinarith only [hεL]
  have hcut : (Nat.card (graphBallVertices g.graph o ell) : ℝ) *
      DeficientGraph.boundarySchurConstant d B * δ ≤ 1 / 2 := S.cut_small g o
  have hTT : ∀ x y : Tm, ‖g.G z x.val.val y.val.val - M.extensionGreen q z x.val y.val‖ ≤ δ := by
    intro x y
    exact hblocks x.val y.val (Or.inl ((deletionNeighborhood_inner_mem g.graph o i.val j.val ell r _).mp x.property))
      (Or.inl ((deletionNeighborhood_inner_mem g.graph o i.val j.val ell r _).mp y.property))
  have hrow : ∀ x : Tm, ‖g.G z i.val x.val.val - M.extensionGreen q z
      (deletionNeighborhoodLeft g.graph o i.val j.val ell r) x.val‖ ≤ δ := by
    intro x
    exact hblocks (deletionNeighborhoodLeft g.graph o i.val j.val ell r) x.val (Or.inr (Or.inl rfl))
      (Or.inl ((deletionNeighborhood_inner_mem g.graph o i.val j.val ell r _).mp x.property))
  have hcol : ∀ y : Tm, ‖g.G z y.val.val j.val - M.extensionGreen q z y.val
      (deletionNeighborhoodRight g.graph o i.val j.val ell r)‖ ≤ δ := by
    intro y
    exact hblocks y.val (deletionNeighborhoodRight g.graph o i.val j.val ell r) (Or.inl ((deletionNeighborhood_inner_mem g.graph o i.val j.val ell r _).mp y.property))
      (Or.inr (Or.inr rfl))
  have ht : ‖g.G z i.val j.val - M.extensionGreen q z
      (deletionNeighborhoodLeft g.graph o i.val j.val ell r)
      (deletionNeighborhoodRight g.graph o i.val j.val ell r)‖ ≤ δ :=
    hblocks (deletionNeighborhoodLeft g.graph o i.val j.val ell r)
      (deletionNeighborhoodRight g.graph o i.val j.val ell r) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  have hdelete := g.neighborhood_deleted_comparison hd o i.val j.val ell r R hr i.property j.property
    hmargin hballs q z hz hq B hB hnear (S.reference_small q hprior) (S.deleted_small q hprior)
    δ hδ hTT hrow hcol ht hcut
  have hlogDelete := model_deletion_error_log_bound d hd B hB0 ell
    (Nat.card (graphBallVertices g.graph o ell)) δ ((K + 1) * ε) L hδ hL S.depth_cap
    (S.cut_scale g o) (by dsimp only [δ]; ring_nf; exact le_rfl)
  have hdeletion : ‖(g.deficient.delete (graphBallVertices g.graph o ell)).G z i j -
      (M.delete Tm).extensionGreen q z ii jj‖ ≤ modelDeletionLogConstant d B * L ^ 3 * ((K + 1) * ε) :=
    hdelete.trans hlogDelete
  have hTconn : (M.graph.induce Tm).Connected :=
    graphBall_connected M.graph (deletionNeighborhoodRoot g.graph o i.val j.val ell r) ell
  have hdelClass := M.componentwise_connected_deletion_budget
    (g.deletionNeighborhoodModel_zero_deficit o i.val j.val ell r) hMbudget Tm hTconn
  have hdelDiam : ∀ x y, (M.delete Tm).graph.dist x y ≤ 2 * r + (finiteOmega d + 2) * (2 * r + 1) :=
    deletedNeighborhood_distance_bound g.graph o i.val j.val ell r R (finiteOmega d)
      hr i.property j.property hmargin (hballs o)
  have hdelLocal := S.localization.deleted_model hd hβ (M.delete Tm) hdelClass q hz hq hB hprior
    hdelDiam ii jj
  have hid := g.deletionNeighborhoodModel_deleted_P o i.val j.val ell r i.property j.property q z
  have hmodel : ‖(M.delete Tm).extensionGreen q z ii jj -
      g.deletedP (graphBallVertices g.graph o ell) r z q i j‖ ≤ K * L * ε := by
    rw [← hid]
    exact hdelLocal
  have htri := (norm_sub_le_norm_sub_add_norm_sub ((g.deficient.delete (graphBallVertices g.graph o ell)).G z i j)
    ((M.delete Tm).extensionGreen q z ii jj) (g.deletedP (graphBallVertices g.graph o ell) r z q i j)).trans
      (add_le_add hdeletion hmodel)
  apply htri.trans
  have hpow : L ≤ L ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
  have hlast := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hε
  calc
    _ ≤ modelDeletionLogConstant d B * L ^ 3 * ((K + 1) * ε) + K * L ^ 3 * ε := add_le_add_left hlast _
    _ = sourceDeletionConstant d β B * L ^ 3 * ε := by dsimp only [sourceDeletionConstant, K, A]; ring

end RegularGraph
end LocalLaw
