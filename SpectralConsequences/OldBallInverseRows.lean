import LocalLaw.SourceDeletionComparisonEffective
import LocalLaw.FullOutsideReplacement
import LocalLaw.SupportedRetainedInverse

/-! # Actual old Green precision on the retained cavity ball

The finite reference retained inverse has constant rows. A proved old weak
event and localization supply its entrywise approximation, and source
smallness transfers the rows to the genuine physical principal inverse.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance oldBallInverseRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem old_ball_inverse_rows {N a d : ℕ} {β B : ℝ} {z : ℂ}
    (g : RegularGraph N d) (S : SourceDeletionBounds a d N β B z)
    (ha : 1 ≤ a) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (hlog : ((d-1 : ℕ) : ℝ) ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (R : ℕ) (hr : 1 ≤ effectiveModelRadius a d N β)
    (hmargin : 6*((actualCavityDepth a d N z-1)+effectiveModelRadius a d N β)+2 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hzB : ‖z‖ ≤ B)
    (hprior : ‖q-semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (happrox : ∀ i j, ‖g.G z i j-g.P (effectiveModelRadius a d N β) z q i j‖ ≤
      graphPaperError a d N (logarithmicRadius β d N) z)
    (o : Fin N) (w : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ : Set (Fin N))) :
    let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
    let U := (g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
    (∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ 2*DeficientGraph.boundarySchurConstant d B) ∧
      (∀ j, ∑ i, ‖U⁻¹ i j‖ ≤ 2*DeficientGraph.boundarySchurConstant d B) := by
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let T := graphBallVertices g.graph o ell
  let M := g.deletionNeighborhoodModel o w.val w.val ell r
  let Tm := deletionNeighborhoodInnerSet g.graph o w.val w.val ell r
  let root := deletionNeighborhoodRoot g.graph o w.val w.val ell r
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N rn z
  let A := sourceLocalizationLogCap d β
  let K := DeficientGraph.localizationWeakConstant d B A
  let δ := (K+1)*L*ε
  let C := DeficientGraph.boundarySchurConstant d B
  let e : Tm ↪ Fin N :=
    { toFun := fun t => t.val.val
      inj' := fun _ _ h => Subtype.ext (Subtype.ext h) }
  let φ : Tm ≃ T :=
    { toFun := fun t => ⟨t.val.val,(deletionNeighborhood_inner_mem g.graph o w.val w.val ell r t.val).mp t.property⟩
      invFun := fun t => ⟨⟨t.val,deletionNeighborhood_contains_root_ball g.graph o w.val w.val ell r t.property⟩,
        (deletionNeighborhood_inner_mem g.graph o w.val w.val ell r _).mpr t.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let U := (g.G z).submatrix e e
  let P := (M.extensionGreen q z).submatrix (Subtype.val : Tm → _) (Subtype.val : Tm → _)
  have hL : 1 ≤ L := S.localization.log_one
  have hε : 0 ≤ ε := S.localization.error_nonnegative
  have hA : 0 ≤ A := sourceLocalizationLogCap_nonnegative d hd β hβ
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DeficientGraph.localizationWeakConstant_ge_one d hd B A hA)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hC : 0 ≤ C := by
    have hB0 := (norm_nonneg z).trans hzB
    have hc := finiteExtraReferenceConstant_ge_one d hd
    have hDr : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk : 0 ≤ (d : ℝ)-1 := by linarith
    dsimp only [C,DeficientGraph.boundarySchurConstant]
    positivity
  have hnear : ‖q-semicircleRoot z‖ ≤ 1 := by
    have hh := weak_prior_scaled_norm z q hz ε L hε S.localization.error_scaled hprior
    have hhL : 1 ≤ L^2 := one_le_pow₀ hL
    exact (le_mul_of_one_le_right (norm_nonneg _) hhL).trans hh
  have hbudget := g.deletionNeighborhoodModel_component_budget o w.val w.val ell r R hmargin hballs
  have hdiam : ∀ x y, M.graph.dist x y ≤ 6*(ell+rn)+2 := by
    intro x y
    exact (deletionNeighborhood_distance_bound g.graph o w.val w.val ell r x y).trans
      (by dsimp only [r,effectiveModelRadius,rn]; omega)
  have hlocal (x y : deletionNeighborhoodVertices g.graph o w.val w.val ell r) :
      ‖M.extensionGreen q z x y-M.P r z q x y‖ ≤ K*L*ε :=
    S.localization.full_model_effective ha hd hβ hlog hroom M hbudget.to_componentFinite q hz hq hzB hprior hdiam x y
  have herror : ∀ i j : Tm, ‖(U-P) i j‖ ≤ δ := by
    intro i j
    have hxi : i.val.val ∈ T := (deletionNeighborhood_inner_mem g.graph o w.val w.val ell r i.val).mp i.property
    have hxj : j.val.val ∈ T := (deletionNeighborhood_inner_mem g.graph o w.val w.val ell r j.val).mp j.property
    have hid := g.deletionNeighborhoodModel_P_schur o w.val w.val ell r i.val j.val
      (Or.inl hxi) (Or.inl hxj) q z
    have hloc : ‖g.P r z q i.val.val j.val.val-M.extensionGreen q z i.val j.val‖ ≤ K*L*ε := by
      rw [←hid]
      exact (norm_sub_rev _ _).le.trans (hlocal i.val j.val)
    have ht := (norm_sub_le_norm_sub_add_norm_sub (g.G z i.val.val j.val.val)
      (g.P r z q i.val.val j.val.val) (M.extensionGreen q z i.val j.val)).trans
      (add_le_add (happrox _ _) hloc)
    have hh := le_mul_of_one_le_left hε hL
    change ‖g.G z i.val.val j.val.val-M.extensionGreen q z i.val j.val‖ ≤ _
    exact ht.trans (by dsimp only [δ]; nlinarith only [hh])
  let Rd := 2*rn+(finiteOmega d+2)*(2*rn+1)
  have hdelDiam : ∀ x y, (outsideGraph M.graph Tm).dist x y ≤ Rd := by
    intro x y
    exact (deletedNeighborhood_distance_bound g.graph o w.val w.val ell r R (finiteOmega d)
      hr w.property w.property hmargin (hballs o) x y).trans (by
        dsimp only [Rd]
        exact Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.sub_le rn _))
          (Nat.mul_le_mul_left _ (by dsimp only [r,effectiveModelRadius,rn]; omega)))
  have hrows := M.componentwise_ball_retained_inverse_bounds hd
    (g.deletionNeighborhoodModel_zero_deficit o w.val w.val ell r) hbudget root ell q z hz hq B hzB hnear
    Rd hdelDiam (S.deleted_small q hprior)
  have hPi : IsUnit P := M.extensionGreen_submatrix_isUnit hd
    (⟨Subtype.val,Subtype.val_injective⟩ : Tm ↪ deletionNeighborhoodVertices g.graph o w.val w.val ell r) q z hz hq
  have hUi : IsUnit U := by
    have hh := g.deficient.extensionGreen_submatrix_isUnit hd e (0 : ℂ) z hz (by norm_num)
    simpa only [DeficientGraph.extensionGreen,DeficientGraph.G,boundaryGreen,boundaryMatrix,
      zero_smul,sub_zero,green] using hh
  have hcard : Nat.card Tm = Nat.card T := Nat.card_congr φ
  have hsmall : (Fintype.card Tm : ℝ)*C*δ ≤ 1/2 := by
    have hh := S.cut_small g o
    change (Nat.card T : ℝ)*C*δ ≤ 1/2 at hh
    rw [←hcard] at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  have hphysical := inverse_row_column_stability U P hUi hPi C δ hC hδ hrows.1 hrows.2 herror hsmall
  let Rphysical := (g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
  have hm : U=Rphysical.submatrix φ φ := by ext i j; rfl
  have hi : U⁻¹=Rphysical⁻¹.submatrix φ φ := by rw [hm,Matrix.inv_submatrix_equiv]
  constructor
  · intro i
    have hh := hphysical.1 (φ.symm i)
    rw [hi] at hh
    simp only [Matrix.submatrix_apply,φ.apply_symm_apply] at hh
    rw [Equiv.sum_comp φ (fun j => ‖Rphysical⁻¹ i j‖)] at hh
    exact hh
  · intro j
    have hh := hphysical.2 (φ.symm j)
    rw [hi] at hh
    simp only [Matrix.submatrix_apply,φ.apply_symm_apply] at hh
    rw [Equiv.sum_comp φ (fun i => ‖Rphysical⁻¹ i j‖)] at hh
    exact hh

end SpectralConsequences
