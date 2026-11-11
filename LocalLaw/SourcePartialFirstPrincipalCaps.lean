import LocalLaw.SourcePartialFirstOffDiagonal
import LocalLaw.PrincipalNearDiagonalRows
import LocalLaw.LeafMultiplicityContraction

/-! # Every actual omitted subset of selected B has a bounded inverse block

The full B inverse and its small off-diagonals give true scalar pivots.
Actual principal-block nonsingularity follows from the deficient model.
All subset contraction conditions follow from the source leaf count.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance sourcePartialFirstPrincipalDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_first_principal_caps (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
      let U:=H.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)
      ∀E:Set (s.partialFirstMask selector S),
      let P:=U.submatrix (Subtype.val:E→s.partialFirstMask selector S) (Subtype.val:E→s.partialFirstMask selector S)
      IsUnit P ∧ (∀i,∑j,‖P⁻¹ i j‖≤4*sourcePartialFirstInverseCap d B) ∧
        (∀j,∑i,‖P⁻¹ i j‖≤4*sourcePartialFirstInverseCap d B) := by
  let C:=sourcePartialFirstInverseCap d B
  let K:=sourcePartialFirstOffDiagonalConstant d β B C1
  have hC:0≤C:=by
    dsimp only [C,sourcePartialFirstInverseCap]
    have hce:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hK:0≤K:=by
    dsimp only [K,sourcePartialFirstOffDiagonalConstant]
    have hce:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_partial_first_inverse_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_selected_leaf_multiplicity_contraction a b d 1 β 1 (2*C*K) ha hb hd hβ (by norm_num),
    eventually_ge_atTop 1,eventually_log_ge_nat 1,hdepth]
    with N hinv hoff hcontract hN hlog hdepthN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=K*L*ε
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL:0≤L:=by dsimp only [L];linarith
  have hδ:0≤δ:=by dsimp only [δ];positivity
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hi:=hinv g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have ho:=hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y
  intro S hS E
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let e:=s.partialFirstEmbedding selector S
  let BM:=s.partialFirstMask selector S
  let U:=(M.extensionGreen q z).submatrix e e
  let P:=U.submatrix (Subtype.val:E→BM) (Subtype.val:E→BM)
  let eE:E↪S:=
    {toFun:=fun i=>e i.val
     inj':=by intro i j h;exact Subtype.ext (e.injective h)}
  have hP:IsUnit P:=M.extensionGreen_submatrix_isUnit hd eE q z hz hq
  have hUi:IsUnit U:=(hi S hS).1
  have hUc:∀i:BM,∑j:BM,‖U⁻¹ j i‖≤C:=(hi S hS).2.2
  have hUoff:∀i j:BM,i≠j→‖U i j‖≤δ:=ho S hS
  have hUs:U.IsSymm:=(M.extensionGreen_isSymm q z).submatrix e
  have hn:Fintype.card BM≤1*Nat.card (s.AdmissibleSampleIndex selector):=by
    simpa only [one_mul,Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_injective (Subtype.val:BM→s.AdmissibleSampleIndex selector) Subtype.val_injective
  have hδcap:2*C*δ≤(2*C*K)*L*ε:=by
    dsimp only [δ]
    exact le_of_eq (by ring)
  have hnsmall:=hcontract g o ell hell labels samples selector z hz hfloor (Fintype.card BM) hn
    (1:ℂ) (2*C*δ) (by norm_num) (by positivity) hδcap
  norm_num only [inv_one,norm_one,mul_one] at hnsmall
  have hEcard:(Fintype.card E:ℝ)≤(Fintype.card BM:ℝ):=by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val:E→BM) Subtype.val_injective
  have hEsmall:(Fintype.card E:ℝ)*(2*C)*δ≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_right hEcard (show 0≤2*C*δ by positivity)
    nlinarith only [hh,hnsmall]
  cases isEmpty_or_nonempty BM with
  | inl hEmpty=>
      letI:=hEmpty
      refine ⟨hP,fun i=>?_,fun i=>?_⟩ <;> exact (isEmptyElim i.val)
  | inr hNonempty=>
      letI:=hNonempty
      have hnOne:1≤(Fintype.card BM:ℝ):=by exact_mod_cast Fintype.card_pos_iff.mpr hNonempty
      have hsmall:δ*C≤1/2:=by
        have hh:=mul_le_mul_of_nonneg_right hnOne (show 0≤2*C*δ by positivity)
        have hnδ:0≤C*δ:=mul_nonneg hC hδ
        nlinarith only [hh,hnsmall,hnδ]
      have hh:=principal_near_diagonal_inverse_rows_cols U hUi hUs E hP C δ hC hδ hUc hUoff hsmall hEsmall
      exact ⟨hP,hh⟩

end RegularGraph
end LocalLaw
