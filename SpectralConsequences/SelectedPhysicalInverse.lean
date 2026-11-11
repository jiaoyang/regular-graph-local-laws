import SpectralConsequences.SelectedTipCrossCaps
import LocalLaw.SourcePartialFirstInverseCaps
import LocalLaw.DeletionStability
import LocalLaw.EndpointSurgeryParameters
import LocalLaw.FullOutsideReplacement
import LocalLaw.SelectedFirstGreen

/-! # True inverse rows on every switched sampled-first vertex

The actual endpoint model has a proved inverse bound. Endpoint approximation
transfers it to the physical principal Green block without a target event or
a switched-graph reference-class assumption.
-/

open Filter
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance selectedPhysicalInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def switchedSelectedGreen {N d : ℕ} {ι : Type} [Fintype ι]
    (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (z : ℂ) :=
  (((g.labelledResampledGraph T labels samples selector).deficient.delete T).G z).submatrix
    ((g.admissibleState T labels samples).selectedFirstEmbedding selector)
    ((g.admissibleState T labels samples).selectedFirstEmbedding selector)

theorem eventually_switched_selected_inverse_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ)^b/(N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀ v, graphBallExcess g.graph v (logarithmicRadius (c/4) d N) ≤ finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let U := switchedSelectedGreen g T labels samples selector z
      IsUnit U ∧ (∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ 2*sourcePartialFirstInverseCap d B) ∧
        (∀ j, ∑ i, ‖U⁻¹ i j‖ ≤ 2*sourcePartialFirstInverseCap d B) := by
  let C := sourcePartialFirstInverseCap d B
  let D := sourceEndpointErrorConstant d C1
  have hC : 0 ≤ C := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C,sourcePartialFirstInverseCap]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D,sourceEndpointErrorConstant]
    positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [RegularGraph.eventually_actual_source_endpoint_stability a b d c β B C1
      ha hb hd hc hβ hβc hC1,
    RegularGraph.eventually_source_partial_first_inverse_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    RegularGraph.eventually_endpoint_surgery_smallness a b d β 0 1 (C*D)
      ha hb hd hβ (by norm_num) (by norm_num) (mul_nonneg hC hD),
    RegularGraph.eventually_actual_inner_complement_nonempty a d (by omega) hd,
    eventually_ge_atTop 1,hdepth]
    with N hendpoint hmodel hcontract hnonempty hN hdepthN
  intro g o z hz hfloor hzB Cq badCount hplus hstrong ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let I := s.AdmissibleSampleIndex selector
  let K := s.endpointModelVertices selector r
  let BM := s.partialFirstMask selector K
  let M := g.switchedEndpointModel T labels samples selector r
  let U := switchedSelectedGreen g T labels samples selector z
  let V : Matrix I I ℂ := (M.extensionGreen (g.Q z) z).submatrix
    (s.endpointBaseVertex selector r) (s.endpointBaseVertex selector r)
  let Vmask := (M.extensionGreen (g.Q z) z).submatrix
    (s.partialFirstEmbedding selector K) (s.partialFirstEmbedding selector K)
  let φ : I ≃ BM :=
    { toFun := fun i => ⟨i,(s.endpointBaseVertex selector r i).property⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : (Tᶜ : Set (Fin N)) := Classical.choice (hnonempty g o z)
  have hm := hmodel g o z (g.Q z) hz hzB hfloor (g.Q_im_nonnegative z hz)
    hplus.cavity hstrong labels samples w w K (s.endpointModelVertices_subset_twoTargetEndpointVertices selector r w w)
  change IsUnit Vmask ∧ (∀ i, ∑ j, ‖Vmask⁻¹ i j‖ ≤ C) ∧ (∀ j, ∑ i, ‖Vmask⁻¹ i j‖ ≤ C) at hm
  have hV : V = Vmask.submatrix φ φ := by ext i j; rfl
  have hVi : IsUnit V := hV ▸ (Matrix.isUnit_submatrix_equiv φ φ).mpr hm.1
  have hVinv : V⁻¹ = Vmask⁻¹.submatrix φ φ := by rw [hV,Matrix.inv_submatrix_equiv]
  have hVr : ∀ i, ∑ j, ‖V⁻¹ i j‖ ≤ C := by
    intro i
    rw [hVinv]
    simp only [Matrix.submatrix_apply]
    rw [Equiv.sum_comp φ (fun j => ‖Vmask⁻¹ (φ i) j‖)]
    exact hm.2.1 (φ i)
  have hVc : ∀ j, ∑ i, ‖V⁻¹ i j‖ ≤ C := by
    intro j
    rw [hVinv]
    simp only [Matrix.submatrix_apply]
    rw [Equiv.sum_comp φ (fun i => ‖Vmask⁻¹ i (φ j)‖)]
    exact hm.2.2 (φ j)
  let new := (g.labelledResampledGraph T labels samples selector).deficient.delete T
  have hUi : IsUnit U := by
    have hh := new.extensionGreen_submatrix_isUnit hd (s.selectedFirstEmbedding selector)
      (0 : ℂ) z hz (by norm_num)
    simpa only [DeficientGraph.extensionGreen, boundaryGreen, boundaryMatrix, zero_smul,
      sub_zero, DeficientGraph.G, green] using hh
  let δ := D*g.sourcePrime a (logarithmicRadius β d N) z
  have hδ : 0 ≤ δ := by
    have he := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    dsimp only [δ,RegularGraph.sourcePrime,inflatedPrime]
    positivity
  have herror : ∀ i j, ‖(U-V) i j‖ ≤ δ := by
    intro i j
    exact hendpoint g o z hz hfloor hzB Cq badCount hplus labels samples
      (g.sourceEndpointBaseIndex T labels samples selector i)
      (g.sourceEndpointBaseIndex T labels samples selector j)
  have hn : (Fintype.card I : ℝ) ≤ (Nat.card (s.endpointModelRoots selector) : ℝ) := by
    have hh := Nat.card_le_card_of_injective
      (g.sourceEndpointBaseIndex T labels samples selector)
      (fun i j he => s.admissibleSampleVertex_injective selector (congrArg Subtype.val he))
    simp only [Nat.card_eq_fintype_card] at hh
    simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α := ℝ).mpr hh)
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hc := hcontract g o ell hell labels samples selector z hz hfloor
  simp only [zero_mul,zero_add,one_mul,mul_one] at hc
  have hsmall : (Fintype.card I : ℝ)*C*δ ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hC hδ)
    calc
      _ ≤ (Nat.card (s.endpointModelRoots selector) : ℝ)*C*δ := by nlinarith only [hh]
      _ ≤ 1/2 := by convert hc using 1; dsimp only [δ]; ring
  exact ⟨hUi,inverse_row_column_stability U V hUi hVi C δ hC hδ hVr hVc herror hsmall⟩

end SpectralConsequences
