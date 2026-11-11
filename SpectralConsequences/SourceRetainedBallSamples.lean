import SpectralConsequences.RetainedBallSampleInverse
import SpectralConsequences.SourceOldBallInverseRows
import SpectralConsequences.BoundaryFarAmbient
import LocalLaw.SelectedFirstParameters

/-! # Actual old retained precision on T and all accepted sampled first vertices

The two event assumptions concern the original graph. Every physical inverse
bound is derived from the retained-ball and sampled-block Schur formulas.
-/
open Filter
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceRetainedBallSamplesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

 def oldRetainedBallSampleGreen {N d : ℕ} {ι : Type} [Fintype ι]
    (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (z : ℂ) :=
  (g.G z).submatrix
    (retainedBallSampleEmbedding T ((g.admissibleState T labels samples).selectedFirstEmbedding selector))
    (retainedBallSampleEmbedding T ((g.admissibleState T labels samples).selectedFirstEmbedding selector))

def oldRetainedBallSampleInverseCap (d : ℕ) (B : ℝ) : ℝ :=
  2*DeficientGraph.boundarySchurConstant d B+4*sourceGreenPivotCap d B

theorem eventually_source_retained_ball_sample_inverse_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hB : 0 ≤ B) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ)^b/(N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let U := oldRetainedBallSampleGreen g T labels samples selector z
      IsUnit U ∧ (∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ oldRetainedBallSampleInverseCap d B) ∧
        (∀ j, ∑ i, ‖U⁻¹ i j‖ ≤ oldRetainedBallSampleInverseCap d B) := by
  let P := 2*DeficientGraph.boundarySchurConstant d B
  let C := 2*sourceGreenPivotCap d B
  let V : ℝ := (d:ℝ)*((d:ℝ)+1)
  have hP : 0 ≤ P := by
    have hc := finiteExtraReferenceConstant_ge_one d hd
    have hc2 := finiteReferenceConstant_ge_one d hd
    have hdR : (3:ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk : 0 ≤ (d:ℝ)-1 := by linarith
    dsimp only [P,DeficientGraph.boundarySchurConstant]
    positivity
  have hC : 0 ≤ C := by
    have hc := finiteReferenceConstant_ge_one d hd
    dsimp only [C,sourceGreenPivotCap]
    positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_old_ball_inverse_rows a b d c β B ha hb hd hc hβ hβc hB,
    LocalLaw.RegularGraph.eventually_selectedFirstGreen_inverse_rows a b d c β B C1 ha hb hd hc hβ hβc hC1 hB,
    RegularGraph.eventually_source_selected_inner_cross a d c β hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1,eventually_log_ge_nat (2*(V*P)),hdepth,eventually_ge_atTop 1]
    with N hball hsample hcross hsmall hL hlarge hdepthN hN
  intro g o z hz hfloor hzB Cq badCount hold hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let s := g.admissibleState T labels samples
  let I := s.AdmissibleSampleIndex selector
  let e := s.selectedFirstEmbedding selector
  let f := retainedBallSampleEmbedding T e
  let U := oldRetainedBallSampleGreen g T labels samples selector z
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hpow := doubleLogRadius_base_power_bound a d N hd hL
  have hballcount : (Fintype.card T:ℝ) ≤ V*L^(2*a) := by
    have hn := g.ball_card_sharp o ell hd
    have hh : (Nat.card T:ℝ) ≤ ((d:ℝ)+1)*((d-1:ℕ):ℝ)^ell := by exact_mod_cast hn
    have hpower : ((d-1:ℕ):ℝ)^ell ≤ L^(2*a) :=
      (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d-1 by omega)) hell).trans hpow
    have hbase : ((d:ℝ)+1)*L^(2*a) ≤ V*L^(2*a) := by
      have hdR : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      dsimp only [V]
      exact mul_le_mul_of_nonneg_right (by nlinarith : (d:ℝ)+1 ≤ (d:ℝ)*((d:ℝ)+1)) (by positivity)
    have hh' : (Fintype.card T:ℝ) ≤ ((d:ℝ)+1)*((d-1:ℕ):ℝ)^ell := by
      simpa only [Nat.card_eq_fintype_card] using hh
    exact hh'.trans ((mul_le_mul_of_nonneg_left hpower (by positivity)).trans hbase)
  have hsampcount : (Fintype.card I:ℝ) ≤ V*L^(2*a) := by
    have hn : Fintype.card I ≤ Nat.card (BoundaryOrientedEdge g.graph T) :=
      (Fintype.card_subtype_le _).trans_eq (by simpa only [Nat.card_eq_fintype_card] using Fintype.card_congr labels)
    exact (Nat.cast_le.mpr hn).trans (g.boundary_card_log_bound o a ell hd hL hell)
  have hcap : ε*L^(4*a) ≤ 1 := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hscalar : V*P*ε*L^(2*a) ≤ 1/2 := source_scaled_log_monomial_half a (2*a) L ε (V*P)
    hL hε (mul_nonneg hV hP) hcap (by omega) hlarge
  have hsmallT : (Fintype.card T:ℝ)*P*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hballcount (mul_nonneg hP hε)
    nlinarith only [hh,hscalar]
  have hsmallI : (Fintype.card I:ℝ)*P*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hsampcount (mul_nonneg hP hε)
    nlinarith only [hh,hscalar]
  have hTrows := (hball g o z hz hfloor hzB badCount hold).1
  have hBrows := hsample g o z hz hzB hfloor Cq badCount hplus labels samples
  have hH : g.H.submatrix (Subtype.val : (Tᶜ:Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ:Set (Fin N)) → Fin N) = normalizedAdjacency (outsideGraph g.graph T) d :=
    (normalizedAdjacency_induce g.graph d Tᶜ).symm
  have hBrows' : ∀ i, ∑ j, ‖((green (g.H.submatrix (Subtype.val : (Tᶜ:Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ:Set (Fin N)) → Fin N)) z).submatrix e e)⁻¹ i j‖ ≤ C := by
    rw [hH]
    exact hBrows
  have hcross' := hcross g o z hz badCount hold labels samples
  have hrows := retained_ball_sample_inverse_rows g.H (normalizedAdjacency_isHermitian _ _) T e z hz P C ε
    hP hC hε hTrows hBrows'
    (fun i t => (hcross' i (s.admissibleSampleVertex selector i) (Or.inl rfl) t).1)
    (fun t i => (hcross' i (s.admissibleSampleVertex selector i) (Or.inl rfl) t).2) hsmallT hsmallI
  have hsym : U.IsSymm := by
    have hh := g.deficient.extensionGreen_isSymm (0 : ℂ) z
    have hg : (g.G z).IsSymm := by
      simpa only [DeficientGraph.extensionGreen,DeficientGraph.G,boundaryGreen,boundaryMatrix,
        zero_smul,sub_zero,green] using hh
    exact hg.submatrix f
  have hinvsym : (U⁻¹).IsSymm := by
    show (U⁻¹).transpose=U⁻¹
    rw [Matrix.transpose_nonsing_inv,hsym.eq]
  have hcapid : P+2*C=oldRetainedBallSampleInverseCap d B := by
    dsimp only [P,C,oldRetainedBallSampleInverseCap]
    ring
  have hr : ∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ oldRetainedBallSampleInverseCap d B := by
    intro i
    rw [←hcapid]
    exact hrows i
  refine ⟨embedded_green_submatrix_isUnit g.H (normalizedAdjacency_isHermitian _ _) z hz f,?_,?_⟩
  · exact hr
  · intro j
    calc
      _ = ∑ i, ‖U⁻¹ j i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hinvsym.apply]
      _ ≤ _ := hr j

end SpectralConsequences
