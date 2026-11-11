import SpectralConsequences.OldSampleFormalValues
import SpectralConsequences.SampledDoubleMinor
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.SourceSurgeryParameters

/-! # Actual original two-sample expansion with quadratic weak-event error

All primitive entries of the finite two-pivot expansion are now supplied by
the original graph event and actual eligible samples. No switched event,
conditional mean, or desired residual estimate is a hypothesis.
-/
open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance actualTwoSampleDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def twoSampleEntryCap (d:ℕ) : ℝ := sourceGreenEntryCap d+4
def twoSamplePivotCap (B:ℝ) : ℝ := 2*(B+2)
def twoSampleErrorCap (d:ℕ) (β B:ℝ) : ℝ := |oldSampleFormalConstant d β B|+1
def twoSampleQuadraticConstant (d:ℕ) (β B:ℝ) : ℝ :=
  let C:=twoSampleEntryCap d
  let P:=twoSamplePivotCap B
  (2*P+(4*C+1)*P^2+16*C^2*P^3)*(twoSampleErrorCap d β B)^2

namespace RegularGraph

theorem eventually_actual_two_sample_expansion (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B) :
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let A:=treeEdgeWeight d*g.Q z
      ∀(i j:s.AdmissibleSampleIndex selector),i≠j →
      ‖sampledDoubleMinor g labels samples selector z i j-
        (g.G z (s.admissibleSecondVertex selector i).val (s.admissibleSecondVertex selector j).val+
          A*g.G z (s.admissibleSampleVertex selector i).val (s.admissibleSecondVertex selector j).val+
          A*g.G z (s.admissibleSecondVertex selector i).val (s.admissibleSampleVertex selector j).val+
          A^2*g.G z (s.admissibleSampleVertex selector i).val (s.admissibleSampleVertex selector j).val)‖≤
        twoSampleQuadraticConstant d β B*(Real.log (N:ℝ))^2*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2 := by
  let C:=twoSampleEntryCap d
  let P:=twoSamplePivotCap B
  let K:=twoSampleErrorCap d β B
  have hC:4≤C:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [C,twoSampleEntryCap,sourceGreenEntryCap]
    linarith
  have hP:1≤P:=by dsimp only [P,twoSamplePivotCap];linarith
  have hK:1≤K:=by dsimp only [K,twoSampleErrorCap];linarith [abs_nonneg (oldSampleFormalConstant d β B)]
  let Acap:=sourceObservationLogCap d β
  have hAcap:0≤Acap:=sourceObservationLogCap_nonnegative d hd β hβ.le
  filter_upwards [eventually_old_sample_formal_values a b d c β B ha hb hd hc hβ hβc,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_sourceObservationBounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_formal_kernel_bounds a b d c β B 1 Acap ha hb hd hc hβ hβc (by norm_num) hAcap,
    eventually_source_formal_kernel_inverse_bound a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_formal_edge_bounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_log_ge_nat (4*P*K)]
    with N hvalues hcaps hnum hformal hinv hedge hlarge
  intro g o z hz hzB hfloor badCount hsource ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  let A:=treeEdgeWeight d*q
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=K*L*ε
  have hv:=hvalues g o z hz hzB hfloor badCount hsource labels samples
  have hg:=hcaps g z badCount hz hzB hfloor hsource
  have num:=hnum z hz hfloor
  have hprior:‖q-semicircleRoot z‖≤1*scalarScale (spectralScale z) ε:=by simpa only [one_mul] using hsource.2.1
  have hf:=hformal z q hz hzB hfloor hprior
  have hi:=hinv z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  have hL0:0≤L:=(by norm_num : (0:ℝ)≤1).trans num.log_one
  have hε0:0≤ε:=num.error_nonnegative
  have hK0:0≤K:=by linarith
  have hδ:0≤δ:=mul_nonneg (mul_nonneg hK0 hL0) hε0
  have hε:ε≤δ:=by
    have hh:ε≤L*ε:=le_mul_of_one_le_left num.error_nonnegative num.log_one
    have hh' : L*ε≤K*(L*ε):=le_mul_of_one_le_left (mul_nonneg hL0 hε0) hK
    exact hh.trans (by simpa only [δ,mul_assoc] using hh')
  have hvalue:oldSampleFormalConstant d β B*L*ε≤δ:=by
    apply mul_le_mul_of_nonneg_right _ num.error_nonnegative
    exact mul_le_mul_of_nonneg_right (by
      dsimp only [K,twoSampleErrorCap]
      linarith [le_abs_self (oldSampleFormalConstant d β B)]) (by linarith [num.log_one])
  have hsmall:2*P*δ≤1/2:=by
    have hcap:ε*L^4≤1:=by simpa only [one_pow,one_mul] using num.error_scaled
    have hh:=source_scaled_log_monomial_half 1 1 L ε (2*P*K) num.log_one num.error_nonnegative
      (by positivity) hcap (by norm_num) (by dsimp only [L] at *;nlinarith only [hlarge])
    convert hh using 1
    dsimp only [δ]
    ring
  have hδone:δ≤1:=by nlinarith
  have hpnorm:‖p‖≤C:=hf.2.2.1.trans hC
  have hα:‖treeEdgeWeight d‖^2≤1/2:=by
    rw [treeEdgeWeight_norm_sq d hd]
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hqα:‖q*(treeEdgeWeight d)^2‖≤1:=by
    rw [norm_mul,norm_pow]
    have hh:=mul_le_mul he.1 hα (sq_nonneg _) (by norm_num : (0:ℝ)≤2)
    norm_num at hh
    exact hh
  have hpiv:‖p⁻¹‖≤P:=by
    rw [hf.2.2.2.1]
    exact (norm_sub_le _ _).trans (by dsimp only [P,twoSamplePivotCap];linarith [hi.2,hqα])
  have hG:∀x y,‖g.G z x y‖≤C:=fun x y=>(hg.1 x y).trans (by dsimp only [C,twoSampleEntryCap];linarith)
  have hsym:(g.G z).IsSymm:=by
    have hh:=g.deficient.extensionGreen_isSymm (0:ℂ) z
    simpa only [LocalLaw.RegularGraph.G,LocalLaw.RegularGraph.H,DeficientGraph.extensionGreen,
      DeficientGraph.H,boundaryGreen,boundaryMatrix,zero_smul,sub_zero,green] using hh
  intro i j hij
  let S:=LabelledResamplingState.sampledPairRemoved s selector i j
  let φ:=LabelledResamplingState.sampledPairEquiv s selector i j hij
  let x:=LabelledResamplingState.sampledSecondInPairComplement s selector i j i
  let y:=LabelledResamplingState.sampledSecondInPairComplement s selector i j j
  have hφ0:(φ 0).val=(s.admissibleSampleVertex selector i).val:=vertexPairEquiv_zero _ _ _
  have hφ1:(φ 1).val=(s.admissibleSampleVertex selector j).val:=vertexPairEquiv_one _ _ _
  have hOwn (k:s.AdmissibleSampleIndex selector):
      ‖g.G z (s.admissibleSampleVertex selector k).val (s.admissibleSecondVertex selector k).val+A*p‖≤δ:=by
    have hh:=(hv.2.1 k).trans hvalue
    change ‖g.G z (s.admissibleSampleVertex selector k).val (s.admissibleSecondVertex selector k).val-
      p*(-q*treeEdgeWeight d)‖≤δ at hh
    have heq:p*(-q*treeEdgeWeight d)=-(A*p):=by dsimp only [A];ring
    simpa only [heq,sub_neg_eq_add] using hh
  have hDiag (k:s.AdmissibleSampleIndex selector):
      ‖g.G z (s.admissibleSampleVertex selector k).val (s.admissibleSampleVertex selector k).val-p‖≤δ:=
    (hv.1 k _ (Or.inl rfl)).trans hvalue
  have hCross (k l:s.AdmissibleSampleIndex selector) (hkl:k≠l)
      (u v:(Tᶜ:Set (Fin N))) (hu:u∈s.admissiblePairRoots selector k) (hv':v∈s.admissiblePairRoots selector l):
      ‖g.G z u.val v.val‖≤δ:=(hv.2.2 k l hkl u v hu hv').trans hε
  have hdiagφ (k:Fin 2):‖g.G z (φ k).val (φ k).val-p‖≤δ:=by
    fin_cases k
    · change ‖g.G z (φ 0).val (φ 0).val-p‖≤δ
      rw [hφ0]
      exact hDiag i
    · change ‖g.G z (φ 1).val (φ 1).val-p‖≤δ
      rw [hφ1]
      exact hDiag j
  have hoffφ (k l:Fin 2) (hkl:k≠l):‖g.G z (φ k).val (φ l).val‖≤δ:=by
    fin_cases k <;>fin_cases l
    · exact False.elim (hkl rfl)
    · change ‖g.G z (φ 0).val (φ 1).val‖≤δ
      rw [hφ0,hφ1]
      exact hCross i j hij _ _ (Or.inl rfl) (Or.inl rfl)
    · change ‖g.G z (φ 1).val (φ 0).val‖≤δ
      rw [hφ1,hφ0]
      exact hCross j i (Ne.symm hij) _ _ (Or.inl rfl) (Or.inl rfl)
    · exact False.elim (hkl rfl)
  have hh:=physical_two_pivot_quadratic_expansion g.H (normalizedAdjacency_isHermitian g.graph d)
    S φ z hz x y p A hf.2.1 C P δ (by linarith) hP hδ hδone hpnorm hpiv he.2
    (fun k=>hG _ _) (fun k=>hG _ _)
    (by change ‖g.G z _ _+A*p‖≤δ;rw [hφ0,hsym.apply];exact hOwn i)
    (by change ‖g.G z _ _+A*p‖≤δ;rw [hφ1];exact hOwn j)
    (by change ‖g.G z _ _‖≤δ;rw [hφ1];exact hCross i j hij _ _ (Or.inr rfl) (Or.inl rfl))
    (by change ‖g.G z _ _‖≤δ;rw [hφ0];exact hCross i j hij _ _ (Or.inl rfl) (Or.inr rfl))
    hdiagφ hoffφ hsmall
  change ‖sampledDoubleMinor g labels samples selector z i j - _‖ ≤ _ at hh
  apply hh.trans_eq
  dsimp only [twoSampleQuadraticConstant,C,P,K,δ]
  ring

end RegularGraph
end SpectralConsequences
