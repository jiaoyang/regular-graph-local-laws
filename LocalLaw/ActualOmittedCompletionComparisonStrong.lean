import LocalLaw.ActualOmittedCompletionComparison
import LocalLaw.TwoScaleSchurTarget

/-! # Asymmetric completion with count-free ordinary error

Only the spatial tail pays the leaf count. Uniform errors use the proved
kept-leaf L1 rows on both sides of the exact Schur complement.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
namespace LocalLaw
local instance actualOmittedCompletionStrongDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem actual_omitted_completion_comparison_strong (g:RegularGraph N d)(hd:3≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ)(B C1 A L ε KM KA:ℝ)
    (hz:0<z.im)(hq:0≤q.im)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hA:0≤A)(hL:0≤L)(hε:0≤ε)(hKM:0≤KM)(hKA:0≤KA)
    (hrows:g.LocalCommonIncidenceRows T labels samples selector S q z KM KA)
    (hleaf:g.OmittedKeptLeafDecayControlled hd T labels samples selector S q z B C1 A L ε)
    (hnorm:g.OmittedKeptControlled hd T labels samples selector S q z B C1 ε) :
    let s:=g.admissibleState T labels samples
    let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    ∀u v:s.OmittedCore selector S,∀ri rj:ℕ,
      (∀l:J,(ri:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist u
        (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))) →
      (∀l:J,(rj:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist v
        (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))) →
      let ai:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^ri
      let aj:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^rj
      ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v-
        (g.omittedCommonModel T labels samples selector S).extensionGreen q z u v‖≤
      omittedNormalizationConstant d B C1*ε+(Fintype.card J:ℝ)*(B+2+(KM+KA))*ai*aj+
        (B+2+(KM+KA))*(omittedRestoredErrorConstant d B C1 A*L*ε)*(2*omittedKeptRowConstant d B) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  letI:DecidableEq J:=fun a b=>Classical.propDecidable (a=b)
  let C:=g.omittedCommonModel T labels samples selector S
  let mate:=s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S
  let H:=g.omittedKeptCompletion (by omega:1≤d) T labels samples selector S
  have hC:0≤finiteExtraReferenceConstant d:=by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hconv:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hsp:0≤omittedRestoredSpatialConstant d B A:=by unfold omittedRestoredSpatialConstant;positivity
  have her:0≤omittedRestoredErrorConstant d B C1 A:=by
    unfold omittedRestoredErrorConstant omittedNormalizationConstant omittedNormalizationCoefficient omittedKeptRowConstant
    positivity
  have hm:=g.localCommonRows_kept_mates T labels samples selector S q z KM KA hrows
  intro u v ri rj hri hrj
  let ai:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^ri
  let aj:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^rj
  let δ:=omittedRestoredErrorConstant d B C1 A*L*ε
  have hδ:0≤δ:=by dsimp only [δ];positivity
  have hρ:0≤physicalTransfer d z:=(physicalTransfer_pos d hd z).le
  have hai:0≤ai:=by dsimp only [ai];positivity
  have haj:0≤aj:=by dsimp only [aj];positivity
  have hx (l:J):‖H.extensionGreen q z (.inl u) (.inr l)‖≤ai+δ:=hleaf u l ri (hri l)
  have hy (l:J):‖H.extensionGreen q z (.inr l) (.inl v)‖≤aj+δ:=by
    have hs:=congrArg norm ((H.extensionGreen_isSymm q z).apply (.inl v) (.inr l))
    exact hs.trans_le (hleaf v l rj (hrj l))
  have hcmp:=C.attachLeaves_two_scale_target_change hd mate
    (g.omittedKeptMate_restore_budget T labels samples selector S) q z hz hq B (KM+KA) ai aj δ
    (omittedKeptRowConstant d B) (omittedKeptRowConstant d B) hzB hqnorm
    (add_nonneg hKM hKA) hai haj hδ (fun l=>hm (mate l)) u v hx hy
    (hnorm.1 (.inl u)) (hnorm.2.1 (.inl v))
  have hn:=hnorm.2.2 u v
  have ht:=norm_sub_le_norm_sub_add_norm_sub
    ((g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v)
    (H.extensionGreen q z (.inl u) (.inl v)) (C.extensionGreen q z u v)
  have hn' : ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v-
      H.extensionGreen q z (.inl u) (.inl v)‖≤omittedNormalizationConstant d B C1*ε := by
    rw [norm_sub_rev]
    exact hn
  convert ht.trans (add_le_add hn' hcmp) using 1
  ring

end RegularGraph
end LocalLaw
