import SpectralConsequences.SourceSelectedMinorComparison
import SpectralConsequences.SampledDoubleMinor

/-! # Literal source selected singleton/double-minor replacement

The two labels may coincide; the removed set then is a singleton. The
right-hand Green value is the original full-graph minor, with no T deletion.
-/
open Filter
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance sourceSampledMinorDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem vertexPairSet_card_le_two {I:Type} [Finite I] (i j:I) : Nat.card (vertexPairSet i j)≤2 := by
  let f:Fin 2→vertexPairSet i j:=fun k=>if k=0 then ⟨i,Or.inl rfl⟩ else ⟨j,Or.inr rfl⟩
  have hs:Function.Surjective f:=by
    rintro ⟨v,hv⟩
    rcases hv with rfl|rfl
    · exact ⟨0,by simp [f]⟩
    · exact ⟨1,by simp [f]⟩
  simpa only[Nat.card_eq_fintype_card,Fintype.card_fin] using Nat.card_le_card_of_surjective f hs

namespace RegularGraph

theorem oldOwnSampleMinorEntry_eq_sampledDoubleMinor {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]
    (g:LocalLaw.RegularGraph N d) (labels:ι≃BoundaryOrientedEdge g.graph T)
    (samples:LocalSamplingFiber g.graph T) (selector:ℕ) (z:ℂ)
    (i j:(g.admissibleState T labels samples).AdmissibleSampleIndex selector) :
    let s:=g.admissibleState T labels samples
    oldOwnSampleMinorEntry g.H T (s.selectedFirstEmbedding selector) (s.admissibleSecondVertex selector)
      (selected_first_ne_second s selector) (vertexPairSet i j) z i j =
        sampledDoubleMinor g labels samples selector z i j := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let b:=s.selectedFirstEmbedding selector
  let O:=(retainedBallSampleEmbedding T b) '' sampleOwnRetainedSet T (vertexPairSet i j)
  let S:=LabelledResamplingState.sampledPairRemoved s selector i j
  have hOS:O=S:=by
    ext v
    rw [sample_own_ambient_mem_iff]
    constructor
    · rintro ⟨k,hk,hkv⟩
      rcases hk with rfl|rfl
      · exact Or.inl hkv.symm
      · exact Or.inr hkv.symm
    · intro hv
      rcases hv with hv|hv
      · exact ⟨i,Or.inl rfl,hv.symm⟩
      · exact ⟨j,Or.inr rfl,hv.symm⟩
  let x:=sampleTipRetainedComplement T b (s.admissibleSecondVertex selector) (selected_first_ne_second s selector) i
  let y:=sampleTipRetainedComplement T b (s.admissibleSecondVertex selector) (selected_first_ne_second s selector) j
  have hx:x.val∉O:=by rintro ⟨u,_,hu⟩;exact x.property ⟨u,hu⟩
  have hy:y.val∉O:=by rintro ⟨u,_,hu⟩;exact y.property ⟨u,hu⟩
  exact green_principal_entry_set_congr g.H z Oᶜ Sᶜ (congrArg Set.compl hOS) x.val y.val hx hy
    (hOS ▸ hx) (hOS ▸ hy)

theorem eventually_source_sampled_minor_comparison (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hC1:1≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      ∀i j:s.AdmissibleSampleIndex selector,
      ‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j)-
        sampledDoubleMinor g labels samples selector z i j‖≤
        sourceSelectedMinorConstant d B C1*
          ((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ)*
          (g.sourcePrime a (logarithmicRadius β d N) z)^2 := by
  filter_upwards [eventually_source_selected_minor_comparison a b d c β B C1 ha hb hd hc hβ hβc hB hC1]
    with N hcomp
  intro g o z hz hfloor hzB Cq badCount hold hplus ι _ labels samples
  dsimp only
  intro i j
  have hh:=hcomp g o z hz hfloor hzB Cq badCount hold hplus labels samples (vertexPairSet i j)
    (vertexPairSet_card_le_two i j) i j (Or.inl rfl) (Or.inr rfl)
  rw [oldOwnSampleMinorEntry_eq_sampledDoubleMinor g labels samples _ z i j] at hh
  exact hh

end RegularGraph
end SpectralConsequences
