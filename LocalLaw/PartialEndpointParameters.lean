import LocalLaw.PartialSurgeryCoupling
import LocalLaw.EndpointSurgeryParameters

/-! # Actual partial-endpoint cardinality and source contraction budgets -/

open Filter
noncomputable section
namespace LocalLaw
local instance partialEndpointParametersDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

omit [Fintype ι] in
theorem partialEndpoint_card_le_roots (s:LabelledResamplingState V T ι)
    (selector:ℕ) (S:Set (Tᶜ:Set V)) :
    Nat.card (s.PartialEndpointIndex selector S)≤Nat.card (s.endpointModelRoots selector) := by
  have hmem (u:s.PartialEndpointIndex selector S) :
      (s.partialEndpointEmbedding selector S u).val∈s.endpointModelRoots selector := by
    rcases u with a | (b | c)
    · exact Or.inl ⟨s.boundary a.val.val,rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b.val,Or.inl rfl⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨c.val,Or.inr rfl⟩)
  let f:s.PartialEndpointIndex selector S→s.endpointModelRoots selector:=
    fun u=>⟨(s.partialEndpointEmbedding selector S u).val,hmem u⟩
  have hf:Function.Injective f:=by
    intro u v h
    apply (s.partialEndpointEmbedding selector S).injective
    exact Subtype.ext (congrArg (fun x:s.endpointModelRoots selector=>x.val) h)
  exact Nat.card_le_card_of_injective f hf

end LabelledResamplingState
namespace RegularGraph

theorem eventually_partial_endpoint_surgery_smallness (a b d:ℕ) (β C w D:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hβ:0<β) (hC:0≤C) (hw:0≤w) (hD:0≤D) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(ell:ℕ),ell≤doubleLogRadius a d N→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))(selector:ℕ)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      ∀S:Set ((graphBallVertices g.graph o ell)ᶜ:Set (Fin N)),
      let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
      (Fintype.card (s.PartialEndpointIndex selector S):ℝ)*(1+C*w)*w*
        (D*g.sourcePrime a (logarithmicRadius β d N) z)≤1/2 := by
  filter_upwards [eventually_endpoint_surgery_smallness a b d β C w D ha hb hd hβ hC hw hD,
    Filter.eventually_ge_atTop 1] with N hsmall hN
  intro g o ell hell ι _ labels samples selector z hz hfloor S
  let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
  have hc: (Fintype.card (s.PartialEndpointIndex selector S):ℝ)≤(Nat.card (s.endpointModelRoots selector):ℝ):=by
    simpa only [Nat.card_eq_fintype_card] using
      (Nat.cast_le (α:=ℝ).mpr (s.partialEndpoint_card_le_roots selector S))
  have hprime:0≤g.sourcePrime a (logarithmicRadius β d N) z:=by
    unfold sourcePrime inflatedPrime
    exact mul_nonneg (pow_nonneg (by linarith [Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)]) _)
      (graphPaperError_nonnegative a d N _ z hN hz.le)
  have hcoeff:0≤(1+C*w)*w*(D*g.sourcePrime a (logarithmicRadius β d N) z):=by positivity
  have hcount:=mul_le_mul_of_nonneg_right hc hcoeff
  have ht:=hsmall g o ell hell labels samples selector z hz hfloor
  nlinarith only [hcount,ht]

end RegularGraph
end LocalLaw
