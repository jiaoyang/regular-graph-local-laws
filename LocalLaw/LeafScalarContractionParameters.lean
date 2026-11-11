import LocalLaw.PartialEndpointParameters

/-! # Realized inverse contraction for selected scalar leaf blocks -/

open Filter
noncomputable section
namespace LocalLaw
local instance leafScalarContractionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

omit [Fintype ι] in
theorem admissibleSampleIndex_card_le_roots (s:LabelledResamplingState V T ι) (selector:ℕ) :
    Nat.card (s.AdmissibleSampleIndex selector)≤Nat.card (s.endpointModelRoots selector) := by
  let f:s.AdmissibleSampleIndex selector→s.endpointModelRoots selector:=fun i=>
    ⟨s.admissibleSampleVertex selector i,Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl rfl⟩)⟩
  have hf:Function.Injective f:=by
    intro i j hij
    exact s.admissibleSampleVertex_injective selector
      (congrArg (fun u:s.endpointModelRoots selector=>u.val) hij)
  exact Nat.card_le_card_of_injective f hf

end LabelledResamplingState
namespace RegularGraph

theorem eventually_selected_leaf_scalar_contraction (a b d:ℕ) (β P K:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hβ:0<β) (hP:0≤P) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(ell:ℕ),ell≤doubleLogRadius a d N→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))(selector:ℕ)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      ∀(n:ℕ),n≤Nat.card ((g.admissibleState (graphBallVertices g.graph o ell) labels samples).AdmissibleSampleIndex selector)→
      ∀(p:ℂ)(δ:ℝ),‖p⁻¹‖≤P→0≤δ→
      δ≤K*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z→
      (n:ℝ)*‖p⁻¹‖*δ≤1/2 := by
  let D:=|K|+1
  have hD:0≤D:=by dsimp only [D];positivity
  filter_upwards [eventually_endpoint_surgery_smallness a b d β 0 1 (P*D) ha hb hd hβ
    (by norm_num) (by norm_num) (mul_nonneg hP hD),eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hsmall hL hN
  intro g o ell hell ι _ labels samples selector z hz hfloor n hn p δ hp hδ hδcap
  let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εprime:=g.sourcePrime a (logarithmicRadius β d N) z
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0:0≤L:=by linarith
  have hKD:K≤D:=by dsimp only [D];linarith [le_abs_self K]
  have hLcube:L≤L^3:=by simpa only [pow_one] using pow_le_pow_right₀ hL (by omega:1≤3)
  have hδprime:δ≤D*εprime:=hδcap.trans (by
    calc
      K*L*ε≤D*L*ε:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKD hL0) hε
      _≤D*L^3*ε:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLcube hD) hε
      _=D*εprime:=by change D*L^3*ε=D*(L^3*ε);ring)
  have hprime:0≤εprime:=by
    change 0≤L^3*ε
    positivity
  have hc:(n:ℝ)≤(Nat.card (s.endpointModelRoots selector):ℝ):=
    Nat.cast_le.mpr (hn.trans (s.admissibleSampleIndex_card_le_roots selector))
  have ht:=hsmall g o ell hell labels samples selector z hz hfloor
  simp only [zero_mul,zero_add,add_zero,one_mul,mul_one] at ht
  calc
    _≤(n:ℝ)*P*δ:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hδ
    _≤(n:ℝ)*P*(D*εprime):=mul_le_mul_of_nonneg_left hδprime (mul_nonneg (Nat.cast_nonneg _) hP)
    _=(n:ℝ)*((P*D)*εprime):=by ring
    _≤(Nat.card (s.endpointModelRoots selector):ℝ)*((P*D)*εprime):=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _≤1/2:=ht

end RegularGraph
end LocalLaw
