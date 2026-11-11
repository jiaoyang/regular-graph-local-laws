import LocalLaw.ActualPartialBInverseCaps
import LocalLaw.PartialEndpointParameters

/-! # Realized inverse rows for the actual retained sampled-first block -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance partialFirstInverseParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_partial_first_inverse_of_covariance (a b d : ℕ) (β PInv Kcov : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hβ : 0<β) (hPInv : 0≤PInv) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(ell : ℕ),ell≤doubleLogRadius a d N→
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))(selector : ℕ)(z q p : ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→q≠0→p≠0→
      p⁻¹=q⁻¹-q*treeEdgeWeight d^2→‖q‖≤2→‖p‖≤4→‖treeEdgeWeight d*q‖≤1→
      ‖q⁻¹‖≤PInv→‖p⁻¹‖≤PInv→∀S:Set ((graphBallVertices g.graph o ell)ᶜ:Set (Fin N)),
      let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
      let e:=s.partialEndpointEmbedding selector S
      let G:=((g.deficient.delete (graphBallVertices g.graph o ell)).restrict S).extensionGreen q z
      let H:=(((g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples selector).deficient.delete
        (graphBallVertices g.graph o ell)).restrict S).extensionGreen q z
      let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
      let AM:=s.partialBoundaryMask selector S
      let BM:=s.partialFirstMask selector S
      let Missing:=A⁻¹-partialMissingCharge AM BM q (treeEdgeWeight d)
      (∀i,∑j,‖(A⁻¹-Matrix.diagonal (fun _:AM=>q*treeEdgeWeight d^2))⁻¹ i j‖≤4*finiteExtraReferenceConstant d)→
      IsUnit Missing→(∀i,∑j,‖Missing⁻¹ i j‖≤4*finiteExtraReferenceConstant d)→
      (∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤
        Kcov*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z)→
      let U:=H.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)
      IsUnit U ∧ (∀i,∑j,‖U⁻¹ i j‖≤2*(PInv+4*finiteExtraReferenceConstant d)) ∧
        (∀j,∑i,‖U⁻¹ i j‖≤2*(PInv+4*finiteExtraReferenceConstant d)) := by
  let K:=4*finiteExtraReferenceConstant d
  let C:=4+2*K
  let M:=1+C*4
  let D:=|Kcov|+1
  let Jcap:=PInv+K
  have hK : 0≤K := by dsimp only [K]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hC : 0≤C := by dsimp only [C]; positivity
  have hM : 0≤M := by dsimp only [M]; positivity
  have hD : 0≤D := by dsimp only [D]; positivity
  have hJ : 0≤Jcap := add_nonneg hPInv hK
  filter_upwards [eventually_partial_endpoint_surgery_smallness a b d β C 4 D ha hb hd hβ hC (by norm_num) hD,
    eventually_partial_endpoint_surgery_smallness a b d β 0 1 (Jcap*2*M^2*D) ha hb hd hβ
      (by norm_num) (by norm_num) (by positivity),eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hcontract hmass hL hN
  intro g o ell hell ι _ labels samples selector z q p hz hfloor hq hq0 hp0 hrel hqnorm hpnorm ham hqinv hpinv S
  dsimp only
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  let Missing:=A⁻¹-partialMissingCharge AM BM q (treeEdgeWeight d)
  let n:ℝ:=Fintype.card (s.PartialEndpointIndex selector S)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εprime:=g.sourcePrime a (logarithmicRadius β d N) z
  let δ:=D*εprime
  let w:=2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2
  let J:=PInv+‖treeEdgeWeight d‖^2*K
  let σ:=2*(1+C*w)^2*δ
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0 : 0≤L := by linarith
  have hprime : εprime=L^3*ε := rfl
  have hprime0 : 0≤εprime := by rw [hprime]; positivity
  have hδ : 0≤δ := mul_nonneg hD hprime0
  have hn : 0≤n := Nat.cast_nonneg _
  have hαsq : ‖treeEdgeWeight d‖^2≤1 := by
    rw [treeEdgeWeight_norm_sq d hd]
    have hDreal : (3:ℝ)≤d := Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hα : ‖treeEdgeWeight d‖≤1 := by nlinarith [norm_nonneg (treeEdgeWeight d)]
  have hw0 : 0≤w := by dsimp only [w]; positivity
  have hw : w≤4 := by
    have hh:=mul_le_mul hqnorm hαsq (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)
    dsimp only [w]
    nlinarith
  have hMw : 1+C*w≤M := by
    have hh:=mul_le_mul_of_nonneg_left hw hC
    dsimp only [M]
    linarith
  have hMw0 : 0≤1+C*w := by positivity
  have hsmall : n*(1+C*w)*w*δ≤1/2 := by
    have hh:=hcontract g o ell hell labels samples selector z hz hfloor S
    have hprod:=mul_le_mul hMw hw hw0 hM
    calc
      _=(n*δ)*((1+C*w)*w) := by ring
      _≤(n*δ)*(M*4) := mul_le_mul_of_nonneg_left hprod (mul_nonneg hn hδ)
      _=n*(1+C*4)*4*(D*εprime) := by dsimp only [δ,M]; ring
      _≤1/2 := hh
  have hJ0 : 0≤J := by dsimp only [J]; positivity
  have hJcap : J≤Jcap := by
    dsimp only [J,Jcap]
    exact add_le_add_left (mul_le_of_le_one_left hK hαsq) _
  have hσ : σ≤2*M^2*δ := by
    dsimp only [σ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMw0 hMw 2) (by norm_num)) hδ
  have hσ0 : 0≤σ := by dsimp only [σ]; positivity
  have hcard : (Fintype.card BM:ℝ)≤n := by
    have hc:=Nat.card_le_card_of_injective
      (fun b:BM=>(Sum.inr (Sum.inl b):s.PartialEndpointIndex selector S))
      (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h))
    simpa only [Nat.card_eq_fintype_card,n] using (Nat.cast_le (α:=ℝ).mpr hc)
  have hBsmall : (Fintype.card BM:ℝ)*J*σ≤1/2 := by
    have hh:=hmass g o ell hell labels samples selector z hz hfloor S
    simp only [zero_mul,zero_add,add_zero,one_mul,mul_one] at hh
    calc
      _≤n*Jcap*(2*M^2*δ) := mul_le_mul
        (mul_le_mul hcard hJcap hJ0 hn) hσ hσ0 (mul_nonneg hn hJ)
      _=n*((Jcap*2*M^2*D)*εprime) := by dsimp only [δ]; ring
      _≤1/2 := hh
  intro hrestored hmissing hmissingRows herr
  have hKD : Kcov≤D := by dsimp only [D]; linarith [le_abs_self Kcov]
  have hLcube : L≤L^3 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by omega:1≤3)
  have hcovcap : Kcov*L*ε≤δ := by
    calc
      _≤D*L*ε := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKD hL0) hε
      _≤D*L^3*ε := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLcube hD) hε
      _=δ := by dsimp only [δ]; rw [hprime]; ring
  have hout:=g.partial_model_first_inverse_caps hd T labels samples selector S q p z hz hq hq0 hp0 hrel
    4 PInv K δ (by norm_num) hPInv hK hδ (hqnorm.trans (by norm_num)) hpnorm ham hqinv hpinv
    hrestored hmissing hmissingRows (fun i j=>(herr i j).trans hcovcap) hsmall hBsmall
  refine ⟨hout.1,fun i=>?_,fun j=>?_⟩
  · exact (hout.2.1 i).trans (mul_le_mul_of_nonneg_left hJcap (by norm_num))
  · exact (hout.2.2 j).trans (mul_le_mul_of_nonneg_left hJcap (by norm_num))

end RegularGraph
end LocalLaw
