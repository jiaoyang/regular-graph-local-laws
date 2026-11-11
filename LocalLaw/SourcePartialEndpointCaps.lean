import LocalLaw.ActualPartialEndpointCaps
import LocalLaw.PartialEndpointParameters
import LocalLaw.PartialSamplePhysical

/-! # Realized contraction and constant rows for actual partial endpoints

The error O(log(N)*epsilon) is used only for contraction. Counting the
included accepted endpoints and the source error smallness removes both
finite numerical smallness hypotheses from the actual row theorem.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourcePartialEndpointCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourcePartialEndpointRowCap (d:ℕ):ℝ:=5+8*finiteExtraReferenceConstant d

namespace RegularGraph

theorem eventually_partial_endpoint_rows_of_covariance (a b d:ℕ) (β Kcov:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hβ:0<β) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(ell:ℕ),ell≤doubleLogRadius a d N→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))(selector:ℕ)(z q p:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→q≠0→p≠0→
      p⁻¹=q⁻¹-q*treeEdgeWeight d^2→‖q‖≤2→‖p‖≤4→‖treeEdgeWeight d*q‖≤1→
      ∀S:Set ((graphBallVertices g.graph o ell)ᶜ:Set (Fin N)),
      let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
      let e:=s.partialEndpointEmbedding selector S
      let G:=((g.deficient.delete (graphBallVertices g.graph o ell)).restrict S).extensionGreen q z
      let H:=(((g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples selector).deficient.delete
        (graphBallVertices g.graph o ell)).restrict S).extensionGreen q z
      let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
      (∀i,∑j,‖(A⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2))⁻¹ i j‖≤
        4*finiteExtraReferenceConstant d)→
      (∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤
        Kcov*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀i,∑j,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d)∧
        (∀j,∑i,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d) := by
  let C:=4+2*(4*finiteExtraReferenceConstant d)
  let M:=1+C*4
  let D:=|Kcov|+1
  have hC:0≤C:=by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C]
    positivity
  have hM:0≤M:=by dsimp only [M];positivity
  have hD:0≤D:=by dsimp only [D];positivity
  have hDm:0≤2*M^2*D:=by positivity
  filter_upwards [eventually_partial_endpoint_surgery_smallness a b d β C 4 D ha hb hd hβ hC (by norm_num) hD,
    eventually_partial_endpoint_surgery_smallness a b d β 0 1 (2*M^2*D) ha hb hd hβ (by norm_num) (by norm_num) hDm,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hcontract hmass hL hN
  intro g o ell hell ι _ labels samples selector z q p hz hfloor hq hq0 hp0 hrel hqnorm hpnorm ham S
  dsimp only
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let n:ℝ:=Fintype.card (s.PartialEndpointIndex selector S)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εprime:=g.sourcePrime a (logarithmicRadius β d N) z
  let δ:=D*εprime
  let w:=2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0:0≤L:=by linarith
  have hprime:εprime=L^3*ε:=rfl
  have hprime0:0≤εprime:=by rw [hprime];positivity
  have hδ:0≤δ:=mul_nonneg hD hprime0
  have hn:0≤n:=Nat.cast_nonneg _
  have hαsq:‖treeEdgeWeight d‖^2≤1:=by
    rw [treeEdgeWeight_norm_sq d hd]
    have hDreal:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hα:‖treeEdgeWeight d‖≤1:=by nlinarith [norm_nonneg (treeEdgeWeight d)]
  have hw0:0≤w:=by dsimp only [w];positivity
  have hw:w≤4:=by
    have hh:=mul_le_mul hqnorm hαsq (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)
    dsimp only [w]
    nlinarith
  have hMw:1+C*w≤M:=by
    have hh:=mul_le_mul_of_nonneg_left hw hC
    dsimp only [M]
    linarith
  have hMw0:0≤1+C*w:=by positivity
  have hcount:=hcontract g o ell hell labels samples selector z hz hfloor S
  have hsmall:n*(1+C*w)*w*δ≤1/2:=by
    have hprod:=mul_le_mul hMw hw hw0 hM
    change n*(1+C*4)*4*(D*εprime)≤1/2 at hcount
    calc
      _=(n*δ)*((1+C*w)*w):=by ring
      _≤(n*δ)*(M*4):=mul_le_mul_of_nonneg_left hprod (mul_nonneg hn hδ)
      _=n*(1+C*4)*4*(D*εprime):=by dsimp only [δ,M];ring
      _≤1/2:=hcount
  have hmass0:=hmass g o ell hell labels samples selector z hz hfloor S
  simp only [zero_mul,zero_add,add_zero,one_mul,mul_one] at hmass0
  have hmassBound:n*(2*(1+C*w)^2*δ)≤1:=by
    have hpow:=pow_le_pow_left₀ hMw0 hMw 2
    change n*((2*M^2*D)*εprime)≤1/2 at hmass0
    calc
      _=(2*n*δ)*(1+C*w)^2:=by ring
      _≤(2*n*δ)*M^2:=mul_le_mul_of_nonneg_left hpow (by positivity)
      _=n*((2*M^2*D)*εprime):=by dsimp only [δ];ring
      _≤1/2:=hmass0
      _≤1:=by norm_num
  intro hrestored herr
  have hKD:Kcov≤D:=by dsimp only [D];linarith [le_abs_self Kcov]
  have hLcube:L≤L^3:=by simpa only [pow_one] using pow_le_pow_right₀ hL (by omega:1≤3)
  have hσ:Kcov*L*ε≤δ:=by
    calc
      _≤D*L*ε:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKD hL0) hε
      _≤D*L^3*ε:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLcube hD) hε
      _=δ:=by dsimp only [δ];rw [hprime];ring
  have herrδ:∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ:=
    fun i j=>(herr i j).trans hσ
  have hK0:0≤4*finiteExtraReferenceConstant d:=by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hq4:‖q‖≤4:=hqnorm.trans (by norm_num)
  have hout:=g.partial_model_vacuum_row_caps hd T labels samples selector S q p z hz hq hq0 hp0 hrel
    4 (4*finiteExtraReferenceConstant d) δ (by norm_num) hK0 hδ hq4 hpnorm ham
    hrestored herrδ hsmall hmassBound
  have hfinal:4+2*(4*finiteExtraReferenceConstant d)+1=sourcePartialEndpointRowCap d:=by
    unfold sourcePartialEndpointRowCap
    ring
  simpa only [hfinal] using hout

end RegularGraph
end LocalLaw
