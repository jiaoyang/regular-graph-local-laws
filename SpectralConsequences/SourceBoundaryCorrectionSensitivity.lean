import SpectralConsequences.BoundaryCorrectionContinuity
import SpectralConsequences.SourceTruncatedParameterBounds
import SpectralConsequences.SourceCavityConditionalDrift
import LocalLaw.SourceFormalEdgeBounds
import SpectralConsequences.TrivialPoleCancellation

/-! The actual q-dependent averaged corrections differ from the physical
Section7 corrections by a fixed logarithmic factor times Psi times the pole. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceBoundaryCorrectionSensitivityDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def boundaryCorrectionSensitivityConstant (d:ℕ) (β:ℝ):ℝ:=
  ((d:ℝ)*((d:ℝ)+1))^2*
    (8*(2*finiteExtraReferenceConstant d)*truncatedParameterContinuityConstant d β+
      4*(2*finiteExtraReferenceConstant d)^2)

namespace RegularGraph
variable {N d:ℕ}

theorem traceBoundaryCorrectionCoefficient_physical (g:LocalLaw.RegularGraph N d)(hd:3≤d)
    (o:Fin N)(ell:ℕ)(hell:1≤ell)(hTree:(graphBall g.graph o ell).IsTree)(z:ℂ)(hz:0<z.im):
    traceBoundaryCorrectionCoefficient g o ell (semicircleRoot z) z=
      traceCorrectionCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z):=by
  have h:=full_boundary_offdiag_correction g hd o ell hell hTree z hz
  have hα:(treeEdgeWeight d)^2=1/((d-1:ℕ):ℂ):=by
    rw [treeEdgeWeight_sq d hd,Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  have hs:(∑e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑f:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if e=f then 0 else fullBoundaryWeight g o ell (semicircleRoot z) z e*
          fullBoundaryWeight g o ell (semicircleRoot z) z f/((d-1:ℕ):ℂ))=
      (∑e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑f:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if e=f then 0 else fullBoundaryWeight g o ell (semicircleRoot z) z e*
          fullBoundaryWeight g o ell (semicircleRoot z) z f)/((d-1:ℕ):ℂ):=by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;>simp
  rw [←h,hs]
  dsimp only [traceBoundaryCorrectionCoefficient]
  rw [hα]
  ring

theorem cavityBoundaryCorrectionCoefficient_physical (g:LocalLaw.RegularGraph N d)(hd:3≤d)
    (o:Fin N)(ell:ℕ)(hell:2≤ell)(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree)(z:ℂ)(hz:0<z.im):
    finiteBoundaryCorrection ((treeEdgeWeight d)^2) (treeEdgeWeight d) (semicircleRoot z)
      (cavityBoundaryWeight g o ell hell j hjo (semicircleRoot z) z)=cavityCorrectionCoefficient d ell (semicircleRoot z):=by
  let m:=semicircleRoot z
  let α:=treeEdgeWeight d
  let k:ℂ:=((d-1:ℕ):ℂ)
  have hk:k≠0:=Nat.cast_ne_zero.mpr (by omega)
  have hK:k^ell≠0:=pow_ne_zero ell hk
  have hα:α^2=1/k:=by dsimp only [α,k];rw [treeEdgeWeight_sq d hd,Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  dsimp only [finiteBoundaryCorrection]
  rw [cavity_boundary_all_label_weights g hd o ell hell j hjo hTree _ z hz (semicircleRoot_im_pos hz).le,
    radialCavityColumn_fixed _ _ _ (semicircleRoot_equation z)]
  change α^2*(1+α*m)^2*(k^(ell+1)*(k^(ell+1)-1)*(m*(-m*α)^ell)^2)=_
  have hp:(-m*α)^(2*ell)=m^(2*ell)/k^ell:=by
    calc
      _=((-m*α)^2)^ell:=by rw [←pow_mul]
      _=(m^2*α^2)^ell:=by rw [mul_pow,neg_sq]
      _=m^(2*ell)/k^ell:=by rw [hα,mul_pow,div_pow,one_pow,←pow_mul];ring
  rw [mul_pow,←pow_mul,show ell*2=2*ell by omega,hp,hα]
  unfold cavityCorrectionCoefficient
  change 1/k*(1+α*m)^2*(k^(ell+1)*(k^(ell+1)-1)*(m^2*(m^(2*ell)/k^ell)))=
    (k^(ell+1)-1)*m^(2*ell+2)*(1+m*α)^2
  rw [pow_succ,pow_add]
  field_simp [hk,hK]
  ring

theorem eventually_source_boundary_correction_sensitivity (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let bound:=boundaryCorrectionSensitivityConstant d β*Real.log (N:ℝ)^(4*a+1)*
        scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)*‖trivialPole N d z‖
      ‖traceBoundaryCorrectionCoefficient g o ell (g.Q z) z*trivialPole N d z-
        trivialTraceCorrection N d ell z‖≤bound ∧
      ∃hell:2≤ell,∀(j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o),
        ‖cavityMeanCorrection g o ell hell j hjo (g.Q z) z-trivialCavityCorrection N d ell z‖≤bound:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_truncated_parameter_bounds a b d c β B ha hb hd hc hβ hβc,
    eventually_source_formal_edge_bounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,hdepth] with N hparam hformal hmargin hlog hdepth
  intro g o z hz hfloor hzB badCount hold hTree
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let F:=BoundaryOrientedEdge g.graph T
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Ψ:=scalarScale (spectralScale z) ε
  let C:=2*finiteExtraReferenceConstant d
  let H:=truncatedParameterContinuityConstant d β
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let n:ℝ:=Fintype.card F
  have hC:0≤C:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C];positivity
  have hH:0≤H:=by
    have hh:=sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [H,truncatedParameterContinuityConstant];positivity
  have hU:0≤U:=by dsimp only [U];positivity
  have hell:2≤ell:=by
    have hh:(2:ℝ)≤(ell:ℝ):=by
      have hp:=(actualCavityDepth_radius_bounds a d N z hdepth).1
      dsimp only [ell];linarith
    exact_mod_cast hh
  have hellB:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have htree:(graphBall g.graph o ell).IsTree:=graphBall_tree_mono g.graph o (by dsimp only [ell];omega) hTree
  have htree1:(graphBall g.graph o (ell+1)).IsTree:=graphBall_tree_mono g.graph o (by dsimp only [ell];omega) hTree
  have hprior:‖g.Q z-semicircleRoot z‖≤Ψ:=hold.2.1
  have hp:=hparam g o z (g.Q z) hz hfloor (g.Q_im_nonnegative z hz) hprior htree
  have hq:‖treeEdgeWeight d*g.Q z‖≤1:=
    (hformal z (g.Q z) hz hzB hfloor (by simpa only [one_mul] using hprior)).2
  have hα:‖treeEdgeWeight d‖≤1:=(treeEdgeWeight_norm_le_three_quarters d hd).trans (by norm_num)
  have hm:‖treeEdgeWeight d*semicircleRoot z‖≤1:=by
    rw [norm_mul]
    exact (mul_le_mul hα (semicircleRoot_norm_lt_one hz).le (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hc':‖(treeEdgeWeight d)^2‖≤1:=by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hα
  have hn:n≤U*L^(2*a):=by
    simpa only [n,F,Nat.card_eq_fintype_card] using g.boundary_card_log_bound o a ell hd hlog hellB
  have hbound (w v:F→ℂ) (hw:∀i,‖w i‖≤C) (hv:∀i,‖v i‖≤C)
      (hchange:∀i,‖w i-v i‖≤H*L*‖g.Q z-semicircleRoot z‖):
      ‖(finiteBoundaryCorrection ((treeEdgeWeight d)^2) (treeEdgeWeight d) (g.Q z) w-
        finiteBoundaryCorrection ((treeEdgeWeight d)^2) (treeEdgeWeight d) (semicircleRoot z) v)*trivialPole N d z‖≤
        boundaryCorrectionSensitivityConstant d β*L^(4*a+1)*Ψ*‖trivialPole N d z‖:=by
    rw [norm_mul]
    have hh:=finiteBoundaryCorrection_continuity ((treeEdgeWeight d)^2) (treeEdgeWeight d) (g.Q z)
      (semicircleRoot z) w v C (H*L) hC (mul_nonneg hH (by linarith)) hα hq hm hw hv hchange
    have hnum:n^2*(8*C*(H*L)+4*C^2)≤boundaryCorrectionSensitivityConstant d β*L^(4*a+1):=by
      have hn2:n^2≤(U*L^(2*a))^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2
      have hcoef:8*C*(H*L)+4*C^2≤(8*C*H+4*C^2)*L:=by
        nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg C)]
      have hh:=mul_le_mul hn2 hcoef (by positivity) (by positivity)
      apply hh.trans_eq
      dsimp only [boundaryCorrectionSensitivityConstant,U,C,H]
      rw [mul_pow,←pow_mul,show 2*a*2=4*a by omega,pow_succ]
      ring
    have hmul:‖(treeEdgeWeight d)^2‖*n^2*(8*C*(H*L)+4*C^2)*‖g.Q z-semicircleRoot z‖≤
        boundaryCorrectionSensitivityConstant d β*L^(4*a+1)*Ψ:=by
      have hfirst:‖(treeEdgeWeight d)^2‖*(n^2*(8*C*(H*L)+4*C^2))≤
          boundaryCorrectionSensitivityConstant d β*L^(4*a+1):=
        (mul_le_of_le_one_left (by positivity) hc').trans hnum
      have hsecond:=mul_le_mul hfirst hprior (norm_nonneg _)
        ((by positivity:0≤‖(treeEdgeWeight d)^2‖*(n^2*(8*C*(H*L)+4*C^2))).trans hfirst)
      convert hsecond using 1;ring
    exact mul_le_mul_of_nonneg_right (hh.trans hmul) (norm_nonneg _)
  constructor
  · let w:F→ℂ:=fullBoundaryWeight g o ell (g.Q z) z
    let v:F→ℂ:=fullBoundaryWeight g o ell (semicircleRoot z) z
    have hh:=hbound w v (fun i=>(hp.1 _ _).1) (fun i=>(hp.1 _ _).2.1) (fun i=>(hp.1 _ _).2.2)
    have he:finiteBoundaryCorrection ((treeEdgeWeight d)^2) (treeEdgeWeight d) (g.Q z) w=
        traceBoundaryCorrectionCoefficient g o ell (g.Q z) z:=rfl
    have he':finiteBoundaryCorrection ((treeEdgeWeight d)^2) (treeEdgeWeight d) (semicircleRoot z) v=
        traceCorrectionCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z):=
      traceBoundaryCorrectionCoefficient_physical g hd o ell (by omega) htree z hz
    rw [he,he'] at hh
    simpa only [trivialTraceCorrection,sub_mul] using hh
  · refine ⟨hell,?_⟩
    intro j hjo
    let w:F→ℂ:=cavityBoundaryWeight g o ell hell j hjo (g.Q z) z
    let v:F→ℂ:=cavityBoundaryWeight g o ell hell j hjo (semicircleRoot z) z
    have hh:=hbound w v (fun i=>(hp.2 j _ _).1) (fun i=>(hp.2 j _ _).2.1) (fun i=>(hp.2 j _ _).2.2)
    rw [cavityBoundaryCorrectionCoefficient_physical g hd o ell hell j hjo htree1 z hz] at hh
    convert hh using 1
    congr 1
    dsimp only [cavityMeanCorrection,finiteBoundaryCorrection,trivialCavityCorrection,w,trivialPole]
    ring

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_boundary_correction_sensitivity
