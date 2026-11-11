import SpectralConsequences.EndpointGreenMeans
import SpectralConsequences.FiniteMeanAlgebra

/-! # The averaged quadratic two-sample leading term

All four unrestricted Green entries have the same exact pole contribution.
The resulting square is obtained by finite linearity, with the actual
outside-edge normalization error kept explicit.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace SpectralConsequences
open LocalLaw
namespace RegularGraph
variable {N d:ℕ}

theorem outside_quadratic_green_mean (g:LocalLaw.RegularGraph N d) (T:Set (Fin N))
    (hN:0<N) (hd:0<d) (hT:4*Nat.card T≤N) (z:ℂ) (hz:0<z.im)
    (C:ℝ) (hC:0≤C) (hG:∀i j,‖g.G z i j‖≤C) (a:ℂ) (ha:‖a‖≤1) :
    ‖finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
      finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>
        g.G z e.val.2 f.val.2+a*g.G z e.val.1 f.val.2+
          a*g.G z e.val.2 f.val.1+a^2*g.G z e.val.1 f.val.1))-
      (1+a)^2*((N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹)‖≤
      32*C*(Nat.card T:ℝ)/(N:ℝ) := by
  let Mcc:=finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
    finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>g.G z e.val.2 f.val.2))
  let Mbc:=finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
    finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>g.G z e.val.1 f.val.2))
  let Mcb:=finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
    finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>g.G z e.val.2 f.val.1))
  let Mbb:=finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
    finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>g.G z e.val.1 f.val.1))
  let pole:=(N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹
  let e:=8*C*(Nat.card T:ℝ)/(N:ℝ)
  have he:0≤e:=by dsimp only [e];positivity
  have hcc:‖Mcc-pole‖≤e:=outside_endpoint_green_mean g T hN hd hT z hz C hC hG false false
  have hbc:‖Mbc-pole‖≤e:=outside_endpoint_green_mean g T hN hd hT z hz C hC hG true false
  have hcb:‖Mcb-pole‖≤e:=outside_endpoint_green_mean g T hN hd hT z hz C hC hG false true
  have hbb:‖Mbb-pole‖≤e:=outside_endpoint_green_mean g T hN hd hT z hz C hC hG true true
  have hlin:finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
      finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>
        g.G z e.val.2 f.val.2+a*g.G z e.val.1 f.val.2+
          a*g.G z e.val.2 f.val.1+a^2*g.G z e.val.1 f.val.1)) =
      Mcc+a*Mbc+a*Mcb+a^2*Mbb:=by
    simp_rw [finiteComplexMean_add,finiteComplexMean_const_mul]
    rfl
  rw [hlin]
  change ‖Mcc+a*Mbc+a*Mcb+a^2*Mbb-(1+a)^2*pole‖≤_
  have hid:Mcc+a*Mbc+a*Mcb+a^2*Mbb-(1+a)^2*pole =
      (Mcc-pole)+a*(Mbc-pole)+a*(Mcb-pole)+a^2*(Mbb-pole):=by ring
  rw [hid]
  have hb:‖a*(Mbc-pole)‖≤e:=by
    rw [norm_mul]
    exact (mul_le_mul ha hbc (norm_nonneg _) (by norm_num)).trans_eq (one_mul e)
  have hc':‖a*(Mcb-pole)‖≤e:=by
    rw [norm_mul]
    exact (mul_le_mul ha hcb (norm_nonneg _) (by norm_num)).trans_eq (one_mul e)
  have hd':‖a^2*(Mbb-pole)‖≤e:=by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha 2) hbb
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hh:‖(Mcc-pole)+a*(Mbc-pole)+a*(Mcb-pole)+a^2*(Mbb-pole)‖≤4*e:=by
    have hsum:=(norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hcc hb)) hc')) hd')
    linarith
  apply hh.trans_eq
  dsimp only [e]
  ring

end RegularGraph
end SpectralConsequences
