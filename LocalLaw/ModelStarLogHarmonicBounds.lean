import LocalLaw.StarHarmonicBounds
import LocalLaw.StarCouplingRows
import LocalLaw.CappedNeighborDecay

/-! # Finite actual-model harmonic envelopes at capped ambient distances -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace LocalLaw
local instance modelStarBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) modelStarBoundsRangeDecidable {L W:Type} (a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V I J W:Type} [Fintype V] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq I] [DecidableEq J] {d:ℕ}

theorem actual_star_harmonic_log_bounds (g:DeficientGraph V d)(hd:3≤d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))
    (hng:∀v j,g.graph.Adj v.val (a j)→v∈Set.range e)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(Bcap:ℝ)(hzB:‖z‖≤Bcap)
    (η:V→W)(H:SimpleGraph W)(r:ℕ)(x:I⊕J)(B K D L ε:ℝ)
    (hB:0≤B)(hK:0≤K)(hD:0≤D)(hL:1≤L)(hε:0≤ε)(hn:Nat.card J≤2)
    (hrow:∑j:J,‖g.extensionGreen q z (embeddedStarEmbedding a e x) (a j)‖≤B*L)
    (hfar:∀i j, g.extensionMatrix q z (a j) (e i).val≠0→
      2≤cappedGraphDistance H r (η (embeddedStarEmbedding a e x)) (η (e i).val)→
      ‖g.extensionGreen q z (embeddedStarEmbedding a e x) (a j)‖≤
        K*L*physicalTransfer d z^(cappedGraphDistance H r (η (embeddedStarEmbedding a e x)) (η (e i).val)-2)+D*L*ε) :
    let R:=((g.delete (Set.range a)).extensionGreen q z).submatrix e e
    let E:=embeddedStarEmbedding a e
    let G:=(g.extensionGreen q z).submatrix E E
    let T:=(Bcap+1)*‖(treeEdgeWeight d)⁻¹‖
    (∑i:I,‖(G.submatrix id Sum.inl*R⁻¹) x i‖)≤(1+B*(d:ℝ))*L ∧
      ∀i:I,‖(G.submatrix id Sum.inl*R⁻¹) x i‖≤
        (1+2*(d:ℝ)*(B+K)*T^2)*L*
          physicalTransfer d z^(cappedGraphDistance H r (η (E x)) (η (e i).val))+
          2*(d:ℝ)*D*L*ε := by
  dsimp only
  let E:=embeddedStarEmbedding a e
  let G:=(g.extensionGreen q z).submatrix E E
  let R:=((g.delete (Set.range a)).extensionGreen q z).submatrix e e
  let A:=G.submatrix id Sum.inl*R⁻¹
  let U:=(g.extensionMatrix q z).submatrix a (fun i:I=>(e i).val)
  let ρ:=physicalTransfer d z
  let T:=(Bcap+1)*‖(treeEdgeWeight d)⁻¹‖
  have hρ:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hL0:0≤L:=by linarith
  have hd0:0≤(d:ℝ):=Nat.cast_nonneg _
  have hf:=g.actual_star_harmonic_entries hd a e hng q z hz hq
  have hcouple:=g.actual_star_coupling_rows hd a e q z
  have hcoeff (i:I):A x i=(if x=Sum.inl i then 1 else 0)-∑j:J,G x (.inr j)*U j i:=hf.1 x i
  have hGR:(∑j:J,‖G x (.inr j)‖)≤B*L:=hrow
  refine ⟨?_,?_⟩
  · have hh:=harmonic_row_l1 (G.submatrix id Sum.inr) U A x (B*L) d
      (mul_nonneg hB hL0) hd0 hcoeff hGR hcouple.1
    exact hh.trans (by nlinarith only[hL])
  intro i
  let n:=cappedGraphDistance H r (η (E x)) (η (e i).val)
  have hp:ρ^(n-2)≤T^2*ρ^n:=physical_power_sub_two d hd z Bcap hzB n
  have hG (j:J)(hj:U j i≠0):‖G x (.inr j)‖≤(B+K)*L*T^2*ρ^n+D*L*ε:=by
    by_cases hn2:2≤n
    · have hh:=hfar i j hj hn2
      change ‖G x (.inr j)‖≤K*L*ρ^(n-2)+D*L*ε at hh
      have hscaled:=mul_le_mul_of_nonneg_left hp (mul_nonneg hK hL0)
      have hBterm:0≤B*L*T^2*ρ^n:=by positivity
      exact hh.trans (by nlinarith only [hscaled,hBterm])
    · have hn0:n-2=0:=by omega
      rw[hn0,pow_zero] at hp
      have hpoint:‖G x (.inr j)‖≤B*L:=
        (Finset.single_le_sum (f:=fun k:J=>‖G x (.inr k)‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ j)).trans hGR
      have hscale:B*L≤B*L*(T^2*ρ^n):=by
        exact le_mul_of_one_le_right (mul_nonneg hB hL0) hp
      have hrest:0≤K*L*T^2*ρ^n+D*L*ε:=by positivity
      exact hpoint.trans (hscale.trans (by nlinarith only [hrest]))
  have hdelta:‖(if x=Sum.inl i then (1:ℂ) else 0)‖≤L*ρ^n:=by
    have hh:=capped_delta_envelope (fun v=>η (E v)) H r x i ρ hρ
    exact hh.trans (le_mul_of_one_le_left (pow_nonneg hρ _) hL)
  have hF:0≤(B+K)*L*T^2*ρ^n+D*L*ε:=by positivity
  have hb:=harmonic_entry_bound (G.submatrix id Sum.inr) U A x i (L*ρ^n) d
    ((B+K)*L*T^2*ρ^n+D*L*ε) (mul_nonneg hL0 (pow_nonneg hρ _)) hd0 hF
    (hcoeff i) hdelta (fun j=>g.actual_star_coupling_entry hd a e q z i j) hG
  have hnR:(Fintype.card J:ℝ)≤2:=by exact_mod_cast (show Fintype.card J≤2 by simpa only[Nat.card_eq_fintype_card] using hn)
  have hcount:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnR hF) hd0
  change ‖A x i‖≤(1+2*(d:ℝ)*(B+K)*T^2)*L*ρ^n+2*(d:ℝ)*D*L*ε
  apply hb.trans
  calc
    _≤L*ρ^n+2*((B+K)*L*T^2*ρ^n+D*L*ε)*(d:ℝ):=add_le_add_left hcount _
    _=_:=by ring

end DeficientGraph
end LocalLaw
