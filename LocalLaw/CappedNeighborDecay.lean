import LocalLaw.CappedPairCapture
import LocalLaw.PhysicalTailRadiusLoss

/-! # Neighbor shifts of capped target distances

Unreachable vertices keep their capped distance; no default zero natural
distance is introduced across components.
-/

noncomputable section
namespace LocalLaw
variable {V:Type*}

theorem cappedGraphDistance_self (G:SimpleGraph V)(r:ℕ)(x:V) :
    cappedGraphDistance G r x x=0 := by
  rw[cappedGraphDistance,if_pos (SimpleGraph.Reachable.refl _),SimpleGraph.dist_self,Nat.min_zero]

theorem capped_delta_envelope {I J:Type} [DecidableEq I] [DecidableEq J]
    (E:I⊕J→V)(G:SimpleGraph V)(r:ℕ)(x:I⊕J)(u:I)(ρ:ℝ)(hρ:0≤ρ) :
    ‖(if x=Sum.inl u then (1:ℂ) else 0)‖≤ρ^(cappedGraphDistance G r (E x) (E (.inl u))) := by
  by_cases h:x=Sum.inl u
  · subst x
    simp [cappedGraphDistance_self]
  · simp only [if_neg h,norm_zero]
    exact pow_nonneg hρ _

theorem capped_neighbor_far (G:SimpleGraph V)(r:ℕ)(x u b:V)(hub:G.Adj u b)
    (hdi:2≤cappedGraphDistance G r x u) :
    (((cappedGraphDistance G r x u-2)+1:ℕ):ℕ∞)≤G.edist x b := by
  have htri:G.edist x u≤G.edist x b+1:=by
    calc
      _≤G.edist x b+G.edist b u:=G.edist_triangle
      _=G.edist x b+1:=by rw[SimpleGraph.edist_eq_one_iff_adj.mpr hub.symm]
  have hh:(((cappedGraphDistance G r x u-1:ℕ):ℕ∞)+1)≤G.edist x b+1:=by
    have he:(cappedGraphDistance G r x u-1)+1=cappedGraphDistance G r x u:=by omega
    have he' : (((cappedGraphDistance G r x u-1:ℕ):ℕ∞)+1)=(cappedGraphDistance G r x u:ℕ∞):=by exact_mod_cast he
    rw[he']
    exact (cappedGraphDistance_coe_le_edist G r x u).trans htri
  have hout:((cappedGraphDistance G r x u-1:ℕ):ℕ∞)≤G.edist x b:=
    (WithTop.add_le_add_iff_right (show (1:ℕ∞)≠⊤ by simp)).mp hh
  convert hout using 1
  congr 1
  omega

theorem positive_power_sub_two (ρ T:ℝ)(hρ:0<ρ)(hρone:ρ≤1)(hT:ρ⁻¹≤T)(n:ℕ) :
    ρ^(n-2)≤T^2*ρ^n := by
  have hT0:0≤T:=(inv_nonneg.mpr hρ.le).trans hT
  have hT1:1≤T:=(one_le_inv₀ hρ).mpr hρone |>.trans hT
  let k:=min n 2
  have hk:k≤n:=min_le_left _ _
  have hk2:k≤2:=min_le_right _ _
  have he:n-k=n-2:=by dsimp only [k];omega
  have hp:(ρ⁻¹)^k≤T^2:=(pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hT k).trans
    (pow_le_pow_right₀ hT1 hk2)
  rw[←he,pow_sub₀ ρ (ne_of_gt hρ) hk,←inv_pow]
  exact (mul_le_mul_of_nonneg_left hp (pow_nonneg hρ.le _)).trans_eq (mul_comm _ _)

theorem physical_power_sub_two (d:ℕ)(hd:3≤d)(z:ℂ)(B:ℝ)(hzB:‖z‖≤B)(n:ℕ) :
    physicalTransfer d z^(n-2)≤
      ((B+1)*‖(treeEdgeWeight d)⁻¹‖)^2*physicalTransfer d z^n := by
  have hρ1:physicalTransfer d z≤1:=by
    nlinarith [physicalTransfer_sq_le_half d hd z,(physicalTransfer_pos d hd z).le]
  exact positive_power_sub_two _ _ (physicalTransfer_pos d hd z) hρ1
    (physicalTransfer_inverse_bound d hd z B hzB) n

end LocalLaw
