import LocalLaw.SmallSampleKernelRestoration

/-! Actual restoration of an arbitrary inner set from far deleted-core rows. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance farInnerRestorationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

theorem extensionGreen_cross_of_cut_entries (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x:(Tᶜ:Set V))(b:T)(f C:ℝ)(hf:0≤f)
    (hcut:∀j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖≤f)
    (hcol:(∑j:T,‖g.extensionGreen q z j.val b.val‖)≤C):
    ‖g.extensionGreen q z x.val b.val‖≤f*C:=by
  let e:((Tᶜ:Set V)⊕T)≃V:=(Equiv.sumComm _ _).trans (Equiv.Set.sumCompl T)
  let M:Matrix ((Tᶜ:Set V)⊕T) ((Tᶜ:Set V)⊕T) ℂ:=(g.extensionMatrix q z).submatrix e e
  have hM:IsUnit M:=(Matrix.isUnit_submatrix_equiv e e).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hcore:M.toBlocks₁₁=(g.delete T).extensionMatrix q z:=by
    rw[g.extensionMatrix_delete]
    ext i j
    rfl
  have hcu:IsUnit M.toBlocks₁₁:=hcore ▸ (g.delete T).extensionMatrix_isUnit hd q z hz hq
  have hcross:M.toBlocks₁₂=g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V):=
    g.extensionMatrix_cross21 T q z
  have hi:M⁻¹=(g.extensionGreen q z).submatrix e e:=Matrix.inv_submatrix_equiv (g.extensionMatrix q z) e e
  have he:=congrArg (fun A:Matrix (Tᶜ:Set V) T ℂ=>A x b) (inverse_block12_from_core M hM hcu)
  rw[hi,hcore,hcross] at he
  change g.extensionGreen q z x.val b.val= -_ at he
  rw[he,norm_neg,Matrix.mul_apply]
  calc
    _≤∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
        (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖*‖g.extensionGreen q z j.val b.val‖:=by
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun j:T=>(((g.delete T).extensionGreen q z*g.H.submatrix
          (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j)*g.extensionGreen q z j.val b.val)
    _≤∑j:T,f*‖g.extensionGreen q z j.val b.val‖:=
      Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (hcut j) (norm_nonneg _))
    _=f*∑j:T,‖g.extensionGreen q z j.val b.val‖:=(Finset.mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left hcol hf

theorem extensionGreen_far_inner_restoration (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x y:(Tᶜ:Set V))(F C:ℝ)(hF:0≤F)
    (hleft:∀b:T,∀v:(Tᶜ:Set V),g.graph.Adj v.val b.val→‖(g.delete T).extensionGreen q z x v‖≤F)
    (hright:∀b:T,∀v:(Tᶜ:Set V),g.graph.Adj v.val b.val→‖(g.delete T).extensionGreen q z y v‖≤F)
    (hT:∀b:T,(∑c:T,‖g.extensionGreen q z c.val b.val‖)≤C):
    ‖g.extensionGreen q z x.val y.val-(g.delete T).extensionGreen q z x y‖≤
      (Nat.card T:ℝ)*(d:ℝ)^2*F^2*C:=by
  let U:=(g.delete T).extensionGreen q z*g.H.submatrix
    (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hsqrt:1≤Real.sqrt ((d:ℝ)-1):=by
    have hh:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
    nlinarith [Real.sqrt_nonneg ((d:ℝ)-1)]
  have hratio:(d:ℝ)/Real.sqrt ((d:ℝ)-1)≤d:=by
    apply (div_le_iff₀ (by linarith:0<Real.sqrt ((d:ℝ)-1))).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hcut (v:(Tᶜ:Set V))(hv:∀b:T,∀w:(Tᶜ:Set V),g.graph.Adj w.val b.val→
      ‖(g.delete T).extensionGreen q z v w‖≤F)(b:T):‖U v b‖≤F*(d:ℝ):=
    (g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) v b F hF
      (fun w hw=>hv b w hw)).trans (mul_le_mul_of_nonneg_left hratio hF)
  have hcross (b:T):‖g.extensionGreen q z b.val y.val‖≤(F*(d:ℝ))*C:=by
    rw[(g.extensionGreen_isSymm q z).apply]
    exact g.extensionGreen_cross_of_cut_entries hd T q z hz hq y b (F*(d:ℝ)) C
      (by positivity) (hcut y hright) (hT b)
  rw[g.extensionGreen_core_restore_identity hd T q z hz hq x y]
  have he:(g.delete T).extensionGreen q z x y-(∑b:T,U x b*g.extensionGreen q z b.val y.val)-
      (g.delete T).extensionGreen q z x y= -∑b:T,U x b*g.extensionGreen q z b.val y.val:=by ring
  rw[he,norm_neg]
  calc
    _≤∑b:T,‖U x b‖*‖g.extensionGreen q z b.val y.val‖:=by
      simpa only[norm_mul] using norm_sum_le Finset.univ (fun b:T=>U x b*g.extensionGreen q z b.val y.val)
    _≤∑_b:T,(F*(d:ℝ))*((F*(d:ℝ))*C):=Finset.sum_le_sum (fun b _=>
      mul_le_mul (hcut x hleft b) (hcross b) (norm_nonneg _) (by positivity))
    _=(Nat.card T:ℝ)*(d:ℝ)^2*F^2*C:=by simp only[Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card];ring

end DeficientGraph
end LocalLaw
