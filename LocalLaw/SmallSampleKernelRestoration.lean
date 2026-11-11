import LocalLaw.SmallSampleCutRows
import LocalLaw.DeletedSampleCrossRows

/-! # Entire kernels after restoring at most two sampled vertices

A half-distance split suffices here: every sampled vertex is far from at
least one target. This retains a spatial tail and a logarithmic residual,
without imposing a reference-class hypothesis on the restored graph.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance smallSampleKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p

private theorem smallSample_inverse_block11_from_core {I J:Type}
    [Fintype I][Fintype J][DecidableEq I][DecidableEq J]
    (M:Matrix (I⊕J) (I⊕J) ℂ)(hM:IsUnit M)(hc:IsUnit M.toBlocks₁₁) :
    (M⁻¹).toBlocks₁₁=M.toBlocks₁₁⁻¹-M.toBlocks₁₁⁻¹*M.toBlocks₁₂*(M⁻¹).toBlocks₂₁ := by
  have hm:M*M⁻¹=1:=Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  have he:M.toBlocks₁₁*(M⁻¹).toBlocks₁₁+M.toBlocks₁₂*(M⁻¹).toBlocks₂₁=1:=by
    ext i j
    have hh:=congrArg (fun A:Matrix (I⊕J) (I⊕J) ℂ=>A (.inl i) (.inl j)) hm
    simpa only[Matrix.mul_apply,Fintype.sum_sum_type,Matrix.add_apply,
      Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.of_apply,
      Matrix.one_apply,Sum.inl.injEq] using hh
  have hh:=congrArg (fun A:Matrix I I ℂ=>M.toBlocks₁₁⁻¹*A) he
  dsimp only at hh
  rw[Matrix.mul_add,←Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hc),Matrix.one_mul,Matrix.mul_one] at hh
  rw[←Matrix.mul_assoc] at hh
  exact eq_sub_iff_add_eq.mpr hh

namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

theorem extensionGreen_core_restore_identity (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x y:(Tᶜ:Set V)) :
    g.extensionGreen q z x.val y.val=(g.delete T).extensionGreen q z x y-
      ∑b:T,(((g.delete T).extensionGreen q z*g.H.submatrix
        (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b)*g.extensionGreen q z b.val y.val := by
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
  have hh:=congrArg (fun A:Matrix (Tᶜ:Set V) (Tᶜ:Set V) ℂ=>A x y)
    (smallSample_inverse_block11_from_core M hM hcu)
  rw[hi,hcore,hcross] at hh
  simpa only[Matrix.sub_apply,Matrix.mul_apply,Matrix.toBlocks₁₁,Matrix.toBlocks₂₁,
    Matrix.submatrix_apply,Matrix.of_apply,e,Equiv.trans_apply,Equiv.sumComm_apply,
    Equiv.Set.sumCompl_apply_inl,Equiv.Set.sumCompl_apply_inr] using hh

omit [DecidableEq V] in
private theorem smallSample_far_one_side (g:DeficientGraph V d)(x y b:V)(h:ℕ)
    (hfar:((2*h+2:ℕ):ℕ∞)≤g.graph.edist x y) :
    ((h+1:ℕ):ℕ∞)≤g.graph.edist x b ∨ ((h+1:ℕ):ℕ∞)≤g.graph.edist y b := by
  by_cases hx:((h+1:ℕ):ℕ∞)≤g.graph.edist x b
  · exact Or.inl hx
  · right
    apply (ENat.add_one_le_iff (ENat.coe_ne_top h)).mpr
    apply lt_of_not_ge
    intro hy
    have hxb:g.graph.edist x b≤(h:ℕ∞):=by
      apply le_of_not_gt
      intro hlt
      exact hx ((ENat.add_one_le_iff (ENat.coe_ne_top h)).mpr hlt)
    have hh:g.graph.edist x y≤((2*h:ℕ):ℕ∞):=by
      calc
        _≤g.graph.edist x b+g.graph.edist b y:=g.graph.edist_triangle
        _≤(h:ℕ∞)+(h:ℕ∞):=add_le_add hxb (by simpa only[SimpleGraph.edist_comm] using hy)
        _=((2*h:ℕ):ℕ∞):=by norm_cast;omega
    have hb:2*h+2≤2*h:=ENat.coe_le_coe.mp (hfar.trans hh)
    omega

/-- A raw entire-kernel bound. The residual is retained, not hidden in an entry-cap assumption. -/
theorem small_sample_entire_kernel_raw (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(K L ε C δ:ℝ)
    (hK:0≤K)(hL:0≤L)(hε:0≤ε)(hεone:ε≤1)(hC:0≤C)(hδ:0≤δ)
    (hT:Nat.card T≤2)(hcore:g.LeafCoreDecayBound T q z K L ε)
    (hB:∀b:T,∑c:T,‖g.extensionGreen q z b.val c.val‖≤C)
    (hoff:∀b c:T,b≠c→‖g.extensionGreen q z b.val c.val‖≤δ)
    (x y:V)(h:ℕ)(hfar:((2*h+2:ℕ):ℕ∞)≤g.graph.edist x y) :
    let F:=K*L*physicalTransfer d z^h+K*L*ε
    let f:=F*((d:ℝ)/Real.sqrt ((d:ℝ)-1))
    let a:=4*(d:ℝ)*K*L
    ‖g.extensionGreen q z x y‖≤F+2*(f*(a*C)+a*(C*f+δ*a))+(C*f+δ*a)+δ := by
  dsimp only
  let F:=K*L*physicalTransfer d z^h+K*L*ε
  let f:=F*((d:ℝ)/Real.sqrt ((d:ℝ)-1))
  let a:=4*(d:ℝ)*K*L
  let U:=(g.delete T).extensionGreen q z*g.H.submatrix
    (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)
  change ‖g.extensionGreen q z x y‖≤F+2*(f*(a*C)+a*(C*f+δ*a))+(C*f+δ*a)+δ
  have ht:0≤physicalTransfer d z^h:=pow_nonneg (physicalTransfer_pos d hd z).le h
  have hF:0≤F:=by dsimp only[F];positivity
  have hf:0≤f:=by dsimp only[f];positivity
  have ha:0≤a:=by dsimp only[a];positivity
  have hg:0≤C*f+δ*a:=by positivity
  have hfc:0≤f*(a*C):=by positivity
  have hag:0≤a*(C*f+δ*a):=by positivity
  have hc:∀u v:(Tᶜ:Set V),∀n:ℕ,(n:ℕ∞)≤(g.delete T).graph.edist u v→
      ‖(g.delete T).extensionGreen q z u v‖≤K*L*physicalTransfer d z^n+K*L*ε:=by
    intro u v n hn
    have he:=hcore u v n hn
    have hi:=extensionGreen_decidableEq_eq (g.delete T)
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw[hi] at he
    exact he
  have hcutCanonical:=g.small_sample_cut_rows hd T q z K L ε hK hL hε hεone hT hcore
  have hcut:∀u:(Tᶜ:Set V),∑b:T,‖U u b‖≤a:=by
    have hi:=extensionGreen_decidableEq_eq (g.delete T)
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw[hi] at hcutCanonical
    exact hcutCanonical
  have hcutPoint (u:(Tᶜ:Set V))(b:T):‖U u b‖≤a:=
    (Finset.single_le_sum (fun j _=>norm_nonneg (U u j)) (Finset.mem_univ b)).trans (hcut u)
  have hcrossRows:=g.deleted_sample_cross_rows hd T q z hz hq a C hC hcutCanonical hB
  have hcrossPoint (u:(Tᶜ:Set V))(b:T):‖g.extensionGreen q z u.val b.val‖≤a*C:=
    (Finset.single_le_sum (fun j _=>norm_nonneg (g.extensionGreen q z u.val j.val)) (Finset.mem_univ b)).trans (hcrossRows u)
  have hdiag (b:T):‖g.extensionGreen q z b.val b.val‖≤C:=
    (Finset.single_le_sum (fun j _=>norm_nonneg (g.extensionGreen q z b.val j.val)) (Finset.mem_univ b)).trans (hB b)
  have hcutFar (u:(Tᶜ:Set V))(b:T)(hu:((h+1:ℕ):ℕ∞)≤g.graph.edist u.val b.val):‖U u b‖≤f:=by
    have hb:b.val∉pairBallVertices g.graph u.val u.val h:=by
      intro hb
      have hh:g.graph.edist u.val b.val≤(h:ℕ∞):=hb.elim id id
      have hh':h+1≤h:=ENat.coe_le_coe.mp (hu.trans hh)
      omega
    apply g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) u b F hF
    intro v hv
    exact hc u v h (((omitted_pair_neighbor_far g.graph u.val u.val b.val v.val h hb hv).1).trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) Tᶜ).toHom u v))
  have hcrossFar (u:(Tᶜ:Set V))(b:T)(hu:((h+1:ℕ):ℕ∞)≤g.graph.edist u.val b.val):
      ‖g.extensionGreen q z u.val b.val‖≤C*f+δ*a:=
    g.deleted_sample_cross_bound hd T q z hz hq u b C δ f a hC hδ hf (hdiag b)
      (fun j hj=>hoff j b hj) (hcutFar u b hu) (hcut u)
  have hsym:=g.extensionGreen_isSymm q z
  by_cases hx:x∈T
  · by_cases hy:y∈T
    · have hxy:(⟨x,hx⟩:T)≠⟨y,hy⟩:=by
        intro he
        have hv:x=y:=congrArg Subtype.val he
        have hh:2*h+2≤0:=ENat.coe_le_coe.mp (by simpa only[hv,SimpleGraph.edist_self] using hfar)
        omega
      exact (hoff ⟨x,hx⟩ ⟨y,hy⟩ hxy).trans (by linarith)
    · have hyfar:((h+1:ℕ):ℕ∞)≤g.graph.edist y x:=by
        rw[SimpleGraph.edist_comm]
        exact (ENat.coe_le_coe.mpr (by omega: h+1≤2*h+2)).trans hfar
      rw[←hsym.apply x y]
      exact (hcrossFar ⟨y,hy⟩ ⟨x,hx⟩ hyfar).trans (by linarith)
  · by_cases hy:y∈T
    · have hxfar:((h+1:ℕ):ℕ∞)≤g.graph.edist x y:=
        (ENat.coe_le_coe.mpr (by omega:h+1≤2*h+2)).trans hfar
      exact (hcrossFar ⟨x,hx⟩ ⟨y,hy⟩ hxfar).trans (by linarith)
    · let x0:(Tᶜ:Set V):=⟨x,hx⟩
      let y0:(Tᶜ:Set V):=⟨y,hy⟩
      have hcorefar:(h:ℕ∞)≤(g.delete T).graph.edist x0 y0:=
        ((ENat.coe_le_coe.mpr (by omega:h≤2*h+2)).trans hfar).trans
          (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) Tᶜ).toHom x0 y0)
      have he:=g.extensionGreen_core_restore_identity hd T q z hz hq x0 y0
      have hp (b:T):‖U x0 b*g.extensionGreen q z b.val y‖≤f*(a*C)+a*(C*f+δ*a):=by
        rw[norm_mul]
        rcases g.smallSample_far_one_side x y b.val h hfar with hxb|hyb
        · have hb:‖g.extensionGreen q z b.val y‖≤a*C:=by
            rw[hsym.apply y b.val]
            exact hcrossPoint y0 b
          exact (mul_le_mul (hcutFar x0 b hxb) hb (norm_nonneg _) hf).trans (by linarith)
        · have hb:‖g.extensionGreen q z b.val y‖≤C*f+δ*a:=by
            rw[hsym.apply y b.val]
            exact hcrossFar y0 b hyb
          exact (mul_le_mul (hcutPoint x0 b) hb (norm_nonneg _) ha).trans (by linarith)
      have hn:(Fintype.card T:ℝ)≤2:=by exact_mod_cast (show Fintype.card T≤2 by simpa only[Nat.card_eq_fintype_card] using hT)
      have hs:‖∑b:T,U x0 b*g.extensionGreen q z b.val y‖≤2*(f*(a*C)+a*(C*f+δ*a)):=by
        calc
          _≤∑b:T,‖U x0 b*g.extensionGreen q z b.val y‖:=norm_sum_le _ _
          _≤∑_b:T,(f*(a*C)+a*(C*f+δ*a)):=Finset.sum_le_sum (fun b _=>hp b)
          _=(Fintype.card T:ℝ)*(f*(a*C)+a*(C*f+δ*a)):=by simp;ring
          _≤_:=mul_le_mul_of_nonneg_right hn (by positivity)
      rw[he]
      have hbase:‖(g.delete T).extensionGreen q z x0 y0‖≤F:=hc x0 y0 h hcorefar
      exact (norm_sub_le _ _).trans ((add_le_add hbase hs).trans (by linarith))

end DeficientGraph
end LocalLaw
