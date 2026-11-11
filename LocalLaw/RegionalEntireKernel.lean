import LocalLaw.SmallSampleKernelRestoration
import LocalLaw.LeafCoreFarAdapter

/-! # Entire-kernel decay from true fixed cut and sampled row masses

The sampled sum is split by which target is far. Each side pays its actual
row mass, so there is no sampled-vertex count factor.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance regionalEntireDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

theorem entire_kernel_of_fixed_rows (g:DeficientGraph V d)(hd:3≤d)(T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (K L ε A D U B:ℝ)(hK:0≤K)(hL:0≤L)(hε:0≤ε)(hA:0≤A)(hD:0≤D)(hU:0≤U)(hB:0≤B)
    (hcore:∀x y:(Tᶜ:Set V),∀h:ℕ,(h:ℕ∞)≤(g.delete T).graph.edist x y→
      ‖(g.delete T).extensionGreen q z x y‖≤K*L*physicalTransfer d z^h+K*L*ε)
    (hcut:∀x:(Tᶜ:Set V),(∑b:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖)≤U)
    (hwhole:∀x:V,∑b:T,‖g.extensionGreen q z x b.val‖≤B)
    (hcolumn:∀(x:V)(b:T)(h:ℕ),((h+1:ℕ):ℕ∞)≤g.graph.edist x b.val→
      ‖g.extensionGreen q z x b.val‖≤A*L*physicalTransfer d z^h+D*L*ε)
    (x y:V)(h:ℕ)(hfar:((2*h+2:ℕ):ℕ∞)≤g.graph.edist x y) :
    ‖g.extensionGreen q z x y‖≤
      (K*(1+(d:ℝ)*B)+A*(U+1))*L*physicalTransfer d z^h+
      (K*(1+(d:ℝ)*B)+D*(U+1))*L*ε := by
  let F:=K*L*physicalTransfer d z^h+K*L*ε
  let S:=A*L*physicalTransfer d z^h+D*L*ε
  have ht:0≤physicalTransfer d z^h:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hF:0≤F:=by dsimp only[F];positivity
  have hS:0≤S:=by dsimp only[S];positivity
  have hd0:0≤(d:ℝ):=Nat.cast_nonneg _
  have hcoarse:S≤F*(1+(d:ℝ)*B)+S*(U+1):=by
    nlinarith only [mul_nonneg hF (show 0≤1+(d:ℝ)*B by positivity),mul_nonneg hS hU]
  have hresult:F*(1+(d:ℝ)*B)+S*(U+1)=
      (K*(1+(d:ℝ)*B)+A*(U+1))*L*physicalTransfer d z^h+
      (K*(1+(d:ℝ)*B)+D*(U+1))*L*ε:=by dsimp only[F,S];ring
  have hfarOne:((h+1:ℕ):ℕ∞)≤g.graph.edist x y:=
    (ENat.coe_le_coe.mpr (show h+1≤2*h+2 by omega)).trans hfar
  by_cases hx:x∈T
  · have hh:=hcolumn y ⟨x,hx⟩ h (by simpa only[SimpleGraph.edist_comm] using hfarOne)
    rw[(g.extensionGreen_isSymm q z).apply y x]
    exact hh.trans (hcoarse.trans_eq hresult)
  by_cases hy:y∈T
  · exact (hcolumn x ⟨y,hy⟩ h hfarOne).trans (hcoarse.trans_eq hresult)
  let x0:(Tᶜ:Set V):=⟨x,hx⟩
  let y0:(Tᶜ:Set V):=⟨y,hy⟩
  let C:=(g.delete T).extensionGreen q z*g.H.submatrix
    (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)
  have hfarSide (b:T):((h+1:ℕ):ℕ∞)≤g.graph.edist x b.val ∨ ((h+1:ℕ):ℕ∞)≤g.graph.edist y b.val:=by
    by_cases hb:((h+1:ℕ):ℕ∞)≤g.graph.edist x b.val
    · exact Or.inl hb
    · right
      apply (ENat.add_one_le_iff (ENat.coe_ne_top h)).mpr
      apply lt_of_not_ge
      intro hb'
      have hxb:g.graph.edist x b.val≤(h:ℕ∞):=by
        apply le_of_not_gt
        intro hh
        exact hb ((ENat.add_one_le_iff (ENat.coe_ne_top h)).mpr hh)
      have hxy:g.graph.edist x y≤((2*h:ℕ):ℕ∞):=by
        calc
          _≤g.graph.edist x b.val+g.graph.edist b.val y:=g.graph.edist_triangle
          _≤(h:ℕ∞)+(h:ℕ∞):=add_le_add hxb (by simpa only[SimpleGraph.edist_comm] using hb')
          _=((2*h:ℕ):ℕ∞):=by norm_cast;omega
      have hn:2*h+2≤2*h:=ENat.coe_le_coe.mp (hfar.trans hxy)
      omega
  have hratio:(d:ℝ)/Real.sqrt ((d:ℝ)-1)≤d:=by
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    have hs:1≤Real.sqrt ((d:ℝ)-1):=by
      have hh:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
      nlinarith [Real.sqrt_nonneg ((d:ℝ)-1)]
    apply (div_le_iff₀ (by linarith:0<Real.sqrt ((d:ℝ)-1))).mpr
    nlinarith
  have hcutFar (b:T)(hb:((h+1:ℕ):ℕ∞)≤g.graph.edist x b.val):‖C x0 b‖≤F*(d:ℝ):=by
    have hnot:b.val∉pairBallVertices g.graph x x h:=by
      intro hm
      have hn:h+1≤h:=ENat.coe_le_coe.mp (hb.trans (hm.elim id id))
      omega
    have hnear (v:(Tᶜ:Set V))(hv:g.graph.Adj v.val b.val):‖(g.delete T).extensionGreen q z x0 v‖≤F:=
      hcore x0 v h (((omitted_pair_neighbor_far g.graph x x b.val v.val h hnot hv).1).trans
        (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) Tᶜ).toHom x0 v))
    exact (g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) x0 b F hF hnear).trans
      (mul_le_mul_of_nonneg_left hratio hF)
  have hterm (b:T):‖C x0 b*g.extensionGreen q z b.val y‖≤
      (F*(d:ℝ))*‖g.extensionGreen q z b.val y‖+S*‖C x0 b‖:=by
    rw[norm_mul]
    rcases hfarSide b with hb|hb
    · exact (mul_le_mul_of_nonneg_right (hcutFar b hb) (norm_nonneg _)).trans
        (le_add_of_nonneg_right (mul_nonneg hS (norm_nonneg _)))
    · have hs:‖g.extensionGreen q z b.val y‖≤S:=by
        rw[(g.extensionGreen_isSymm q z).apply y b.val]
        exact hcolumn y b h hb
      have hh:=mul_le_mul_of_nonneg_left hs (norm_nonneg (C x0 b))
      nlinarith only [hh,mul_nonneg (mul_nonneg hF hd0) (norm_nonneg (g.extensionGreen q z b.val y))]
  have hwholeY:(∑b:T,‖g.extensionGreen q z b.val y‖)≤B:=by
    simpa only[(g.extensionGreen_isSymm q z).apply y] using hwhole y
  have hsum:‖∑b:T,C x0 b*g.extensionGreen q z b.val y‖≤(F*(d:ℝ))*B+S*U:=by
    calc
      _≤∑b:T,‖C x0 b*g.extensionGreen q z b.val y‖:=norm_sum_le _ _
      _≤∑b:T,((F*(d:ℝ))*‖g.extensionGreen q z b.val y‖+S*‖C x0 b‖):=Finset.sum_le_sum (fun b _=>hterm b)
      _=(F*(d:ℝ))*(∑b:T,‖g.extensionGreen q z b.val y‖)+S*(∑b:T,‖C x0 b‖):=by
        rw[Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      _≤_:=add_le_add (mul_le_mul_of_nonneg_left hwholeY (mul_nonneg hF hd0))
        (mul_le_mul_of_nonneg_left (hcut x0) hS)
  have hxy:(h:ℕ∞)≤(g.delete T).graph.edist x0 y0:=
    ((ENat.coe_le_coe.mpr (show h≤2*h+2 by omega)).trans hfar).trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) Tᶜ).toHom x0 y0)
  rw[g.extensionGreen_core_restore_identity hd T q z hz hq x0 y0]
  exact ((norm_sub_le _ _).trans (add_le_add (hcore x0 y0 h hxy) hsum)).trans
    (by
      rw[←hresult]
      change F+(F*(d:ℝ)*B+S*U)≤F*(1+(d:ℝ)*B)+S*(U+1)
      nlinarith only[hS])

end DeficientGraph
end LocalLaw
