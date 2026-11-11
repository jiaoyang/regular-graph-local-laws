import LocalLaw.CutStarReduction
import LocalLaw.StarHarmonicBounds
import LocalLaw.StarCouplingRows

/-! # Harmonic L1 rows for actual captured inner-cut restoration

The actual target-to-T row mass controls both harmonic factors. Neither
an inverse row bound nor a cardinality bound on the restored T is assumed.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance cutStarHarmonicRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) cutStarHarmonicRangeDecidable {L W:Type}(a:L↪W):
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

theorem cut_star_harmonic_l1 (g:DeficientGraph V d)(hd:3≤d)(T S I:Set V)
    (hTS:T⊆S)(hIS:I⊆S)(hIT:∀v∈I,v∉T)
    (hcut:∀t∈T,∀v,g.graph.Adj t v→v∉T→v∈I)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B:ℝ)(hB:0≤B):
    let a:=cutInnerEmbedding T S hTS
    let e:=cutCoreEmbedding T S I hTS hIS hIT
    let E:=embeddedStarEmbedding a e
    let R:=(((g.restrict S).delete (Set.range a)).extensionGreen q z).submatrix e e
    let G:=((g.restrict S).extensionGreen q z).submatrix E E
    ∀x:I⊕T,(∑t:T,‖(g.restrict S).extensionGreen q z (E x) (a t)‖)≤B→
      ((∑i:I,‖(G.submatrix id Sum.inl*R⁻¹) x i‖)≤1+(d:ℝ)*B) ∧
      ((∑i:I,‖(R⁻¹*G.submatrix Sum.inl id) i x‖)≤1+(d:ℝ)*B):=by
  dsimp only
  let a:=cutInnerEmbedding T S hTS
  let e:=cutCoreEmbedding T S I hTS hIS hIT
  let E:=embeddedStarEmbedding a e
  let R:=(((g.restrict S).delete (Set.range a)).extensionGreen q z).submatrix e e
  let G:=((g.restrict S).extensionGreen q z).submatrix E E
  have hng:∀v t,(g.restrict S).graph.Adj v.val (a t)→v∈Set.range e:=by
    intro v t hadj
    have hout:v.val.val∉T:=fun ht=>v.property ((cutInner_range_iff T S hTS v.val).mpr ht)
    have hi:v.val.val∈I:=hcut t.val t.property v.val.val hadj.symm hout
    exact ⟨⟨v.val.val,hi⟩,Subtype.ext (Subtype.ext rfl)⟩
  have hentry:=(g.restrict S).actual_star_harmonic_entries hd a e hng q z hz hq
  have hcoupling:=(g.restrict S).actual_star_coupling_rows hd a e q z
  intro x hx
  have hleft:=harmonic_row_l1 (G.submatrix id Sum.inr)
    (fun t i=>(g.restrict S).extensionMatrix q z (a t) (e i).val)
    (G.submatrix id Sum.inl*R⁻¹) x B (d:ℝ) hB (Nat.cast_nonneg _)
    (hentry.1 x) hx hcoupling.1
  have hcol:(∑t:T,‖G (.inr t) x‖)≤B:=by
    convert hx using 1
    apply Finset.sum_congr rfl
    intro t _
    exact congrArg norm (((g.restrict S).extensionGreen_isSymm q z).apply (E x) (a t))
  have hr (i:I):(R⁻¹*G.submatrix Sum.inl id) i x=
      (if x=.inl i then 1 else 0)-∑t:T,G (.inr t) x*(g.restrict S).extensionMatrix q z (e i).val (a t):=by
    have hh:(R⁻¹*G.submatrix Sum.inl id) i x=
        (if (.inl i:I⊕T)=x then 1 else 0)-
          ∑t:T,(g.restrict S).extensionMatrix q z (e i).val (a t)*G (.inr t) x:=hentry.2 i x
    rw[hh]
    apply congrArg₂ (fun p q:ℂ=>p-q)
    · by_cases hi:x=(.inl i:I⊕T)
      · simp only[hi,if_true]
      · simp only[if_neg hi,if_neg (Ne.symm hi)]
    · exact Finset.sum_congr rfl (fun t _=>mul_comm _ _)
  have hright:=harmonic_row_l1 (fun y t=>G (.inr t) y)
    (fun t i=>(g.restrict S).extensionMatrix q z (e i).val (a t))
    (fun y i=>(R⁻¹*G.submatrix Sum.inl id) i y) x B (d:ℝ) hB (Nat.cast_nonneg _)
    hr hcol hcoupling.2
  exact ⟨hleft.trans_eq (by ring),hright.trans_eq (by ring)⟩

end DeficientGraph
end LocalLaw
