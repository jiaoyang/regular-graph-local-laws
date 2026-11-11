import SpectralConsequences.OldMinorCommonQuadratic
import SpectralConsequences.SourceRetainedBallSamples
import SpectralConsequences.OldSampleFormalValues
import SpectralConsequences.SelectedTipCrossCaps

/-! # Actual original own-sample minors are quadratically close to the common minor

Only original-graph source events are assumed. The removed own set is any
set of at most two accepted sampled first vertices and contains both target
labels. The conclusion is uniform over all labelled samples.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance sourceOldMinorCommonDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def oldMinorPivotConstant (d:ℕ) (B:ℝ):ℝ:=|sourceGreenPivotCap d B|+1
def oldMinorEntryConstant (d:ℕ):ℝ:=|guardedGreenEntryCap d|+1
def oldMinorRetainedConstant (d:ℕ) (B:ℝ):ℝ:=|oldRetainedBallSampleInverseCap d B|+1

def oldOwnSampleMinorEntry {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (H:Matrix V V ℂ) (T:Set V) (b:I↪(Tᶜ:Set V)) (c:I→(Tᶜ:Set V))
    (hcb:∀i j,b j≠c i) (Q:Set I) (z:ℂ) (i j:I):ℂ:=
  let f:=retainedBallSampleEmbedding T b
  let O:=f '' sampleOwnRetainedSet T Q
  let x:=sampleTipRetainedComplement T b c hcb i
  let y:=sampleTipRetainedComplement T b c hcb j
  green (H.submatrix (Subtype.val:(Oᶜ:Set V)→V) (Subtype.val:(Oᶜ:Set V)→V)) z
    ⟨x.val,fun h=>x.property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
    ⟨y.val,fun h=>y.property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩

def oldCommonSampleEntry {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (H:Matrix V V ℂ) (T:Set V) (b:I↪(Tᶜ:Set V)) (c:I→(Tᶜ:Set V))
    (hcb:∀i j,b j≠c i) (z:ℂ) (i j:I):ℂ:=
  let f:=retainedBallSampleEmbedding T b
  green (H.submatrix (Subtype.val:((Set.range f)ᶜ:Set V)→V)
    (Subtype.val:((Set.range f)ᶜ:Set V)→V)) z
    (sampleTipRetainedComplement T b c hcb i) (sampleTipRetainedComplement T b c hcb j)

theorem eventually_source_old_minor_common_comparison (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hC1:0≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let e:=s.selectedFirstEmbedding selector
      let tips:=s.admissibleSecondVertex selector
      let hne:=selected_first_ne_second s selector
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      ∀(Q:Set (s.AdmissibleSampleIndex selector)),Nat.card Q≤2→
      ∀i j,i∈Q→j∈Q→
      ‖oldOwnSampleMinorEntry g.H T e tips hne Q z i j-oldCommonSampleEntry g.H T e tips hne z i j‖≤
        ((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ)*oldMinorRetainedConstant d B*
          ((1+4*oldMinorPivotConstant d B*oldMinorEntryConstant d)*ε)^2 := by
  let P:=oldMinorPivotConstant d B
  let A:=oldMinorEntryConstant d
  let C:=oldMinorRetainedConstant d B
  have hP:0≤P:=by dsimp only[P,oldMinorPivotConstant];positivity
  have hA:0≤A:=by dsimp only[A,oldMinorEntryConstant];positivity
  have hC:0≤C:=by dsimp only[C,oldMinorRetainedConstant];positivity
  filter_upwards [eventually_source_retained_ball_sample_inverse_rows a b d c β B C1 ha hb hd hc hβ hβc hB hC1,
    RegularGraph.eventually_old_sample_formal_values a b d c β B ha hb hd hc hβ hβc,
    RegularGraph.eventually_source_selected_inner_cross a d c β hd hc hβ hβc,
    eventually_actualGuardedGreenCaps a b d c β C1 B ha hb hd hc hβ hβc hC1 hB,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_log_ge_nat (4*P),eventually_ge_atTop 1]
    with N hretained hsample hinner hcaps herror hL hlarge hN
  intro g o z hz hfloor hzB Cq badCount hold hplus ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let I:=s.AdmissibleSampleIndex selector
  let e:=s.selectedFirstEmbedding selector
  let tips:=s.admissibleSecondVertex selector
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let L:=Real.log (N:ℝ)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos (by linarith:0<L) _)).mp
    (by simpa only[one_div] using herror z hz hfloor)
  have hεone:ε≤1:=by
    have hh:=mul_le_mul_of_nonneg_left (show 1≤L^(4*a) from one_le_pow₀ hL) hε
    nlinarith only[hh,hcap]
  have hεA:ε≤A:=hεone.trans (by dsimp only[A,oldMinorEntryConstant];linarith [abs_nonneg (guardedGreenEntryCap d)])
  have hsmall0:(2*P)*ε≤1/2:=by
    have hh:=source_scaled_log_monomial_half a 0 L ε (2*P) hL hε (by positivity) hcap (by omega)
      (by nlinarith only[hlarge])
    simpa only[pow_zero,mul_one] using hh
  have hu:=hretained g o z hz hfloor hzB Cq badCount hold hplus labels samples
  have hf:=hsample g o z hz hzB hfloor badCount hold labels samples
  have ht:=hinner g o z hz badCount hold labels samples
  have hcps:=hcaps g o z hz hzB hfloor Cq badCount hplus
  have hrows:∀i,∑j,‖((green g.H z).submatrix (retainedBallSampleEmbedding T e)
      (retainedBallSampleEmbedding T e))⁻¹ i j‖≤C:=by
    intro i
    exact (hu.2.1 i).trans (by dsimp only[C,oldMinorRetainedConstant];linarith [le_abs_self (oldRetainedBallSampleInverseCap d B)])
  have hpivot:∀i,‖(g.G z (e i).val (e i).val)⁻¹‖≤P:=by
    intro i
    exact (hcps.full_pivot (e i).val).trans (by dsimp only[P,oldMinorPivotConstant];linarith [le_abs_self (sourceGreenPivotCap d B)])
  have hbb:∀i j:I,i≠j→‖g.G z (e i).val (e j).val‖≤ε:=by
    intro i j hij
    exact hf.2.2 i j hij (e i) (e j) (Or.inl rfl) (Or.inl rfl)
  have hcb:∀i j:I,i≠j→‖g.G z (tips i).val (e j).val‖≤ε:=by
    intro i j hij
    exact hf.2.2 i j hij (tips i) (e j) (Or.inr (Set.mem_singleton _)) (Or.inl rfl)
  have hbc:∀i j:I,i≠j→‖g.G z (e j).val (tips i).val‖≤ε:=by
    intro i j hij
    exact hf.2.2 j i hij.symm (e j) (tips i) (Or.inl rfl) (Or.inr (Set.mem_singleton _))
  have hown:∀i,‖g.G z (tips i).val (e i).val‖≤A:=by
    intro i
    have hadj:g.graph.Adj (tips i).val (e i).val:=(s.samples (s.boundary i.val)).property.1.symm
    exact (hcps.full_adj _ _ hadj).trans (by dsimp only[A,oldMinorEntryConstant];linarith [le_abs_self (guardedGreenEntryCap d)])
  have hown':∀i,‖g.G z (e i).val (tips i).val‖≤A:=by
    intro i
    have hadj:g.graph.Adj (e i).val (tips i).val:=(s.samples (s.boundary i.val)).property.1
    exact (hcps.full_adj _ _ hadj).trans (by dsimp only[A,oldMinorEntryConstant];linarith [le_abs_self (guardedGreenEntryCap d)])
  intro Q hcard i j hi hj
  have hn:(Fintype.card Q:ℝ)≤2:=by simpa only[Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr hcard)
  have hsmall:(Fintype.card Q:ℝ)*P*ε≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_right hn (mul_nonneg hP hε)
    nlinarith only[hh,hsmall0]
  have hh:=old_small_minor_common_quadratic g.H (normalizedAdjacency_isHermitian _ _) T e tips
    (selected_first_ne_second s selector) z hz P A C ε hP hA hC hε hrows hpivot hbb hcb hbc hown hown'
    (fun i t=>(ht i (e i) (Or.inl rfl) t).1) (fun i t=>(ht i (e i) (Or.inl rfl) t).2)
    (fun i t=>(ht i (tips i) (Or.inr (Set.mem_singleton _)) t).1)
    (fun i t=>(ht i (tips i) (Or.inr (Set.mem_singleton _)) t).2) hεA Q hcard hsmall i j hi hj
  have hcount:(Fintype.card (I⊕T):ℝ)≤((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ):=by
    have hi':Nat.card I≤Nat.card (BoundaryOrientedEdge g.graph T):=
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (Nat.card_congr labels)
    simpa only[Nat.card_eq_fintype_card,Fintype.card_sum,Nat.cast_add] using
      (add_le_add_right (Nat.cast_le (α:=ℝ).mpr hi') (Nat.card T:ℝ))
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hC) (sq_nonneg _))

end SpectralConsequences
