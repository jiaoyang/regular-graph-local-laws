import LocalLaw.MatchedStarReduction

/-! # Actual captured stars after restriction and outer-vertex deletion

The two retained vertex sets may omit different outer vertices. All those
omitted-neighbor deficits remain in their respective cores. Captured inner
stars still have exactly the same precision rows, which suffices for lifting.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance restrictedStarsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}
local instance (priority := 2000) restrictedStarsRangeDecidable {L W:Type} (a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a) := fun _=>Classical.propDecidable _

def restrictedStarInner (S A J:Set V)(hJS:J⊆S)(hJA:∀v∈J,v∉A) :
    J ↪ ({v:S|v.val∈A}ᶜ:Set S) where
  toFun j:=⟨⟨j.val,hJS j.property⟩,hJA j.val j.property⟩
  inj' := fun _ _ h=>Subtype.ext (congrArg (fun v=>v.val.val) h)

def restrictedStarCore (S A I J:Set V)(hIS:I⊆S)(hIA:∀v∈I,v∉A)
    (hJS:J⊆S)(hJA:∀v∈J,v∉A)(hIJ:∀v∈I,v∉J) :
    I ↪ ((Set.range (restrictedStarInner S A J hJS hJA))ᶜ:Set ({v:S|v.val∈A}ᶜ:Set S)) where
  toFun i:=⟨⟨⟨i.val,hIS i.property⟩,hIA i.val i.property⟩,by
    rintro ⟨j,h⟩
    have he:j.val=i.val:=congrArg (fun v=>v.val.val) h
    exact hIJ i.val i.property (he ▸ j.property)⟩
  inj' := fun _ _ h=>Subtype.ext (congrArg (fun v=>v.val.val.val) h)

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d:ℕ}

private theorem restricted_deleted_star_row (g:DeficientGraph V d)(S A:Set V)
    (v w:({u:S|u.val∈A}ᶜ:Set S))
    (hcap:∀u,g.graph.Adj v.val.val u→u∈S)(q z:ℂ) :
    ((g.restrict S).delete {u:S|u.val∈A}).extensionMatrix q z v w=
      g.extensionMatrix q z v.val.val w.val.val := by
  rw [(g.restrict S).extensionMatrix_delete]
  exact g.restrict_extensionMatrix_captured_row S v.val hcap q z w.val

/-- Exact two-model reduction, preserving all omitted-outer-neighbor charges. -/
theorem restricted_deleted_star_difference (g:DeficientGraph V d)(hd:3≤d)
    (S₀ S₁ A I J:Set V)(hI₀:I⊆S₀)(hI₁:I⊆S₁)(hJ₀:J⊆S₀)(hJ₁:J⊆S₁)
    (hIA:∀v∈I,v∉A)(hJA:∀v∈J,v∉A)(hIJ:∀v∈I,v∉J)
    (hcap₀:∀b∈J,∀v,g.graph.Adj b v→v∈S₀)
    (hcap₁:∀b∈J,∀v,g.graph.Adj b v→v∈S₁)
    (hcore:∀b∈J,∀v,g.graph.Adj b v→v∉A→v∉J→v∈I)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let g₀:=(g.restrict S₀).delete {v:S₀|v.val∈A}
    let g₁:=(g.restrict S₁).delete {v:S₁|v.val∈A}
    let a:=restrictedStarInner S₀ A J hJ₀ hJA
    let b:=restrictedStarInner S₁ A J hJ₁ hJA
    let e:=restrictedStarCore S₀ A I J hI₀ hIA hJ₀ hJA hIJ
    let f:=restrictedStarCore S₁ A I J hI₁ hIA hJ₁ hJA hIJ
    let R:=((g₀.delete (Set.range a)).extensionGreen q z).submatrix e e
    let P:=((g₁.delete (Set.range b)).extensionGreen q z).submatrix f f
    let GM:=(g₀.extensionGreen q z).submatrix (embeddedStarEmbedding a e) (embeddedStarEmbedding a e)
    let GN:=(g₁.extensionGreen q z).submatrix (embeddedStarEmbedding b f) (embeddedStarEmbedding b f)
    IsUnit R ∧ IsUnit P ∧
      GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let g₀:=(g.restrict S₀).delete {v:S₀|v.val∈A}
  let g₁:=(g.restrict S₁).delete {v:S₁|v.val∈A}
  let a:=restrictedStarInner S₀ A J hJ₀ hJA
  let b:=restrictedStarInner S₁ A J hJ₁ hJA
  let e:=restrictedStarCore S₀ A I J hI₀ hIA hJ₀ hJA hIJ
  let f:=restrictedStarCore S₁ A I J hI₁ hIA hJ₁ hJA hIJ
  apply g₀.matched_star_inverse_difference g₁ hd a b e f ?_ ?_ q z hz hq ?_ ?_
  · intro v j hadj
    have hj:v.val.val.val∉J:=by
      intro hj
      exact v.property ⟨⟨v.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hi:v.val.val.val∈I:=hcore j.val j.property v.val.val.val hadj.symm v.val.property hj
    exact ⟨⟨v.val.val.val,hi⟩,Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  · intro v j hadj
    have hj:v.val.val.val∉J:=by
      intro hj
      exact v.property ⟨⟨v.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hi:v.val.val.val∈I:=hcore j.val j.property v.val.val.val hadj.symm v.val.property hj
    exact ⟨⟨v.val.val.val,hi⟩,Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  · intro i j
    exact (g.restricted_deleted_star_row S₀ A (a i) (a j) (hcap₀ i.val i.property) q z).trans
      (g.restricted_deleted_star_row S₁ A (b i) (b j) (hcap₁ i.val i.property) q z).symm
  · intro i j
    rw [(g₀.extensionMatrix_isSymm q z).apply, (g₁.extensionMatrix_isSymm q z).apply]
    exact (g.restricted_deleted_star_row S₀ A (a j) (e i).val (hcap₀ j.val j.property) q z).trans
      (g.restricted_deleted_star_row S₁ A (b j) (f i).val (hcap₁ j.val j.property) q z).symm

end DeficientGraph
end LocalLaw
