import LocalLaw.SourceRetainedExpansion

/-! # Exact entries of the fixed expanded-ball reference -/

noncomputable section
namespace LocalLaw
local instance sourceRetainedEntriesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

/-- Single retained entries are values of the fixed ordinary expanded-ball
model, with its actual original inherited zero deficit. -/
theorem sourceRetainedReference_entry_expanded_ball (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (q z : ℂ) (x y : graphBallVertices g.graph o ell) :
    g.sourceRetainedReference (graphBallVertices g.graph o ell) r q z x y =
      (g.deficient.restrict (graphBallVertices g.graph o (ell+r+1))).extensionGreen q z
        ⟨x.val, graphBallVertices_mono g.graph o (by omega) x.property⟩
        ⟨y.val, graphBallVertices_mono g.graph o (by omega) y.property⟩ := by
  have hset := filled_centralBoundary_eq_ball g.graph o ell r
  have hcongr (S L : Set (Fin N)) (h : S = L) (u v : Fin N)
      (huS : u ∈ S) (hvS : v ∈ S) (huL : u ∈ L) (hvL : v ∈ L) :
      (g.deficient.restrict S).extensionGreen q z ⟨u, huS⟩ ⟨v, hvS⟩ =
        (g.deficient.restrict L).extensionGreen q z ⟨u, huL⟩ ⟨v, hvL⟩ := by
    subst L
    rfl
  exact hcongr _ _ hset x.val y.val _ _ _ _

end RegularGraph
end LocalLaw
