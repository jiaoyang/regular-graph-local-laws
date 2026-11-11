import LocalLaw.ComponentModel
import LocalLaw.DeficientGraphIso

/-! # An isolated nested restriction has the same genuine finite kernel -/

noncomputable section
namespace LocalLaw
local instance nestedIsolatedModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The isolated cutoff is relative to the larger finite model. No global
isolation, component reference bound or model approximation is required. -/
theorem nested_isolated_extensionGreen (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S K : Set V) (hKS : K ⊆ S)
    (hcut : ∀ x ∈ K, ∀ y ∈ S, y ∉ K → ¬g.graph.Adj x y)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (x y : K) :
    (g.restrict S).extensionGreen q z ⟨x.val, hKS x.property⟩ ⟨y.val, hKS y.property⟩ =
      (g.restrict K).extensionGreen q z x y := by
  let C : Set S := {v | v.val ∈ K}
  let e : ((g.restrict S).restrict C).graph ≃g (g.restrict K).graph :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      invFun := fun v => ⟨⟨v.val, hKS v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hblock := (g.restrict S).restrict_extensionGreen_of_isolated hd C
    (fun a ha b hb => hcut a.val ha b.val b.property hb) q z hz hq
  have hiso := (g.restrict K).extensionGreen_iso ((g.restrict S).restrict C) e (fun _ => rfl) q z
  have hh := congrFun (congrFun hblock ⟨⟨x.val, hKS x.property⟩, x.property⟩)
    ⟨⟨y.val, hKS y.property⟩, y.property⟩
  rw [← hiso] at hh
  exact hh.symm

end DeficientGraph
end LocalLaw
