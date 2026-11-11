import LocalLaw.LocalizationComponents

/-!
# Actual intrinsic diameter of a singly attached deleted component

The unique-attachment distance identity turns ambient diameter into a root
distance bound in the component. A triangle inequality then gives twice the
ambient cap, without identifying ambient and deleted distances.
-/

noncomputable section
namespace LocalLaw
local instance pendantDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) pendantComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem unique_cut_component_diameter (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (c : CutComponent G S) (hcount : cutMultiplicity G S c = 1)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (a b : c.supp) :
    (cutComponentGraph G S c).dist a b ≤ 2 * R := by
  obtain ⟨e, _⟩ := Nat.card_eq_one_iff_exists.mp hcount
  let root := cutAttachmentRoot G S c e
  have hroot : ∀ y : c.supp, (cutComponentGraph G S c).dist root y ≤ R := by
    intro y
    have hid := unique_cut_attachment_distance G hG S c hcount e e.val.val.1 e.val.property.2.1 y
    rw [G.dist_self] at hid
    have hh := hR e.val.val.1 y.val.val
    dsimp only [root]
    omega
  have ht := c.connected_induce_supp.dist_triangle (u := a) (v := root) (w := b)
  change (cutComponentGraph G S c).dist a b ≤ (cutComponentGraph G S c).dist a root +
    (cutComponentGraph G S c).dist root b at ht
  have ha := hroot a
  have hb := hroot b
  rw [show (cutComponentGraph G S c).dist root a = (cutComponentGraph G S c).dist a root from
    (cutComponentGraph G S c).dist_comm] at ha
  omega

/-- Ordinary components in the localization split inherit a proved
diameter cap for the refined cavity feedback theorem. -/
theorem ordinary_cut_component_diameter (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hS : S.Nonempty) (c : CutComponent G S)
    (hcharge : cutExcessCharge G S c = 0)
    (R : ℕ) (hR : ∀ x y, G.dist x y ≤ R) (a b : c.supp) :
    (cutComponentGraph G S c).dist a b ≤ 2 * R :=
  unique_cut_component_diameter G hG S c ((cut_charge_zero_iff G S hG hS c).mp hcharge).2 R hR a b

end LocalLaw
