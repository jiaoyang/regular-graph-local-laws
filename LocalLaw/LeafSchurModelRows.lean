import LocalLaw.LeafSchurRows

/-! # Remaining-leaf row and decay bounds for genuine model inverses -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance leafSchurModelRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V L J : Type} [Fintype V] [Fintype L] [Fintype J] {d : ℕ}

theorem attachLeaves_remaining_rows_cols (g : DeficientGraph V d) (hd : 3≤d)
    (mate : L→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (e : J→V) (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0)
    (δ U A B : ℝ) (hδ : 0≤δ) (hB : 0≤B)
    (herror : ∀l k:L,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
      (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card L:ℝ)*‖p⁻¹‖*δ≤1/2)
    (hbase : ∀i,∑j:J,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i) (.inl (e j))‖≤U)
    (hcross : ∀i,∑l:L,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i) (.inr l)‖≤A)
    (hremaining : ∀l,∑j:J,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inr l) (.inl (e j))‖≤B) :
    (∀i,∑j:J,‖g.extensionGreen q z i (e j)‖≤U+2*A*‖p⁻¹‖*B) ∧
      (∀i,∑j:J,‖g.extensionGreen q z (e j) i‖≤U+2*A*‖p⁻¹‖*B) := by
  let M:=(g.attachLeaves (by omega) mate hrestore).extensionMatrix q z
  have hM:IsUnit M:=(g.attachLeaves (by omega) mate hrestore).extensionMatrix_isUnit hd q z hz hq
  have hcore:M.toBlocks₁₁=g.extensionMatrix q z:=
    g.attachLeaves_extensionMatrix_principal (by omega) mate hrestore q z
  have hc:IsUnit M.toBlocks₁₁:=hcore ▸ g.extensionMatrix_isUnit hd q z hz hq
  have hrows:=core_inverse_scalar_leaf_remaining_rows M hM hc e p hp δ U A B hδ hB
    herror hsmall hbase hcross hremaining
  rw [hcore] at hrows
  refine ⟨hrows,fun i=>?_⟩
  simpa only [(g.extensionGreen_isSymm q z).apply] using hrows i

theorem attachLeaves_deleted_kernel_decay (g : DeficientGraph V d) (hd : 3≤d)
    (mate : L→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0) (i j : V)
    (δ A B C T ρ : ℝ) (hδ : 0≤δ) (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hρ : 0≤ρ)
    (D : ℕ) (di dj : L→ℕ)
    (herror : ∀l k:L,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
      (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card L:ℝ)*‖p⁻¹‖*δ≤1/2)
    (ha : (∑l:L,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i) (.inr l)‖)≤A)
    (hb : (∑l:L,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inr l) (.inl j)‖)≤B)
    (hbase : ‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i) (.inl j)‖≤C*ρ^D)
    (hfirst : ∀l,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i) (.inr l)‖≤C*ρ^(di l))
    (hsecond : ∀l,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inr l) (.inl j)‖≤C*ρ^(dj l))
    (hconvolution : (∑l:L,ρ^(di l+dj l))≤T*ρ^D) :
    ‖g.extensionGreen q z i j‖≤(C+‖p⁻¹‖*C^2*T)*ρ^D+2*‖p⁻¹‖^2*δ*A*B := by
  let M:=(g.attachLeaves (by omega) mate hrestore).extensionMatrix q z
  have hM:IsUnit M:=(g.attachLeaves (by omega) mate hrestore).extensionMatrix_isUnit hd q z hz hq
  have hcore:M.toBlocks₁₁=g.extensionMatrix q z:=
    g.attachLeaves_extensionMatrix_principal (by omega) mate hrestore q z
  have hc:IsUnit M.toBlocks₁₁:=hcore ▸ g.extensionMatrix_isUnit hd q z hz hq
  have hi:=scalar_diagonal_inverse_stability (M⁻¹).toBlocks₂₂ p hp
    (core_inverse_leaf_schur M hM hc).1 δ hδ herror hsmall
  have hh:=core_inverse_scalar_leaf_decay M hM hc i j p (2*‖p⁻¹‖^2*δ) A B C T ρ
    (by positivity) hA hB hC hρ D di dj ha hb hi hbase hfirst hsecond hconvolution
  rw [hcore] at hh
  exact hh

end DeficientGraph
end LocalLaw
