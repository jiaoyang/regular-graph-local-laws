import SpectralConsequences.ExteriorError

/-! # Realized exterior heights, window, branch and nominal-error bounds -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw

structure ExteriorSourceParameters (a b:ℝ) (d N:ℕ) (β M:ℝ) : Prop where
  size_positive : 0<N
  log_one : 1≤Real.log (N:ℝ)
  height_positive : 0<exteriorHeight β N
  height_one : exteriorHeight β N≤1
  window_positive : 0<edgeWindow β N
  window_one : edgeWindow β N≤1
  height_floor : Real.log (N:ℝ)^b/(N:ℝ)≤exteriorHeight β N
  mesh_margin : exteriorHeight β N≤edgeWindow β N/2
  mesh_width : M≤((N^2:ℕ):ℝ)*exteriorHeight β N
  error_cap : ∀E:ℝ,2+edgeWindow β N/2≤|E|→
    realSourcePaperError a d N (logarithmicRadius β d N)
      ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)≤(N:ℝ)^(-15*β/16)
  reference_cap : ∀E:ℝ,2+edgeWindow β N/2≤|E|→
    (kestenMcKayStieltjes d ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)).im≤(N:ℝ)^(-15*β/16)
  small_branch : ∀E:ℝ,2+edgeWindow β N/2≤|E|→
    realSourcePaperError a d N (logarithmicRadius β d N)
      ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)≤
        spectralScale ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)/Real.log (N:ℝ)
  reference_trace_small : ∀E:ℝ,2+edgeWindow β N/2≤|E|→
    ((N:ℝ)*exteriorHeight β N)*
      (kestenMcKayStieltjes d ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)).im≤1/16

theorem eventually_exterior_source_parameters (a b:ℝ) (d:ℕ) (β M:ℝ)
    (hd:3≤d) (hβ:0<β) (hβsmall:β≤1/128):
    ∀ᶠ N:ℕ in atTop,ExteriorSourceParameters a b d N β M := by
  let K:=(((d-1:ℕ):ℝ)+3)
  have hNlarge:∀ᶠ N:ℕ in atTop,M≤(N:ℝ):=
    (tendsto_natCast_atTop_atTop: Tendsto (fun N:ℕ=>(N:ℝ)) atTop atTop).eventually (eventually_ge_atTop M)
  filter_upwards [eventually_const_mul_log_rpow_le K (8*a+4) (β/16) (by linarith),
    eventually_const_mul_log_rpow_le 4 0 (1-29*β/8) (by linarith),
    eventually_const_mul_log_rpow_le 2 1 (7*β/8) (by linarith),
    eventually_const_mul_log_rpow_le 2 0 (1-25*β/16) (by linarith),
    eventually_const_mul_log_rpow_le 1 b (3*β/2) (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1,hNlarge,
    eventually_const_mul_log_rpow_le 16 0 (β/2) (by linarith)]
    with N herror hreference hbranch hmesh hfloor hL hN hNM htraceReference
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  have hη:0<exteriorHeight β N:=Real.rpow_pos_of_pos hNp _
  have hΔ:0<edgeWindow β N:=Real.rpow_pos_of_pos hNp _
  have hscale:=exterior_height_scale β N (by omega)
  have hη1:exteriorHeight β N≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hΔ1:edgeWindow β N≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  simp only[Real.rpow_zero,Real.rpow_one,mul_one,one_mul] at hreference hbranch hmesh hfloor htraceReference
  have hεcap:∀E:ℝ,2+edgeWindow β N/2≤|E|→
      realSourcePaperError a d N (logarithmicRadius β d N)
        ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)≤(N:ℝ)^(-15*β/16):=by
    intro E hE
    apply (realSourcePaperError_exterior_bound a d N β E hd hN hβsmall hL hE).trans
    have hh:=mul_le_mul_of_nonneg_right herror (Real.rpow_nonneg hNp.le (-β))
    calc
      _≤(N:ℝ)^(β/16)*(N:ℝ)^(-β):=hh
      _=_:=by rw [←Real.rpow_add hNp];congr 1;ring
  have hrefStrong:∀E:ℝ,2+edgeWindow β N/2≤|E|→
      (kestenMcKayStieltjes d ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)).im≤(N:ℝ)^(-2*β):=by
    intro E hE
    have hh:=kestenMcKayStieltjes_im_exterior d hd E (exteriorHeight β N) (edgeWindow β N/2) hη (by positivity) hE
    apply hh.trans
    have hid:exteriorHeight β N/(edgeWindow β N/2)^2=(N:ℝ)^(-1+13*β/8)*4:=by
      dsimp only[exteriorHeight,edgeWindow]
      rw [div_pow,←Real.rpow_mul_natCast hNp.le (-β/16) 2]
      have hpow:(N:ℝ)^(-1+3*β/2)/(N:ℝ)^((-β/16)*(2:ℕ))=(N:ℝ)^(-1+13*β/8):=by
        rw [←Real.rpow_sub hNp]
        congr 1
        push_cast
        ring
      calc
        _=((N:ℝ)^(-1+3*β/2)/(N:ℝ)^((-β/16)*(2:ℕ)))*4:=by
          rw [div_div_eq_mul_div]
          norm_num
          ring
        _=_:=by rw [hpow]
    rw [hid]
    have hh':=mul_le_mul_of_nonneg_left hreference (Real.rpow_nonneg hNp.le (-1+13*β/8))
    calc
      _≤(N:ℝ)^(-1+13*β/8)*(N:ℝ)^(1-29*β/8):=hh'
      _=_:=by rw [←Real.rpow_add hNp];congr 1;ring
  have href:∀E:ℝ,2+edgeWindow β N/2≤|E|→
      (kestenMcKayStieltjes d ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)).im≤(N:ℝ)^(-15*β/16):=by
    intro E hE
    exact (hrefStrong E hE).trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  refine ⟨by omega,hL,hη,hη1,hΔ,hΔ1,?_,?_,?_,hεcap,href,?_,?_⟩
  · apply (div_le_iff₀ hNp).mpr
    exact hfloor.trans_eq (by rw [←hscale];ring)
  · have hh:=mul_le_mul_of_nonneg_right hmesh hη.le
    have hid:(N:ℝ)^(1-25*β/16)*exteriorHeight β N=edgeWindow β N:=by
      dsimp only[exteriorHeight,edgeWindow]
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    rw [hid] at hh
    linarith
  · have hMscale:1≤(N:ℝ)*exteriorHeight β N:=by rw [hscale];exact Real.one_le_rpow hN1 (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hMscale hNp.le
    push_cast
    nlinarith only[hNM,hh]
  · intro E hE
    have hh:=mul_le_mul_of_nonneg_right hbranch (Real.rpow_nonneg hNp.le (-15*β/16))
    have hid:(N:ℝ)^(7*β/8)*(N:ℝ)^(-15*β/16)=edgeWindow β N:=by
      dsimp only[edgeWindow]
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    rw [hid] at hh
    have hs:=spectralScale_exterior_lower E (exteriorHeight β N) (edgeWindow β N) hη.le hE
    apply (le_div_iff₀ (by linarith:0<Real.log (N:ℝ))).mpr
    have he:=mul_le_mul_of_nonneg_right (hεcap E hE) (by linarith:0≤Real.log (N:ℝ))
    nlinarith only[hh,hs,he]
  · intro E hE
    calc
      _≤((N:ℝ)*exteriorHeight β N)*(N:ℝ)^(-2*β):=
        mul_le_mul_of_nonneg_left (hrefStrong E hE) (mul_nonneg hNp.le hη.le)
      _=(N:ℝ)^(-β/2):=by rw [hscale,←Real.rpow_add hNp];congr 1;ring
      _≤1/16:=by
        rw [show -β/2=-(β/2) by ring,Real.rpow_neg hNp.le]
        simpa only[one_div] using one_div_le_one_div_of_le (by norm_num:(0:ℝ)<16) htraceReference

end SpectralConsequences
