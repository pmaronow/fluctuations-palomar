module

public import ComparisonSignedCavityActualTargetInitialFourAlong
public import ComparisonSignedCavityActualNaturalFourTerminalAlong
public import ComparisonSignedCavityActualHistorySquareResourceAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def ActualTargetInitialResidualApproxAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (saving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1) → (w n).star∈us → (∀u∈uniformMasses Lnet,u∈us) →
    ((Lnet+1:ℕ):ℝ)⁻¹≤(M n).xs →∀ᶠjGrid : ℕ in atTop,
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U i : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U≤as.length),
    ∀x : ℝ,(M n).xs≤x → x≤W n → partitionPoint 0 as i≤Cmass*x →
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |nativeActualTargetLongitudinalResponse (M n) as i U-
        nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]|≤
        3*((dim n+1:ℕ):ℝ)^(-saving)*x^3

theorem exists_actual_same_star_initial_residual_approx_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs gamma : ℝ}
    (hm : 0 < m) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hTemp : 0≤Temp) (hTstar : 0 < Tstar) (hgamma : 0 < gamma) (Cmass : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp)
    (hroot : ∀ᶠn in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n))
    (Hp : ∀degree : ℕ,0<degree →∃A : ℝ,1≤A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0<threshold ∧∃saving : ℝ,0<saving ∧∀depth : ℕ,threshold≤depth →
      ActualTargetInitialResidualApproxAlong depth saving Cmass M W w := by
  let c:=starMassBandConstant cu Az/cu
  let cK:=3*Tstar*c/8
  have hc : 0<c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hcK : 0<cK:=by dsimp only [cK];positivity
  have Hclock : ∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hlo,_,_⟩:=hn.1
    exact hlo
  obtain ⟨threshold,hthreshold,saving,hsaving,Hterminal⟩:=
    exists_actual_original_continuum_natural_centered_four_G_terminal_decay_of_pair_budgets_of_eventual_total_clock_along
      hm hC0 hTemp hgamma hcK Cmass dim hdim M W hxs hWlim htotal w Hclock Hp
  have Hfrozen:=hdim.eventually (eventually_actual_inherited_initial_frozen_response_cubic
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    Bclock Temp hTemp hm hC0)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨threshold,hthreshold,min m saving,lt_min hm hsaving,?_⟩
  intro depth hdepth
  filter_upwards [Hterminal depth hdepth,Hfrozen,htotal,hroot,HW,Hclock] with n hnT hnF ht hr hw1 hnK
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hnT Lnet us hus hstar hret hmesh,
    hnF (M n) ht hr ((hxs n).trans hw1) us hus] with jGrid hjT hjF
  dsimp only at hjT hjF ⊢
  intro U i hi hs hU x hxsx hxW hmass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW:=(M n).hxs.trans_le (hxs n)
  have hx:=(M n).hxs.trans_le hxsx
  have hK : 0<nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star := by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us jGrid hstar)]
    exact (mul_pos hcK hW).trans_le hnK
  have HE:=actual_target_response_eq_four_iteration (M n) as (W n) i star U hi hs hU ho hW.ne' hK depth
  dsimp only at HE
  have HF:=hjF i star U (hi.trans (hs.le.trans hU)) (W n) x hxsx
  have HT:=hjT U i hi hs hU x hxsx hxW hmass
  have hN : (1:ℝ)≤(dim n+1:ℕ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n))
  have H1:=Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_left m saving))
  have H2:=Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right m saving))
  have Hscale : (M n).xs^2*x≤x^3 := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (M n).hxs.le hxsx 2) hx.le]
  have HF' := HF.trans (mul_le_mul_of_nonneg_right H1 (pow_nonneg hx.le 3))
  have HT' : |nativeActualOriginalContinuumCenteredFourGFrontier (M n) as (W n) i star U hi hs hU depth|≤
      2*((dim n+1:ℕ):ℝ)^(-min m saving)*x^3 := by
    apply HT.trans
    have H:=mul_le_mul H2 Hscale (by positivity : (0:ℝ)≤(M n).xs^2*x)
      (Real.rpow_nonneg (by positivity) (-min m saving))
    have H':=mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2)
    convert H' using 1 <;> ring
  rw [HE]
  rw [show nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier (M n) as (W n) i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse (M n) U (W n) st.freeze-
      nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]=
      nativeActualOriginalContinuumCenteredFourGFrontier (M n) as (W n) i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse (M n) U (W n) st.freeze by ring]
  have H:=(abs_sub _ _).trans (add_le_add HT' HF')
  exact H.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
