module

public import ComparisonSignedCavitySecondLowActualHistoryFullWeightedForestB0ModulusAlong
public import ComparisonSignedCavityActualStrongSharpSourceCutReadout
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualBoundarySchedule

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_initial_successor_low_cut_mass_le
    {A xs : ℝ} {us : List PositiveMass} (hus : ∀u∈us,u.val ≤ 1)
    {jGrid i : ℕ} (hmesh : ((jGrid+1:ℕ):ℝ)⁻¹ ≤ xs)
    (hmi : partitionPoint 0 (finiteCutMasses us jGrid) i ≤ A*xs) :
    partitionPoint 0 (finiteCutMasses us jGrid) (i+1) ≤ (A+1)*xs := by
  have H:=partitionPoint_step_le_mesh (finiteCutMasses us jGrid)
    (finiteCutMasses_mesh us hus jGrid) (by positivity) i
  nlinarith

def ActualInitialFullB0OnStrongGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        let old:=pre++(mid++tail)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
            [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
          .secondLow|/(chi*K (pre.length+mid.length)) ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

theorem actual_selected_bad_history_initial_full_b0_on_strong_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFullB0OnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  let F:=max (1+2*cu) (1+1/Rmacro)
  obtain ⟨Cf,Ci,hCf,hCi,Hsource,eps,heps,hepslim,HB⟩:=
    actual_second_low_actual_history_full_weighted_forest_B0_modulus_along
      (eta:=m) 1 0 2 depth A (A+1) A Ccal Rmacro F Cx cK hcK hCx hTemp hA0.le
      (by positivity) hA0.le hCcal hm hm hdelta hroom (by linarith) hcl hcu hAz hC0 hCt
      hmacro hRhalf (le_max_left _ _) (le_max_right _ _) hc0 hmargin hcapmargin
      dim hdim root M epsilon shell hepsilon hb hh Hhistory W hcanonical hWlim w hcompare hw
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cout:=Ci*A*Cerr/Cd+1
  let err n:=eps n/Cd
  have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCout : 0 < Cout:=by dsimp only [Cout];positivity
  have herr n : 0 ≤ err n:=div_nonneg (heps n) hCd.le
  have errlim : Tendsto err atTop (𝓝 0):=by
    simpa only [err,zero_div] using hepslim.div_const Cd
  refine ⟨Cout,hCout,err,herr,errlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HB,Hcuts,Hsource,HW] with n hn hcuts hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx0 : 0 < (M n).xs:=(M n).hxs
  have herrn : 0 ≤ err n:=herr n
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (eventually_le_nhds (M n).hxs)
  filter_upwards [hn L us hus hstar hret hmesh,Hmesh] with jGrid hj hmeshFine
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  obtain ⟨_,_,_,_,Hhighmass,_,Hfour,HstarR,Hz,HCx,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have Hlow : partitionPoint 0 as (pre.length+1) ≤ (A+1)*(M n).xs:=
    actual_initial_successor_low_cut_mass_le hus hmeshFine hmi
  have Hri:=hcuts.finite_net_initial_radius_gap us hus hstar hhigh jGrid pre.length
    (by rw [←hindex];omega)
  have Hraw:=hj pre mid tail hcut.symm hindex (pre.length+1) U HU [.initial] st hP (by simp) rfl
    (nativeActualInitialState_leaves_le old i star seedMass (hi.trans (HI.le.trans HU)))
    hmid (by omega) (by omega) (by omega) HI Hlow Hupper
    (M n).xs (high n).val (high n).property le_rfl hxW hmi
    (by simpa only [hindex] using Hmass) Hfour Hz Hri (by simpa only [hindex] using HstarR)
    (by simpa only [Hhighmass] using HCx) Hhighmass hnodes (by simpa only [hindex] using HstarK)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] at Hraw
  have ho' : MassOrdered 0 old:=by dsimp only [old];rw [hcut];exact ho
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old star:=by
    dsimp only [old,star];rw [hcut,hindex];exact HstarK
  obtain ⟨hden,_,Hden⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsClocks (hxW.trans hW1) hW hcK ho' HI HU HK
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have hDi : 0 ≤ Di:=by dsimp only [Di,nativeOriginalCutLowErrorRadius];positivity
  change 0 < chi*K star at hden
  change Cd*W n ≤ chi*K star at Hden
  change |nativeActualFourOtherCategorySum (M n) U (W n)
    (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth [st]) .secondLow|/(chi*K star) ≤
      Cout*(M n).xs^2*Di+err n*(M n).xs^3
  apply (div_le_iff₀ hden).2
  apply Hraw.trans
  have Hmass:=mul_le_mul_of_nonneg_left Hupper
    (show 0 ≤ Ci*Cerr*(M n).xs^2*Di by positivity)
  have Hcoef : Ci*A*Cerr/Cd ≤ Cout:=by dsimp only [Cout];linarith
  have HC:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Hcoef (sq_nonneg (M n).xs)) hDi
  have HC':=mul_le_mul_of_nonneg_right (add_le_add HC (le_refl (err n*(M n).xs^3)))
    (show 0 ≤ Cd*W n by positivity)
  have HD:=mul_le_mul_of_nonneg_left Hden
    (show 0 ≤ Cout*(M n).xs^2*Di+err n*(M n).xs^3 by positivity)
  apply le_trans ?_ HD
  apply le_trans ?_ HC'
  calc
    _=(Ci*Cerr*(M n).xs^2*Di)*partitionPoint 0 as U+eps n*W n*(M n).xs^3:=by
      dsimp only [Cerr,Di,as]
      ring
    _ ≤ (Ci*Cerr*(M n).xs^2*Di)*(A*W n)+eps n*W n*(M n).xs^3:=
      add_le_add Hmass le_rfl
    _ = _:=by dsimp only [err];field_simp [hCd.ne']

end OAI.SKFluctuations.Cavity
