module

public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry
public import ComparisonSignedCavitySecondLowFullCenteredB0AmplitudeAlong
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail) →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(V U k : ℕ) (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (_hU : U ≤ (pre++(mid++tail)).length)
      (seed : List NativeResourceMark) (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P → P.resources.length ≤ degree →
      0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → pre.length+mid.length < U → T.leaves ≤ rBound →
      partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*W n →
    ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      4*W n ≤ (M n).R (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as pre.length) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    |((W n)⁻¹)^k*nativeActualOriginalCenteredResourceB0 (M n) U P| ≤
      |P.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

theorem actual_second_low_actual_history_full_resource_B0_modulus_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0) (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  classical
  obtain ⟨Cf,hCf,HS⟩:=actual_selected_bad_history_small_source_clocks hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
  have HP (a : Fin (degree+1)):=actual_second_low_full_centered_B0_modulus_along a.val rBound
    Cmass Ccut Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCcut hCouter hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim M W hcanonical hWlim w HS Hcompare hw
  choose Ci Cm Csaved Cstar Crep hCi hCmRate hCsaved hCstar hCrep HC using HP
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget (D:=D)
    (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let CI:=1+∑a,Ci a
  have hCI : 0 < CI:=by
    have HH : 0 ≤ ∑a : Fin (degree+1),Ci a:=Finset.sum_nonneg (fun a _=>(hCi a).le)
    dsimp only [CI];linarith
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  let amp:=fun a n=>actualSecondLowFullCenteredB0Amplitude (M n) eta Temp Cf Couter (Cstar a) (Csaved a) (Cm a) (Crep a)
  have hamp a n : 0 ≤ amp a n:=actual_second_low_full_centered_B0_amplitude_nonneg (M n) eta Temp Cf Couter _ _ _ _
    hTemp hCouter (hCstar a).le (hCsaved a).le (hCmRate a).le (hCrep a).le
  let eps:=fun n=>A^degree*∑a,amp a n
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE];exact hWlim
  have Hamp a : Tendsto (amp a) atTop (𝓝 0):=actual_second_low_full_centered_B0_amplitude_tendsto_zero_along heta hm hdelta hroom
    hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hCouter dim hdim root M epsilon shell hb hh Hhistory Hcompare HL
  have Heps : Tendsto eps atTop (𝓝 0):=by
    have HH:=(tendsto_finsetSum Finset.univ (fun a _=>Hamp a)).const_mul (A^degree)
    simpa only [Finset.sum_const_zero,mul_zero] using HH
  refine ⟨Cf,A^degree*CI,hCf,by positivity,HS,eps,?_,Heps,?_⟩
  · intro n
    exact mul_nonneg (pow_nonneg hA0.le _) (Finset.sum_nonneg (fun a _=>hamp a n))
  · have HX : ∀ᶠn in atTop,(M n).xs ≤ 1:=by
      filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with n hn
      rw [hcanonical n] at hn
      exact (M n).canonical_direct_test_band_ge_scale.trans hn
    filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA,HS,HX] with n hnC hnA hnS hnX
    intro L us hus hstar hret hmesh
    filter_upwards [Filter.eventually_all.mpr (fun a : Fin (degree+1)=>hnC a L us hus hstar hret hmesh),
      hnA (M n) hnS hnX L us hus hret hmesh] with jGrid hgC hgA
    dsimp only at hgC hgA ⊢
    intro pre mid tail hparts hindex V U k T hU seed P hP hdegree hmid hV hiV hVstar hs hT hcut houter
      x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
    have Hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus Hnodes
      jGrid U (by simpa only [hparts] using hU) HsourceMass
    rw [hparts] at hgC hgA hindex hcut houter hmi hms Hhigh Hz Hri Hrs Hdyadic ⊢
    let as:=pre++(mid++tail)
    have hi : pre.length ≤ pre.length+mid.length:=by omega
    have hstar : pre.length+mid.length < as.length:=hs.trans_le hU
    have hdepth : seed.length+k ≤ degree:=by rw [←hP.total_factor_depth];exact hdegree
    have hLive : P.live.factors.length ≤ degree:=by
      have HH : P.live.tags.length ≤ P.resources.length:=by simp only [NativeResourceTerm.resources,List.length_append];omega
      simp only [NativeResourceMonomial.tags,List.length_map] at HH
      exact HH.trans hdegree
    let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
    let G:=nativeActualResourceCanonicalShape P.live hi hstar
    let initial:=nativeActualResourceInitialFactors P.live
    let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
    let AI:=partitionPoint 0 as U*(M n).xs*Cerr*
      (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))
    let AX:=W n*(M n).xs^2
    let price:=Ci a*AI+amp a n*AX
    have ho:MassOrdered 0 as:=by
      dsimp only [as]
      rw [←hparts]
      exact finiteCutMasses_ordered us hus jGrid
    have hxs0 : 0 < (M n).xs:=(M n).hxs
    have hx0 : 0 < x:=hxs0.trans_le hx
    have hW : 0 < W n:=hx0.trans_le hxW
    have hmassU : 0 ≤ partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
    have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
    have hdi : 0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length:=Real.sqrt_nonneg _
    have hAI : 0 ≤ AI:=by dsimp only [AI];positivity
    have hAX : 0 ≤ AX:=by dsimp only [AX];positivity
    have hprice : 0 ≤ price:=add_nonneg (mul_nonneg (hCi a).le hAI) (mul_nonneg (hamp a n) hAX)
    have Hbare:=hgC a pre mid tail rfl T G (fun _=>NativeSourceFactorForm.centered) initial P.live.test.target U hU V
      x sourceMass hsourceMass hindex hmid hV hiV hVstar hs (hP.persistentLowForks hi) hT hcut houter hx hxW
      (native_actual_resource_canonical_factors_LOW P.live hi hs hU)
      (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x (W n) hmi hms)
      (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms Hhigh Hz
      (native_actual_resource_canonical_source_radius_gate (M n) P.live hi hstar _ Hri Hrs) Hri Hrs HCx Hdyadic
    rw [native_actual_resource_live_scale_eq_annotations] at Hbare
    have Hpair:=hgA U pre.length (pre.length+mid.length) T P (hdegree.trans (by omega))
      (hi.trans hstar.le) hstar.le x (W n) hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
    have HB:=actual_resource_full_B0_normalized_profile_le (M n) hP hdepth ho hi hstar hA hx hxW hprice Hpair
      (by
        dsimp only
        rw [show nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as=
          (fun j=>(M n).hf (partitionPoint 0 as j)+(M n).bf (partitionPoint 0 as j)*
            orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)) by rfl]
        unfold nativeSecondLowFreshFullB0Source
        dsimp only
        convert Hbare using 1; dsimp only [AI,AX,price,amp,Cerr,as]; ring)
    have HCi : Ci a ≤ CI:=by
      have HH:=Finset.single_le_sum (fun a _=>(hCi a).le) (Finset.mem_univ a)
      dsimp only [CI];linarith
    have Hsum : amp a n ≤ ∑b,amp b n:=Finset.single_le_sum (fun b _=>hamp b n) (Finset.mem_univ a)
    have HD:=add_le_add (mul_le_mul_of_nonneg_right HCi hAI) (mul_le_mul_of_nonneg_right Hsum hAX)
    have hscale : 0 ≤ nativeResourceScale x (W n) 1 seed:=(actual_resource_raw_scale_pos seed hx0 hW).le
    apply HB.trans
    have HH:=mul_le_mul_of_nonneg_left HD
      (show 0 ≤ |P.coefficient| *A^degree*nativeResourceScale x (W n) 1 seed by positivity)
    convert HH using 1; dsimp only [AI,AX,price,eps,Cerr]; ring

end OAI.SKFluctuations.Cavity
