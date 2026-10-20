module

public import ComparisonSignedCavitySecondLowActualConstantResourceStarOnlyB0SavingAlong
public import ComparisonSignedCavitySecondLowActualConstantResourceStarOnlyHalfB0SavingAlong
public import ComparisonSignedCavitySecondLowActualConstantChildStarOnlyB0CategoryAlong
public import ComparisonActualHighOnlyLowB0FullCenteredSourceAlong
public import ComparisonActualHighOnlyLowB0ResourceReadoutSourceAlong
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlyLowB0ConstantResourceInterfacesSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
theorem actual_inherited_constant_resource_star_only_full_B0_saving_along_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualConstantResourceStarOnlyFullB0SavingOnEveryFinalNetAlong_high_only degree rBound Cmass Couter Rmacro Cx
        eps dim M W w := by
  classical
  have HP (a : Fin (degree+1)):=actual_second_low_star_only_full_centered_B0_saving_along_high_only
    a.val rBound Cmass Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCouter hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  choose Cm Cstar Crep hCmRate hCstar hCrep HC using HP
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_high_only (D:=D)
    (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  let amp:=fun a n=>actualSecondLowFullCenteredB0Amplitude_high_only (M n) eta Temp Cf Couter (Cstar a) 0 (Cm a) (Crep a)
  have hamp a n : 0 ≤ amp a n:=actual_second_low_full_centered_B0_amplitude_nonneg_high_only (M n) eta Temp Cf Couter _ 0 _ _
    hTemp hCouter (hCstar a).le (le_refl 0) (hCmRate a).le (hCrep a).le
  let eps:=fun n=>A^degree*∑a,amp a n
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE];exact hWlim
  have Hamp a : Tendsto (amp a) atTop (𝓝 0):=actual_second_low_star_only_full_B0_amplitude_regular_tendsto_zero_along_high_only
    heta hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hCouter dim hdim M Hcompare HL Hclock Homit Hcutoff
  have Heps : Tendsto eps atTop (𝓝 0):=by
    have H:=(tendsto_finsetSum Finset.univ (fun a _=>Hamp a)).const_mul (A^degree)
    simpa only [Finset.sum_const_zero,mul_zero] using H
  refine ⟨eps,?_,Heps,?_⟩
  · intro n
    exact mul_nonneg (pow_nonneg hA0.le _) (Finset.sum_nonneg (fun a _=>hamp a n))
  · have HX : ∀ᶠn in atTop,(M n).xs ≤ 1:=by
      filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),Hcutoff] with n hn hnCutoff
      rw [hcanonical n] at hn
      exact (M n).canonical_direct_test_band_ge_scale.trans hn
    filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA,Hsource,HX,Hcutoff] with n hnC hnA hnS hnX hnCutoff
    intro L us hus hstar hret hmesh
    filter_upwards [Filter.eventually_all.mpr (fun a : Fin (degree+1)=>hnC a L us hus hstar hret hmesh),
      hnA (M n) hnCutoff.1 hnCutoff.2 hnS hnX L us hus hret hmesh] with jGrid hgC hgA
    dsimp only at hgC hgA ⊢
    intro mid tail hparts hindex U k T hU P hP hdegree hmid hs hT houter hms Hhigh Hz Hrs
      sourceMass hsourceMass HCx HsourceMass Hnodes
    have Hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus Hnodes
      jGrid U (by simpa only [hparts] using hU) HsourceMass
    rw [hparts] at hgC hgA hindex houter hms Hhigh Hz Hrs Hdyadic
    let as:=mid++tail
    have hi : 0 ≤ mid.length:=Nat.zero_le _
    have hstar : mid.length < as.length:=hs.trans_le hU
    have hdepth : ([] : List NativeResourceMark).length+k ≤ degree:=by simpa only [List.length_nil,zero_add] using hdegree
    have Hdegree : P.resources.length ≤ degree:=by rw [hP.total_factor_depth];simpa using hdegree
    have hLive : P.live.factors.length ≤ degree:=by
      have HH : P.live.tags.length ≤ P.resources.length:=by simp only [NativeResourceTerm.resources,List.length_append];omega
      simp only [NativeResourceMonomial.tags,List.length_map] at HH
      exact HH.trans Hdegree
    let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
    let G:=nativeActualResourceCanonicalShape P.live hi hstar
    let initial_high_only:=nativeActualResourceInitialFactors P.live
    let price:=amp a n*W n*(M n).xs^2
    have ho:MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
    have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
    have hW : 0 < W n:=(M n).hxs.trans_le hxW
    have hprice : 0 ≤ price:=by dsimp only [price];exact mul_nonneg (mul_nonneg (hamp a n) hW.le) (sq_nonneg _)
    have Hbare:=hgC a mid tail rfl T G (fun _=>NativeSourceFactorForm.centered) initial_high_only P.live.test.target U hU
      (M n).xs sourceMass hsourceMass
      hindex hmid hs (hP.constant_persistentLowForks rfl hs) hT
      houter le_rfl hxW
      (by intro e;rw [native_actual_constant_resource_canonical_factor_split_star hP hi hstar];exact hs)
      (native_actual_constant_resource_canonical_source_mass hP hi hstar Cmass (M n).xs (W n) hms)
      hms Hhigh Hz
      (native_actual_constant_resource_canonical_source_radius_gate_high_only (M n) hP hi hstar _ Hrs)
      Hrs HCx Hdyadic
    rw [native_actual_resource_live_scale_eq_annotations] at Hbare
    have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
      simp only [partitionPoint,partitionValues_zero,id_eq]
      exact mul_nonneg hCm (M n).hxs.le
    have Hpair:=hgA U 0 mid.length T P (Hdegree.trans (by omega)) (hi.trans hstar.le) hstar.le
      (M n).xs (W n) le_rfl hxW Hmi hms 1 1 (by norm_num) (by norm_num)
    have HB:=actual_resource_full_B0_normalized_profile_le_high_only (M n) hP hdepth ho hi hstar hA le_rfl hxW hprice Hpair
      (by
        dsimp only
        rw [show nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as=
          (fun j=>(M n).hf (partitionPoint 0 as j)+(M n).bf (partitionPoint 0 as j)*
            orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)) by rfl]
        unfold nativeSecondLowFreshFullB0Source
        dsimp only
        convert Hbare using 1; dsimp only [price,amp,as]; ring)
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at HB
    have Hsum : amp a n ≤ ∑b,amp b n:=Finset.single_le_sum (fun b _=>hamp b n) (Finset.mem_univ a)
    apply HB.trans
    have H:=mul_le_mul_of_nonneg_right Hsum
      (show 0 ≤ |P.coefficient| *A^degree*W n*(M n).xs^2 by positivity)
    convert H using 1 <;> (try dsimp only [price,eps]) <;> ring

end OAI.SKFluctuations.Cavity
