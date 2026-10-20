module

public import ComparisonSignedCavitySecondLowFullCenteredB0ModulusAlong
public import ComparisonActualHighOnlyLowB0CenteredReplacementConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0AmplitudeSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
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
theorem actual_second_low_full_centered_B0_modulus_along_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (a rBound : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
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
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Ci Cm Csaved Cstar Crep : ℝ,0<Ci ∧ 0<Cm ∧ 0<Csaved ∧ 0<Cstar ∧ 0<Crep ∧
      ActualSecondLowFullCenteredB0ModulusOnEveryFinalNetAlong_high_only a rBound Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci
        (fun n=>actualSecondLowFullCenteredB0Amplitude_high_only (M n) eta Temp Cf Couter Cstar Csaved Cm Crep)
        dim M W w := by
  obtain ⟨Ci,Cm,Csaved,Cstar,hCi,hCmRate,hCsaved,hCstar,Hmod⟩:=
    actual_second_low_centered_fresh_B0_modulo_c_replacement_budget_along_high_only a rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta.le hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Crep,hCrep,Hrep⟩:=
    eventually_actual_minimum_inherited_second_low_centered_occupied_c_replacement_budget_along_high_only
      (D:=D) a rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨Ci,Cm,Csaved,Cstar,Crep,hCi,hCmRate,hCsaved,hCstar,hCrep,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have HWmacro:=hWlim.eventually (eventually_le_nhds (by linarith : (0:ℝ)<Rmacro/2))
  filter_upwards [Hmod,Hrep,Hsource,Hcompare,HW1,HWmacro,Hcutoff] with n hnM hnR hs hc hw1 hmacroW hnCutoff
  have hxsW:(M n).xs≤W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hWdef:W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=by
    rw [hcanonical];rfl
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnM L us hus hStarNode hret hmesh,
    hnR (M n) hnCutoff.1 hnCutoff.2 hs (hxsW.trans hw1) hc L us hus hret hmesh] with k hkM hkR
  dsimp only at hkM hkR ⊢
  rw [←hWdef] at hkR
  intro pre mid tail hparts T G forms initial s U hU V x sourceMass hsourceMass
    hstarEq hmid hV hiV hVstar hstarU hpersistent hLeaves hcut houter hxsx hxW hLOW hmass
    Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  rw [hparts] at hkM hkR hstarEq hcut houter Hmi Hms Hhigh Hz Hrlow Hri Hrs ⊢
  rw [←hstarEq] at hkM
  let as:=pre++(mid++tail)
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
  let p0:=sourceMonomialScale x (W n) initial
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
    partitionPoint 0 as U/(dim n+1:ℕ)
  have ho:MassOrdered 0 as:=by
    change MassOrdered 0 (pre++(mid++tail))
    rw [←hparts]
    exact finiteCutMasses_ordered us hus k
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hp0:0≤p0:=by
    have hx:0<x:=(M n).hxs.trans_le hxsx
    dsimp [p0];unfold sourceMonomialScale;positivity
  have HWU:W n≤(M n).R (partitionPoint 0 as U):=by linarith [Hhigh,hW]
  have HRstar:(M n).R (partitionPoint 0 as (pre.length+mid.length))≤(M n).R (partitionPoint 0 as U)/2:=by
    have HH:=Hrs.trans (min_le_left _ _)
    linarith [Hhigh,hW]
  have HZhalf:(M n).z≤(M n).R (partitionPoint 0 as U)/2:=by
    have HH:=Hz.trans (min_le_left _ _)
    linarith [Hhigh,hW]
  have HB:=hkM pre.length V U T hU hV hiV hVstar hstarU hpersistent hcut hLeaves houter HWU HRstar HZhalf
    G forms initial x hxsx hxW hmass s
  have HR:=hkR pre mid tail rfl T G forms initial s U hU x sourceMass hsourceMass
    hmid hstarU hpersistent hLeaves hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  change |nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s
    (pre.length+mid.length) hU Pc|≤_ at HB
  change |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
    (pre.length+mid.length) hU Pc|≤Crep*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0 at HR
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have HC:|χ^2|≤1:=by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg χ) (native_second_low_original_chi_abs_le_one ho U K) 2).trans_eq (by norm_num)
  have HCR:|χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
      (pre.length+mid.length) hU Pc|≤Crep*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0:=by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right HC (abs_nonneg _)).trans ((one_mul _).le.trans HR)
  have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
  have Hrho:rho≤((M n).actualOriginalLowErrorDensitySaving (Couter+1)+
      (1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
    dsimp [rho]
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 (M n).hxs.ne')]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
  have Hr:=mul_le_mul_of_nonneg_left Hrho
    (mul_nonneg (mul_nonneg (mul_nonneg hCmRate.le hW.le) HCerr) hp0)
  let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
  have HA:|nativeSecondLowJointLedger (dim n) q U b h K g.tree
      (fun σ=>Pc (g.restRestrict σ)) [g.embed s,g.mark]/2|≤
      |nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s
        (pre.length+mid.length) hU Pc|+
      |χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
        (pre.length+mid.length) hU Pc|:=by
    convert abs_add_le (nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s
      (pre.length+mid.length) hU Pc)
      (χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
        (pre.length+mid.length) hU Pc) using 1
    dsimp only [nativeSecondLowFreshB0MinusCReplacementSource,g,χ,as]
    ring_nf
  apply HA.trans ((add_le_add HB HCR).trans ?_)
  dsimp only [actualSecondLowFullCenteredB0Amplitude_high_only,actualHistorySecondLowFreshReplacementAmplitude_high_only]
  convert add_le_add_left Hr
    (Ci*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
      Cstar*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0+
      Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0+
      Crep*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0) using 1 <;>
    dsimp only [Pc,P,p0,Cerr,di,rho,q,b,h,K,as] <;> ring_nf

end OAI.SKFluctuations.Cavity
