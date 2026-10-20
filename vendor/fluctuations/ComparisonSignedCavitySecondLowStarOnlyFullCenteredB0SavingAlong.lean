module

public import ComparisonSignedCavitySecondLowStarOnlyFullRawB0BudgetAlong
public import ComparisonSignedCavitySecondLowFullCenteredB0AmplitudeAlong
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def ActualSecondLowStarOnlyFullCenteredB0SavingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Couter Rmacro Cx : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(mid tail : List PositiveMass) (_hparts : as=mid++tail)
          (T : ClockTree (Spin (dim n)×Bool) (mid++tail))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (mid++tail).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          mid.length=retainedMassPrefixIndex (w n).star.val as →
          0 < mid.length → mid.length < U →
          NativePersistentLowForks mid.length mid.length U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*(W n) →
          (M n).xs ≤ x → x ≤ (W n) →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
          partitionPoint 0 as (mid.length) ≤ Cmass*(W n) →
          4*(W n) ≤ (M n).R (partitionPoint 0 as U) →
          (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,(M n).R (G.sourceLowMass e) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          (M n).R (partitionPoint 0 as (mid.length)) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*(M n).xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (mid++tail) U →
        let P:=(G.canonicalMinimumSource (M n) forms).restProduct
        let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
        let g:=nativeFreshAtSlot T 0 s mid.length
        let p0:=sourceMonomialScale x (W n) initial
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree
          (fun σ=>Pc (g.restRestrict σ)) [g.embed s,g.mark]/2| ≤
          eps n*(W n)*(M n).xs^2*p0

theorem actual_second_low_star_only_full_centered_B0_saving_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cm Cstar Crep : ℝ,0<Cm ∧ 0<Cstar ∧ 0<Crep ∧
      ActualSecondLowStarOnlyFullCenteredB0SavingOnEveryFinalNetAlong degree rBound Cmass Couter Rmacro Cx
        (fun n=>actualSecondLowFullCenteredB0Amplitude (M n) eta Temp Cf Couter Cstar 0 Cm Crep)
        dim M W w := by
  obtain ⟨CmA,CstarA,CrepA,hCmA,hCstarA,hCrepA,HA⟩:=actual_second_low_star_only_full_raw_B0_budget_along
    degree rBound Cmass Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCouter hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Cm0,Cstar0,Crep0,hCm0,hCstar0,hCrep0,H0⟩:=actual_second_low_star_only_full_raw_B0_budget_along
    0 rBound Cmass Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCouter hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^degree
  have hCmean:0<Cmean:=by dsimp [Cmean];positivity
  let Cm:=CmA+Cmean*Cm0
  let Cstar:=CstarA+Cmean*Cstar0
  let Crep:=CrepA+Cmean*Crep0
  have hCmRate:0<Cm:=by dsimp [Cm];positivity
  refine ⟨Cm,Cstar,Crep,hCmRate,by dsimp [Cstar];positivity,by dsimp [Crep];positivity,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HA,H0,hdim.eventually Hmean,Hsource,HW1] with n hnA hn0 hnmean hs hw1
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnA L us hus hStarNode hret hmesh,hn0 L us hus hStarNode hret hmesh,
    hnmean (M n) hs (hxsW.trans hw1) L us hus hret hmesh] with k hkA hk0 hkmean
  dsimp only at hkA hk0 hkmean ⊢
  intro mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hindex hmid hstar hpersistent hLeaves houter hxsx hxW hLOW hmass Hms Hhigh Hz Hrlow Hrs HCx Hdyadic
  rw [hparts] at hkmean houter Hms Hhigh Hz Hrlow Hrs ⊢
  let as:=mid++tail
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
  let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
  let g:=nativeFreshAtSlot T 0 s mid.length
  let p0:=sourceMonomialScale x (W n) initial
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
  let S:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2
  let V:=W n*Cerr*rho
  let R:=(dim n:ℝ)^(-eta)*W n*(M n).xs^2
  let B:=nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2
  let B0:=nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2
  let μ:=nativeOriginalRestTestExpectation (dim n) q U b h K T P
  have ho:MassOrdered 0 as:=by change MassOrdered 0 (mid++tail);rw [←hparts];exact finiteCutMasses_ordered us hus k
  have hx:0<x:=(M n).hxs.trans_le hxsx
  have hW:0<W n:=hx.trans_le hxW
  have hp0:0≤p0:=by dsimp [p0];unfold sourceMonomialScale;positivity
  have HCerr:0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have HM:|μ|≤Cmean*p0:=by
    simpa only [μ,Cmean,P,p0,q,b,h,K,as,mul_assoc] using hkmean U T hLeaves G forms initial x (W n) hxsx hxW hmass
  have HP:|B|≤CstarA*S*p0+CmA*V*p0+CrepA*R*p0:=by
    have HH:=hkA mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
      hindex hmid hstar hpersistent hLeaves (by simpa only [hparts] using houter) hxsx hxW hLOW hmass
      (by simpa only [hparts] using Hms) (by simpa only [hparts] using Hhigh) (by simpa only [hparts] using Hz)
      (by simpa only [hparts] using Hrlow) (by simpa only [hparts] using Hrs) HCx Hdyadic
    simpa only [B,S,V,R,P,p0,Cerr,rho,q,b,h,K,g,as,hparts,mul_assoc] using HH
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hp0:sourceMonomialScale x (W n) (∅:Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product];exact Fin.prod_univ_zero _
  have H1:|B0|≤Cstar0*S+Cm0*V+Crep0*R:=by
    have HH:=hk0 mid tail hparts T G0 Fin.elim0 ∅ s U hU x sourceMass hsourceMass
      hindex hmid hstar hpersistent hLeaves (by simpa only [hparts] using houter) hxsx hxW
      (fun e=>e.elim0) (fun e=>e.elim0) (by simpa only [hparts] using Hms)
      (by simpa only [hparts] using Hhigh) (by simpa only [hparts] using Hz)
      (fun e=>e.elim0) (by simpa only [hparts] using Hrs) HCx Hdyadic
    have HP0:(G0.canonicalMinimumSource (M n) Fin.elim0).restProduct=(fun _=>1):=by
      funext σ;simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    rw [HP0] at HH
    simp only [Hp0,mul_one] at HH
    simpa only [B0,S,V,R,Cerr,rho,q,b,h,K,g,as,hparts,mul_assoc] using HH
  have Hcenter:nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun σ=>Pc (g.restRestrict σ))
      [g.embed s,g.mark]/2=B-μ*B0:=by
    dsimp only [Pc,nativeOriginalCenteredRestTest,B,B0,μ]
    rw [native_second_low_joint_ledger_sub_const]
    ring
  have HB:|nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun σ=>Pc (g.restRestrict σ))
      [g.embed s,g.mark]/2|≤Cstar*S*p0+Cm*V*p0+Crep*R*p0:=by
    rw [Hcenter,sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg,abs_mul]
    apply (add_le_add HP (mul_le_mul HM H1 (abs_nonneg _) (mul_nonneg hCmean.le hp0))).trans_eq
    dsimp only [Cm,Cstar,Crep]
    ring
  have Hrho:rho≤((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
    dsimp [rho]
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 (M n).hxs.ne')]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
  have HR:=mul_le_mul_of_nonneg_left Hrho (mul_nonneg (mul_nonneg (mul_nonneg hCmRate.le hW.le) HCerr) hp0)
  apply HB.trans
  dsimp only [actualSecondLowFullCenteredB0Amplitude,actualHistorySecondLowFreshReplacementAmplitude]
  convert add_le_add_left HR (Cstar*S*p0+Crep*R*p0) using 1 <;>
    dsimp only [S,V,R,Cerr,rho,p0,q,b,h,K,as,P,Pc,g] <;> ring_nf

end OAI.SKFluctuations.Cavity
