module

public import ComparisonSignedCavitySecondLowStarOnlyFullRawB0BudgetAlong
public import ComparisonSignedCavitySecondLowStarOnlyFullCenteredB0SavingAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0ModuloUnweightedSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0UnobservedPhysicalSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0AmplitudeSourceAlong
public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedOccupiedCReplacementBudgetAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
def ActualSecondLowStarOnlyFullRawB0BudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Couter Rmacro Cx Cerr Cmoving Cstar Crep : ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(mid tail : List PositiveMass) (_hparts : as=mid++tail)
          (T : ClockTree (Spin (dim n)×Bool) (mid++tail))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial_original_q : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (mid++tail).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          mid.length=retainedMassPrefixIndex (w n).star.val as →
          0 < mid.length → mid.length < U →
          NativePersistentLowForks mid.length mid.length U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*(W n) →
          (M n).xs ≤ x → x ≤ (W n) →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial_original_q e) →
          partitionPoint 0 as (mid.length) ≤ Cmass*(W n) →
          4*(W n) ≤ (M n).sweepRadius (partitionPoint 0 as U) →
          (M n).z ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,(M n).sweepRadius (G.sourceLowMass e) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          (M n).sweepRadius (partitionPoint 0 as (mid.length)) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*(M n).xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (mid++tail) U →
        let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
        let g:=nativeFreshAtSlot T 0 s mid.length
        let p0:=sourceMonomialScale x (W n) initial_original_q
        let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree
          (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2| ≤
          Cstar*((dim n+1:ℕ):ℝ)^(-saving)*(W n)*(M n).xs^2*p0+
          Cmoving*(W n)*Cerr*rho*p0+
          Crep*(dim n:ℝ)^(-eta)*(W n)*(M n).xs^2*p0

theorem actual_second_low_star_only_full_raw_B0_budget_along_original_q
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cm Cstar Crep : ℝ,0<Cm ∧ 0<Cstar ∧ 0<Crep ∧
      ActualSecondLowStarOnlyFullRawB0BudgetOnEveryFinalNetAlong_original_q degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cm Cstar Crep dim M W w := by
  obtain ⟨Cm,Cobs,hCmRate,hCobs,Hmod⟩:=actual_second_low_star_only_fresh_B0_modulo_unweighted_budget_along_original_q
    degree rBound Cmass Couter Ccal hTemp hCf hCm hCouter hCcal heta.le
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Cbase,hCbase,Hbase⟩:=actual_second_low_star_occupied_old_c_baseline_budget_along_original_q
    degree rBound Cmass Couter hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  obtain ⟨Crep,hCrep,Hrep⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨Cm,16+Cbase,Cobs+Crep,hCmRate,by positivity,add_pos hCobs hCrep,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have HWmacro:=hWlim.eventually (eventually_le_nhds (by linarith : (0:ℝ)<Rmacro/2))
  filter_upwards [Hmod,Hbase,Hrep,Hsource,Hcompare,HW1,HWmacro,Hcutoff] with n hnM hnB hnR hs hc hw1 hmacroW hnCutoff
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have hWdef:W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)):=by
    rw [hcanonical];rfl
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnM L us hus hStarNode hret hmesh,hnB L us hus hStarNode hret hmesh,
    hnR (M n) hnCutoff.1 hnCutoff.2 hs (hxsW.trans hw1) hc L us hus hret hmesh] with k hkM hkB hkR
  dsimp only at hkM hkB hkR ⊢
  rw [←hWdef] at hkR
  intro mid tail hparts T G forms initial_original_q s U hU x sourceMass hsourceMass
    hindex hmid hstar hpersistent hLeaves houter hxsx hxW hLOW hmass Hms Hhigh Hz Hrlow Hrs HCx Hdyadic
  rw [hparts] at hkM hkB hkR hindex houter Hms Hhigh Hz Hrlow Hrs ⊢
  rw [←hindex] at hkB
  let as:=mid++tail
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
  let g:=nativeFreshAtSlot T 0 s mid.length
  let Pg:=fun σ=>P (g.restRestrict σ)
  let p0:=sourceMonomialScale x (W n) initial_original_q
  have ho:MassOrdered 0 as:=by change MassOrdered 0 (mid++tail);rw [←hparts];exact finiteCutMasses_ordered us hus k
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have HWU:W n≤(M n).sweepRadius (partitionPoint 0 as U):=by linarith [Hhigh,hW]
  have Hhalf:(M n).sweepRadius (partitionPoint 0 as mid.length)≤(M n).sweepRadius (partitionPoint 0 as U)/2:=by
    have HH:=Hrs.trans (min_le_left _ _);linarith [Hhigh,hW]
  have HZhalf:(M n).z≤(M n).sweepRadius (partitionPoint 0 as U)/2:=by
    have HH:=Hz.trans (min_le_left _ _);linarith [Hhigh,hW]
  have BM:=hkM mid tail rfl hindex U T hU hmid hstar hpersistent hLeaves houter HWU Hhalf HZhalf
    G forms initial_original_q x hxsx hxW hmass s
  have BB:=hkB U T hU hstar hLeaves hpersistent houter G forms initial_original_q x hxsx hxW hmass s
  have Hweak:NativePersistentLowForks 0 mid.length U T:=by
    intro a z;rcases hpersistent a z with H|H|H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr H)
  have Hmi:partitionPoint 0 as 0≤Cmass*W n:=by
    have HH:partitionPoint 0 as 0=0:=by simp [partitionPoint]
    rw [HH];exact mul_nonneg hCm hW.le
  have HR0:(M n).sweepRadius 0=(M n).data.rmin:=(M n).R_zero
  have Hri:(M n).sweepRadius (partitionPoint 0 as 0)≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4):=by
    have HH:partitionPoint 0 as 0=0:=by simp [partitionPoint]
    rw [HH,HR0]
    exact (M n).hz.1.trans Hz
  have HRlocal:=hkR [] mid tail
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at HRlocal
  have BR:=HRlocal trivial T G forms initial_original_q s U hU x sourceMass hsourceMass
    hmid hstar Hweak hLeaves hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:|χ^2|≤1:=by
    rw [abs_pow];exact (pow_le_pow_left₀ (abs_nonneg χ) (native_second_low_original_chi_abs_le_one ho U K) 2).trans_eq (by norm_num)
  have BC:|χ^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s mid.length hU P|≤
      Cbase*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0:=by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans_eq (one_mul _)).trans BB
  have RC:|χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s mid.length hU P|≤
      Crep*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0:=by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans_eq (one_mul _)).trans BR
  have Hjoin:=native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement
    (dim n) q U b h K T ho s mid.length hstar hU P
  have HE:nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2=
      (nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
        χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P)+
      χ^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s mid.length hU P+
      χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s mid.length hU P:=by
    rw [Hjoin];ring
  change |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2|≤_
  rw [HE]
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_add_le _ _).trans (add_le_add BM BC)) RC).trans_eq
  dsimp only [p0,q,b,h,K,as,χ,P,Pg]
  ring

def ActualSecondLowStarOnlyFullCenteredB0SavingOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Couter Rmacro Cx : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(mid tail : List PositiveMass) (_hparts : as=mid++tail)
          (T : ClockTree (Spin (dim n)×Bool) (mid++tail))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial_original_q : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (mid++tail).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          mid.length=retainedMassPrefixIndex (w n).star.val as →
          0 < mid.length → mid.length < U →
          NativePersistentLowForks mid.length mid.length U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*(W n) →
          (M n).xs ≤ x → x ≤ (W n) →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial_original_q e) →
          partitionPoint 0 as (mid.length) ≤ Cmass*(W n) →
          4*(W n) ≤ (M n).sweepRadius (partitionPoint 0 as U) →
          (M n).z ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,(M n).sweepRadius (G.sourceLowMass e) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          (M n).sweepRadius (partitionPoint 0 as (mid.length)) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*(M n).xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (mid++tail) U →
        let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
        let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
        let g:=nativeFreshAtSlot T 0 s mid.length
        let p0:=sourceMonomialScale x (W n) initial_original_q
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree
          (fun σ=>Pc (g.restRestrict σ)) [g.embed s,g.mark]/2| ≤
          eps n*(W n)*(M n).xs^2*p0

theorem actual_second_low_star_only_full_centered_B0_saving_along_original_q
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cm Cstar Crep : ℝ,0<Cm ∧ 0<Cstar ∧ 0<Crep ∧
      ActualSecondLowStarOnlyFullCenteredB0SavingOnEveryFinalNetAlong_original_q degree rBound Cmass Couter Rmacro Cx
        (fun n=>actualSecondLowFullCenteredB0Amplitude_original_q (M n) eta Temp Cf Couter Cstar 0 Cm Crep)
        dim M W w := by
  obtain ⟨CmA,CstarA,CrepA,hCmA,hCstarA,hCrepA,HA⟩:=actual_second_low_star_only_full_raw_B0_budget_along_original_q
    degree rBound Cmass Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCouter hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Cm0,Cstar0,Crep0,hCm0,hCstar0,hCrep0,H0⟩:=actual_second_low_star_only_full_raw_B0_budget_along_original_q
    0 rBound Cmass Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCouter hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^degree
  have hCmean:0<Cmean:=by dsimp [Cmean];positivity
  let Cm:=CmA+Cmean*Cm0
  let Cstar:=CstarA+Cmean*Cstar0
  let Crep:=CrepA+Cmean*Crep0
  have hCmRate:0<Cm:=by dsimp [Cm];positivity
  refine ⟨Cm,Cstar,Crep,hCmRate,by dsimp [Cstar];positivity,by dsimp [Crep];positivity,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HA,H0,hdim.eventually Hmean,Hsource,HW1,Hcutoff] with n hnA hn0 hnmean hs hw1 hnCutoff
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnA L us hus hStarNode hret hmesh,hn0 L us hus hStarNode hret hmesh,
    hnmean (M n) hnCutoff.1 hnCutoff.2 hs (hxsW.trans hw1) L us hus hret hmesh] with k hkA hk0 hkmean
  dsimp only at hkA hk0 hkmean ⊢
  intro mid tail hparts T G forms initial_original_q s U hU x sourceMass hsourceMass
    hindex hmid hstar hpersistent hLeaves houter hxsx hxW hLOW hmass Hms Hhigh Hz Hrlow Hrs HCx Hdyadic
  rw [hparts] at hkmean houter Hms Hhigh Hz Hrlow Hrs ⊢
  let as:=mid++tail
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
  let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
  let g:=nativeFreshAtSlot T 0 s mid.length
  let p0:=sourceMonomialScale x (W n) initial_original_q
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
    simpa only [μ,Cmean,P,p0,q,b,h,K,as,mul_assoc] using hkmean U T hLeaves G forms initial_original_q x (W n) hxsx hxW hmass
  have HP:|B|≤CstarA*S*p0+CmA*V*p0+CrepA*R*p0:=by
    have HH:=hkA mid tail hparts T G forms initial_original_q s U hU x sourceMass hsourceMass
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
    have HP0:(G0.canonicalOriginalQSource (M n) Fin.elim0).restProduct=(fun _=>1):=by
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
  dsimp only [actualSecondLowFullCenteredB0Amplitude_original_q,actualHistorySecondLowFreshReplacementAmplitude_original_q]
  convert add_le_add_left HR (Cstar*S*p0+Crep*R*p0) using 1 <;>
    dsimp only [S,V,R,Cerr,rho,p0,q,b,h,K,as,P,Pc,g] <;> ring_nf

end OAI.SKFluctuations.Cavity
