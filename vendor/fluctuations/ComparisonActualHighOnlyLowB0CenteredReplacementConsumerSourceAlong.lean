module

public import ComparisonSignedCavitySecondLowActualCenteredFreshReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowInheritedCenteredOccupiedCReplacementBudgetAlong
public import ComparisonActualHighOnlyLowB0FreshReplacementConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0UnobservedPhysicalSourceAlong
public import ComparisonActualHighOnlySecondLowInheritedOccupiedCReplacementBudgetAlong

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
theorem actual_second_low_centered_fresh_B0_modulo_c_replacement_budget_along_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving Csaved Cstar : ℝ,0<Cinitial ∧ 0<Cmoving ∧ 0<Csaved ∧ 0<Cstar ∧
      ActualSecondLowCenteredFreshReplacementBudgetOnEveryFinalNetAlong_high_only degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving Csaved Cstar dim M W w := by
  obtain ⟨CiA,CmA,CsA,CstarA,hCiA,hCmA,hCsA,hCstarA,HA⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along_high_only degree rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Ci0,Cm0,Cs0,Cstar0,hCi0,hCm0,hCs0,hCstar0,H0⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along_high_only 0 rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget_high_only
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^degree
  have hCmean:0 < Cmean:=by dsimp [Cmean];positivity
  refine ⟨CiA+Cmean*Ci0,CmA+Cmean*Cm0,CsA+Cmean*Cs0,CstarA+Cmean*Cstar0,
    by positivity,by positivity,by positivity,by positivity,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [HA,H0,hdim.eventually Hmean,Hsource,HW,Hcutoff] with n hnA hn0 hnm hnS hnW hnCutoff
  have hxsW:(M n).xs ≤ W n:=by rw [hcanonical n];exact le_max_left _ _
  intro L us hus hstar hret hmesh
  filter_upwards [hnA L us hus hstar hret hmesh,hn0 L us hus hstar hret hmesh,
    hnm (M n) hnCutoff.1 hnCutoff.2 hnS (hxsW.trans hnW) L us hus hret hmesh] with jGrid hgA hg0 hgm
  dsimp only at hgA hg0 hgm ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let p0:=sourceMonomialScale x (W n) initial
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
    partitionPoint 0 as U/(dim n+1:ℕ)
  let AI:=partitionPoint 0 as U*(M n).xs*Cerr*di
  let AS:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2
  let AM:=W n*Cerr*rho
  let AH:=((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2
  have hp0:0 ≤ p0:=by
    have hx:0 < x:=(M n).hxs.trans_le hxsx
    have hW:0 < W n:=hx.trans_le hxW
    dsimp [p0]
    unfold sourceMonomialScale
    positivity
  have Hm:|nativeOriginalRestTestExpectation (dim n) q U b h K T P| ≤ Cmean*p0:=by
    simpa only [Cmean,P,p0,mul_assoc] using
      hgm U T hT G forms initial x (W n) hxsx hxW hmass
  have HP:|nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s star hU P| ≤
      CiA*AI*p0+CstarA*AS*p0+CmA*AM*p0+CsA*AH*p0:=by
    convert hgA i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G forms initial x hxsx hxW hmass s using 1;
      dsimp only [nativeSecondLowFreshB0MinusCReplacementSource,P,p0,Cerr,AI,AS,AM,AH,di,rho]; ring
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hp0:sourceMonomialScale x (W n) (∅ : Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product]
    exact Fin.prod_univ_zero _
  have H1:|nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s star hU (fun _=>1)| ≤
      Ci0*AI+Cstar0*AS+Cm0*AM+Cs0*AH:=by
    have HH:=hg0 i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G0 Fin.elim0 ∅ x hxsx hxW (fun e=>e.elim0) s
    have HP0:(G0.canonicalHighOnlySource (M n) Fin.elim0).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    rw [HP0] at HH
    simp only [Hp0,mul_one] at HH
    simpa only [nativeSecondLowFreshB0MinusCReplacementSource,AI,AS,AM,AH,Cerr,di,rho,mul_assoc] using HH
  rw [native_second_low_original_centered_fresh_B0_minus_c_replacement]
  rw [sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul]
  apply (add_le_add HP (mul_le_mul Hm H1 (abs_nonneg _) (mul_nonneg hCmean.le hp0))).trans_eq
  dsimp only [AI,AS,AM,AH,di,rho,Cerr,p0]
  ring

theorem eventually_actual_minimum_inherited_second_low_centered_occupied_c_replacement_budget_along_high_only
    (a rBound : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (s : T.Slot) (U : ℕ) (hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.R (partitionPoint 0 as U) →
          M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.R (partitionPoint 0 as pre.length) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
          (pre.length+mid.length) hU (nativeOriginalCenteredRestTest (dim n) q U b h K T
            (G.canonicalHighOnlySource M forms).restProduct)| ≤
          C*(dim n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along_high_only
    (D:=D) a rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Czero,hCzero,H0⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along_high_only
    (D:=D) 0 rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget_high_only
    (D:=D) a rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^a
  have hCmean:0 < Cmean:=by dsimp [Cmean];positivity
  refine ⟨Ca+Cmean*Czero,by positivity,?_⟩
  filter_upwards [HA,H0,hdim.eventually Hmean] with n hnA hn0 hnm
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnA M hs0 hsxs HS hxs hcompare L us hus hret hmesh,
    hn0 M hs0 hsxs HS hxs hcompare L us hus hret hmesh,
    hnm M hs0 hsxs HS hxs L us hus hret hmesh] with k hkA hk0 hkm
  dsimp only at hkA hk0 hkm ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hT hLeaves hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let P:=(G.canonicalHighOnlySource M forms).restProduct
  let p0:=sourceMonomialScale x W initial
  let rate:=(dim n:ℝ)^(-eta)*W*M.xs^2
  have hp0:0 ≤ p0:=by
    have hx:0 < x:=M.hxs.trans_le hxsx
    have hW:0 < W:=hx.trans_le hxW
    dsimp [p0]
    unfold sourceMonomialScale
    positivity
  have Hm:|nativeOriginalRestTestExpectation (dim n) q U b h K T P| ≤ Cmean*p0:=by
    rw [hparts] at hkm
    simpa only [Cmean,P,p0,W,q,b,h,K,hparts,mul_assoc] using
      hkm U T hLeaves G forms initial x W hxsx hxW hmass
  have HP:|nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P| ≤
      Ca*rate*p0:=by
    simpa only [P,p0,rate,mul_assoc] using
      hkA pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass hmid hstar hT
        hLeaves hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hp0:sourceMonomialScale x W (∅ : Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product]
    exact Fin.prod_univ_zero _
  have H1:|nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU (fun _=>1)| ≤
      Czero*rate:=by
    have HH:=hk0 pre mid tail hparts T G0 Fin.elim0 ∅ s U hU x sourceMass hsourceMass
      hmid hstar hT hLeaves hxsx hxW hWmacro (fun e=>e.elim0) (fun e=>e.elim0)
      Hmi Hms Hhigh Hz (fun e=>e.elim0) Hri Hrs HCx Hdyadic
    have HP0:(G0.canonicalHighOnlySource M Fin.elim0).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    rw [HP0] at HH
    dsimp only [W] at Hp0
    simpa only [rate,W,Hp0,mul_one,mul_assoc] using HH
  change |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU
    (nativeOriginalCenteredRestTest (dim n) q U b h K T P)| ≤ _
  change |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU
    (fun σ=>P σ-nativeOriginalRestTestExpectation (dim n) q U b h K T P)| ≤ _
  rw [native_second_low_fresh_occupied_c_replacement_sub_const,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul]
  apply (add_le_add HP (mul_le_mul Hm H1 (abs_nonneg _) (mul_nonneg hCmean.le hp0))).trans_eq
  dsimp only [rate,p0]
  ring

end OAI.SKFluctuations.Cavity
