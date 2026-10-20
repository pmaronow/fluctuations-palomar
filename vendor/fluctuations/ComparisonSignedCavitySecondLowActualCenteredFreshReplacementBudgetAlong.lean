module

public import ComparisonSignedCavitySecondLowActualFreshReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget
public import ComparisonSignedCavitySecondLowCenteredReplacementSource
public import ComparisonSignedCavitySecondLowInheritedTwoLowCloneBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

def ActualSecondLowCenteredFreshReplacementBudgetOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Ccut Couter Cerr Cinitial Cmoving Csaved Cstar : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V≤Ccut*(M n).xs → T.leaves≤rBound →
          partitionPoint 0 as U≤Couter*W n → W n≤(M n).R (partitionPoint 0 as U) →
          (M n).R (partitionPoint 0 as star)≤(M n).R (partitionPoint 0 as U)/2 →
          (M n).z≤(M n).R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x → x≤W n →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e) →
        ∀s : T.Slot,
          let P:=(G.canonicalMinimumSource (M n) forms).restProduct
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s star hU
            (nativeOriginalCenteredRestTest (dim n) q U b h K T P)|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            Cstar*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0+
            Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0

theorem actual_second_low_centered_fresh_B0_modulo_c_replacement_budget_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving Csaved Cstar : ℝ,0<Cinitial ∧ 0<Cmoving ∧ 0<Csaved ∧ 0<Cstar ∧
      ActualSecondLowCenteredFreshReplacementBudgetOnEveryFinalNetAlong degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving Csaved Cstar dim M W w := by
  obtain ⟨CiA,CmA,CsA,CstarA,hCiA,hCmA,hCsA,hCstarA,HA⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along degree rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Ci0,Cm0,Cs0,Cstar0,hCi0,hCm0,hCs0,hCstar0,H0⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along 0 rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^degree
  have hCmean:0 < Cmean:=by dsimp [Cmean];positivity
  refine ⟨CiA+Cmean*Ci0,CmA+Cmean*Cm0,CsA+Cmean*Cs0,CstarA+Cmean*Cstar0,
    by positivity,by positivity,by positivity,by positivity,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [HA,H0,hdim.eventually Hmean,Hsource,HW] with n hnA hn0 hnm hnS hnW
  have hxsW:(M n).xs ≤ W n:=by rw [hcanonical n];exact le_max_left _ _
  intro L us hus hstar hret hmesh
  filter_upwards [hnA L us hus hstar hret hmesh,hn0 L us hus hstar hret hmesh,
    hnm (M n) hnS (hxsW.trans hnW) L us hus hret hmesh] with jGrid hgA hg0 hgm
  dsimp only at hgA hg0 hgm ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
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
    have HP0:(G0.canonicalMinimumSource (M n) Fin.elim0).restProduct=(fun _=>1):=by
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

end OAI.SKFluctuations.Cavity
