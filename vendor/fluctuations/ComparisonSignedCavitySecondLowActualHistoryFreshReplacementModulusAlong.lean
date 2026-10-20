module

public import ComparisonSignedCavitySecondLowActualFreshReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowInheritedConstantB0AmplitudeAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 50000000

 def actualHistorySecondLowFreshReplacementAmplitude
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (eta Temp Cf Couter Cstar Csaved Cmoving : ℝ) : ℝ :=
  Cstar*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))+
    Csaved*((n+1:ℕ):ℝ)^(-eta)+
    Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (M.actualOriginalLowErrorDensitySaving (Couter+1)+(1/(n+1:ℕ):ℝ)/M.xs^2)

 theorem actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Csaved Cmoving Ccompare c0 : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCompare : 0≤Ccompare) (hCouter : 0≤Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualHistorySecondLowFreshReplacementAmplitude (M n)
      eta Temp Cf Couter Cstar Csaved Cmoving) atTop (𝓝 0) := by
  have HD:=actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh Hhistory
    hsmall hWlim (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have Hstar:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<32))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hsaved:=(tendsto_rpow_neg_atTop heta).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have H:=((Hstar.const_mul Cstar).add (Hsaved.const_mul Csaved)).add
    ((HD.add HI).const_mul (Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))
  simpa only [actualHistorySecondLowFreshReplacementAmplitude,Function.comp_def,mul_zero,add_zero] using H

def ActualHistorySecondLowFreshReplacementModulusOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Cerr Cinitial : ℝ) (eps : ℕ→ℝ)
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
          let g:=nativeFreshAtSlot T 0 s star
          let P:=(G.canonicalMinimumSource (M n) forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
            χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            eps n*W n*(M n).xs^2*p0

 theorem actual_second_low_actual_history_fresh_B0_modulo_replacement_modulus_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0≤epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0≤Cf ∧ 0<Ci ∧ ∃eps : ℕ→ℝ,(∀n,0≤eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFreshReplacementModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  obtain ⟨Cf,hCf,HS⟩:=actual_selected_bad_history_small_source_clocks hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨Ci,Cm,Csaved,Cstar,hCi,hCmRate,hCsaved,hCstar,H⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along degree rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta.le hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w HS Hcompare hw
  let eps:=fun n=>actualHistorySecondLowFreshReplacementAmplitude (M n) eta Temp Cf Couter Cstar Csaved Cm
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE]
    exact hWlim
  refine ⟨Cf,Ci,hCf,hCi,eps,?_,actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along
    heta hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hCouter dim hdim root M
    epsilon shell hb hh Hhistory Hcompare HL,?_⟩
  · intro n
    have HD:0 < (M n).actualOriginalLowErrorDensitySaving (Couter+1):=
      (M n).actualOriginalLowErrorDensitySaving_pos (by linarith)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    dsimp [eps,actualHistorySecondLowFreshReplacementAmplitude]
    positivity
  · filter_upwards [H] with n hn
    intro L us hus hstar hret hmesh
    filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
    dsimp only at hgrid ⊢
    intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G forms initial x hxsx hxW hmass s
    have HB:=hgrid i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G forms initial x hxsx hxW hmass s
    let as:=finiteCutMasses us jGrid
    let p0:=sourceMonomialScale x (W n) initial
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hx:0 < (M n).xs:=(M n).hxs
    have hW:0 < W n:=hx.trans_le (hxsx.trans hxW)
    have hp0:0≤p0:=by
      dsimp [p0]
      rw [←source_factor_scale_product]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (hx.trans_le hxsx) hW initial e).le
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have Hrho:(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
        partitionPoint 0 as U/(dim n+1:ℕ)≤
        ((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
    have Hr:=mul_le_mul_of_nonneg_left Hrho
      (mul_nonneg (mul_nonneg (mul_nonneg hCmRate.le hW.le) HCerr) hp0)
    apply HB.trans
    dsimp [eps,actualHistorySecondLowFreshReplacementAmplitude]
    convert add_le_add_left Hr
      (Ci*partitionPoint 0 as U*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))*p0+
        Cstar*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0+
        Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0) using 1 <;> ring

end OAI.SKFluctuations.Cavity
