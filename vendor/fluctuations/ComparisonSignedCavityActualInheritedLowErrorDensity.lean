module

public import ComparisonSignedCavityActualLowErrorSaving
public import ComparisonSignedCavityInheritedErrorTransport
public import ComparisonNativeActualShellHistoryThermalBounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem actual_minimum_inherited_current_low_error_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf C : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hC : 0 < C)
    (hsource : NativeActualSmallSourceClocks a Temp Cf) (hxs1 : a.xs ≤ 1)
    (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) a.bf a.hf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (C*a.canonicalDirectTestBandScale) 1 →
      ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ClockTree.edgeBudget 0 as
          (nativeWholeLawErrorRadius n as
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (cutLowError n U b h K)) ≤
          actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (a.actualOriginalLowErrorDensitySaving C*a.xs^2+1/(n+1:ℕ)) := by
  filter_upwards [a.actual_cut_low_error_edgeBudget_on_every_final_net C hC us hu] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass l t hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) a.bf a.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let M:=4*Cf+2*Temp
  let E:=actualLowErrorComparisonConstant M Temp
  let R:=nativeOriginalCutLowErrorRadius n a.bf a.hf as
  let site:=(1/(n+1:ℕ):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hu jGrid
  have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
    actual_minimum_inherited_current_low_error_radius_le_original a Temp Cf hTemp hCf hsource hxs1 ho U hl ht j hj)
  have heq : (fun j=>if j<U then E*(R j+site) else 0)=
      (fun j=>E*(if j<U then R j else 0)+(E*site)*(if j<U then 1 else 0)) := by
    funext j
    split_ifs <;> ring
  change ClockTree.edgeBudget 0 as _ ≤ ClockTree.edgeBudget 0 as
    (fun j=>if j<U then E*(R j+site) else 0) at Hmono
  rw [heq,actual_low_edgeBudget_linear] at Hmono
  have HD:=hgrid U hU hmass
  have HE : 0 ≤ E:=actualLowErrorComparisonConstant_nonneg M hTemp
  have Hfirst:=mul_le_mul_of_nonneg_left HD HE
  have Hsite:=mul_le_mul_of_nonneg_left (actual_low_edgeBudget_ones_le ho U hU)
    (show 0 ≤ E*site by dsimp [site];positivity)
  apply Hmono.trans ((add_le_add Hfirst Hsite).trans_eq _)
  dsimp only [E,M,site]
  ring

def actualMinimumInheritedLowErrorDensityAmplitude
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Temp Cf C : ℝ) : ℝ :=
  actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (a.actualOriginalLowErrorDensitySaving C+(1/(n+1:ℕ):ℝ)/a.xs^2)

theorem actualMinimumInheritedLowErrorDensityAmplitude_shell_history_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (T epsilon shell : ℕ→ℝ) (ts : ℕ→List ComparisonHistoryTerm)
    (hb : ∀n u,(a n).b u=historyMatrixClock (T n) (epsilon n) (shell n) (ts n) u)
    (hh : ∀n u,(a n).h u=historyFieldClock (ts n) u)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>actualMinimumInheritedLowErrorDensityAmplitude (a n) Temp Cf C) atTop (𝓝 0) := by
  have HS:=NativeOverlapMinimum.actualOriginalLowErrorDensitySaving_shell_history_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs a hsmall hWlim T epsilon shell ts hb hh C hC
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero hm hC0 a
  have H:=(HS.add HI).const_mul (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp)
  simpa only [actualMinimumInheritedLowErrorDensityAmplitude,add_zero,mul_zero] using H

theorem actual_minimum_inherited_current_low_error_saved_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf C : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hC : 0 < C)
    (hsource : NativeActualSmallSourceClocks a Temp Cf) (hxs1 : a.xs ≤ 1)
    (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) a.bf a.hf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (C*a.canonicalDirectTestBandScale) 1 →
      ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ClockTree.edgeBudget 0 as
          (nativeWholeLawErrorRadius n as
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (cutLowError n U b h K)) ≤
          actualMinimumInheritedLowErrorDensityAmplitude a Temp Cf C*a.xs^2 := by
  filter_upwards [actual_minimum_inherited_current_low_error_density_on_every_final_net a Temp Cf C
    hTemp hCf hC hsource hxs1 us hu] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass l t hl ht
  apply (hj U hU hmass l t hl ht).trans_eq
  unfold actualMinimumInheritedLowErrorDensityAmplitude
  have hx:=a.hxs.ne'
  rw [mul_assoc,add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx)]

end OAI.SKFluctuations.Cavity
