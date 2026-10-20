module

public import ComparisonActualHighOnlyStrongInitialLowDensitySourceAlong
public import ComparisonNativeActualCutLowErrorDensityProducer
public import ComparisonNativeOriginalLowErrorEdgeBudget
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonSignedCavityActualLowErrorSavingAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
namespace ActualHighOnlyOverlapMinimum
def actualOriginalLowErrorDensitySaving
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (C : ℝ) : ℝ :=
  (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
    Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2))/a.xs^2+
      1/(n+1:ℕ)

theorem actualOriginalLowErrorDensitySaving_pos
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) {C : ℝ} (hC : 0 < C) :
    0 < a.actualOriginalLowErrorDensitySaving C := by
  have HI : 0 ≤ (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
      Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2))/a.xs^2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact intervalIntegral.integral_nonneg
      (le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one)
      (fun _ _=>Real.sqrt_nonneg _)
  unfold actualOriginalLowErrorDensitySaving
  exact add_pos_of_nonneg_of_pos HI (by positivity)

theorem actual_cut_low_error_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0 < C) (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠj : ℕ in atTop,
      (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
        Real.sqrt (physicalSampledCutLowErrorSecond n a.bf a.hf
          (finiteCutMasses us j) (finiteCutMasses_ordered us hu j) u)) ≤
        a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
  have hb:=a.bf_monotone
  have hh:=a.hf_monotone
  have hq : min (C*a.canonicalDirectTestBandScale) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have Hfine:=physicalSampledCutLowError_integral_tendsto n a.bf a.hf hb hh
    (finiteCutMasses us) (fun j=>((j+1:ℕ):ℝ)⁻¹)
    (finiteCutMasses_ordered us hu) (finiteCutMasses_end us hu) (finiteCutMasses_mesh us hu)
    uniformMasses_mesh_tendsto hq
  have hgap : (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
      Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) <
      a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
    unfold actualOriginalLowErrorDensitySaving
    have hx:=a.hxs
    have hp : 0 < (1/(n+1:ℕ):ℝ)*a.xs^2 := by positivity
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
    linarith
  exact Hfine.eventually (eventually_le_nhds hgap)

theorem actual_cut_low_error_edgeBudget_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0 < C) (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (C*a.canonicalDirectTestBandScale) 1 →
        ClockTree.edgeBudget 0 as (fun k=>if k<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as k else 0) ≤
          a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
  filter_upwards [a.actual_cut_low_error_density_on_every_final_net C hC us hu] with j hj
  dsimp only
  intro U hU hmass
  let as:=finiteCutMasses us j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hu j
  rw [native_low_edgeBudget_eq_prefix_integral ho U hU]
  have heq : massStepFunction as (nativeOriginalCutLowErrorRadius n a.bf a.hf as)=
      fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n a.bf a.hf as ho u) := by
    funext u
    exact (physicalSampledCutLowErrorRadius_eq_massStepFunction n a.bf a.hf as ho u).symm
  rw [heq]
  have hi:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalSampledCutLowErrorSecond_intervalIntegrable n a.bf a.hf
      a.bf_monotone
      a.hf_monotone
      as ho (finiteCutMasses_mesh us hu j))
  have hq : min (C*a.canonicalDirectTestBandScale) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have hiq:=hi.mono_set (by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  apply (intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1 hmass
    (ae_of_all _ (fun u=>Real.sqrt_nonneg (physicalSampledCutLowErrorSecond n a.bf a.hf as ho u))) hiq).trans
  exact hj

theorem actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (Homit : Tendsto (fun n=>(a n).data.s/(a n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(a n).data.s≤1/4 ∧ (a n).data.s≤(a n).xs)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(a n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  have HI:=regular_minimum_strong_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim a hsmall hWlim hclock Homit Hcutoff C hC
  have Hinv : Tendsto (fun n : ℕ=>1/((dim n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  simpa only [actualOriginalLowErrorDensitySaving,add_zero] using HI.add Hinv

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
theorem actual_low_error_omitted_site_ratio_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/(n+1:ℕ):ℝ)/a.xs^2 ≤ C0^2*a.context.N^(-((2:ℝ)/3+2*m)) := by
  have H:=a.canonical_high_mass_inverse_power hC0 2
  simp only [Nat.cast_ofNat,show (2:ℝ)/6=(1:ℝ)/3 by norm_num] at H
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.context.hN.le (-((2:ℝ)/3)))
  have HE : a.context.N^(-((2:ℝ)/3))=a.context.N^((1:ℝ)/3)/a.context.N := by
    calc
      _=a.context.N^(((1:ℝ)/3)-1) := by congr 1;ring
      _=a.context.N^((1:ℝ)/3)/a.context.N^((1:ℝ)) := Real.rpow_sub a.context.hN _ _
      _=_ := by rw [Real.rpow_one]
  have HL : a.context.N^(-((2:ℝ)/3))*(1/(a.context.N^((1:ℝ)/3)*a.xs^2))=
      (1/(n+1:ℕ):ℝ)/a.xs^2 := by
    rw [HE]
    have hpow : a.context.N^((1:ℝ)/3)≠0:=(Real.rpow_pos_of_pos a.context.hN _).ne'
    have hx:=a.hxs.ne'
    have hN:=a.context.hN.ne'
    change _=(1/a.context.N)/a.xs^2
    field_simp
  have HR : a.context.N^(-((2:ℝ)/3))*(C0^2*a.context.N^(-(2:ℝ)*m))=
      C0^2*a.context.N^(-((2:ℝ)/3+2*m)) := by
    rw [mul_left_comm,←Real.rpow_add a.context.hN]
    congr 2
    ring
  rw [HL,HR] at HM
  exact HM

theorem actual_low_error_omitted_site_ratio_tendsto_zero_along_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(1/(dim n+1:ℕ):ℝ)/(a n).xs^2) atTop (𝓝 0) := by
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < (2:ℝ)/3+2*m by positivity)).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim:=Hpow.const_mul (C0^2)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by have hx:=(a n).hxs;positivity)
    (fun n=>actual_low_error_omitted_site_ratio_le_high_only (a n) hC0)
  simpa only [ActualHighOnlyComparisonData.N,Function.comp_def] using Hlim

theorem actual_minimum_inherited_current_low_error_density_on_every_final_net_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf C : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hC : 0 < C)
    (hsource : ActualHighOnlySmallSourceClocks a Temp Cf) (hxs1 : a.xs ≤ 1)
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
    actual_minimum_inherited_current_low_error_radius_le_original_high_only a Temp Cf hTemp hCf hsource hxs1 ho U hl ht j hj)
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

def actualMinimumInheritedLowErrorDensityAmplitude_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Temp Cf C : ℝ) : ℝ :=
  actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (a.actualOriginalLowErrorDensitySaving C+(1/(n+1:ℕ):ℝ)/a.xs^2)

theorem actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>actualMinimumInheritedLowErrorDensityAmplitude_high_only (M n) Temp Cf C) atTop (𝓝 0) := by
  have HS:=ActualHighOnlyOverlapMinimum.actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall hWlim hclock Homit Hcutoff C hC
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along_high_only hm hC0 dim hdim M
  have H:=(HS.add HI).const_mul (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp)
  simpa only [actualMinimumInheritedLowErrorDensityAmplitude_high_only,add_zero,mul_zero] using H

theorem actual_minimum_inherited_current_low_error_saved_density_on_every_final_net_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf C : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hC : 0 < C)
    (hsource : ActualHighOnlySmallSourceClocks a Temp Cf) (hxs1 : a.xs ≤ 1)
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
          actualMinimumInheritedLowErrorDensityAmplitude_high_only a Temp Cf C*a.xs^2 := by
  filter_upwards [actual_minimum_inherited_current_low_error_density_on_every_final_net_high_only a Temp Cf C
    hTemp hCf hC hsource hxs1 us hu] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass l t hl ht
  apply (hj U hU hmass l t hl ht).trans_eq
  unfold actualMinimumInheritedLowErrorDensityAmplitude_high_only
  have hx:=a.hxs.ne'
  rw [mul_assoc,add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx)]

end OAI.SKFluctuations.Cavity
