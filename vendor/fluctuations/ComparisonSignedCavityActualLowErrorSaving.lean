module

public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem actual_low_error_omitted_site_ratio_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
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

theorem actual_low_error_omitted_site_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (a : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(1/(n+1:ℕ):ℝ)/(a n).xs^2) atTop (𝓝 0) := by
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < (2:ℝ)/3+2*m by positivity)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have Hlim:=Hpow.const_mul (C0^2)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by have hx:=(a n).hxs;positivity)
    (fun n=>actual_low_error_omitted_site_ratio_le (a n) hC0)
  simpa only [NativeOverlapContext.N,Function.comp_def] using Hlim

def actualMinimumLowErrorDensityAmplitude
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Temp C : ℝ) : ℝ :=
  actualLowErrorComparisonConstant (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp*
    (a.actualOriginalLowErrorDensitySaving C+(1/(n+1:ℕ):ℝ)/a.xs^2)

theorem actualMinimumLowErrorDensityAmplitude_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Temp Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hb : ∀n u,(a n).b u=Temp) (hh : ∀n u,(a n).h u=0)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>actualMinimumLowErrorDensityAmplitude (a n) Temp C) atTop (𝓝 0) := by
  have HS:=NativeOverlapMinimum.actualOriginalLowErrorDensitySaving_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs a hsmall hWlim hb hh C hC
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero hm hC0 a
  have H:=(HS.add HI).const_mul
    (actualLowErrorComparisonConstant (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp)
  simpa only [actualMinimumLowErrorDensityAmplitude,add_zero,mul_zero] using H

theorem actual_minimum_current_low_error_saved_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (Temp C : ℝ) (hTemp : 0 ≤ Temp) (hC : 0 < C)
    (hbareb : ∀u,a.b u=Temp) (hbareh : ∀u,a.h u=0) (hxs1 : a.xs ≤ 1)
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
            (cutLowError n U b h K)) ≤ actualMinimumLowErrorDensityAmplitude a Temp C*a.xs^2 := by
  filter_upwards [actual_minimum_current_low_error_density_on_every_final_net a hcl hAz Temp C hTemp hC
    hbareb hbareh hxs1 us hu] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass l t hl ht
  apply (hj U hU hmass l t hl ht).trans_eq
  unfold actualMinimumLowErrorDensityAmplitude
  have hx:=a.hxs.ne'
  rw [mul_assoc,add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx)]

end OAI.SKFluctuations.Cavity
