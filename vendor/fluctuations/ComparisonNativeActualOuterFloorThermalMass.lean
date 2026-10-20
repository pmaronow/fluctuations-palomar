module

public import ComparisonNativeActualFloorThermalMass

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem comparison_floor_tail_mass_le {N delta U rlo : ℝ}
    (hN : 0 < N) (hU : 0 < U) (hrlo : 0 < rlo) (hrlo1 : rlo ≤ 1) :
    (∫r in Icc rlo 1,comparisonFloor N delta U r) ≤ N^delta*U^2/rlo := by
  have hc := comparisonFloor_continuousOn (δ:=delta) hN hU hrlo.le
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (hr : r∈uIcc rlo 1)=>comparisonFloor_antiderivative (δ:=delta) hN hU
      (by have hr' : r∈Icc rlo 1 := by simpa only [uIcc_of_le hrlo1] using hr
          exact hrlo.le.trans hr'.1))
    (hc.intervalIntegrable_of_Icc hrlo1)
  have he' : (∫r in rlo..1,comparisonFloor N delta U r)=
      N^delta*U^2/(rlo+N^(2*delta)*U)-N^delta*U^2/(1+N^(2*delta)*U) := by
    convert he using 1
    ring
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hrlo1,he']
  have htail : 0 ≤ N^delta*U^2/(1+N^(2*delta)*U) := by positivity
  have hden : rlo ≤ rlo+N^(2*delta)*U := le_add_of_nonneg_right (by positivity)
  exact (sub_le_self _ htail).trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ N^delta*U^2) hrlo hden)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_mass_slab_radius_lower
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {lo r : ℝ} (hlo : cu*Az*a.xs < lo)
    (hr : r∈Icc (0:ℝ) 1) (hmass : lo ≤ a.alpha.val.val r) : lo/cu ≤ r := by
  have hzr : a.z ≤ r := by
    by_contra hh
    have hrz : r ≤ a.z := (lt_of_not_ge hh).le
    have halpha := a.alpha.val.property.2 hrz
    have hzreg := (a.regular a.z ⟨le_rfl,a.hz.2⟩).2
    have hzupper := mul_le_mul_of_nonneg_left a.hzxs hcu.le
    nlinarith
  have hreg := (a.regular r ⟨hzr,hr.2⟩).2
  exact (div_le_iff₀ hcu).mpr (by linarith)

theorem actual_floor_mass_of_lower_radius
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (A : Set ℝ) (hA : MeasurableSet A) {rlo : ℝ} (hrlo : 0 < rlo) (hrlo1 : rlo ≤ 1)
    (hlower : ∀r∈A, rlo ≤ r) :
    let b := g.toModel dphys e hlog hnd
    (∫u in 0..1,(A∩nativeActualPositiveSet b).indicator (fun _=>(1:ℝ)) (a.R u)) ≤
      a.context.N^delta*a.context.U^2/rlo := by
  dsimp only
  let b := g.toModel dphys e hlog hnd
  let F := A∩nativeActualPositiveSet b
  have hF : MeasurableSet F := hA.inter (nativeActualPositiveSet_measurable b)
  have hsub : F ⊆ Icc (0:ℝ) 1 := fun r hr=>hr.2.1
  have houter : F ⊆ Icc rlo 1 := fun r hr=>⟨hlower r hr.1,hr.2.1.2⟩
  change (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (b.R u)) ≤ _
  rw [nativeActual_radius_mask_mass b F hF hsub]
  have he : (∫r in Icc (0:ℝ) 1,F.indicator (deriv a.alpha.val.val) r)=
      ∫r in Icc (0:ℝ) 1,F.indicator (comparisonFloor a.context.N delta a.context.U) r := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [p.hfloor] with r hr hri
    by_cases hm : r∈F
    · simp only [indicator_of_mem hm,hr hri hm.2.2]
    · simp only [indicator_of_notMem hm]
  rw [setIntegral_indicator hF,inter_eq_right.mpr hsub] at he
  change (∫r in F,deriv a.alpha.val.val r) ≤ _
  rw [he]
  rw [setIntegral_indicator hF,inter_eq_right.mpr hsub]
  have hki : IntegrableOn (comparisonFloor a.context.N delta a.context.U) (Icc rlo 1) :=
    (comparisonFloor_continuousOn (δ:=delta) a.context.hN a.context.hU hrlo.le).integrableOn_Icc
  have hmono : (∫r in F,comparisonFloor a.context.N delta a.context.U r) ≤
      ∫r in Icc rlo 1,comparisonFloor a.context.N delta a.context.U r := by
    apply setIntegral_mono_set hki
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (comparisonFloor_pos (δ:=delta) a.context.hN a.context.hU (hrlo.le.trans hr.1)).le
    · exact Eventually.of_forall fun r hr=>houter hr
  exact hmono.trans (comparison_floor_tail_mass_le a.context.hN a.context.hU hrlo hrlo1)

theorem actual_outer_floor_thermal_mass_of_normalized_B
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (A : Set ℝ) (hA : MeasurableSet A) {rlo hi K : ℝ}
    (hrlo : 0 < rlo) (hrlo1 : rlo ≤ 1) (hlower : ∀r∈A,rlo ≤ r) (hK : 0 ≤ K)
    (hscale : ∀r∈A, a.alpha.val.val r ≤ hi)
    (hB : ∀u∈Ioc (0:ℝ) 1, orderedPathB (n+1) a.bf a.hf u ≤ K*(a.xs+u)^2) :
    let b := g.toModel dphys e hlog hnd
    (∫u in 0..1,(A∩nativeActualPositiveSet b).indicator (fun _=>1) (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
      K*(a.xs+hi)^2*a.context.N^delta*a.context.U^2/rlo := by
  dsimp only
  let b := g.toModel dphys e hlog hnd
  let F := A ∩ nativeActualPositiveSet b
  let mask := fun u => F.indicator (fun _=>(1:ℝ)) (b.R u)
  let C := K*(a.xs+hi)^2
  have hF : MeasurableSet F := hA.inter (nativeActualPositiveSet_measurable b)
  have hsub : F ⊆ Icc (0:ℝ) 1 := fun r hr => hr.2.1
  have hmass : (∫u in 0..1,mask u) ≤ a.context.N^delta*a.context.U^2/rlo :=
    a.actual_floor_mass_of_lower_radius p g dphys e hlog hnd A hA hrlo hrlo1 hlower
  have hmask : Measurable mask := (measurable_const.indicator hF).comp
    (comparisonSweepQuantile_continuous b.hc b.hk b.hkc b.hm b.hM b.alpha).measurable
  have hiMask : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmask zero_le_one
      (fun u _ => by dsimp [mask]; by_cases h:b.R u∈F <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hiT := nativeActualThermal_mask_integrable b F hF
  have hb : (∫u in 0..1,mask u*b.thermal u) ≤ ∫u in 0..1,C*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one hiT (hiMask.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hune
    have hup : u∈Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne hu.1 hune.symm,hu.2⟩
    by_cases hm : b.R u∈F
    · have hs := hscale (b.R u) hm.1
      change b.alpha.val.val (b.R u) ≤ hi at hs
      rw [comparisonSweepQuantile_spec b.hc b.hk b.hkc b.hm b.hM b.alpha hu] at hs
      have hp := pow_le_pow_left₀ (by linarith [a.hxs,hu.1] : 0≤a.xs+u)
        (add_le_add (le_refl a.xs) hs) 2
      have hmul := mul_le_mul_of_nonneg_left hp hK
      have hraw := hB u hup
      simp only [mask,indicator_of_mem hm,one_mul,mul_one]
      change orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2 ≤
        K*(a.xs+hi)^2
      nlinarith [sq_nonneg (orderedPathS (n+1) a.bf a.hf u)]
    · simp only [mask,indicator_of_notMem hm,zero_mul,mul_zero,le_refl]
  rw [intervalIntegral.integral_const_mul] at hb
  have hcoef : 0 ≤ C := by dsimp [C]; exact mul_nonneg hK (sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_left hmass hcoef
  change (∫u in 0..1,mask u*b.thermal u) ≤ _
  exact hb.trans (by simpa only [C,mul_div_assoc,mul_assoc] using hc)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
