module

public import ComparisonNativeLocalCapScaleBounds
public import ComparisonNativeGlobalErrorAssemblySelective

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_floor_local_mass_le
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (A : Set ℝ) (hA : MeasurableSet A) :
    let b := g.toModel dphys e hlog hnd
    (∫u in 0..1,(A∩nativeActualPositiveSet b).indicator (fun _=>(1:ℝ)) (a.R u)) ≤
      a.context.N^(-delta)*a.context.U := by
  dsimp only
  let b := g.toModel dphys e hlog hnd
  let F := A ∩ nativeActualPositiveSet b
  have hF : MeasurableSet F := hA.inter (nativeActualPositiveSet_measurable b)
  have hsub : F ⊆ Icc (0:ℝ) 1 := fun r hr=>hr.2.1
  change (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (b.R u)) ≤ _
  rw [nativeActual_radius_mask_mass b F hF hsub]
  have hf : ∀ᵐr, r∈Icc (0:ℝ) 1 → r∈F →
      deriv a.alpha.val.val r=comparisonFloor a.context.N delta a.context.U r := by
    filter_upwards [p.hfloor] with r hr hri hrF
    exact hr hri hrF.2.2
  have hn := comparisonFloor_region_mass a.context.hN a.context.hU
    (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) F hF a.alpha.val.val hf
  rw [setIntegral_indicator hF,inter_eq_right.mpr hsub] at hn
  exact hn

theorem actual_floor_thermal_mass_of_normalized_B
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (A : Set ℝ) (hA : MeasurableSet A) {hi K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀r∈A, a.alpha.val.val r ≤ hi)
    (hB : ∀u∈Ioc (0:ℝ) 1, orderedPathB (n+1) a.bf a.hf u ≤ K*(a.xs+u)^2) :
    let b := g.toModel dphys e hlog hnd
    (∫u in 0..1,(A∩nativeActualPositiveSet b).indicator (fun _=>1) (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
      K*(a.xs+hi)^2*a.context.N^(-delta)*a.context.U := by
  dsimp only
  let b := g.toModel dphys e hlog hnd
  let F := A ∩ nativeActualPositiveSet b
  let mask := fun u => F.indicator (fun _=>(1:ℝ)) (b.R u)
  let C := K*(a.xs+hi)^2
  have hF : MeasurableSet F := hA.inter (nativeActualPositiveSet_measurable b)
  have hsub : F ⊆ Icc (0:ℝ) 1 := fun r hr => hr.2.1
  have hmass : (∫u in 0..1,mask u) ≤ a.context.N^(-delta)*a.context.U := by
    rw [nativeActual_radius_mask_mass b F hF hsub]
    have hf : ∀ᵐr, r∈Icc (0:ℝ) 1 → r∈F →
        deriv a.alpha.val.val r=comparisonFloor a.context.N delta a.context.U r := by
      filter_upwards [p.hfloor] with r hr hri hrF
      exact hr hri hrF.2.2
    have hn := comparisonFloor_region_mass a.context.hN a.context.hU
      (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) F hF a.alpha.val.val hf
    rw [setIntegral_indicator hF,inter_eq_right.mpr hsub] at hn
    exact hn
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
  exact hb.trans (by simpa only [C,mul_assoc] using hc)

end NativeOverlapMinimum

theorem eventually_actual_minimum_floor_thermal_mass
    (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ, 0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (p : a.Potential) (g : a.BandGeometry p)
        (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
        (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
        (A : Set ℝ), MeasurableSet A → ∀hi : ℝ,
        (∀r∈A, a.alpha.val.val r ≤ hi) →
        let b := g.toModel dphys e hlog hnd
        (∫u in 0..1,(A∩nativeActualPositiveSet b).indicator (fun _=>1) (a.R u)*
          (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
          K*(a.xs+hi)^2*a.context.N^(-delta)*a.context.U := by
  obtain ⟨K,hK,hB⟩ := eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hB] with n hn
  intro a p g dphys e hlog hnd A hA hi hscale
  exact a.actual_floor_thermal_mass_of_normalized_B p g dphys e hlog hnd A hA hK.le hscale (hn a)

end OAI.SKFluctuations.LaplaceWindowFormalization
