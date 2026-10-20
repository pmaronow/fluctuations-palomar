module

public import ComparisonNativeGlobalErrorAssemblyDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

abbrev nativeActualPositiveSet (m : NativeBandModel) : Set ℝ :=
  Icc (0:ℝ) 1 ∩ m.H ⁻¹' Ioi 0

theorem nativeActualPositiveSet_measurable (m : NativeBandModel) :
    MeasurableSet (nativeActualPositiveSet m) := by
  have hc : ContinuousOn m.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn
  have hclosed : IsClosed (Icc (0:ℝ) 1 ∩ m.H ⁻¹' Iic 0) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have he : nativeActualPositiveSet m =
      Icc (0:ℝ) 1 \ (Icc (0:ℝ) 1 ∩ m.H ⁻¹' Iic 0) := by
    ext r
    simp only [nativeActualPositiveSet,mem_inter_iff,mem_preimage,mem_Ioi,
      Set.mem_sdiff,mem_Iic]
    constructor
    · rintro ⟨hr,hpos⟩
      exact ⟨hr,fun hh=>not_le_of_gt hpos hh.2⟩
    · rintro ⟨hr,hnot⟩
      exact ⟨hr,lt_of_not_ge (fun hle=>hnot ⟨hr,hle⟩)⟩
  rw [he]
  exact measurableSet_Icc.diff hclosed.measurableSet

theorem actual_native_error_eq_nonpositive_add_positive (m : NativeBandModel) :
    (∫u in 0..1,m.comparisonErrorDensity u)=
      (∫u in 0..1,(nativeNegativeSet m∪nativeActualContactSet m).indicator
        (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..1,(nativeActualPositiveSet m).indicator
        (fun _=>1) (m.R u)*m.comparisonErrorDensity u) := by
  have hn := nativeActualError_mask_integrable m _
    ((nativeNegativeSet_open m).measurableSet.union (nativeActualContactSet_measurable m))
  have hp := nativeActualError_mask_integrable m _ (nativeActualPositiveSet_measurable m)
  rw [←intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1:ℝ)] with u hune hu
  have hu : u∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
  have hR0 : m.R 0=0 := by
    simpa only [m.alpha.property.1] using comparisonSweepQuantile_inverse
      m.hc m.hk m.hkc m.hm m.hM m.alpha (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hR1 : m.R 1=1 := by
    simpa only [m.alpha.property.2.1] using comparisonSweepQuantile_inverse
      m.hc m.hk m.hkc m.hm m.hM m.alpha (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hs := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
  have hlo := hs (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) (Ioc_subset_Icc_self hu) hu.1
  have hhi := hs (Ioc_subset_Icc_self hu) (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) hu1
  change m.R 0 < m.R u at hlo
  change m.R u < m.R 1 at hhi
  rw [hR0] at hlo
  rw [hR1] at hhi
  have hri : m.R u∈Ioo (0:ℝ) 1 := ⟨hlo,hhi⟩
  have hrc : m.R u∈Icc (0:ℝ) 1 := Ioo_subset_Icc_self hri
  rcases lt_trichotomy (m.H (m.R u)) 0 with hneg|hzero|hpos
  · have hnmem : m.R u∈nativeNegativeSet m∪nativeActualContactSet m := Or.inl ⟨hri,hneg⟩
    have hpmem : m.R u∉nativeActualPositiveSet m := by
      intro hh
      have hhpos : 0 < m.H (m.R u) := hh.2
      exact lt_asymm hneg hhpos
    simp only [indicator_of_mem hnmem,indicator_of_notMem hpmem,one_mul,zero_mul,add_zero]
  · have hnmem : m.R u∈nativeNegativeSet m∪nativeActualContactSet m := Or.inr ⟨hrc,hzero⟩
    have hpmem : m.R u∉nativeActualPositiveSet m := by
      intro hh
      have hhpos : 0 < m.H (m.R u) := hh.2
      exact (ne_of_gt hhpos) hzero
    simp only [indicator_of_mem hnmem,indicator_of_notMem hpmem,one_mul,zero_mul,add_zero]
  · have hpmem : m.R u∈nativeActualPositiveSet m := ⟨hrc,hpos⟩
    have hnmem : m.R u∉nativeNegativeSet m∪nativeActualContactSet m := by
      rintro (hh|hh)
      · have hhneg : m.H (m.R u) < 0 := hh.2
        exact lt_asymm hhneg hpos
      · have hhzero : m.H (m.R u)=0 := hh.2
        exact (ne_of_gt hpos) hhzero
    simp only [indicator_of_mem hpmem,indicator_of_notMem hnmem,one_mul,zero_mul,zero_add]

namespace NativeOverlapMinimum
variable {n:ℕ} {margin delta cl cu Az C0 Ct D Bclock:ℝ}

theorem profile_upper_scale
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (hcu:0 < cu) (hAz:0≤Az) {r:ℝ} (hr:r∈Icc (0:ℝ) 1) :
    a.xs+a.alpha.val.val r≤(1+cu*(Az+1))*(a.xs+r) := by
  have hbound : a.alpha.val.val r≤cu*(Az*a.xs+r) := by
    by_cases hzr:a.z≤r
    · have hh := (a.regular r ⟨hzr,hr.2⟩).2
      nlinarith [mul_nonneg (mul_nonneg hcu.le hAz) a.hxs.le]
    · have hh := (a.alpha.val.property.2 (le_of_not_ge hzr)).trans
        (a.regular a.z ⟨le_rfl,a.hz.2⟩).2
      have hz := mul_le_mul_of_nonneg_left a.hzxs hcu.le
      nlinarith [mul_nonneg hcu.le hr.1]
  have hcuxs := mul_nonneg hcu.le a.hxs.le
  have hcur := mul_nonneg (mul_nonneg hcu.le hAz) hr.1
  nlinarith [hr.1]

theorem full_error_assembly_of_finite_band_consumers
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p:a.Potential) (g:a.BandGeometry p)
    (dphys:ℕ) (e:Fin (dphys+1)≃FeatureIndex (n+1))
    (hlog:1≤Real.log a.context.N) (hnd:1/a.context.N≤a.context.d)
    (bands:NativeFiniteBandConsumers (g.toModel dphys e hlog hnd))
    (hshort:nativeCapTravel (g.toModel dphys e hlog hnd) < 1)
    {K:ℝ} (hK:0≤K) (hcl:0 < cl) (hcu:0 < cu) (hAz:0≤Az)
    (hB:∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u≤K*(a.xs+u)^2) :
    a.FullErrorAssemblyTarget bands.budget K := by
  let m := g.toModel dphys e hlog hnd
  have hn := actual_full_native_nonpositive_error_le_of_finite_band_consumers m bands hshort
  have hi := actual_native_near_zero_error_of_normalized_B m hK hcl hAz a.hz a.hzxs
    (fun r hr=>(a.regular r hr).1) hB
  rw [nativeBroadNearZero_integral_eq_initial_mass] at hi
  have hp := actual_comparison_floor_error_of_normalized_B m (nativeActualPositiveSet m)
    (nativeActualPositiveSet_measurable m) a.hxs.le hK
    (show 0≤1+cu*(Az+1) by positivity)
    (by
      filter_upwards [p.hfloor] with r hf hr hrp
      exact hf hr hrp.2)
    hB (fun r hr _=>a.profile_upper_scale hcu hAz hr)
  have he := actual_native_error_eq_nonpositive_add_positive m
  unfold FullErrorAssemblyTarget
  change (∫u in 0..1,m.comparisonErrorDensity u)≤_
  rw [he]
  exact (add_le_add (hn.trans (add_le_add le_rfl hi)) hp)

theorem eventually_full_error_assembly_of_finite_band_consumers
    (Bclock:ℝ) (hm:0 < margin) (hdelta:0 < delta) (hroom:delta < 3*margin)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0≤Az) (hC0:0 < C0) (hCt:0≤Ct) :
    ∃K:ℝ,0 < K ∧ ∀ᶠ n:ℕ in atTop,
      ∀(a:NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (p:a.Potential) (g:a.BandGeometry p)
        (dphys:ℕ) (e:Fin (dphys+1)≃FeatureIndex (n+1))
        (hlog:1≤Real.log a.context.N) (hnd:1/a.context.N≤a.context.d)
        (bands:NativeFiniteBandConsumers (g.toModel dphys e hlog hnd)),
        a.FullErrorAssemblyTarget bands.budget K := by
  obtain ⟨K,hK,hB⟩ := eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have htravel := eventually_comparisonTravel_small (C:=C0) (D:=D)
    (m:=margin) (δ:=delta) (ε:=1 / (|D| + 1)) hC0 (by linarith)
    (by positivity)
  have hBs : ∀ᶠ n:ℕ in atTop,
      ∀a:NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
        ∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u≤K*(a.xs+u)^2 := by
    exact (tendsto_add_atTop_nat 1).eventually hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hBs,(tendsto_add_atTop_nat 1).eventually htravel] with n hn ht
  intro a p g dphys e hlog hnd bands
  have hscale : comparisonLowerScale (n+1 :ℕ) a.context.E a.context.d≤a.context.d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.context.hd).mpr (by simpa only [pow_two] using a.hupper)
  have hcap := ht a.context.E a.context.d a.context.hE a.context.hd
    a.hdD a.hupper a.hlower
  have hε : 0≤1 / (|D| + 1) := by positivity
  have hbound := hcap.trans (mul_le_mul_of_nonneg_left
    (hscale.trans (a.hdD.trans (le_abs_self D))) hε)
  have hunit : (1 / (|D| + 1))* |D| < 1 := by
    have hden : 0 < |D| + 1 := by positivity
    rw [one_div_mul_eq_div]
    exact (div_lt_one hden).mpr (by linarith)
  have hshort : nativeCapTravel (g.toModel dphys e hlog hnd) < 1 := hbound.trans_lt hunit
  exact a.full_error_assembly_of_finite_band_consumers p g dphys e hlog hnd bands
    hshort hK.le hcl hcu hAz (hn a)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
