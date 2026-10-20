module

public import ComparisonPhysicalGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀ r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonSweepQuantile_spec (α : inverseIntegralConstraints 0 0 k M)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    α.val.val (comparisonSweepQuantile hc hk hkc hm hM α u)=u := by
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM α hu]
  exact constrainedQuantile_spec zero_le_one hc hk hkc hm hM α ⟨u,hu⟩

theorem comparisonSweepQuantile_lipschitzOn (α : inverseIntegralConstraints 0 0 k M) :
    LipschitzOnWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩
      (comparisonSweepQuantile hc hk hkc hm hM α) (Icc (0:ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hh := (constrainedQuantile_lipschitz zero_le_one hc hk hkc hm hM α).dist_le_mul
    ⟨u,hu⟩ ⟨v,hv⟩
  simpa only [comparisonSweepQuantile_eq hc hk hkc hm hM α hu,
    comparisonSweepQuantile_eq hc hk hkc hm hM α hv,Subtype.dist_eq,NNReal.coe_mk,one_div] using hh

theorem comparisonSweepQuantile_strictMono (α : inverseIntegralConstraints 0 0 k M) :
    StrictMonoOn (comparisonSweepQuantile hc hk hkc hm hM α) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hh := comparisonSweepQuantile_monotone hc hk hkc hm hM α huv.le
  have hne : comparisonSweepQuantile hc hk hkc hm hM α u≠
      comparisonSweepQuantile hc hk hkc hm hM α v := by
    intro he
    have ht := congrArg α.val.val he
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α hu,
      comparisonSweepQuantile_spec hc hk hkc hm hM α hv] at ht
    exact huv.ne ht
  exact lt_of_le_of_ne hh hne

theorem comparisonSweepQuantile_zero (α : inverseIntegralConstraints 0 0 k M) :
    comparisonSweepQuantile hc hk hkc hm hM α 0=0 := by
  simpa only [α.property.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α (r := 0) (by norm_num)

theorem comparisonSweepQuantile_one (α : inverseIntegralConstraints 0 0 k M) :
    comparisonSweepQuantile hc hk hkc hm hM α 1=1 := by
  simpa only [α.property.2.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α (r := 1) (by norm_num)

theorem comparisonSweepQuantile_gap (α : inverseIntegralConstraints 0 0 k M)
    (hMp : 0<M 1) {u v : ℝ} (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u≤v) :
    (M 1)⁻¹*(v-u)≤comparisonSweepQuantile hc hk hkc hm hM α v-
      comparisonSweepQuantile hc hk hkc hm hM α u := by
  have hq := comparisonSweepQuantile_monotone hc hk hkc hm hM α huv
  have hh := (inverseIntegralConstraints_lipschitz hm hM α.property).dist_le_mul
    (comparisonSweepQuantile hc hk hkc hm hM α v) (comparisonSweepQuantile_bounds hc hk hkc hm hM α v)
    (comparisonSweepQuantile hc hk hkc hm hM α u) (comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  rw [comparisonSweepQuantile_spec hc hk hkc hm hM α hv,
    comparisonSweepQuantile_spec hc hk hkc hm hM α hu] at hh
  simp only [NNReal.coe_mk,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr huv),
    abs_of_nonneg (sub_nonneg.mpr hq)] at hh
  exact (inv_mul_le_iff₀ hMp).mpr hh

theorem comparisonSweepQuantile_ae_slope (α : inverseIntegralConstraints 0 0 k M)
    (hMc : Continuous M) (hMp : ∀u∈Icc (0:ℝ) 1,0<M u) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      (M u)⁻¹≤deriv (comparisonSweepQuantile hc hk hkc hm hM α) u ∧
      deriv (comparisonSweepQuantile hc hk hkc hm hM α) u≤
        (k (comparisonSweepQuantile hc hk hkc hm hM α u))⁻¹ := by
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  have hal := inverseIntegralConstraints_lipschitz hm hM α.property
  have had : α.val∈inverseDifferentialConstraints 0 0 k M := by
    rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hMc hm hM]
    exact α.property
  obtain ⟨_,_,_,_,hder⟩ := had
  have hac : AbsolutelyContinuousOnInterval α.val.val 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨M 1,hM⟩)
    simpa only [uIcc_of_le zero_le_one] using hal
  have hdiff : ∀ᵐ r∂volume,r∈Icc (0:ℝ) 1 → DifferentiableAt ℝ α.val.val r := by
    simpa only [uIcc_of_le zero_le_one] using hac.ae_differentiableAt
  have hboth : ∀ᵐ r∂volume,r∈Icc (0:ℝ) 1 → DifferentiableAt ℝ α.val.val r ∧
      k r≤deriv α.val.val r ∧ deriv α.val.val r≤M (α.val.val r) := by
    filter_upwards [hdiff,hder] with r hd hb hr
    exact ⟨hd hr,hb hr⟩
  have hpull := ae_inverse_pullback hal
    (fun u (_ : u∈Icc (0:ℝ) 1) => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
    (fun u hu => comparisonSweepQuantile_spec hc hk hkc hm hM α hu) hboth
  filter_upwards [hpull,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with u hp hu0 hu1 hu
  have hui : u∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩
  have hspec : α.val.val (q u)=u := comparisonSweepQuantile_spec hc hk hkc hm hM α hu
  have hbd := (hp hu).2
  have hkp : 0<k (q u) := hc.trans_le (hkc (q u) (comparisonSweepQuantile_bounds hc hk hkc hm hM α u))
  have hdp : 0<deriv α.val.val (q u) := hkp.trans_le hbd.1
  have hleft : ∀ᶠ v in 𝓝 u,α.val.val (q v)=v := by
    filter_upwards [Icc_mem_nhds hui.1 hui.2] with v hv
    exact comparisonSweepQuantile_spec hc hk hkc hm hM α hv
  have hd := ((hp hu).1.hasDerivAt.of_local_left_inverse
    (comparisonSweepQuantile_continuous hc hk hkc hm hM α).continuousAt hdp.ne' hleft).deriv
  change deriv q u=(deriv α.val.val (q u))⁻¹ at hd
  change (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹
  rw [hd]
  rw [hspec] at hbd
  exact ⟨(inv_le_inv₀ (hMp u hu) hdp).mpr hbd.2,
    (inv_le_inv₀ hdp hkp).mpr hbd.1⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
