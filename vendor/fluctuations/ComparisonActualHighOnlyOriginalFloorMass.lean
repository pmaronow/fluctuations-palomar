module

public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyPotential
public import ComparisonNativeActualOriginalFloorMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
attribute [local instance] Measure.Subtype.measureSpace
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.positiveRadiusSet
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : Set ℝ := Icc (0:ℝ) 1 ∩ p.H ⁻¹' Ioi 0

theorem Potential.positiveRadiusSet_measurable
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : MeasurableSet p.positiveRadiusSet := by
  have hc : ContinuousOn p.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using p.hH.continuousOn
  have hclosed : IsClosed (Icc (0:ℝ) 1 ∩ p.H ⁻¹' Iic 0) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have he : p.positiveRadiusSet=Icc (0:ℝ) 1 \ (Icc (0:ℝ) 1 ∩ p.H ⁻¹' Iic 0) := by
    ext r
    simp only [positiveRadiusSet,mem_inter_iff,mem_preimage,mem_Ioi,Set.mem_sdiff,mem_Iic]
    constructor
    · rintro ⟨hr,hpos⟩
      exact ⟨hr,fun hh=>not_le_of_gt hpos hh.2⟩
    · rintro ⟨hr,hnot⟩
      exact ⟨hr,lt_of_not_ge (fun hh=>hnot ⟨hr,hh⟩)⟩
  rw [he]
  exact measurableSet_Icc.diff hclosed.measurableSet

def Potential.positiveMassMask
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : ℝ := p.positiveRadiusSet.indicator (fun _=>1) (M.R u)

theorem Potential.positiveMassMask_zero_iff
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : p.positiveMassMask u=0 ↔ p.H (M.R u) ≤ 0 := by
  have hr := omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  by_cases hp : 0 < p.H (M.R u)
  · have hm : M.R u∈p.positiveRadiusSet := ⟨hr,hp⟩
    simp [positiveMassMask,hm,not_le_of_gt hp]
  · have hm : M.R u∉p.positiveRadiusSet := fun h=>hp h.2
    simp [positiveMassMask,hm,le_of_not_gt hp]

theorem Potential.positiveMassMask_integrable
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : IntegrableOn p.positiveMassMask (Icc (0:ℝ) 1) := by
  have hm : Measurable p.positiveMassMask :=
    (measurable_const.indicator p.positiveRadiusSet_measurable).comp
      (omittedSweepQuantile_continuous zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).measurable
  have hi : IntervalIntegrable p.positiveMassMask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>by dsimp [positiveMassMask];by_cases h:M.R u∈p.positiveRadiusSet <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  exact intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one |>.mp hi

theorem Potential.positiveMassMask_mass_le
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    (∫u in Icc (0:ℝ) 1,p.positiveMassMask u) ≤ M.data.s+M.context.N^(-delta)*M.context.U := by
  have hi : IntervalIntegrable p.positiveMassMask volume 0 1:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr p.positiveMassMask_integrable
  have hilo : IntervalIntegrable p.positiveMassMask volume 0 M.data.s:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl M.data.hs1)
  have hihi : IntervalIntegrable p.positiveMassMask volume M.data.s 1:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc M.data.hs.1 le_rfl)
  have Hlow : (∫u in 0..M.data.s,p.positiveMassMask u) ≤ M.data.s := by
    have H:=intervalIntegral.integral_mono_on M.data.hs.1 hilo intervalIntegrable_const
      (fun u hu=>show p.positiveMassMask u≤1 by
        dsimp only [Potential.positiveMassMask]
        by_cases h:M.R u∈p.positiveRadiusSet <;> simp [h])
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_zero,mul_one] using H
  have Hsubst : (∫u in M.data.s..1,p.positiveMassMask u)=
      ∫r in Icc (0:ℝ) 1,deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r := by
    have H:=M.shiftedNativeModel.mass_radius_cell_substitution p.positiveMassMask
      (show M.data.s∈Icc M.data.s 1 from ⟨le_rfl,M.data.hs1⟩)
      (show (1:ℝ)∈Icc M.data.s 1 from ⟨M.data.hs1,le_rfl⟩) M.data.hs1
    rw [M.shiftedNativeModel.R_left,M.shiftedNativeModel.R_one] at H
    apply H.trans
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    have Hinv:=M.shiftedNativeModel.R_inverse hr
    change M.R (M.alpha.val.val r)=r at Hinv
    dsimp only [Potential.positiveMassMask]
    rw [Hinv]
  have hsub : p.positiveRadiusSet ⊆ Icc (0:ℝ) 1 := inter_subset_left
  have hf : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈p.positiveRadiusSet →
      deriv M.alpha.val.val r=comparisonFloor M.context.N delta M.context.U r := by
    filter_upwards [p.hfloor] with r hr hri hp
    exact hr hri hp.2
  have H:=comparisonFloor_region_mass M.context.hN M.context.hU
    (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) p.positiveRadiusSet
    p.positiveRadiusSet_measurable M.alpha.val.val hf
  have he : (fun r=>deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r)=
      p.positiveRadiusSet.indicator (deriv M.alpha.val.val) := by
    funext r
    by_cases h:r∈p.positiveRadiusSet <;> simp [h]
  rw [he,setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub] at Hsubst
  rw [setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub] at H
  have Hhigh : (∫u in M.data.s..1,p.positiveMassMask u) ≤ M.context.N^(-delta)*M.context.U:=
    Hsubst.trans_le H
  have Hadd:=intervalIntegral.integral_add_adjacent_intervals hilo hihi
  have Heq : (∫u in Icc (0:ℝ) 1,p.positiveMassMask u)=∫u in 0..1,p.positiveMassMask u := by
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  rw [Heq,←Hadd]
  exact add_le_add Hlow Hhigh

variable {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def Potential.originalOrderFloor (p : M.Potential) : Set ParisiFinite.OrderPoint :=
  {w | 0 < p.H (M.R w)}

theorem Potential.originalOrderFloor_eq_preimage (p : M.Potential) :
    p.originalOrderFloor=(fun w : ParisiFinite.OrderPoint=>M.R w) ⁻¹' p.positiveRadiusSet := by
  ext w
  have hr:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (w:ℝ)
  exact ⟨fun hw=>⟨hr,hw⟩,fun hw=>hw.2⟩

theorem Potential.originalOrderFloor_measurable (p : M.Potential) :
    MeasurableSet p.originalOrderFloor := by
  rw [p.originalOrderFloor_eq_preimage]
  exact p.positiveRadiusSet_measurable.preimage
    ((omittedSweepQuantile_continuous zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).measurable.comp measurable_subtype_coe)

theorem Potential.originalOrderFloor_indicator (p : M.Potential) (w : ParisiFinite.OrderPoint) :
    p.originalOrderFloor.indicator (fun _=>(1:ℝ)) w=p.positiveMassMask w := by
  rw [p.originalOrderFloor_eq_preimage]
  rfl

theorem Potential.originalOrderFloor_mass_le (p : M.Potential) (v : ℝ) :
    ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}).real
      p.originalOrderFloor ≤ M.data.s+M.context.N^(-delta)*M.context.U := by
  have hglobal : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      p.originalOrderFloor ≤ M.data.s+M.context.N^(-delta)*M.context.U := by
    rw [←integral_indicator_one p.originalOrderFloor_measurable]
    simp_rw [show (1 : ParisiFinite.OrderPoint→ℝ)=(fun _=>(1:ℝ)) from rfl,
      p.originalOrderFloor_indicator]
    change (∫w : unitInterval,p.positiveMassMask (w:ℝ)∂volume) ≤ _
    rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe]
    exact p.positiveMassMask_mass_le
  rw [measureReal_restrict_apply' (measurableSet_le measurable_subtype_coe measurable_const)]
  exact (measureReal_mono inter_subset_left).trans hglobal

theorem Potential.originalOrderFloor_normalized_mass_le
    (p : M.Potential) (v : ℝ) {x : ℝ} (hx : 0 < x) :
    (comparisonNormalizedClockMass x v).real p.originalOrderFloor ≤
      (M.data.s+M.context.N^(-delta)*M.context.U)/x := by
  unfold comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  have H:=div_le_div_of_nonneg_right (p.originalOrderFloor_mass_le v) hx.le
  convert H using 1; ring

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
