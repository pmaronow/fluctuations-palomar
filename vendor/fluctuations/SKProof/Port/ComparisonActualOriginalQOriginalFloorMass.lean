module

public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import ComparisonActualHighWallThetaZeroSelectedPotential
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
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.positiveRadiusSet
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : Set ℝ := Icc M.data.rmin 1 ∩ p.H ⁻¹' Ioi 0

theorem Potential.positiveRadiusSet_measurable
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : MeasurableSet p.positiveRadiusSet := by
  have hc : ContinuousOn p.H (Icc M.data.rmin 1) := by
    simpa only [uIcc_of_le M.data.hr] using p.hH.continuousOn
  have hclosed : IsClosed (Icc M.data.rmin 1 ∩ p.H ⁻¹' Iic 0) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have he : p.positiveRadiusSet=Icc M.data.rmin 1 \ (Icc M.data.rmin 1 ∩ p.H ⁻¹' Iic 0) := by
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
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : ℝ := p.positiveRadiusSet.indicator (fun _=>1) (M.sweepRadius u)

theorem Potential.positiveMassMask_zero_iff
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : p.positiveMassMask u=0 ↔ p.H (M.sweepRadius u) ≤ 0 := by
  have hr := M.sweepRadius_bounds u

  by_cases hp : 0 < p.H (M.sweepRadius u)
  · have hm : M.sweepRadius u∈p.positiveRadiusSet := ⟨hr,hp⟩
    simp [positiveMassMask,hm,not_le_of_gt hp]
  · have hm : M.sweepRadius u∉p.positiveRadiusSet := fun h=>hp h.2
    simp [positiveMassMask,hm,le_of_not_gt hp]

theorem Potential.positiveMassMask_integrable
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : IntegrableOn p.positiveMassMask (Icc (0:ℝ) 1) := by
  have hm : Measurable p.positiveMassMask :=
    (measurable_const.indicator p.positiveRadiusSet_measurable).comp
      (M.sweepRadius_continuous).measurable

  have hi : IntervalIntegrable p.positiveMassMask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>by dsimp [positiveMassMask];by_cases h:M.sweepRadius u∈p.positiveRadiusSet <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  exact intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one |>.mp hi

theorem Potential.positiveMassMask_mass_le
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    (∫u in Icc (0:ℝ) 1,p.positiveMassMask u) ≤ M.data.s+M.data.N^(-delta)*M.data.U := by
  have hi : IntervalIntegrable p.positiveMassMask volume 0 1:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr p.positiveMassMask_integrable
  have hilo : IntervalIntegrable p.positiveMassMask volume 0 M.data.s:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl M.data.hs1)
  have hihi : IntervalIntegrable p.positiveMassMask volume M.data.s 1:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have Hlow : (∫u in 0..M.data.s,p.positiveMassMask u) ≤ M.data.s := by
    have H:=intervalIntegral.integral_mono_on M.data.hs.1.le hilo intervalIntegrable_const
      (fun u hu=>show p.positiveMassMask u≤1 by
        dsimp only [Potential.positiveMassMask]
        by_cases h:M.sweepRadius u∈p.positiveRadiusSet <;> simp [h])
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_zero,mul_one] using H
  have Hsubst : (∫u in M.data.s..1,p.positiveMassMask u)=
      ∫r in Icc M.data.rmin 1,deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r := by
    have H:=M.shiftedNativeModel.mass_radius_cell_substitution p.positiveMassMask
      (show M.data.s∈Icc M.data.s 1 from ⟨le_rfl,M.data.hs1⟩)
      (show (1:ℝ)∈Icc M.data.s 1 from ⟨M.data.hs1,le_rfl⟩) M.data.hs1
    rw [M.shiftedNativeModel.R_left,M.shiftedNativeModel.R_one] at H
    apply H.trans
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    have Hinv:=M.shiftedNativeModel.R_inverse hr
    change M.sweepRadius (M.alpha.val.val r)=r at Hinv
    dsimp only [Potential.positiveMassMask]
    rw [Hinv]
  have hsub : p.positiveRadiusSet ⊆ Icc M.data.rmin 1 := inter_subset_left
  have hf : ∀ᵐr,r∈Icc M.data.rmin 1 → r∈p.positiveRadiusSet →
      deriv M.alpha.val.val r=comparisonFloor M.data.N delta M.data.U r := by
    filter_upwards [p.hfloor] with r hr hri hp
    exact hr hri hp.2
  have H:=comparisonFloor_region_mass M.data.hN M.data.hU
    (show M.data.rmin∈Icc (0:ℝ) 1 from ⟨M.data.rmin_nonneg,M.data.hr⟩) p.positiveRadiusSet
    p.positiveRadiusSet_measurable M.alpha.val.val hf
  have he : (fun r=>deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r)=
      p.positiveRadiusSet.indicator (deriv M.alpha.val.val) := by
    funext r
    by_cases h:r∈p.positiveRadiusSet <;> simp [h]
  rw [he,setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub] at Hsubst
  rw [setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub] at H
  have Hhigh : (∫u in M.data.s..1,p.positiveMassMask u) ≤ M.data.N^(-delta)*M.data.U:=
    Hsubst.trans_le H
  have Hadd:=intervalIntegral.integral_add_adjacent_intervals hilo hihi
  have Heq : (∫u in Icc (0:ℝ) 1,p.positiveMassMask u)=∫u in 0..1,p.positiveMassMask u := by
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  rw [Heq,←Hadd]
  exact add_le_add Hlow Hhigh

variable {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def Potential.originalOrderFloor (p : M.Potential) : Set ParisiFinite.OrderPoint :=
  {w | 0 < p.H (M.sweepRadius w)}

theorem Potential.originalOrderFloor_eq_preimage (p : M.Potential) :
    p.originalOrderFloor=(fun w : ParisiFinite.OrderPoint=>M.sweepRadius w) ⁻¹' p.positiveRadiusSet := by
  ext w
  have hr:=M.sweepRadius_bounds (w:ℝ)

  exact ⟨fun hw=>⟨hr,hw⟩,fun hw=>hw.2⟩

theorem Potential.originalOrderFloor_measurable (p : M.Potential) :
    MeasurableSet p.originalOrderFloor := by
  rw [p.originalOrderFloor_eq_preimage]
  exact p.positiveRadiusSet_measurable.preimage
    ((M.sweepRadius_continuous).measurable.comp measurable_subtype_coe)

theorem Potential.originalOrderFloor_indicator (p : M.Potential) (w : ParisiFinite.OrderPoint) :
    p.originalOrderFloor.indicator (fun _=>(1:ℝ)) w=p.positiveMassMask w := by
  rw [p.originalOrderFloor_eq_preimage]
  rfl

theorem Potential.originalOrderFloor_mass_le (p : M.Potential) (v : ℝ) :
    ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}).real
      p.originalOrderFloor ≤ M.data.s+M.data.N^(-delta)*M.data.U := by
  have hglobal : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      p.originalOrderFloor ≤ M.data.s+M.data.N^(-delta)*M.data.U := by
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
      (M.data.s+M.data.N^(-delta)*M.data.U)/x := by
  unfold comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  have H:=div_le_div_of_nonneg_right (p.originalOrderFloor_mass_le v) hx.le
  convert H using 1; ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
