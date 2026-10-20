module

public import ComparisonActualHighWallThetaZeroCapComponents
public import ComparisonActualHighWallThetaZeroSelectedAmplitude
public import ComparisonShiftedNativeMassSliceGeometry
public import ComparisonNativeActualOuterFloorThermalMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def Potential.positiveSet (P : Q.Potential) : Set ℝ :=
  Icc Q.data.rmin 1 ∩ P.H ⁻¹' Ioi 0

theorem Potential.positiveSet_measurable (P : Q.Potential) :
    MeasurableSet P.positiveSet := by
  have hc : ContinuousOn P.H (Icc Q.data.rmin 1) := by
    simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
  have hclosed : IsClosed (Icc Q.data.rmin 1 ∩ P.H ⁻¹' Iic 0) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have heq : P.positiveSet = Icc Q.data.rmin 1 \ (Icc Q.data.rmin 1 ∩ P.H ⁻¹' Iic 0) := by
    ext r
    simp only [Potential.positiveSet,Set.mem_sdiff,mem_inter_iff,mem_preimage,
      mem_Ioi,mem_Iic]
    constructor
    · rintro ⟨hr,hp⟩
      exact ⟨hr,fun h=>not_le_of_gt hp h.2⟩
    · rintro ⟨hr,hp⟩
      exact ⟨hr,lt_of_not_ge (fun h=>hp ⟨hr,h⟩)⟩
  rw [heq]
  exact measurableSet_Icc.diff hclosed.measurableSet

theorem actual_mass_slab_radius_lower
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {lo r : ℝ} (hlo : cu*Az*Q.xs < lo)
    (hr : r ∈ Icc Q.data.rmin 1) (hmass : lo ≤ Q.alpha.val.val r) :
    lo/cu ≤ r := by
  have hzr : Q.z ≤ r := by
    by_contra hh
    have halpha := Q.alpha.val.property.2 (lt_of_not_ge hh).le
    have hzreg := (Q.regular Q.z ⟨le_rfl,Q.hz.2⟩).2
    have hzupper := mul_le_mul_of_nonneg_left Q.hzxs hcu.le
    nlinarith only [halpha,hzreg,hzupper,hlo,hmass]
  have hreg := (Q.regular r ⟨hzr,hr.2⟩).2
  exact (div_le_iff₀ hcu).mpr (by linarith only [hmass,hreg])

theorem Potential.positive_floor_mass_global (P : Q.Potential) :
    (∫u in Q.data.s..1,P.positiveSet.indicator (fun _=>(1:ℝ))
      (Q.shiftedNativeModel.R u)) ≤
        Q.data.N^(-delta)*comparisonSmallMass Q.data.N Q.data.E := by
  let model := Q.shiftedNativeModel
  let mask := fun u=>P.positiveSet.indicator (fun _=>(1:ℝ)) (model.R u)
  have hsubst := model.mass_radius_cell_substitution mask
    (show Q.data.s∈Icc Q.data.s 1 from ⟨le_rfl,Q.data.hs1⟩)
    (show (1:ℝ)∈Icc Q.data.s 1 from ⟨Q.data.hs1,le_rfl⟩) Q.data.hs1
  rw [model.R_left,model.R_one] at hsubst
  have he : (∫r in Icc Q.data.rmin 1,deriv Q.alpha.val.val r*
      mask (Q.alpha.val.val r))=
        ∫r in Icc Q.data.rmin 1,P.positiveSet.indicator (deriv Q.alpha.val.val) r := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    have hinv := model.R_inverse hr
    dsimp only [mask]
    rw [hinv]
    by_cases hp:r∈P.positiveSet <;> simp [hp]
  have hf : ∀ᵐ r, r ∈ Icc Q.data.rmin 1 → r ∈ P.positiveSet →
      deriv Q.alpha.val.val r=comparisonFloor Q.data.N delta
        (comparisonSmallMass Q.data.N Q.data.E) r := by
    filter_upwards [P.hfloor] with r hr hri hp
    exact hr hri hp.2
  have Hfloor := comparisonFloor_region_mass Q.data.hN Q.data.hU
    ⟨Q.data.hrbounds.1.le,Q.data.hr⟩ P.positiveSet
    P.positiveSet_measurable Q.alpha.val.val hf
  have hposSub : P.positiveSet ⊆ Icc Q.data.rmin 1 := inter_subset_left
  rw [setIntegral_indicator P.positiveSet_measurable,
    inter_eq_right.mpr hposSub] at Hfloor
  change (∫u in Q.data.s..1,mask u) ≤ _
  rw [hsubst,he,setIntegral_indicator P.positiveSet_measurable,
    inter_eq_right.mpr hposSub]
  exact Hfloor

theorem Potential.positive_floor_mass_on_band
    (P : Q.Potential) (hcu : 0 < cu) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1)
    (houter : cu*Az*Q.xs < lo) :
    (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u)) ≤
      Q.data.N^delta*(comparisonSmallMass Q.data.N Q.data.E)^2/(lo/cu) := by
  let model := Q.shiftedNativeModel
  let rlo := model.R lo
  let rhi := model.R hi
  let pos := P.positiveSet.indicator (fun _=>(1:ℝ))
  have hloI : lo ∈ Icc Q.data.s 1 := ⟨hlo,hlohi.trans hhi⟩
  have hhiI : hi ∈ Icc Q.data.s 1 := ⟨hlo.trans hlohi,hhi⟩
  have hrlo := model.R_bounds lo
  have hrhi := model.R_bounds hi
  have hrlo0 : 0 < rlo := Q.data.hrbounds.1.trans_le hrlo.1
  have hrlohi : rlo ≤ rhi := model.R_monotone hlohi
  have hspec : Q.alpha.val.val rlo=lo := model.R_spec hloI
  have hrloLower : lo/cu ≤ rlo := Q.actual_mass_slab_radius_lower hcu houter hrlo hspec.ge
  have hsub : Icc rlo rhi ⊆ Icc Q.data.rmin 1 := Icc_subset_Icc hrlo.1 hrhi.2
  have hsubst := model.mass_radius_cell_substitution
    (fun u=>pos (model.R u)) hloI hhiI hlohi
  change (∫u in lo..hi,pos (model.R u))=
    ∫r in Icc rlo rhi,deriv Q.alpha.val.val r*pos (model.R (Q.alpha.val.val r)) at hsubst
  have he : (∫r in Icc rlo rhi,deriv Q.alpha.val.val r*pos (model.R (Q.alpha.val.val r)))=
      ∫r in Icc rlo rhi,Q.data.k r*pos r := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [P.hfloor] with r hr hri
    rw [model.R_inverse (hsub hri)]
    by_cases hp : r∈P.positiveSet
    · have hd := hr (hsub hri) hp.2
      simp only [pos,indicator_of_mem hp,hd, mul_one]
    · simp only [pos,indicator_of_notMem hp,mul_zero]
  rw [hsubst,he]
  have hposMeas : Measurable pos := measurable_const.indicator P.positiveSet_measurable
  have hki : IntegrableOn Q.data.k (Icc rlo rhi) :=
    ((comparisonFloor_continuousOn (δ:=delta) Q.data.hN Q.data.hU hrlo0.le).mono
      (Icc_subset_Icc le_rfl hrhi.2)).integrableOn_Icc
  have hipos : IntegrableOn (fun r=>Q.data.k r*pos r) (Icc rlo rhi) := by
    simpa only [IntegrableOn,Pi.mul_apply,mul_comm] using
      hki.bdd_mul (c:=(1:ℝ)) hposMeas.aestronglyMeasurable.restrict
        (Eventually.of_forall (fun r=>by
          by_cases hp:r∈P.positiveSet <;> simp [pos,hp]))
  have Hpoint : (∫r in Icc rlo rhi,Q.data.k r*pos r)≤∫r in Icc rlo rhi,Q.data.k r := by
    apply integral_mono_ae hipos hki
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hk0 : 0≤Q.data.k r :=
      (comparisonFloor_pos (δ:=delta) Q.data.hN Q.data.hU (hrlo0.le.trans hr.1)).le
    by_cases hp:r∈P.positiveSet <;> simp [pos,hp,hk0]
  have htailInt : IntegrableOn Q.data.k (Icc rlo 1) :=
    (comparisonFloor_continuousOn (δ:=delta) Q.data.hN Q.data.hU hrlo0.le).integrableOn_Icc
  have Hmono : (∫r in Icc rlo rhi,Q.data.k r)≤∫r in Icc rlo 1,Q.data.k r := by
    apply setIntegral_mono_set htailInt
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (comparisonFloor_pos (δ:=delta) Q.data.hN Q.data.hU (hrlo0.le.trans hr.1)).le
    · exact Eventually.of_forall (Icc_subset_Icc le_rfl hrhi.2)
  have Htail := comparison_floor_tail_mass_le (delta:=delta)
    Q.data.hN Q.data.hU hrlo0 hrlo.2
  have hlo0 : 0 < lo := Q.data.hs.1.trans_le hlo
  exact (Hpoint.trans (Hmono.trans Htail)).trans
    (div_le_div_of_nonneg_left (by positivity) (div_pos hlo0 hcu) hrloLower)

theorem Potential.thermal_sign_partition_on_band
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    (∫u in lo..hi,Q.shiftedNativeModel.thermal u) =
      (∫u in lo..hi,(P.negativeSet ∪ P.contactSet).indicator (fun _=>(1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)+
      (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) := by
  let model := Q.shiftedNativeModel
  have hmi : MeasurableSet (P.negativeSet ∪ P.contactSet) :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hn := (model.thermal_mask_integrable _ hmi).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi)
  have hp := (model.thermal_mask_integrable _ P.positiveSet_measurable).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi)
  rw [←intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne hi] with u hune hu
  have hu0 : u∈Ioc lo hi := by simpa only [uIoc_of_le hlohi] using hu
  have huOpen : u∈Ioo lo hi := ⟨hu0.1,lt_of_le_of_ne hu0.2 hune⟩
  have hum : u∈Icc Q.data.s 1 := ⟨hlo.trans huOpen.1.le,huOpen.2.le.trans hhi⟩
  have hR : model.R u∈Ioo Q.data.rmin 1 := by
    have hleft : model.R Q.data.s < model.R u :=
      model.R_strictMonoOn ⟨le_rfl,Q.data.hs1⟩ hum (hlo.trans_lt huOpen.1)
    have hright : model.R u < model.R 1 :=
      model.R_strictMonoOn hum ⟨Q.data.hs1,le_rfl⟩ (huOpen.2.trans_le hhi)
    rw [show model.R Q.data.s = Q.data.rmin from model.R_left] at hleft
    rw [model.R_one] at hright
    exact ⟨hleft,hright⟩
  have hnon : (model.R u∈P.negativeSet∪P.contactSet) ↔ P.H (model.R u)≤0 := by
    constructor
    · rintro (h|h)
      · exact h.2.le
      · exact h.2.le
    · intro h
      rcases lt_or_eq_of_le h with hneg|hz
      · exact Or.inl ⟨hR,hneg⟩
      · exact Or.inr ⟨Ioo_subset_Icc_self hR,hz⟩
  have hpos : (model.R u∈P.positiveSet) ↔ 0<P.H (model.R u) :=
    ⟨fun h=>h.2,fun h=>⟨Ioo_subset_Icc_self hR,h⟩⟩
  by_cases hH : 0<P.H (model.R u)
  · have hp : model.R u∈P.positiveSet := hpos.mpr hH
    have hn : model.R u∉P.negativeSet∪P.contactSet := fun h=>not_le_of_gt hH (hnon.mp h)
    simp only [indicator_of_mem hp,indicator_of_notMem hn,zero_mul,one_mul,zero_add]
    rfl
  · have hn : model.R u∈P.negativeSet∪P.contactSet := hnon.mpr (le_of_not_gt hH)
    have hp : model.R u∉P.positiveSet := fun h=>hH (hpos.mp h)
    simp only [indicator_of_mem hn,indicator_of_notMem hp,one_mul,zero_mul,add_zero]
    rfl

end ActualThetaZeroOverlapMinimum

theorem eventually_actual_theta_zero_positive_floor_thermal_on_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀(Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (lo hi : ℝ),
        Q.data.s ≤ lo → lo ≤ hi → hi ≤ 1 → cu*Az*Q.xs < lo →
        (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
          K*(Q.xs+hi)^2*Q.data.N^delta*
            (comparisonSmallMass Q.data.N Q.data.E)^2/(lo/cu) := by
  obtain ⟨K,hK,Hamp⟩ := eventually_actual_theta_zero_selected_B_normalized
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [Hamp] with n hn
  intro Q P lo hi hlo hlohi hhi houter
  let model := Q.shiftedNativeModel
  let mask := fun u=>P.positiveSet.indicator (fun _=>(1:ℝ)) (model.R u)
  let C := K*(Q.xs+hi)^2
  have hband : Icc lo hi⊆Icc (0:ℝ) 1 :=
    Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi
  have hiT := (model.thermal_mask_integrable P.positiveSet P.positiveSet_measurable).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact hband)
  have hmaskMeas : Measurable mask :=
    (measurable_const.indicator P.positiveSet_measurable).comp model.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume lo hi := by
    have hfull : IntervalIntegrable mask volume 0 1 := by
      simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmaskMeas
        (show (0:ℝ) ≤ 1 from zero_le_one)
        (fun u _=>by dsimp [mask];by_cases h:model.R u∈P.positiveSet <;> simp [h])
        (intervalIntegrable_const (c:=(1:ℝ)))
    exact hfull.mono_set (by
      rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
      exact hband)
  have hmass := P.positive_floor_mass_on_band hcu hlo hlohi hhi houter
  have Hpoint : (∫u in lo..hi,mask u*model.thermal u) ≤
      ∫u in lo..hi,C*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict hlohi hiT (hiMask.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have huPos : u∈Ioc (0:ℝ) 1 :=
      ⟨Q.data.hs.1.trans_le (hlo.trans hu.1),hu.2.trans hhi⟩
    have Hraw := hn Q u huPos
    have hsq := pow_le_pow_left₀ (add_pos Q.hxs huPos.1).le
      (show Q.xs+u ≤ Q.xs+hi by linarith [hu.2]) 2
    have Hthermal : model.thermal u ≤ C := by
      change orderedPathB (n+1) Q.sweepBf Q.sweepHf u-
        (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2≤C
      have HH:=mul_le_mul_of_nonneg_left hsq hK.le
      exact (sub_le_self _ (sq_nonneg (orderedPathS (n+1) Q.sweepBf Q.sweepHf u))).trans
        (Hraw.trans HH)
    have hmask0 : 0 ≤ mask u := by
      dsimp [mask]
      by_cases hp:model.R u∈P.positiveSet <;> simp [hp]
    calc
      mask u*model.thermal u ≤ mask u*C := mul_le_mul_of_nonneg_left Hthermal hmask0
      _ = C*mask u := mul_comm _ _
  rw [intervalIntegral.integral_const_mul] at Hpoint
  have hC : 0≤C := by dsimp [C];positivity
  have Hmass := mul_le_mul_of_nonneg_left hmass hC
  have Hfinal := Hpoint.trans Hmass
  change (∫u in lo..hi,mask u*model.thermal u) ≤ _
  convert Hfinal using 1 <;> dsimp only [C] <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
