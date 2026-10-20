module

public import ComparisonActualHighWallFloorThermalDistinct
public import ComparisonNativeActualOuterFloorThermalMass
public import ComparisonShiftedNativeBandCarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_mass_slab_radius_lower
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {lo r : ℝ} (hlo : cu*Az*M.xs < lo)
    (hr : r∈Icc M.data.rmin 1) (hmass : lo≤M.alpha.val.val r) : lo/cu≤r := by
  have hzr : M.z≤r := by
    by_contra hh
    have halpha := M.alpha.val.property.2 (lt_of_not_ge hh).le
    have hzreg := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have hzupper := mul_le_mul_of_nonneg_left M.hzxs hcu.le
    nlinarith only [halpha,hzreg,hzupper,hlo,hmass]
  have hreg := (M.regular r ⟨hzr,hr.2⟩).2
  exact (div_le_iff₀ hcu).mpr (by linarith only [hmass,hreg])

theorem Potential.positiveMassMask_outer_on_band
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (hcu : 0 < cu) {lo hi : ℝ}
    (hlo : M.data.s≤lo) (hlohi : lo≤hi) (hhi : hi≤1) (hscale : cu*Az*M.xs<lo) :
    (∫u in Ioo lo hi,p.positiveMassMask u)≤
      M.data.N^delta*(comparisonSmallMass M.data.N M.data.E)^2/(lo/cu) := by
  let model := M.shiftedNativeModel
  let rlo := M.data.wallRadius M.alpha lo
  let rhi := M.data.wallRadius M.alpha hi
  let pos := ({r | 0 < p.starExtendedH r}).indicator (fun _=>(1:ℝ))
  have hrlo := M.data.wallRadius_bounds M.alpha lo
  have hrhi := M.data.wallRadius_bounds M.alpha hi
  have hrlo0 : 0 < rlo := M.data.hrbounds.1.trans_le hrlo.1
  have hrhi1 : rhi≤1 := hrhi.2
  have hrlohi : rlo≤rhi := M.data.wallRadius_monotone M.alpha hlohi
  have hrlo1 : rlo≤1 := hrlo.2
  have hspec := M.data.wallRadius_spec M.alpha ⟨hlo,hlohi.trans hhi⟩
  have hlower : lo/cu≤rlo := M.actual_mass_slab_radius_lower hcu hscale hrlo hspec.ge
  have hsub : Icc rlo rhi⊆Icc M.data.rmin 1 := Icc_subset_Icc hrlo.1 hrhi.2
  have hsubst := model.mass_radius_cell_substitution p.positiveMassMask
    ⟨hlo,hlohi.trans hhi⟩ ⟨hlo.trans hlohi,hhi⟩ hlohi
  rw [intervalIntegral.integral_of_le hlohi,integral_Ioc_eq_integral_Ioo] at hsubst
  change (∫u in Ioo lo hi,p.positiveMassMask u)=
    ∫r in Icc rlo rhi,deriv M.alpha.val.val r*p.positiveMassMask (M.alpha.val.val r) at hsubst
  have he : (∫r in Icc rlo rhi,deriv M.alpha.val.val r*p.positiveMassMask (M.alpha.val.val r))=
      ∫r in Icc rlo rhi,M.data.k r*pos r := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [p.hfloor] with r hr hri
    have hext : p.starExtendedH r=p.H r := by
      dsimp only [Potential.starExtendedH]
      rw [projIcc_of_mem M.data.hr (hsub hri)]
    have hm : p.positiveMassMask (M.alpha.val.val r)=pos r := by
      dsimp only [Potential.positiveMassMask,comparisonCalibrationFloor,pos]
      simp only [indicator_apply,mem_ofPred_eq]
      simp only [M.data.wallRadius_inverse M.alpha (hsub hri),hext]
    rw [hm]
    by_cases hp : 0 < p.starExtendedH r
    · have hd := hr (hsub hri) (hext ▸ hp)
      rw [hd]
    · simp only [pos,indicator_of_notMem (show r∉{r | 0 < p.starExtendedH r} from hp),mul_zero]
  rw [hsubst,he]
  have hposMeas : Measurable pos := measurable_const.indicator
    (measurableSet_lt measurable_const p.starExtendedH_continuous.measurable)
  have hki : IntegrableOn M.data.k (Icc rlo rhi) :=
    ((comparisonFloor_continuousOn (δ:=delta) M.data.hN M.data.hU hrlo0.le).mono
      (Icc_subset_Icc le_rfl hrhi1)).integrableOn_Icc
  have hipos : IntegrableOn (fun r=>M.data.k r*pos r) (Icc rlo rhi) := by
    simpa only [IntegrableOn,Pi.mul_apply,mul_comm] using hki.bdd_mul (c:=(1:ℝ)) hposMeas.aestronglyMeasurable.restrict
      (Eventually.of_forall (fun r=>by
        by_cases hp:r∈{r | 0 < p.starExtendedH r} <;> simp [pos,hp]))
  have Hpoint : (∫r in Icc rlo rhi,M.data.k r*pos r)≤∫r in Icc rlo rhi,M.data.k r := by
    apply integral_mono_ae hipos hki
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hk0 : 0≤M.data.k r :=
      (comparisonFloor_pos (δ:=delta) M.data.hN M.data.hU (hrlo0.le.trans hr.1)).le
    by_cases hp:r∈{r | 0 < p.starExtendedH r} <;> simp [pos,hp,hk0]
  have htailInt : IntegrableOn M.data.k (Icc rlo 1) :=
    (comparisonFloor_continuousOn (δ:=delta) M.data.hN M.data.hU hrlo0.le).integrableOn_Icc
  have Hmono : (∫r in Icc rlo rhi,M.data.k r)≤∫r in Icc rlo 1,M.data.k r := by
    apply setIntegral_mono_set htailInt
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (comparisonFloor_pos (δ:=delta) M.data.hN M.data.hU (hrlo0.le.trans hr.1)).le
    · exact Eventually.of_forall (Icc_subset_Icc le_rfl hrhi1)
  have Htail := comparison_floor_tail_mass_le (delta:=delta) M.data.hN M.data.hU hrlo0 hrlo1
  have hlo0 : 0 < lo := M.data.hs.1.trans_le hlo
  exact (Hpoint.trans (Hmono.trans Htail)).trans
    (div_le_div_of_nonneg_left (by positivity) (div_pos hlo0 hcu) hlower)

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_outer_floor_thermal_on_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀p : M.Potential,∀lo hi : ℝ,M.data.s≤lo → lo≤hi → hi≤1 → cu*Az*M.xs < lo →
      (∫u in Ioo lo hi,p.positiveMassMask u*
        (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))≤
        K*(M.xs+hi)^2*M.data.N^delta*(comparisonSmallMass M.data.N M.data.E)^2/(lo/cu) := by
  obtain ⟨K,hK,Hamp⟩ := eventually_actual_high_wall_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M p lo hi hlo hlohi hhi hscale
  let F := fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  let C := K*(M.xs+hi)^2
  have hsub : Ioo lo hi⊆Icc (0:ℝ) 1 :=
    fun u hu=>⟨M.data.hs.1.le.trans (hlo.trans hu.1.le),hu.2.le.trans hhi⟩
  have hiF : IntegrableOn F (Ioo lo hi) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))).mono_set hsub
  have hmaskmeas : Measurable p.positiveMassMask := by
    rw [p.positiveMassMask_extended]
    apply measurable_const.indicator
    exact measurableSet_lt measurable_const
      (p.starExtendedH_continuous.comp (M.data.wallRadius_lipschitz M.alpha).continuous).measurable
  have hmask01 u : p.positiveMassMask u=0 ∨ p.positiveMassMask u=1 := by
    dsimp [ActualHighWallOverlapMinimum.Potential.positiveMassMask]
    by_cases h:u∈comparisonCalibrationFloor p.H (M.data.wallRadius M.alpha) <;> simp [h]
  have himul : IntegrableOn (fun u=>p.positiveMassMask u*F u) (Ioo lo hi) := by
    apply hiF.bdd_mul (c:=(1:ℝ)) hmaskmeas.aestronglyMeasurable.restrict
    filter_upwards [] with u
    rcases hmask01 u with h|h <;> simp [h]
  have himask := (p.positiveMassMask_on_band hlo hlohi hhi).1
  have hmass := p.positiveMassMask_outer_on_band hcu hlo hlohi hhi hscale
  have hiC : IntegrableOn (fun u=>p.positiveMassMask u*C) (Ioo lo hi) := himask.mul_const C
  have Hbound : (∫u in Ioo lo hi,p.positiveMassMask u*F u)≤
      ∫u in Ioo lo hi,p.positiveMassMask u*C := by
    apply integral_mono_ae himul hiC
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hum : u∈Ioc (0:ℝ) 1 := ⟨M.data.hs.1.trans_le (hlo.trans hu.1.le),hu.2.le.trans hhi⟩
    have H := hn M u hum
    have Hscale := pow_le_pow_left₀ (add_pos M.hxs hum.1).le
      (add_le_add_right hu.2.le M.xs) 2
    have Hupper : F u≤C :=
      (sub_le_self _ (sq_nonneg _)).trans
        (H.trans (mul_le_mul_of_nonneg_left Hscale hK.le))
    have hmask0 : 0≤p.positiveMassMask u := by
      rcases hmask01 u with h|h <;> simp [h]
    exact mul_le_mul_of_nonneg_left Hupper hmask0
  rw [integral_mul_const] at Hbound
  have Hmass := mul_le_mul_of_nonneg_right hmass (show 0≤C from by dsimp [C];positivity)
  exact Hbound.trans (Hmass.trans_eq (by dsimp [C];ring))

end OAI.SKFluctuations.LaplaceWindowFormalization
