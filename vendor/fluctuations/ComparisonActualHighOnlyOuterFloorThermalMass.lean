module

public import ComparisonActualHighOnlyInitialFloorThermal
public import ComparisonActualHighOnlyInnovation
public import ComparisonShiftedNativeThermalGeometry
public import ComparisonNativeActualOuterFloorThermalMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem actual_mass_slab_radius_lower (hcu : 0 < cu) {lo r : ℝ}
    (hlo : cu*Az*a.xs < lo) (hr : r∈Icc (0:ℝ) 1) (hmass : lo ≤ a.alpha.val.val r) : lo/cu ≤ r := by
  have hzr : a.z ≤ r := by
    by_contra hh
    have halpha:=a.alpha.val.property.2 (lt_of_not_ge hh).le
    have hzreg:=(a.regular a.z ⟨le_rfl,a.hz.2⟩).2
    have hzupper:=mul_le_mul_of_nonneg_left a.hzxs hcu.le
    nlinarith
  have hreg:=(a.regular r ⟨hzr,hr.2⟩).2
  exact (div_le_iff₀ hcu).mpr (by linarith)

theorem radius_mask_mass_above_zero
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1) :
    (∫u in 0..1,A.indicator (fun _=>(1:ℝ)) (a.R u))=∫r in A,deriv a.alpha.val.val r := by
  let m:=a.shiftedNativeModel
  let mask:=fun u=>A.indicator (fun _=>(1:ℝ)) (m.R u)
  have hm : Measurable mask:=(measurable_const.indicator hA).comp m.R_continuous.measurable
  have hi : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>by dsimp [mask];by_cases h:m.R u∈A <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hilo:=hi.mono_set (by
    rw [uIcc_of_le a.data.hs.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl a.data.hs1)
  have hihi:=hi.mono_set (by
    rw [uIcc_of_le a.data.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc a.data.hs.1 le_rfl)
  have hlow : (∫u in 0..a.data.s,mask u)=0 := by
    have hzero : (∫u in (0:ℝ)..a.data.s,(0:ℝ))=0 := intervalIntegral.integral_zero
    apply Eq.trans ?_ hzero
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    have huu : u∈Icc (0:ℝ) a.data.s:=by
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le a.data.hs.1] using hu)
    have H:=m.R_monotone huu.2
    rw [m.R_left] at H
    have Hz : m.R u=0:=le_antisymm H (m.R_bounds u).1
    have hnot : m.R u∉A:=fun h=>by have hh:=(hAD h).1;rw [Hz] at hh;exact (lt_irrefl _ hh)
    exact indicator_of_notMem hnot _
  have Hsubst:=m.mass_radius_cell_substitution mask
    (show a.data.s∈Icc m.u0 1 from ⟨le_rfl,a.data.hs1⟩)
    (show (1:ℝ)∈Icc m.u0 1 from ⟨a.data.hs1,le_rfl⟩) a.data.hs1
  rw [m.R_left,m.R_one] at Hsubst
  have he : (∫r in Icc (0:ℝ) 1,deriv a.alpha.val.val r*mask (a.alpha.val.val r))=
      ∫r in Icc (0:ℝ) 1,A.indicator (deriv a.alpha.val.val) r := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    have Hinv:=m.R_inverse hr
    change m.R (a.alpha.val.val r)=r at Hinv
    dsimp only [mask]
    rw [Hinv]
    by_cases h:r∈A <;> simp [h]
  rw [he,setIntegral_indicator hA,inter_eq_right.mpr (hAD.trans Ioo_subset_Icc_self)] at Hsubst
  change (∫u in 0..1,mask u)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi,hlow,zero_add]
  exact Hsubst

theorem Potential.actual_floor_mass_above_zero
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1) :
    (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>(1:ℝ)) (a.R u)) ≤
      a.data.N^(-delta)*a.data.U := by
  let F:=A∩P.positiveRadiusSet
  have hF : MeasurableSet F:=hA.inter P.positiveRadiusSet_measurable
  have hsub : F⊆Icc (0:ℝ) 1:=(inter_subset_left.trans hAD).trans Ioo_subset_Icc_self
  rw [a.radius_mask_mass_above_zero F hF (inter_subset_left.trans hAD)]
  have hf : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈F →
      deriv a.alpha.val.val r=comparisonFloor a.data.N delta a.data.U r := by
    filter_upwards [P.hfloor] with r hr hri hp
    exact hr hri hp.2.2
  have H:=comparisonFloor_region_mass a.data.hN a.data.hU
    (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) F hF a.alpha.val.val hf
  rw [setIntegral_indicator hF,inter_eq_right.mpr hsub] at H
  exact H

theorem Potential.actual_floor_mass_of_lower_radius
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    {rlo : ℝ} (hrlo : 0 < rlo) (hrlo1 : rlo ≤ 1) (hlower : ∀r∈A,rlo ≤ r) :
    (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>(1:ℝ)) (a.R u)) ≤
      a.data.N^delta*a.data.U^2/rlo := by
  let F:=A∩P.positiveRadiusSet
  have hF : MeasurableSet F:=hA.inter P.positiveRadiusSet_measurable
  have hsub : F⊆Icc (0:ℝ) 1:=(inter_subset_left.trans hAD).trans Ioo_subset_Icc_self
  have houter : F⊆Icc rlo 1:=fun r hr=>⟨hlower r hr.1,(hAD hr.1).2.le⟩
  rw [a.radius_mask_mass_above_zero F hF (inter_subset_left.trans hAD)]
  have he : (∫r in F,deriv a.alpha.val.val r)=∫r in F,comparisonFloor a.data.N delta a.data.U r := by
    apply setIntegral_congr_ae hF
    filter_upwards [P.hfloor] with r hr hri
    exact hr (hsub hri) hri.2.2
  rw [he]
  have hki : IntegrableOn (comparisonFloor a.data.N delta a.data.U) (Icc rlo 1):=
    (comparisonFloor_continuousOn (δ:=delta) a.data.hN a.data.hU hrlo.le).integrableOn_Icc
  have Hmono : (∫r in F,comparisonFloor a.data.N delta a.data.U r) ≤
      ∫r in Icc rlo 1,comparisonFloor a.data.N delta a.data.U r := by
    apply setIntegral_mono_set hki
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (comparisonFloor_pos (δ:=delta) a.data.hN a.data.hU (hrlo.le.trans hr.1)).le
    · exact Eventually.of_forall fun r hr=>houter hr
  exact Hmono.trans (comparison_floor_tail_mass_le a.data.hN a.data.hU hrlo hrlo1)

theorem Potential.actual_floor_thermal_le_of_mass
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    {hi K massBound : ℝ} (hK : 0 ≤ K) (hscale : ∀r∈A,a.alpha.val.val r ≤ hi)
    (hB : ∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u ≤ K*(a.xs+u)^2)
    (hmass : (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>(1:ℝ)) (a.R u)) ≤ massBound) :
    (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u) ≤
      K*(a.xs+hi)^2*massBound := by
  let m:=a.shiftedNativeModel
  let F:=A∩P.positiveRadiusSet
  let mask:=fun u=>F.indicator (fun _=>(1:ℝ)) (m.R u)
  let C:=K*(a.xs+hi)^2
  have hF : MeasurableSet F:=hA.inter P.positiveRadiusSet_measurable
  have hmask : Measurable mask:=(measurable_const.indicator hF).comp m.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmask zero_le_one
      (fun u _=>by dsimp [mask];by_cases h:m.R u∈F <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hiT:=m.thermal_mask_integrable F hF
  have hb : (∫u in 0..1,mask u*m.thermal u) ≤ ∫u in 0..1,C*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one hiT (hiMask.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
      with u hu hune
    have hup : u∈Ioc (0:ℝ) 1:=⟨lt_of_le_of_ne hu.1 hune.symm,hu.2⟩
    by_cases hm : m.R u∈F
    · have hs:=hscale (m.R u) hm.1
      have hhigh : a.data.s < u:=a.radius_high_mass (hAD hm.1).1
      have hspec:=m.R_spec ⟨hhigh.le,hu.2⟩
      rw [hspec] at hs
      have hp:=pow_le_pow_left₀ (add_nonneg a.hxs.le hu.1)
        (by linarith only [hs] : a.xs+u ≤ a.xs+hi) 2
      have hmul:=mul_le_mul_of_nonneg_left hp hK
      have hraw:=hB u hup
      simp only [mask,indicator_of_mem hm,one_mul,mul_one]
      change orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2 ≤ K*(a.xs+hi)^2
      nlinarith [sq_nonneg (orderedPathS (n+1) a.bf a.hf u)]
    · simp only [mask,indicator_of_notMem hm,zero_mul,mul_zero,le_refl]
  rw [intervalIntegral.integral_const_mul] at hb
  have hc:=mul_le_mul_of_nonneg_left hmass (mul_nonneg hK (sq_nonneg (a.xs+hi)))
  change (∫u in 0..1,mask u*m.thermal u) ≤ _
  exact hb.trans hc

theorem Potential.actual_outer_floor_thermal_mass_of_normalized_B
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    {rlo hi K : ℝ} (hrlo : 0 < rlo) (hrlo1 : rlo ≤ 1) (hlower : ∀r∈A,rlo ≤ r)
    (hK : 0 ≤ K) (hscale : ∀r∈A,a.alpha.val.val r ≤ hi)
    (hB : ∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u ≤ K*(a.xs+u)^2) :
    (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u) ≤
      K*(a.xs+hi)^2*a.data.N^delta*a.data.U^2/rlo := by
  simpa only [mul_div_assoc,mul_assoc] using P.actual_floor_thermal_le_of_mass A hA hAD hK hscale hB
    (P.actual_floor_mass_of_lower_radius A hA hAD hrlo hrlo1 hlower)

end ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_positive_radius_floor_thermal
    (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀P : a.Potential,∀A : Set ℝ,
      MeasurableSet A → A⊆Ioo (0:ℝ) 1 → ∀hi : ℝ,(∀r∈A,a.alpha.val.val r ≤ hi) →
      ((∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u) ≤
        K*(a.xs+hi)^2*(a.data.N^(-delta)*a.data.U)) ∧
      (∀rlo : ℝ,0 < rlo → rlo ≤ 1 → (∀r∈A,rlo ≤ r) →
        (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u) ≤
          K*(a.xs+hi)^2*a.data.N^delta*a.data.U^2/rlo) := by
  obtain ⟨K,hK,Hamp⟩:=eventually_actual_high_only_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro a hs hsxs P A hA hAD hi hscale
  have hB : ∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u ≤ K*(a.xs+u)^2:=
    fun u hu=>hn a hs hsxs u hu
  exact ⟨P.actual_floor_thermal_le_of_mass A hA hAD hK.le hscale hB
    (P.actual_floor_mass_above_zero A hA hAD),
    fun rlo hrlo hrlo1 hlower=>P.actual_outer_floor_thermal_mass_of_normalized_B A hA hAD
      hrlo hrlo1 hlower hK.le hscale hB⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
