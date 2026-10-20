module

public import SKProof.Port.ComparisonActualOriginalQOuterFloorThermalMass
public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch
public import SKProof.Port.ComparisonActualOriginalQRadiusSingleCutIntegral
public import ComparisonSignedCavityActualStarSelection
public import SKProof.OriginalQSharpWindowCentralSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.positive_mass_mask_on_high_band_le
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z : ℝ} (ha : M.data.s ≤ a) (_haz : a < z) (hz : z ≤ 1) :
    (∫u in Ioo a z,p.positiveMassMask u) ≤ M.data.N^(-delta)*M.data.U := by
  let A:=Ioo M.data.rmin 1
  let F:=A∩p.positiveRadiusSet
  let mask:=fun u=>F.indicator (fun _=>(1:ℝ)) (M.sweepRadius u)
  have hF : MeasurableSet F:=measurableSet_Ioo.inter p.positiveRadiusSet_measurable
  have hm : Measurable mask:=(measurable_const.indicator hF).comp
    M.shiftedNativeModel.R_continuous.measurable
  have hi : IntervalIntegrable mask volume 0 1:=by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>by dsimp only [mask];by_cases H:M.sweepRadius u∈F <;> simp [H])
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hiIcc : IntegrableOn mask (Icc (0:ℝ) 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi
  have hsub : Ioo a z⊆Icc (0:ℝ) 1:=
    fun u hu=>⟨M.data.hs.1.le.trans (ha.trans hu.1.le),hu.2.le.trans hz⟩
  have Heq : (∫u in Ioo a z,p.positiveMassMask u)=(∫u in Ioo a z,mask u):=by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have hui : u∈Icc M.data.s 1:=⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
    have hr:=M.shiftedNativeModel.R_bounds u
    have HS:=M.shiftedNativeModel.R_spec hui
    change M.alpha.val.val (M.sweepRadius u)=u at HS
    have hr0 : M.data.rmin < M.sweepRadius u:=by
      by_contra H
      have H0 : M.sweepRadius u=M.data.rmin:=le_antisymm (le_of_not_gt H) hr.1
      rw [H0,M.alpha.property.1] at HS
      linarith only [HS,ha,hu.1]
    have hr1 : M.sweepRadius u < 1:=by
      by_contra H
      have H1 : M.sweepRadius u=1:=le_antisymm hr.2 (le_of_not_gt H)
      rw [H1,M.alpha.property.2.1] at HS
      linarith only [HS,hu.2,hz]
    have hA : M.sweepRadius u∈A:=⟨hr0,hr1⟩
    dsimp only [Potential.positiveMassMask,mask,F]
    by_cases HP:M.sweepRadius u∈p.positiveRadiusSet <;> simp [hA,HP]
  rw [Heq]
  apply (setIntegral_mono_set hiIcc _ (Eventually.of_forall hsub)).trans
  · have H:=p.actual_floor_mass_above_zero A measurableSet_Ioo (Subset.rfl)
    rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc] at H
    exact H
  · exact ae_of_all _ (fun u=>by
      dsimp only [mask];by_cases H:M.sweepRadius u∈F <;> simp [H])

theorem Potential.exists_thermal_good_star_off_floor_at_cap_travel_original_q
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z t : ℝ} (ha : M.data.s ≤ a) (haz : a < z) (hz : z ≤ 1)
    (ht : 0 ≤ t)
    (hsmall : (∫u in Ioo a z,orderedPathB (n+1) M.sweepBf M.sweepHf u-
      (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) < t*((z-a)-M.data.N^(-delta)*M.data.U)) :
    ∃u∈Ioo a z,p.H (M.sweepRadius u) ≤ 0 ∧
      orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2 ≤ t ∧
      (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2 ≤ 16*M.cavityCapTravel^2+2*t := by
  let f:=fun u=>orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2
  have hsub : Ioo a z⊆Icc (0:ℝ) 1:=
    fun u hu=>⟨M.data.hs.1.le.trans (ha.trans hu.1.le),hu.2.le.trans hz⟩
  have hhigh : ∀u∈Ioo a z,u∈Icc M.data.s 1:=fun u hu=>⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
  have hiF : IntegrableOn f (Icc (0:ℝ) 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp M.original_thermal_intervalIntegrable
  have hf0 u (hu : u∈Ioo a z) : 0 ≤ f u :=
    M.shiftedNativeModel.thermal_nonneg
      ⟨M.data.hs.1.trans_le (ha.trans hu.1.le),(hsub hu).2⟩
  have hmass:=p.positive_mass_mask_on_high_band_le ha haz hz
  have hP : ∀ᵐu,u∈Ioo a z → p.H (M.sweepRadius u) ≤ 0 →
      (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2 ≤ 16*M.cavityCapTravel^2+2*f u:=by
    filter_upwards [p.all_nonpositive_squared_mismatch_ae_high_mass] with u hu hui hh
    exact hu (hhigh u hui) hh
  have hbudget : (∫u in Ioo a z,f u) <
      t*((z-a)-(∫u in Ioo a z,p.positiveMassMask u)):=
    hsmall.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left hmass _) ht)
  obtain ⟨u,hu,hm,hf,hp⟩:=exists_good_point_off_mask_ae haz ht
    (hiF.mono_set hsub) (p.positiveMassMask_integrable.mono_set hsub)
    (Eventually.of_forall hf0)
    (Eventually.of_forall (fun u _=>by
      dsimp only [Potential.positiveMassMask]
      by_cases H:M.sweepRadius u∈p.positiveRadiusSet <;> simp [H])) hP hbudget
  have hh:=(p.positiveMassMask_zero_iff u).mp hm
  exact ⟨u,hu,hh,hf,(hp hh).trans (by linarith)⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
