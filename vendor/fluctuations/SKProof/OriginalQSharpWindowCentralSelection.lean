module

public import SKProof.OriginalQAllCapMismatch
public import SKProof.OriginalQStrongHighMassBand
public import ComparisonActualHighWallThetaZeroPositiveFloorThermal
public import ComparisonActualHighWallThetaZeroSmallMassScale
public import ComparisonSignedCavityActualStarSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.exists_thermal_good_star_off_floor_original_q
    (p : Q.Potential) {a z t : ℝ} (ha : Q.data.s ≤ a) (haz : a < z) (hz : z ≤ 1)
    (ht : 0 ≤ t)
    (hsmall : (∫ u in Ioo a z, orderedPathB (n+1) Q.sweepBf Q.sweepHf u -
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2) <
      t*((z-a)-Q.data.N^(-delta)*comparisonSmallMass Q.data.N Q.data.E)) :
    ∃ u ∈ Ioo a z, p.H (Q.sweepRadius u) ≤ 0 ∧
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u -
        (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2 ≤ t ∧
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2 ≤
        16*(Q.data.rmin+Q.cavityCapTravel)^2+2*t := by
  let f := fun u => orderedPathB (n+1) Q.sweepBf Q.sweepHf u -
    (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2
  let mask := fun u => p.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)
  have hsub : Ioo a z ⊆ Icc (0:ℝ) 1 :=
    fun u hu => ⟨Q.data.hs.1.le.trans (ha.trans hu.1.le), hu.2.le.trans hz⟩
  have hhigh : ∀ u ∈ Ioo a z, u ∈ Icc Q.data.s 1 :=
    fun u hu => ⟨ha.trans hu.1.le, hu.2.le.trans hz⟩
  have hiF : IntegrableOn f (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n Q.sweepBf Q.sweepHf
        Q.sweep_bf_monotone Q.sweep_hf_monotone)
  have hf0 (u : ℝ) (hu : u ∈ Ioo a z) : 0 ≤ f u :=
    Q.shiftedNativeModel.thermal_nonneg
      ⟨Q.data.hs.1.trans_le (ha.trans hu.1.le), (hsub hu).2⟩
  have hm : Measurable mask :=
    (measurable_const.indicator p.positiveSet_measurable).comp
      Q.shiftedNativeModel.R_continuous.measurable
  have hmi : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _ => by
        dsimp only [mask]
        by_cases H : Q.shiftedNativeModel.R u ∈ p.positiveSet <;> simp [H])
      (intervalIntegrable_const (c := (1:ℝ)))
  have hmiIcc : IntegrableOn mask (Icc Q.data.s 1) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hmi).mono_set
      (Icc_subset_Icc Q.data.hs.1.le le_rfl)
  have hmask0 (u : ℝ) : 0 ≤ mask u := by
    dsimp only [mask]
    by_cases H : Q.shiftedNativeModel.R u ∈ p.positiveSet <;> simp [H]
  have hmass : (∫ u in Ioo a z, mask u) ≤ Q.data.N^(-delta)*comparisonSmallMass Q.data.N Q.data.E := by
    have H := p.positive_floor_mass_global
    rw [intervalIntegral.integral_of_le Q.data.hs1, ← integral_Icc_eq_integral_Ioc] at H
    exact (setIntegral_mono_set hmiIcc (ae_of_all _ hmask0)
      (Eventually.of_forall (fun u hu => hhigh u hu))).trans H
  have hP : ∀ᵐ u, u ∈ Ioo a z → p.H (Q.sweepRadius u) ≤ 0 →
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2 ≤
        16*(Q.data.rmin+Q.cavityCapTravel)^2+2*f u := by
    filter_upwards [p.all_nonpositive_squared_mismatch_ae_high_mass_original_q]
      with u hu hui hh
    exact hu (hhigh u hui) hh
  have hbudget : (∫ u in Ioo a z, f u) < t*((z-a)-(∫ u in Ioo a z, mask u)) :=
    hsmall.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left hmass _) ht)
  obtain ⟨u, hu, hm0, hf, hp⟩ := exists_good_point_off_mask_ae haz ht
    (hiF.mono_set hsub) (hmiIcc.mono_set (fun u hu => hhigh u hu))
    (Eventually.of_forall hf0)
    (Eventually.of_forall (fun u _ => by
      dsimp only [mask]
      by_cases H : Q.shiftedNativeModel.R u ∈ p.positiveSet <;> simp [H])) hP hbudget
  have hh : p.H (Q.sweepRadius u) ≤ 0 := by
    by_contra H
    have hr := Q.shiftedNativeModel.R_bounds u
    have hp : Q.shiftedNativeModel.R u ∈ p.positiveSet := ⟨hr, lt_of_not_ge H⟩
    simp only [mask, indicator_of_mem hp] at hm0
    norm_num at hm0
  exact ⟨u, hu, hh, hf, (hp hh).trans (by linarith only [hf])⟩

open NativeOverlapMinimum

theorem eventually_floor_mass_polynomial_original_q
    {m delta cl cu Az C0 Ct D Bclock c1 : ℝ}
    (hC0 : 0 < C0) (hc1 : c1 < 3*m+delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs ≤ W →
        M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E) ≤ (1/2)*M.data.N^(-c1)*W := by
  have H := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1/2)
      (q:=-(3*m+delta)) (r:=-c1) (by norm_num) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxs
  have hW : 0 < W := M.hxs.trans_le hxs
  have hratio : (comparisonSmallMass M.data.N M.data.E)/W ≤ C0^3*M.data.N^(-3*m) :=
    (div_le_div_of_nonneg_left M.data.hU.le M.hxs hxs).trans
      (M.small_mass_ratio hC0)
  have Hmul := mul_le_mul_of_nonneg_left hratio
    (Real.rpow_nonneg M.data.hN.le (-delta))
  have He : M.data.N^(-delta)*(C0^3*M.data.N^(-3*m)) =
      C0^3*M.data.N^(-(3*m+delta)) := by
    rw [←mul_assoc,mul_comm (M.data.N^(-delta)) (C0^3),mul_assoc,
      ←Real.rpow_add M.data.hN]
    congr 2
    ring
  rw [He] at Hmul
  have Hcoeff : C0^3*M.data.N^(-(3*m+delta)) ≤ (1/2)*M.data.N^(-c1) := by
    simpa only [ActualHighWallData.N] using hn
  have Hratio' : (M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E))/W ≤ (1/2)*M.data.N^(-c1) := by
    simpa only [mul_div_assoc] using Hmul.trans Hcoeff
  exact (div_le_iff₀ hW).mp Hratio'

theorem eventually_sharp_central_mass_selection_of_dyads_original_q
    {Ctest a b c1 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (ha : 0 < a) (hab : a ≤ b) (ha1 : 1 ≤ a)
    (hc1thermal : c1 < actualMassSavingExponent m delta/8)
    (hc1floor : c1 < 3*m+delta)
    (Hdyad : OriginalQIntermediateDyadSaving m delta cl cu Az C0 Ct D Bclock Ctest a b) :
    ∀ᶠn : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ M.xs → 64*M.data.s ≤ a*M.xs →
      ∀W : ℝ,W=M.directTestWorkingScale →
      M.xs^2 ≤ Ctest*laplaceComparisonStrength M.data.d M.lam M.xs →
      W ≤ 1 → 2*b*W ≤ 1 →
      ∀p : M.Potential,∀s t : ℝ,a*W ≤ s → t ≤ b*W → s < t →
        M.data.N^(-c1)*W ≤ t-s →
      ∃u∈Ioo s t,p.H (M.sweepRadius u) ≤ 0 ∧
        orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2 ≤
          M.data.N^(-(actualMassSavingExponent m delta/4))*(M.xs^4/W^2) ∧
        (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2 ≤
          16*(M.data.rmin+M.cavityCapTravel)^2+2*(M.data.N^(-(actualMassSavingExponent m delta/4))*(M.xs^4/W^2)) := by
  let η := actualMassSavingExponent m delta
  have hη : 0 < η := actualMassSavingExponent_pos hm hdelta
  have ha0 : 0 < a := ha
  have Hslab := original_q_strong_high_mass_band_of_dyads_original_q
    hm hdelta ha0 ha1 hab Hdyad
  have Hfloor := eventually_floor_mass_polynomial_original_q
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock) hC0 hc1floor
  have Hthermal := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/4)
      (q:=-(3*η/8)) (r:=-(η/4)-c1) (by norm_num) (by dsimp [η]; linarith))
  filter_upwards [Hslab,Hfloor,Hthermal] with n hnslab hnfloor hnthermal
  intro M hsXs hsHigh W hcanonical hcompare hW1 h2bW p s t hs ht hst hwidth
  have hxs : M.xs ≤ W := by rw [hcanonical];exact M.target_le_direct_test_working_scale
  have hbW : b*W ≤ 1 := by
    have hnonneg : 0 ≤ b*W := mul_nonneg (ha0.le.trans hab) (M.hxs.le.trans hxs)
    linarith only [h2bW,hnonneg]
  have hW : 0 < W := M.hxs.trans_le hxs
  have hxspos := M.hxs
  have hN := M.data.hN
  let F := fun u=>orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2
  have hsubunit : Ioo (a*W) (b*W) ⊆ Icc (0:ℝ) 1 :=
    fun u hu=>⟨(mul_pos ha0 hW).le.trans hu.1.le,hu.2.le.trans hbW⟩
  have hiF : IntegrableOn F (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.sweepBf M.sweepHf
        M.sweep_bf_monotone M.sweep_hf_monotone)
  have hf0 (u : ℝ) (hu : u ∈ Ioo (a*W) (b*W)) : 0 ≤ F u :=
    M.shiftedNativeModel.thermal_nonneg ⟨lt_of_lt_of_le (mul_pos ha0 hW) hu.1.le,
      hu.2.le.trans hbW⟩
  have hsub : Ioo s t ⊆ Ioo (a*W) (b*W) :=
    fun u hu=>⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
  have Hmono : (∫u in Ioo s t,F u) ≤ ∫u in Ioo (a*W) (b*W),F u := by
    apply setIntegral_mono_set (hiF.mono_set hsubunit) _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hf0 u hu
  have Hslab' := hnslab M hsXs hsHigh hcompare
    (by simpa only [←hcanonical] using hW1)
    (by simpa only [←hcanonical] using h2bW)
  rw [←hcanonical] at Hslab'
  have hends : a*W ≤ b*W := mul_le_mul_of_nonneg_right hab hW.le
  rw [intervalIntegral.integral_of_le hends,integral_Ioc_eq_integral_Ioo] at Hslab'
  have HI : (∫u in Ioo s t,F u) ≤ M.data.N^(-(3*η/8))*(M.xs^4/W) :=
    Hmono.trans Hslab'
  have hfloor := hnfloor M W hxs
  have hcoef : M.data.N^(-(3*η/8)) ≤ (1/4)*M.data.N^(-(η/4)-c1) := by
    simpa only [ActualHighWallData.N,one_mul] using hnthermal
  let threshold := M.data.N^(-(η/4))*(M.xs^4/W^2)
  have hthreshold : 0 < threshold := by dsimp [threshold];positivity
  have hstep : 0 < M.data.N^(-c1)*W := by positivity
  have hpow : M.data.N^(-(η/4)-c1) = M.data.N^(-(η/4))*M.data.N^(-c1) := by
    rw [←Real.rpow_add hN]
    congr 1
  have hthermalbound : (∫u in Ioo s t,F u) <
      threshold*((t-s)-M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E)) := by
    calc
      _ ≤ M.data.N^(-(3*η/8))*(M.xs^4/W) := HI
      _ ≤ ((1/4)*M.data.N^(-(η/4)-c1))*(M.xs^4/W) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = threshold*((1/4)*M.data.N^(-c1)*W) := by
        rw [hpow];dsimp [threshold];field_simp [ne_of_gt hW]
      _ < threshold*((1/2)*M.data.N^(-c1)*W) :=
        mul_lt_mul_of_pos_left (by nlinarith only [hstep]) hthreshold
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hfloor,hwidth]) hthreshold.le
  apply p.exists_thermal_good_star_off_floor_original_q _ hst (ht.trans hbW) hthreshold.le hthermalbound
  have HH:=mul_le_mul_of_nonneg_left hxs ha0.le
  linarith only [hsHigh,HH,hs,M.data.hs.1]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
