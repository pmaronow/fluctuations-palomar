module

public import ScalarBoundaryTest
public import FiniteQuantileCDF
public import ScalarLowClockCalibration
public import ActualMixedClockCDF
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem HeatJet.gradient_eq_of_potential_eq (J K : HeatJet 0) (he : J.F = K.F)
    (x : Fin 1 → ℝ) : J.G 0 x = K.G 0 x := by
  have hJ := J.derivF_coord 0 x 0
  have hK := K.derivF_coord 0 x 0
  rw [he] at hJ
  simpa only [zero_smul, add_zero] using hJ.unique hK

theorem ScheduleProfileMatches.prefix_suffix (α : NonnegativeMassProfile)
    (pre post : List HeatClock) (l : ℝ)
    (hm : ScheduleProfileMatches α (pre ++ post) l) :
    ScheduleProfileMatches α pre l ∧
      ScheduleProfileMatches α post (l + scheduleDuration pre) := by
  induction pre generalizing l with
  | nil => simpa [ScheduleProfileMatches, scheduleDuration] using And.intro trivial hm
  | cons c pre ih =>
    obtain ⟨hp, hs⟩ := ih (l + c.time) hm.2
    refine ⟨⟨hm.1, hp⟩, ?_⟩
    simpa only [scheduleDuration, NNReal.coe_add, add_assoc] using hs

theorem scalarPlantedEnergy_le_clock {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : ∀ x ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedEnergy hT α q ≤ T * q := by
  have h := scalarPlantedEnergy_integral_nonnegative hT α hq hq1 hc
  rw [scalarPlantedEnergy_zero, sub_zero] at h
  rw [h]
  apply mul_le_mul_of_nonneg_left _ hT.le
  have hi := intervalIntegral.integral_mono_on hq
    ((scalarPlantedCurvature_continuous hT α).intervalIntegrable 0 q)
    (intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := q) (c := (1 : ℝ)))
    (fun x _ => (scalarPlantedCurvature_bounds hT α x).2)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi

def scalarGradientSchedule (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) : HeatJet 0 :=
  (scalarTerminal.schedule cs).withTest ((scalarTerminal.schedule cs).G 0)
    (scalar_schedule_smoothG cs ho 2 0)

theorem finite_scalar_pair_eq_square_prefix (pre post : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) post)) (x : Fin 1 → ℝ) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) x =
    ((scalarGradientSchedule post ho).square.schedule pre).A x := by
  rw [HeatJet.schedule_A_prefix]
  unfold stepPairMean
  have hF := funext (scalar_schedule_eq_hierarchy post)
  rw [← hF]
  congr 1
  funext y
  have hmean : gaussianHierarchyMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (fun σ => scalarFeature σ (fun _ => 1)) (heatSteps post) y =
      (scalarTerminal.schedule post).G 0 y := by
    have hy : y = fun _ => y 0 := by ext i; rw [Fin.fin_one_eq_zero i]
    rw [hy, ← scalarSourceJet_one_mean ho, scalarSourceJet_one_schedule post ho]
  change gaussianHierarchyMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
    (fun σ => gaussianHierarchyMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (fun τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1))
      (heatSteps post) y) (heatSteps post) y = ((scalarTerminal.schedule post).G 0 y)^2
  simp_rw [gaussianHierarchyMean_const_mul]
  have hm : (fun σ : Bool => scalarFeature σ (fun _ => 1) *
      gaussianHierarchyMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
        (fun τ => scalarFeature τ (fun _ => 1)) (heatSteps post) y) =
      (fun σ => gaussianHierarchyMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
        (fun τ => scalarFeature τ (fun _ => 1)) (heatSteps post) y *
          scalarFeature σ (fun _ => 1)) := by funext σ; ring
  rw [hm, gaussianHierarchyMean_const_mul, hmean]
  ring

theorem finite_scalar_pair_eq_plantedEnergy_of_matches {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (pre post : List HeatClock)
    (htotal : T = scheduleDuration (pre ++ post))
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) post))
    (hm : ScheduleProfileMatches (rescaledMassProfile α hT) (pre ++ post) 0) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 =
      scalarPlantedEnergy hT α (scheduleDuration pre / T) := by
  obtain ⟨hpre, hpost⟩ := ScheduleProfileMatches.prefix_suffix _ pre post 0 hm
  simp only [zero_add] at hpost
  have hs : T * (scheduleDuration pre / T) = scheduleDuration pre := by
    field_simp
  have ht : T * (1 - scheduleDuration pre / T) = scheduleDuration post := by
    have hh := htotal
    rw [scheduleDuration_append, NNReal.coe_add] at hh
    field_simp
    nlinarith
  let J := scalarTailJet hT α (scheduleDuration pre / T)
  let K := scalarGradientSchedule post ho
  have hF : J.F = K.F := by
    funext x
    change (scalarProfileHeatJet (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s / T)).2)
      (T * (scheduleDuration pre / T))
      (Real.toNNReal (T * (1 - scheduleDuration pre / T)))).F x =
        (scalarTerminal.schedule post).F x
    rw [hs, ht, Real.toNNReal_coe]
    exact (scalarProfileHeatJet_F (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s / T)).2) _ _ x).trans
      (finite_scalar_profile_eq_schedule scalarTerminal _
        (fun s => (α.property.1 (s / T)).2) post _ hpost x)
  have hA : J.A = K.A := by
    funext x
    change J.G 0 x = (scalarTerminal.schedule post).G 0 x
    exact HeatJet.gradient_eq_of_potential_eq J K hF x
  have henergy : scalarPlantedEnergy hT α (scheduleDuration pre / T) =
      (K.square.schedule pre).A 0 := by
    unfold scalarPlantedEnergy
    rw [hs, Real.toNNReal_coe]
    change J.square.nonnegativeProfileTest (rescaledMassProfile α hT)
      0 (scheduleDuration pre) 0 = _
    rw [HeatJet.nonnegativeProfileTest_congr J.square K.square hF
      (by change (fun x => (J.A x)^2) = (fun x => (K.A x)^2); rw [hA])]
    exact finite_scalar_profile_test_eq_schedule K.square _
      (fun s => (α.property.1 (s / T)).2) pre 0 hpre 0
  rw [henergy]
  exact finite_scalar_pair_eq_square_prefix pre post ho 0

def actualScalarScheduleMass {T : ℝ} (hT : 0 < T) (cs : List HeatClock)
    (ht : scheduleDuration cs ≤ T) : boundedMassProfiles :=
  quantileMassProfile (normalizedScheduleQuantile T 0 cs)
    (normalizedScheduleQuantile_bounds hT le_rfl cs (by simpa only [zero_add] using ht))

theorem finite_scalar_pair_eq_actual_plantedEnergy {T : ℝ} (hT : 0 < T)
    (pre post : List HeatClock) (htotal : T = scheduleDuration (pre ++ post))
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post))) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 =
      scalarPlantedEnergy hT (actualScalarScheduleMass hT (pre ++ post) htotal.ge)
        (scheduleDuration pre / T) := by
  apply finite_scalar_pair_eq_plantedEnergy_of_matches hT _ pre post htotal
  · apply OrderedSteps.suffix (heatSteps (ι := Fin 1) pre) (heatSteps post)
    simpa only [heatSteps, List.map_append] using ho
  · exact actual_schedule_cdf_matches hT le_rfl (pre ++ post)
      (by simpa only [zero_add] using htotal.ge) ho

theorem finite_scalar_pair_le_clock {T : ℝ} (hT : 0 < T)
    (pre post : List HeatClock) (htotal : T = scheduleDuration (pre ++ post))
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post))) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 ≤
        scheduleDuration pre := by
  rw [finite_scalar_pair_eq_actual_plantedEnergy hT pre post htotal ho]
  have hclock : T * (scheduleDuration pre / T) = scheduleDuration pre := by field_simp
  have hq1 : (scheduleDuration pre : ℝ) / T ≤ 1 := by
    apply (div_le_one hT).mpr
    rw [htotal, scheduleDuration_append, NNReal.coe_add]
    exact le_add_of_nonneg_right (scheduleDuration post).coe_nonneg
  have hc : ∀ x ∈ Ico (0 : ℝ) (scheduleDuration pre / T),
      ContinuousWithinAt (actualScalarScheduleMass hT (pre ++ post) htotal.ge).val
        (Ici x) x := by
    intro x _
    exact quantileMassProfile_right_continuous _ _ x
  exact (scalarPlantedEnergy_le_clock hT
    (actualScalarScheduleMass hT (pre ++ post) htotal.ge)
    (div_nonneg (scheduleDuration pre).coe_nonneg hT.le) hq1 hc).trans_eq hclock

theorem finite_scalar_pair_nonneg {T : ℝ} (hT : 0 < T)
    (pre post : List HeatClock) (htotal : T = scheduleDuration (pre ++ post))
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post))) :
    0 ≤ stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 := by
  rw [finite_scalar_pair_eq_actual_plantedEnergy hT pre post htotal ho]
  exact (scalarPlantedEnergy_bounds hT _ _).1

theorem HeatJet.schedule_A_duration_zero (J : HeatJet 0) (cs : List HeatClock)
    (ht : scheduleDuration cs = 0) : (J.schedule cs).A = J.A := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hz : c.time = 0 ∧ scheduleDuration cs = 0 := by
      exact add_eq_zero.mp ht
    funext x
    change clockTest c.mass (J.schedule cs).F (J.schedule cs).A c.time x = J.A x
    rw [hz.1, NNReal.coe_zero, clockTest_zero, ih hz.2]

theorem finite_scalar_pair_zero_shared_clock (pre post : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) post))
    (ht : scheduleDuration pre = 0) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 = 0 := by
  rw [finite_scalar_pair_eq_square_prefix pre post ho,
    HeatJet.schedule_A_duration_zero _ pre ht]
  change ((scalarTerminal.schedule post).G 0 0)^2 = 0
  have hg := scalarSourceJet_schedule_gradient_zero post ho
  rw [scalarSourceJet_one_schedule post ho] at hg
  simpa only [Pi.zero_def, hg, zero_pow (by decide : 2 ≠ 0)]

theorem finite_scalar_pair_bounds (pre post : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post))) :
    0 ≤ stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 ∧
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 ≤
        scheduleDuration pre := by
  by_cases ht : scheduleDuration (pre ++ post) = 0
  · have hp : scheduleDuration pre = 0 := by
      rw [scheduleDuration_append] at ht
      exact (add_eq_zero.mp ht).1
    have hpost : OrderedSteps 0 (heatSteps (ι := Fin 1) post) := by
      apply OrderedSteps.suffix (heatSteps (ι := Fin 1) pre) (heatSteps post)
      simpa only [heatSteps, List.map_append] using ho
    rw [finite_scalar_pair_zero_shared_clock pre post hpost hp, hp, NNReal.coe_zero]
    exact ⟨le_rfl, le_rfl⟩
  · have hT : 0 < (scheduleDuration (pre ++ post) : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
    exact ⟨finite_scalar_pair_nonneg hT pre post rfl ho,
      finite_scalar_pair_le_clock hT pre post rfl ho⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
