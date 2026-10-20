module

public import ScalarFinitePairBridge
public import SKFluctuationsOAI.Probability.SKFluctuations.Chain

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy

theorem HeatJet.gradient_eq_of_potential_add_constant (J K : HeatJet 0) (c : ℝ)
    (he : K.F = fun x => J.F x + c) (x : Fin 1 → ℝ) : K.G 0 x = J.G 0 x := by
  have hJ := (J.derivF_coord 0 x 0).add_const c
  have hK := K.derivF_coord 0 x 0
  rw [he] at hK
  simpa only [zero_smul, add_zero] using hK.unique hJ

theorem HeatJet.schedule_test_of_potential_add_constant (J K : HeatJet 0) (c : ℝ)
    (hF : K.F = fun x => J.F x + c) (hA : K.A = J.A) (cs : List HeatClock) :
    (K.schedule cs).A = (J.schedule cs).A := by
  induction cs with
  | nil => exact hA
  | cons st cs ih =>
    funext x
    change clockTest st.mass (K.schedule cs).F (K.schedule cs).A st.time x =
      clockTest st.mass (J.schedule cs).F (J.schedule cs).A st.time x
    rw [schedule_potential_add_constant J K c hF cs, ih]
    exact shiftedMean_add_const _ _ _ _ _

theorem finite_scalar_pair_terminal_mass_one_invariant (pre post : List HeatClock)
    (fill : HeatClock) (hm : fill.mass = 1)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) post))
    (ho' : OrderedSteps 0 (heatSteps (ι := Fin 1) (post ++ [fill]))) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps (post ++ [fill]))
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 =
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 := by
  rw [finite_scalar_pair_eq_square_prefix pre _ ho',
    finite_scalar_pair_eq_square_prefix pre _ ho]
  apply congrFun
  apply HeatJet.schedule_test_of_potential_add_constant
    ((scalarGradientSchedule post ho).square)
    ((scalarGradientSchedule (post ++ [fill]) ho').square) (fill.time / 2)
  · exact scalar_schedule_terminal_fill post fill hm
  · funext x
    change ((scalarTerminal.schedule (post ++ [fill])).G 0 x)^2 =
      ((scalarTerminal.schedule post).G 0 x)^2
    rw [HeatJet.gradient_eq_of_potential_add_constant _ _ (fill.time / 2)
      (scalar_schedule_terminal_fill post fill hm) x]

theorem finite_scalar_pair_eq_actual_plantedEnergy_fixed_horizon {T : ℝ} (hT : 0 < T)
    (pre post : List HeatClock) (ht : (scheduleDuration (pre ++ post) : ℝ) ≤ T)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post))) :
    stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (heatSteps pre) (heatSteps post)
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 =
      scalarPlantedEnergy hT (actualScalarScheduleMass hT (pre ++ post) ht)
        (scheduleDuration pre / T) := by
  let cs := pre ++ post
  have ht' : 0 + (scheduleDuration cs : ℝ) ≤ T := by simpa only [zero_add] using ht
  let fill := terminalFillClock cs ht'
  have hfill : fill.mass = 1 := rfl
  have hfTime : (fill.time : ℝ) = T - scheduleDuration cs := by
    simpa only [fill, terminalFillClock, zero_add] using
      Real.coe_toNNReal _ (sub_nonneg.mpr ht')
  have hpost : OrderedSteps 0 (heatSteps (ι := Fin 1) post) := by
    apply OrderedSteps.suffix (heatSteps (ι := Fin 1) pre) (heatSteps post)
    simpa only [heatSteps, List.map_append] using ho
  have hpost' : OrderedSteps 0 (heatSteps (ι := Fin 1) (post ++ [fill])) := by
    simp only [heatSteps, List.map_append]
    apply OrderedSteps.append_bound hpost (by norm_num : (0 : ℝ) ≤ 1)
    · intro st hst
      have hbound : ∀ {a : ℝ} {xs : List (GaussianStep (Fin 1))},
          OrderedSteps a xs → ∀ st ∈ xs, st.1 ≤ 1 := by
        intro a xs ha
        induction xs generalizing a with
        | nil => simp
        | cons x xs ih =>
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ha.2.2.2.bounds.2
          · exact ih ha.2.2.2 y hy
      exact hbound hpost st hst
    · simp [OrderedSteps, hfill]
  have htotal : T = (scheduleDuration (pre ++ (post ++ [fill])) : ℝ) := by
    simp only [← List.append_assoc, scheduleDuration_append, scheduleDuration,
      NNReal.coe_add, add_zero, hfTime, cs]
    ring
  have hm : ScheduleProfileMatches
      (rescaledMassProfile (actualScalarScheduleMass hT cs ht) hT)
        (pre ++ (post ++ [fill])) 0 := by
    have hfirst := actual_schedule_cdf_matches hT (by norm_num : (0 : ℝ) ≤ 0) cs ht' ho
    have hlast : ScheduleProfileMatches (actualScheduleProfile hT (by norm_num) cs ht')
        [fill] (0 + scheduleDuration cs) := by
      constructor
      · intro t hti
        exact actual_schedule_terminal_one hT (by norm_num) cs ht' t hti.1
      · trivial
    simpa only [List.append_assoc, cs, actualScheduleProfile, actualScalarScheduleMass]
      using ScheduleProfileMatches.append _ cs [fill] 0 hfirst hlast
  have he := finite_scalar_pair_eq_plantedEnergy_of_matches hT
    (actualScalarScheduleMass hT cs ht) pre (post ++ [fill]) htotal hpost' hm
  rw [finite_scalar_pair_terminal_mass_one_invariant pre post fill hfill hpost hpost'] at he
  exact he

end OAI.SKFluctuations.LaplaceWindowFormalization
