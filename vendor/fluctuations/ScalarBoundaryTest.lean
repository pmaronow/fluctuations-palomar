module

public import ScalarBoundaryProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem finite_scalar_profile_test_eq_schedule (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ t, α.mass t ≤ 1)
    (cs : List HeatClock) (l : ℝ) (hmatch : ScheduleProfileMatches α cs l)
    (x : Fin 1 → ℝ) :
    J.nonnegativeProfileTest α l (scheduleDuration cs) x = (J.schedule cs).A x := by
  have he : (fun s => (J.terminalPerturb s).nonnegativeProfileValue α l
      (scheduleDuration cs) x) = fun s => ((J.terminalPerturb s).schedule cs).F x := by
    funext s
    exact finite_scalar_profile_eq_schedule (J.terminalPerturb s) α hα cs l hmatch x
  have hL := J.nonnegativeProfile_terminal_deriv_zero α hα l (scheduleDuration cs) x
  have hR := J.schedule_terminal_deriv cs 0 x
  rw [he] at hL
  simpa only [HeatJet.schedule_perturb_zero_A] using hL.unique hR

end OAI.SKFluctuations.LaplaceWindowFormalization
