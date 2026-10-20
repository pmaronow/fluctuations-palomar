module

public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarIntervalStrictArea
public import PureFieldFactorization

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def scheduleDuration : List HeatClock → ℝ≥0
  | [] => 0
  | c :: cs => c.time + scheduleDuration cs

def ScheduleProfileMatches (α : NonnegativeMassProfile) :
    List HeatClock → ℝ → Prop
  | [], _ => True
  | c :: cs, l =>
      (∀ t ∈ Ioo l (l + c.time), α.mass t = c.mass) ∧
        ScheduleProfileMatches α cs (l + c.time)

theorem finite_scalar_profile_eq_schedule (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ t, α.mass t ≤ 1)
    (cs : List HeatClock) (l : ℝ) (hmatch : ScheduleProfileMatches α cs l)
    (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue α l (scheduleDuration cs) x =
      (J.schedule cs).F x := by
  induction cs generalizing J l x with
  | nil =>
    obtain ⟨D, _, hD⟩ := (J.smoothG 0).bound
    exact J.nonnegativeProfile_zero (fun _ => D)
      (fun i x => by simpa only [Fin.fin_one_eq_zero i] using hD x) α hα l x
  | cons c cs ih =>
    let R := J.schedule cs
    have hR : R.F = J.nonnegativeProfileValue α (l + c.time) (scheduleDuration cs) :=
      (funext (fun y => ih J (l + c.time) hmatch.2 y)).symm
    change J.nonnegativeProfileValue α l (c.time + scheduleDuration cs) x = _
    rw [HeatJet.nonnegativeProfile_concat J R α hα l c.time (scheduleDuration cs) hR]
    by_cases ht : c.time = 0
    · rw [ht]
      obtain ⟨D, _, hD⟩ := (R.smoothG 0).bound
      rw [R.nonnegativeProfile_zero (fun _ => D)
        (fun i x => by simpa only [Fin.fin_one_eq_zero i] using hD x) α hα l x]
      change R.F x = clockContinuation c.mass R.F c.time x
      simp only [ht, NNReal.coe_zero, clockContinuation_zero c.positive.ne']
    · have htp : 0 < (c.time : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      rw [R.nonnegativeProfileValue_constant_Ioo α c.positive l c.time htp hmatch.1]
      rfl

theorem HeatJet.nonnegativeProfileValue_zero_Ioo (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ t, α.mass t ≤ 1)
    (l : ℝ) (s : ℝ≥0) (hz : ∀ t ∈ Ioo l (l + s), α.mass t = 0)
    (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue α l s x = clockRoot J.F s x := by
  by_cases hs : s = 0
  · rw [hs]
    obtain ⟨D, _, hD⟩ := (J.smoothG 0).bound
    rw [J.nonnegativeProfile_zero (fun _ => D)
      (fun i x => by simpa only [Fin.fin_one_eq_zero i] using hD x) α hα l x]
    simp only [NNReal.coe_zero, clockRoot_zero_time]
  · let β : NonnegativeMassProfile := ⟨fun _ => 0, fun _ => le_rfl, monotone_const⟩
    have he : α.mass =ᵐ[volume.restrict (Ioc l (l + s))] β.mass := by
      apply ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hz t ht
    rw [J.nonnegativeProfileValue_congr_ae α β l s x he]
    exact J.nonnegativeProfileValue_zero β l s
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)) (fun _ _ => rfl) x

theorem finite_scalar_profile_eq_root_schedule (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ t, α.mass t ≤ 1)
    (s : ℝ≥0) (cs : List HeatClock) (l : ℝ)
    (hz : ∀ t ∈ Ioo l (l + s), α.mass t = 0)
    (hmatch : ScheduleProfileMatches α cs (l + s)) (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue α l (s + scheduleDuration cs) x =
      clockRoot (J.schedule cs).F s x := by
  let R := J.schedule cs
  have hR : R.F = J.nonnegativeProfileValue α (l + s) (scheduleDuration cs) :=
    (funext (fun y => finite_scalar_profile_eq_schedule J α hα cs (l + s) hmatch y)).symm
  rw [HeatJet.nonnegativeProfile_concat J R α hα l s (scheduleDuration cs) hR]
  exact HeatJet.nonnegativeProfileValue_zero_Ioo R α hα l s hz x

theorem schedule_potential_add_constant (J K : HeatJet 0) (c : ℝ)
    (hK : K.F = fun x => J.F x + c) (cs : List HeatClock) :
    (K.schedule cs).F = fun x => (J.schedule cs).F x + c := by
  induction cs with
  | nil => exact hK
  | cons st cs ih =>
    funext x
    change clockContinuation st.mass (K.schedule cs).F st.time x =
      clockContinuation st.mass (J.schedule cs).F st.time x + c
    rw [ih]
    unfold clockContinuation
    exact shiftedContinuation_add_const st.positive.ne'
      ((exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal (st.time : ℝ))).integrable_shift
        (J.schedule cs).lipschitz st.mass) c x

theorem clockRoot_potential_add_constant (J : HeatJet 0) (c t : ℝ) (x : Fin 1 → ℝ) :
    clockRoot (fun y => J.F y + c) t x = clockRoot J.F t x + c := by
  unfold clockRoot zeroContinuation
  rw [integral_add
    ((exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal t)).integrable_lipschitz
      J.lipschitz x) (integrable_const c)]
  simp

end OAI.SKFluctuations.LaplaceWindowFormalization
