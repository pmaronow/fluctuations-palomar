module

public import QuantileLaw
public import ScalarBoundaryProfile
public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarSourceJet

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

attribute [local instance] Measure.Subtype.measureSpace

def scheduleRadiusQuantile (root : ℝ) (cs : List HeatClock) (u : ℝ) : ℝ :=
  stepClockFunction (fun _ : Fin 1 => root) (heatSteps cs) u 0

theorem scheduleRadiusQuantile_cons (root : ℝ) (c : HeatClock)
    (cs : List HeatClock) (u : ℝ) :
    scheduleRadiusQuantile root (c :: cs) u =
      if c.mass ≤ u then scheduleRadiusQuantile (root + c.time) cs u
        else scheduleRadiusQuantile root cs u := by
  exact stepClockFunction_cons _ _ _ _ _

theorem scheduleRadiusQuantile_lower (root : ℝ) (cs : List HeatClock) (u : ℝ) :
    root ≤ scheduleRadiusQuantile root cs u := by
  unfold scheduleRadiusQuantile stepClockFunction
  apply le_add_of_nonneg_right
  apply List.sum_nonneg
  intro x hx
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
  split_ifs <;> positivity

theorem scheduleRadiusQuantile_upper (root : ℝ) (cs : List HeatClock) (u : ℝ) :
    scheduleRadiusQuantile root cs u ≤ root + scheduleDuration cs := by
  induction cs generalizing root with
  | nil => simp [scheduleRadiusQuantile, stepClockFunction, heatSteps, scheduleDuration]
  | cons c cs ih =>
    rw [scheduleRadiusQuantile_cons]
    split_ifs
    · simpa only [scheduleDuration, NNReal.coe_add, add_assoc] using ih (root + c.time)
    · have h := ih root
      have htime := c.time.coe_nonneg
      simp only [scheduleDuration, NNReal.coe_add]
      linarith

theorem scheduleRadiusQuantile_monotone (root : ℝ) (cs : List HeatClock) :
    Monotone (scheduleRadiusQuantile root cs) := by
  intro u v huv
  unfold scheduleRadiusQuantile stepClockFunction
  apply add_le_add le_rfl
  apply List.sum_le_sum
  intro st hst
  by_cases hu : st.1 ≤ u
  · simp only [if_pos hu, if_pos (hu.trans huv), le_refl]
  · by_cases hv : st.1 ≤ v
    · simp only [if_neg hu, if_pos hv]
      exact st.2 0 |>.coe_nonneg
    · simp only [if_neg hu, if_neg hv, le_refl]

theorem scheduleRadiusQuantile_before {root a u : ℝ} {cs : List HeatClock}
    (ho : OrderedSteps a (heatSteps (ι := Fin 1) cs)) (hu : u < a) :
    scheduleRadiusQuantile root cs u = root :=
  stepClockFunction_before _ ho hu _

theorem scheduleRadiusQuantile_sublevel_first {root t : ℝ}
    (c : HeatClock) (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (c :: cs)))
    (ht : t ∈ Ioo root (root + c.time)) (u : ℝ) :
    scheduleRadiusQuantile root (c :: cs) u ≤ t ↔ u < c.mass := by
  by_cases hu : c.mass ≤ u
  · rw [scheduleRadiusQuantile_cons, if_pos hu]
    constructor
    · intro h
      exact False.elim ((not_le_of_gt ht.2)
        ((scheduleRadiusQuantile_lower (root + c.time) cs u).trans h))
    · intro h
      exact False.elim ((not_lt_of_ge hu) h)
  · have hut : u < c.mass := lt_of_not_ge hu
    have hf : scheduleRadiusQuantile root (c :: cs) u = root :=
      scheduleRadiusQuantile_before
        (by exact ⟨ho.2.1, le_rfl, c.positive, ho.2.2.2⟩) hut
    simp only [hf, le_of_lt ht.1, hut, iff_true]

theorem scheduleRadiusQuantile_sublevel_remove_head {root t : ℝ}
    (c : HeatClock) (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) (c :: cs)))
    (ht : root + c.time ≤ t) (u : ℝ) :
    scheduleRadiusQuantile root (c :: cs) u ≤ t ↔
      scheduleRadiusQuantile (root + c.time) cs u ≤ t := by
  by_cases hu : c.mass ≤ u
  · rw [scheduleRadiusQuantile_cons, if_pos hu]
  · have hut : u < c.mass := lt_of_not_ge hu
    rw [scheduleRadiusQuantile_cons, if_neg hu,
      scheduleRadiusQuantile_before ho.2.2.2 hut,
      scheduleRadiusQuantile_before ho.2.2.2 hut]
    exact iff_of_true ((le_add_of_nonneg_right c.time.coe_nonneg).trans ht) ht

theorem uniformOrderMass_before {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      {u | (u : ℝ) < m} = m := by
  have himage : ((↑) : ParisiFinite.OrderPoint → ℝ) '' {u | (u : ℝ) < m} = Ico 0 m := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property.1, hu⟩
    · intro hx
      exact ⟨⟨x, hx.1, hx.2.le.trans hm.2⟩, hx.2, rfl⟩
  change (volume {u : ParisiFinite.OrderPoint | (u : ℝ) < m}).toReal = _
  rw [← volume_image_subtype_coe measurableSet_Icc, himage]
  simp [Real.volume_Ico, Real.toNNReal_of_nonneg hm.1, hm.1]

theorem schedule_cdf_matches (α : NonnegativeMassProfile)
    (root : ℝ) (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs))
    (hCDF : ∀ t, root ≤ t → α.mass t =
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
        {u | scheduleRadiusQuantile root cs (u : ℝ) ≤ t}) :
    ScheduleProfileMatches α cs root := by
  induction cs generalizing root with
  | nil => trivial
  | cons c cs ih =>
    constructor
    · intro t ht
      rw [hCDF t ht.1.le]
      have he : {u : ParisiFinite.OrderPoint |
          scheduleRadiusQuantile root (c :: cs) (u : ℝ) ≤ t} =
            {u : ParisiFinite.OrderPoint | (u : ℝ) < c.mass} := by
        ext u
        exact scheduleRadiusQuantile_sublevel_first c cs ho ht u
      rw [he]
      exact uniformOrderMass_before ⟨c.positive.le, ho.2.2.2.bounds.2⟩
    · apply ih (root + c.time)
      · exact OrderedSteps.lower le_rfl c.positive.le ho.2.2.2
      · intro t ht
        rw [hCDF t ((le_add_of_nonneg_right c.time.coe_nonneg).trans ht)]
        congr 1
        ext u
        exact scheduleRadiusQuantile_sublevel_remove_head c cs ho ht u

def normalizedScheduleQuantile (T root : ℝ) (cs : List HeatClock) (u : ℝ) : ℝ :=
  scheduleRadiusQuantile root cs u / T

theorem normalizedScheduleQuantile_bounds {T root : ℝ} (hT : 0 < T)
    (hr : 0 ≤ root) (cs : List HeatClock)
    (ht : root + scheduleDuration cs ≤ T) :
    ∀ u ∈ Icc (0 : ℝ) 1, normalizedScheduleQuantile T root cs u ∈ Icc (0 : ℝ) 1 := by
  intro u _
  exact ⟨div_nonneg (hr.trans (scheduleRadiusQuantile_lower root cs u)) hT.le,
    (div_le_one hT).mpr ((scheduleRadiusQuantile_upper root cs u).trans ht)⟩

theorem normalizedScheduleQuantile_monotone {T root : ℝ} (hT : 0 ≤ T)
    (cs : List HeatClock) : Monotone (normalizedScheduleQuantile T root cs) :=
  fun _ _ huv => div_le_div_of_nonneg_right (scheduleRadiusQuantile_monotone root cs huv) hT

def actualScheduleProfile {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T) : NonnegativeMassProfile :=
  rescaledMassProfile (quantileMassProfile (normalizedScheduleQuantile T root cs)
    (normalizedScheduleQuantile_bounds hT hr cs ht)) hT

theorem actualScheduleProfile_le_one {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T) (t : ℝ) :
    (actualScheduleProfile hT hr cs ht).mass t ≤ 1 :=
  (quantileMassProfile (normalizedScheduleQuantile T root cs)
    (normalizedScheduleQuantile_bounds hT hr cs ht)).property.1 (t / T) |>.2

theorem actualScheduleProfile_cdf {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T) (t : ℝ) :
    (actualScheduleProfile hT hr cs ht).mass t =
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
        {u | scheduleRadiusQuantile root cs (u : ℝ) ≤ t} := by
  change (quantileMassProfile (normalizedScheduleQuantile T root cs)
    (normalizedScheduleQuantile_bounds hT hr cs ht)).val (t / T) = _
  rw [quantileMassProfile_cdf _
    ((normalizedScheduleQuantile_monotone (root := root) hT.le cs).monotoneOn _)]
  congr 1
  ext u
  exact div_le_div_iff_of_pos_right hT

theorem actual_schedule_cdf_matches {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) :
    ScheduleProfileMatches (actualScheduleProfile hT hr cs ht) cs root :=
  schedule_cdf_matches _ root cs ho
    (fun t _ => actualScheduleProfile_cdf hT hr cs ht t)

theorem actual_schedule_zero_head {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T) :
    ∀ t ∈ Ioo (0 : ℝ) root, (actualScheduleProfile hT hr cs ht).mass t = 0 := by
  intro t hti
  rw [actualScheduleProfile_cdf hT hr cs ht t]
  have he : {u : ParisiFinite.OrderPoint |
      scheduleRadiusQuantile root cs (u : ℝ) ≤ t} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.notMem_empty, iff_false]
    intro hu
    exact (not_le_of_gt hti.2) ((scheduleRadiusQuantile_lower root cs u).trans hu)
  rw [he]
  simp [Measure.real]

theorem actual_schedule_profile_eq_root (J : HeatJet 0)
    {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue (actualScheduleProfile hT hr cs ht) 0
        (NNReal.mk root hr + scheduleDuration cs) x =
      clockRoot (J.schedule cs).F root x := by
  apply finite_scalar_profile_eq_root_schedule J _
    (actualScheduleProfile_le_one hT hr cs ht) (NNReal.mk root hr) cs 0
  · simpa only [NNReal.coe_mk, zero_add] using actual_schedule_zero_head hT hr cs ht
  · simpa only [NNReal.coe_mk, zero_add] using actual_schedule_cdf_matches hT hr cs ht ho

theorem ScheduleProfileMatches.append (α : NonnegativeMassProfile)
    (cs ds : List HeatClock) (l : ℝ)
    (hcs : ScheduleProfileMatches α cs l)
    (hds : ScheduleProfileMatches α ds (l + scheduleDuration cs)) :
    ScheduleProfileMatches α (cs ++ ds) l := by
  induction cs generalizing l with
  | nil => simpa only [List.nil_append, scheduleDuration, NNReal.coe_zero, add_zero] using hds
  | cons c cs ih =>
    refine ⟨hcs.1, ih (l + c.time) hcs.2 ?_⟩
    convert hds using 1
    simp only [scheduleDuration, NNReal.coe_add, add_assoc]

theorem scheduleDuration_append (cs ds : List HeatClock) :
    scheduleDuration (cs ++ ds) = scheduleDuration cs + scheduleDuration ds := by
  induction cs with
  | nil => simp [scheduleDuration]
  | cons c cs ih => simp [scheduleDuration, ih, add_assoc]

def terminalFillClock {T root : ℝ} (cs : List HeatClock)
    (_ht : root + scheduleDuration cs ≤ T) : HeatClock :=
  ⟨1, by norm_num, Real.toNNReal (T - (root + scheduleDuration cs))⟩

theorem actual_schedule_terminal_one {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T) :
    ∀ t, root + scheduleDuration cs < t →
      (actualScheduleProfile hT hr cs ht).mass t = 1 := by
  intro t hti
  rw [actualScheduleProfile_cdf hT hr cs ht t]
  have he : {u : ParisiFinite.OrderPoint |
      scheduleRadiusQuantile root cs (u : ℝ) ≤ t} = univ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (scheduleRadiusQuantile_upper root cs u).trans hti.le
  rw [he]
  simp [Measure.real]

theorem actual_schedule_profile_eq_full_root (J : HeatJet 0)
    {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue (actualScheduleProfile hT hr cs ht) 0 (NNReal.mk T hT.le) x =
      clockRoot (J.schedule (cs ++ [terminalFillClock cs ht])).F root x := by
  have hfill : ((terminalFillClock cs ht).time : ℝ) = T - (root + scheduleDuration cs) := by
    exact Real.coe_toNNReal _ (sub_nonneg.mpr ht)
  have hm : ScheduleProfileMatches (actualScheduleProfile hT hr cs ht)
      [terminalFillClock cs ht] (root + scheduleDuration cs) := by
    constructor
    · intro t hti
      exact actual_schedule_terminal_one hT hr cs ht t hti.1
    · trivial
  have hmatch := ScheduleProfileMatches.append _ cs [terminalFillClock cs ht] root
    (actual_schedule_cdf_matches hT hr cs ht ho) hm
  have hh := finite_scalar_profile_eq_root_schedule J _
    (actualScheduleProfile_le_one hT hr cs ht) (NNReal.mk root hr)
    (cs ++ [terminalFillClock cs ht]) 0
    (by simpa only [NNReal.coe_mk, zero_add] using actual_schedule_zero_head hT hr cs ht)
    (by simpa only [NNReal.coe_mk, zero_add] using hmatch) x
  have heq : NNReal.mk root hr + scheduleDuration (cs ++ [terminalFillClock cs ht]) =
      NNReal.mk T hT.le := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, scheduleDuration_append, scheduleDuration,
      NNReal.coe_zero, add_zero, hfill]
    simp only [NNReal.coe_mk]
    ring
  rw [heq] at hh
  exact hh

def scalarSchedulePressure (root : ℝ) (cs : List HeatClock) : ℝ :=
  stepDisorderPressure (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature (fun _ => 1)
    (fun _ => Real.toNNReal root) (heatSteps cs) 0

theorem heatSteps_total_variance (cs : List HeatClock) :
    ((heatSteps (ι := Fin 1) cs).map (fun st => (st.2 0 : ℝ))).sum = scheduleDuration cs := by
  induction cs with
  | nil => simp [heatSteps, scheduleDuration]
  | cons c cs ih =>
    simp only [heatSteps, List.map_cons, List.sum_cons, scheduleDuration,
      NNReal.coe_add] at *
    exact congrArg (fun z => (c.time : ℝ) + z) ih

theorem scalarSchedulePressure_eq_root (root : ℝ) (hr : 0 ≤ root)
    (cs : List HeatClock) :
    scalarSchedulePressure root cs = clockRoot (scalarTerminal.schedule cs).F root 0 -
      (root + scheduleDuration cs) / 2 := by
  unfold scalarSchedulePressure stepDisorderPressure
  rw [← funext (scalar_schedule_eq_hierarchy cs)]
  simp only [Fin.sum_univ_one, heatSteps_total_variance, mul_one,
    Real.coe_toNNReal _ hr]
  unfold clockRoot
  ring

theorem scalar_schedule_terminal_fill (cs : List HeatClock) (fill : HeatClock)
    (hm : fill.mass = 1) :
    (scalarTerminal.schedule (cs ++ [fill])).F =
      fun x => (scalarTerminal.schedule cs).F x + (fill.time : ℝ) / 2 := by
  rw [HeatJet.schedule_append]
  apply schedule_potential_add_constant
  funext x
  change clockContinuation fill.mass scalarTerminal.F fill.time x = _
  rw [hm]
  simpa only [scalarTerminal_F] using scalarTerminal_mass_one fill.time x

theorem scalar_schedule_value_eq_pressure
    {T root : ℝ} (hT : 0 < T) (hr : 0 ≤ root)
    (cs : List HeatClock) (ht : root + scheduleDuration cs ≤ T)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) :
    scalarParisiValue hT
        (quantileMassProfile (normalizedScheduleQuantile T root cs)
          (normalizedScheduleQuantile_bounds hT hr cs ht)) =
      scalarSchedulePressure root cs + T / 4 *
        (∫ u in (0 : ℝ)..1, normalizedScheduleQuantile T root cs u ^ 2) := by
  have hp := actual_schedule_profile_eq_full_root scalarTerminal hT hr cs ht ho 0
  rw [scalar_schedule_terminal_fill cs (terminalFillClock cs ht) rfl,
    clockRoot_potential_add_constant (scalarTerminal.schedule cs)] at hp
  have hfill : ((terminalFillClock cs ht).time : ℝ) = T - (root + scheduleDuration cs) :=
    Real.coe_toNNReal _ (sub_nonneg.mpr ht)
  rw [hfill] at hp
  unfold scalarParisiValue
  change scalarTerminal.nonnegativeProfileValue (actualScheduleProfile hT hr cs ht)
    0 (NNReal.mk T hT.le) 0 - T / 2 * scalarPenalty _ - T / 4 = _
  rw [hp, quantileMassProfile_penalty _
    ((normalizedScheduleQuantile_monotone (root := root) hT.le cs).monotoneOn _),
    scalarSchedulePressure_eq_root root hr cs]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
