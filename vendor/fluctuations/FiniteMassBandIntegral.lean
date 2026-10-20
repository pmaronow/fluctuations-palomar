module

public import PhysicalBFiniteMassSum

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def massCellSum : List PositiveMass → ℝ → (ℕ → ℝ) → ℝ
  | [], _, _ => 0
  | b :: bs, a, f => (b.val - a) * f 0 + massCellSum bs b.val (fun j => f (j + 1))

theorem massCellSum_add (as : List PositiveMass) (a : ℝ) (f g : ℕ → ℝ) :
    massCellSum as a (fun j => f j + g j) = massCellSum as a f + massCellSum as a g := by
  induction as generalizing a f g with
  | nil => simp [massCellSum]
  | cons b bs ih =>
    simp only [massCellSum, ih]
    ring

theorem massCellSum_const_mul (as : List PositiveMass) (a C : ℝ) (f : ℕ → ℝ) :
    massCellSum as a (fun j => C * f j) = C * massCellSum as a f := by
  induction as generalizing a f with
  | nil => simp [massCellSum]
  | cons b bs ih =>
    simp only [massCellSum, ih]
    ring

theorem massCellSum_mono {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    {f g : ℕ → ℝ} (hfg : ∀ j < as.length, f j ≤ g j) :
    massCellSum as a f ≤ massCellSum as a g := by
  induction as generalizing a f g with
  | nil => exact le_rfl
  | cons b bs ih =>
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hfg 0 (by simp)) (sub_nonneg.mpr ha.2.1)
    · exact ih ha.2.2 (fun j hj => hfg (j + 1) (by simp only [List.length_cons]; omega))

theorem massCellSum_const (as : List PositiveMass) (a C : ℝ) :
    massCellSum as a (fun _ => C) = (partitionEnd a as - a) * C := by
  induction as generalizing a with
  | nil => simp [massCellSum, partitionEnd]
  | cons b bs ih =>
    simp only [massCellSum, partitionEnd, ih]
    ring

theorem massOrdered_start_le_end {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as) :
    a ≤ partitionEnd a as := by
  induction as generalizing a with
  | nil => exact le_rfl
  | cons b bs ih => exact ha.2.1.trans (ih ha.2.2)

theorem massOrdered_mem_le_end {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    {b : PositiveMass} (hb : b ∈ as) : b.val ≤ partitionEnd a as := by
  induction as generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact massOrdered_start_le_end cs ha.2.2
    · exact ih ha.2.2 hb

theorem massStepFunction_skip_prefix (before after : List PositiveMass) (f : ℕ → ℝ)
    (u : ℝ) (hbefore : ∀ b ∈ before, b.val ≤ u) :
    massStepFunction (before ++ after) f u = massStepFunction after (fun j => f (before.length + j)) u := by
  induction before generalizing f with
  | nil => simp only [List.nil_append, List.length_nil, zero_add]
  | cons b before ih =>
    simp only [List.cons_append, massStepFunction, ite_eq_right (not_lt.mpr (hbefore b List.mem_cons_self))]
    rw [ih (fun j => f (j + 1)) (fun c hc => hbefore c (List.mem_cons_of_mem b hc))]
    simp only [List.length_cons]
    congr 1
    funext j
    congr 1
    omega

theorem massStepFunction_ignore_suffix (before after : List PositiveMass) (f : ℕ → ℝ)
    (u : ℝ) (hafter : ∀ b ∈ after, u < b.val) :
    massStepFunction (before ++ after) f u = massStepFunction before f u := by
  induction before generalizing f with
  | nil =>
    cases after with
    | nil => rfl
    | cons b after => simp only [List.nil_append, massStepFunction, ite_eq_left (hafter b List.mem_cons_self)]
  | cons b before ih =>
    simp only [List.cons_append, massStepFunction]
    split_ifs
    · rfl
    · exact ih (fun j => f (j + 1))

theorem massCellSum_eq_integral {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    (f : ℕ → ℝ) :
    massCellSum as a f = ∫ u in a..partitionEnd a as, massStepFunction as f u := by
  induction as generalizing a f with
  | nil => simp [massCellSum, partitionEnd]
  | cons b bs ih =>
    have hbe := massOrdered_start_le_end bs ha.2.2
    simp only [partitionEnd]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (massStepFunction_intervalIntegrable (b :: bs) f a b.val)
      (massStepFunction_intervalIntegrable (b :: bs) f b.val (partitionEnd b.val bs))]
    have hfirst : (∫ u in a..b.val, massStepFunction (b :: bs) f u) = (b.val - a) * f 0 := by
      calc
        _ = ∫ _u in a..b.val, f 0 := intervalIntegral.integral_congr_Ioo_of_le ha.2.1
          (fun u hu => by simp only [massStepFunction, ite_eq_left hu.2])
        _ = _ := by simp
    have hrest : (∫ u in b.val..partitionEnd b.val bs, massStepFunction (b :: bs) f u) =
        ∫ u in b.val..partitionEnd b.val bs, massStepFunction bs (fun j => f (j + 1)) u :=
      intervalIntegral.integral_congr_Ioo_of_le hbe
        (fun u hu => by simp only [massStepFunction, ite_eq_right (not_lt.mpr hu.1.le)])
    rw [hfirst, hrest, ← ih ha.2.2]
    rfl

theorem massStepFunction_internal_band_integral (before band after : List PositiveMass)
    {a c : ℝ} (hbefore : MassOrdered 0 before) (hba : partitionEnd 0 before = a)
    (hband : MassOrdered a band) (hbc : partitionEnd a band = c)
    (hafter : MassOrdered c after) (f : ℕ → ℝ) :
    (∫ u in a..c, massStepFunction (before ++ band ++ after) f u) =
      massCellSum band a (fun j => f (before.length + j)) := by
  have hac : a ≤ c := hbc ▸ massOrdered_start_le_end band hband
  rw [massCellSum_eq_integral band hband, hbc]
  apply intervalIntegral.integral_congr_Ioo_of_le hac
  intro u hu
  rw [List.append_assoc, massStepFunction_skip_prefix before (band ++ after) f u
    (fun b hb => (hba ▸ massOrdered_mem_le_end before hbefore hb).trans hu.1.le)]
  exact massStepFunction_ignore_suffix band after _ u
    (fun b hb => hu.2.trans_le (hafter.le_of_mem hb))

theorem physicalSampledB_internal_band_eq_cutSum (n : ℕ) (b h : ℝ → ℝ≥0)
    (before band after : List PositiveMass) {a c : ℝ}
    (hbefore : MassOrdered 0 before) (hba : partitionEnd 0 before = a)
    (hband : MassOrdered a band) (hbc : partitionEnd a band = c)
    (hafter : MassOrdered c after)
    (hfull : MassOrdered 0 (before ++ band ++ after)) :
    (∫ u in a..c, physicalSampledB n b h (before ++ band ++ after) hfull u) =
      massCellSum band a (fun j => rootLevelPairMean (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (completedPathClock (n + 1) b h 0)
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2)
        (sampleClockSteps (completedPathClock (n + 1) b h) 0 (before ++ band ++ after))
        (before.length + j)) := by
  rw [physicalSampledB_eq_rooted_massStepFunction]
  exact massStepFunction_internal_band_integral before band after hbefore hba hband hbc hafter _

theorem physicalSampledB_internal_band_le_cutBounds (n : ℕ) (b h : ℝ → ℝ≥0)
    (before band after : List PositiveMass) {a c : ℝ}
    (hbefore : MassOrdered 0 before) (hba : partitionEnd 0 before = a)
    (hband : MassOrdered a band) (hbc : partitionEnd a band = c)
    (hafter : MassOrdered c after) (hfull : MassOrdered 0 (before ++ band ++ after))
    (bounds : ℕ → ℝ)
    (hcuts : ∀ j < band.length,
      let steps := sampleClockSteps (completedPathClock (n + 1) b h) 0 (before ++ band ++ after)
      stepPairDisorder (uniformWeight (n + 1)) (finiteFeature (n + 1))
        (completedPathClock (n + 1) b h 0) (steps.take (before.length + j)) (steps.drop (before.length + j))
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2) 0 ≤ bounds j) :
    (∫ u in a..c, physicalSampledB n b h (before ++ band ++ after) hfull u) ≤
      massCellSum band a bounds := by
  rw [physicalSampledB_internal_band_eq_cutSum n b h before band after hbefore hba hband hbc hafter hfull]
  apply massCellSum_mono band hband
  intro j hj
  rw [physicalRootLevelB_eq_stepPairDisorder (n + 1) _ (sampleClockSteps_ordered _ _ hfull)
    _ (before.length + j) (by simp only [sampleClockSteps_length, List.length_append]; omega)]
  exact hcuts j hj

end
end OAI.SKFluctuations.LaplaceWindowFormalization
