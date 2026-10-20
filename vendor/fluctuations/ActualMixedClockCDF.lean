module

public import QuantileLaw
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRetainTwo

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Measure.Subtype.measureSpace

def actualMixedClock (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ) : ℝ :=
  (h u : ℝ) + (b u : ℝ)*orderedPathS n b h u

theorem actualMixedClock_bounds (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    0 ≤ actualMixedClock n b h u ∧ actualMixedClock n b h u ≤ (h u : ℝ)+(b u : ℝ) := by
  have hs := orderedPath_SK_bounds n hn b h hb hh hu
  unfold actualMixedClock
  constructor
  · exact add_nonneg (h u).coe_nonneg (mul_nonneg (b u).coe_nonneg hs.1)
  · have hle := mul_le_mul_of_nonneg_left hs.2.1 (b u).coe_nonneg
    linarith

theorem actualMixedClock_monotone (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    MonotoneOn (actualMixedClock n b h) (Ioc (0 : ℝ) 1) := by
  have hs := (orderedPath_SK_monotone n hn b h hb hh).1
  intro u hu v hv huv
  unfold actualMixedClock
  have hb' : (b u : ℝ) ≤ b v := NNReal.coe_le_coe.mpr (hb ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩ huv)
  have hh' : (h u : ℝ) ≤ h v := NNReal.coe_le_coe.mpr (hh ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩ huv)
  exact add_le_add hh' (mul_le_mul hb' (hs hu hv huv)
    (orderedPath_SK_bounds n hn b h hb hh hu).1 (b v).coe_nonneg)

def actualScalarClockQuantile (T : ℝ) (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else actualMixedClock n b h u / T

theorem actualScalarClockQuantile_on {T u : ℝ} (n : ℕ) (b h : ℝ → ℝ≥0)
    (hu : 0 < u) : actualScalarClockQuantile T n b h u = actualMixedClock n b h u / T := by
  simp only [actualScalarClockQuantile, if_neg (not_le.mpr hu)]

theorem actualScalarClockQuantile_monotone {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    MonotoneOn (actualScalarClockQuantile T n b h) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  by_cases hv0 : v ≤ 0
  · simp only [actualScalarClockQuantile, if_pos hv0, if_pos (huv.trans hv0)]
    exact le_rfl
  · have hvp : 0 < v := lt_of_not_ge hv0
    rw [actualScalarClockQuantile_on n b h hvp]
    by_cases hu0 : u ≤ 0
    · simp only [actualScalarClockQuantile, if_pos hu0]
      exact div_nonneg (actualMixedClock_bounds n hn b h hb hh ⟨hvp, hv.2⟩).1 hT.le
    · rw [actualScalarClockQuantile_on n b h (lt_of_not_ge hu0)]
      exact div_le_div_of_nonneg_right
        (actualMixedClock_monotone n hn b h hb hh ⟨lt_of_not_ge hu0, hu.2⟩ ⟨hvp, hv.2⟩ huv) hT.le

theorem actualScalarClockQuantile_bounds {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) :
    ∀ u ∈ Icc (0 : ℝ) 1, actualScalarClockQuantile T n b h u ∈ Icc (0 : ℝ) 1 := by
  intro u hu
  by_cases hu0 : u ≤ 0
  · simp only [actualScalarClockQuantile, if_pos hu0]
    exact ⟨le_rfl, zero_le_one⟩
  · rw [actualScalarClockQuantile_on n b h (lt_of_not_ge hu0)]
    have hK := actualMixedClock_bounds n hn b h hb hh ⟨lt_of_not_ge hu0, hu.2⟩
    exact ⟨div_nonneg hK.1 hT.le, (div_le_one₀ hT).mpr (hK.2.trans (htotal u hu))⟩

theorem quantileMassProfile_le_of_larger_clock (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    {t v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hclock : t < q v) :
    (quantileMassProfile q hqb).val t ≤ v := by
  rw [quantileMassProfile_cdf q hq hqb]
  have hsub : {u : ParisiFinite.OrderPoint | q (u : ℝ) ≤ t} ⊆ Iio ⟨v, hv⟩ := by
    intro u hu
    change q (u : ℝ) ≤ t at hu
    change (u : ℝ) < v
    by_contra hn
    have hh := hq hv u.property (le_of_not_gt hn)
    linarith
  have hm := measureReal_mono (μ := (uniformOrderMass : Measure ParisiFinite.OrderPoint)) hsub
  have he : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real (Iio ⟨v, hv⟩) = v := by
    change (volume (Iio (⟨v, hv⟩ : ParisiFinite.OrderPoint))).toReal = v
    rw [unitInterval.volume_Iio, ENNReal.toReal_ofReal hv.1]
  exact hm.trans_eq he

theorem scalarProfileOfParisiMeasure_right_continuous
    (ρ : ProbabilityMeasure ParisiFinite.OrderPoint) (t : ℝ) :
    ContinuousWithinAt (scalarProfileOfParisiMeasure ρ).val (Ici t) t := by
  let ν := (ρ : Measure ParisiFinite.OrderPoint).map (fun x : ParisiFinite.OrderPoint => (x : ℝ))
  have he : (scalarProfileOfParisiMeasure ρ).val = cdf ν := by
    funext s
    rw [cdf_eq_real, map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
    rfl
  rw [he]
  exact (cdf ν).right_continuous t

theorem quantileMassProfile_right_continuous (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    ContinuousWithinAt (quantileMassProfile q hqb).val (Ici t) t :=
  scalarProfileOfParisiMeasure_right_continuous _ _

def actualMixedMassProfile {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) :
    boundedMassProfiles :=
  quantileMassProfile (actualScalarClockQuantile T n b h)
    (actualScalarClockQuantile_bounds hT n hn b h hb hh htotal)

theorem actualMixedMassProfile_mem {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) :
    actualMixedMassProfile hT n hn b h hb hh htotal ∈ scalarProfiles :=
  quantileMassProfile_mem _ _

theorem actualMixedMassProfile_right_continuous {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (t : ℝ) :
    ContinuousWithinAt (actualMixedMassProfile hT n hn b h hb hh htotal).val (Ici t) t :=
  quantileMassProfile_right_continuous _ _ _

theorem actualMixedMassProfile_cdf_cap {T v : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T)
    {t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hclock : t < actualMixedClock n b h v / T) :
    (actualMixedMassProfile hT n hn b h hb hh htotal).val t ≤ v := by
  apply quantileMassProfile_le_of_larger_clock _
    (actualScalarClockQuantile_monotone hT n hn b h hb hh) _ ⟨hv.1.le, hv.2⟩
  simpa only [actualScalarClockQuantile_on n b h hv.1] using hclock

end OAI.SKFluctuations.LaplaceWindowFormalization
