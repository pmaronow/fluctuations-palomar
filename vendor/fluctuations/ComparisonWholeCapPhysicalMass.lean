module

public import ComparisonWholeCapEndpoints
public import ActualComparisonScalarUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Filter LaplaceWindowFormalization Hierarchy
open scoped Topology ENNReal
attribute [local instance] Classical.propDecidable

def wholeCapRadiusMass (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1,q u ∈ Icc (0:ℝ) 1) : Measure ℝ :=
  (quantileLaw q hqb : Measure ParisiFinite.OrderPoint).map
    (Subtype.val : ParisiFinite.OrderPoint → ℝ)

instance wholeCapRadiusMass_probability (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1,q u ∈ Icc (0:ℝ) 1) :
    IsProbabilityMeasure (wholeCapRadiusMass q hqb) := by
  unfold wholeCapRadiusMass
  infer_instance

theorem wholeCapRadiusMass_apply (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hqb : ∀ u ∈ Icc (0:ℝ) 1,q u ∈ Icc (0:ℝ) 1)
    {A : Set ℝ} (hA : MeasurableSet A) :
    wholeCapRadiusMass q hqb A=
      (uniformOrderMass : Measure ParisiFinite.OrderPoint) {u | q (u:ℝ)∈A} := by
  rw [wholeCapRadiusMass,Measure.map_apply measurable_subtype_coe hA]
  unfold quantileLaw
  rw [ProbabilityMeasure.map_apply' _
    (quantileOrderMap_measurable q hq hqb).aemeasurable (hA.preimage measurable_subtype_coe)]
  rfl

theorem wholeCapRadiusMass_cdf (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1,q u ∈ Icc (0:ℝ) 1) (r : ℝ) :
    (wholeCapRadiusMass q hqb).real (Iic r)=(quantileMassProfile q hqb).val r := by
  rw [wholeCapRadiusMass,map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  rfl

theorem wholeCapRadiusMass_Ioc (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1,q u ∈ Icc (0:ℝ) 1) {a b : ℝ} (hab : a≤b) :
    (wholeCapRadiusMass q hqb).real (Ioc a b)=
      (quantileMassProfile q hqb).val b-(quantileMassProfile q hqb).val a := by
  rw [← Iic_sdiff_Iic,measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic,
    wholeCapRadiusMass_cdf,wholeCapRadiusMass_cdf]

theorem wholeCap_finite_selection_real_tendsto {U : Set ℝ} (hU : IsOpen U)
    (μ : Measure ℝ) (hfinite : μ U ≠ ∞) :
    ∃ F : ℕ → Finset (ordConnectedSection U), Monotone F ∧
      (∀ r : ordConnectedSection U, ∃ n, r ∈ F n) ∧
      Tendsto (fun n => μ.real (U\wholeCapFiniteUnion U (F n))) atTop (𝓝 0) := by
  obtain ⟨F,hmono,hcover,htail⟩ := wholeCap_finite_selection_tendsto hU μ hfinite
  refine ⟨F,hmono,hcover,?_⟩
  simpa only [Measure.real,Function.comp_def,ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠∞)).comp htail

theorem wholeCap_exists_finite_selection_real {U : Set ℝ} (hU : IsOpen U)
    (μ : Measure ℝ) (hfinite : μ U ≠ ∞) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ F : Finset (ordConnectedSection U), μ.real (U\wholeCapFiniteUnion U F)<epsilon := by
  obtain ⟨F,_,_,htail⟩ := wholeCap_finite_selection_real_tendsto hU μ hfinite
  obtain ⟨n,hn⟩ := (htail.eventually (Iio_mem_nhds hepsilon)).exists
  exact ⟨F n,hn⟩

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc : 0<c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c≤k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem wholeCap_actual_comparison_mass_Ioc (α : inverseIntegralConstraints 0 0 k M)
    {a b : ℝ} (hab : a≤b) :
    (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
      (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real (Ioc a b)=
      α.val.val b-α.val.val a := by
  rw [wholeCapRadiusMass_Ioc _ _ hab,comparisonSweepQuantile_massProfile_eq hc hk hkc hm hM α]

theorem wholeCap_actual_comparison_mass_finite_selection
    (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ} (hU : IsOpen U) :
    ∃ F : ℕ → Finset (ordConnectedSection U), Monotone F ∧
      (∀ r : ordConnectedSection U, ∃ n, r ∈ F n) ∧
      Tendsto (fun n =>
        (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
          (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
          (U\wholeCapFiniteUnion U (F n))) atTop (𝓝 0) :=
  wholeCap_finite_selection_real_tendsto hU _ (by finiteness)

end

end OAI.SKFluctuations.WholeUnitSideKernel
