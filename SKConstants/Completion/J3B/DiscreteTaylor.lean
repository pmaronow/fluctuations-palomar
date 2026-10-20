module

public import SKConstants.Completion.LJ.EnergyNormalization
public import SKConstants.Upstream.OAI.Probability.SKSupport.Foundations.AdaptedIndepIncrement

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport

def spatialRemainder (U m a : ℝ → ℝ → ℝ) (s y z : ℝ) : ℝ :=
  U s z - U s y - m s y * (z - y) - a s y * (z - y) ^ 2 / 2

theorem time_space_increment (U m a : ℝ → ℝ → ℝ) (s t y z : ℝ) :
    U t z - U s y =
      m s y * (z - y) + a s y * (z - y) ^ 2 / 2 +
        spatialRemainder U m a s y z + (U t z - U s z) := by
  unfold spatialRemainder
  ring

theorem time_space_telescope (U m a : ℝ → ℝ → ℝ) (t Y : ℕ → ℝ) (N : ℕ) :
    U (t N) (Y N) - U (t 0) (Y 0) =
      ∑ i ∈ Finset.range N,
        (m (t i) (Y i) * (Y (i + 1) - Y i) +
          a (t i) (Y i) * (Y (i + 1) - Y i) ^ 2 / 2 +
          spatialRemainder U m a (t i) (Y i) (Y (i + 1)) +
          (U (t (i + 1)) (Y (i + 1)) - U (t i) (Y (i + 1)))) := by
  simp_rw [← time_space_increment]
  exact (Finset.sum_range_sub (fun i => U (t i) (Y i)) N).symm

theorem weighted_potential_telescope (p A : ℕ → ℝ) (N : ℕ) :
    p N * A N - p 0 * A 0 =
      (∑ i ∈ Finset.range N, p i * (A (i + 1) - A i)) +
        ∑ i ∈ Finset.range N, (p (i + 1) - p i) * A (i + 1) := by
  rw [← Finset.sum_add_distrib]
  symm
  calc
    _ = ∑ i ∈ Finset.range N, (p (i + 1) * A (i + 1) - p i * A i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := Finset.sum_range_sub (fun i => p i * A i) N

theorem joint_potential_discrete_identity (U m a : ℝ → ℝ → ℝ)
    (t Y B p A : ℕ → ℝ) (c x : ℝ) (N : ℕ) :
    (c * p N * A N + x * Y N - U (t N) (Y N)) -
        (c * p 0 * A 0 + x * Y 0 - U (t 0) (Y 0)) -
        (∑ i ∈ Finset.range N,
          (c * p i * (A (i + 1) - A i) +
            (x - m (t i) (Y i)) * (B (i + 1) - B i))) =
      ∑ i ∈ Finset.range N,
        (c * (p (i + 1) - p i) * A (i + 1) +
          (x - m (t i) (Y i)) * ((Y (i + 1) - Y i) - (B (i + 1) - B i)) -
          a (t i) (Y i) * (Y (i + 1) - Y i) ^ 2 / 2 -
          spatialRemainder U m a (t i) (Y i) (Y (i + 1)) -
          (U (t (i + 1)) (Y (i + 1)) - U (t i) (Y (i + 1)))) := by
  have hprod := weighted_potential_telescope p A N
  have hU := time_space_telescope U m a t Y N
  have hY := Finset.sum_range_sub Y N
  have he : (c * p N * A N + x * Y N - U (t N) (Y N)) -
      (c * p 0 * A 0 + x * Y 0 - U (t 0) (Y 0)) =
      c * (p N * A N - p 0 * A 0) + x * (Y N - Y 0) -
        (U (t N) (Y N) - U (t 0) (Y 0)) := by ring
  rw [he, hprod, hU, ← hY]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spatialRemainder_bound (U m a : ℝ → ℝ → ℝ) (s : ℝ) (C : ℝ)
    (hU : ContDiff ℝ 3 (U s)) (hm : deriv (U s) = m s)
    (ha : deriv (m s) = a s) (hC : ∀ y, |iteratedDeriv 3 (U s) y| ≤ C)
    (y z : ℝ) : |spatialRemainder U m a s y z| ≤ C / 6 * |z - y| ^ 3 := by
  have h := WeakIto.taylor2_bound hU hC y (z - y)
  simpa only [add_sub_cancel, hm, ha, spatialRemainder, mul_assoc, div_eq_mul_inv,
    one_div, mul_comm, mul_left_comm, one_mul] using h

theorem physicalValue_hasDerivAt (β : ℝ) (hβ : β ≠ 0) (v : ℝ)
    (hv : v ∈ Icc (0 : ℝ) (β ^ 2)) (y : ℝ) :
    HasDerivAt (parisiPhysicalValue β (parisiEquilibriumMeasure β) v)
      (actualParisiFullMagnetization β v y) y := by
  have h := (parisiPhysicalValue_spatial_derivatives β hβ
    (parisiEquilibriumMeasure β) v hv).1 y
  simpa only [actualParisiFullMagnetization,
    cdfTimeClamp_eq (parisiPhysicalTime_mem β hβ v hv)] using h

theorem physicalValue_contDiff (β : ℝ) (hβ : β ≠ 0) (v : ℝ)
    (hv : v ∈ Ico (0 : ℝ) (β ^ 2)) :
    ContDiff ℝ 3 (parisiPhysicalValue β (parisiEquilibriumMeasure β) v) := by
  have hq0 : 0 ≤ v / β ^ 2 := div_nonneg hv.1 (sq_nonneg β)
  have hq1 : v / β ^ 2 < 1 := (div_lt_one (sq_pos_of_ne_zero hβ)).mpr hv.2
  have h := (scalarCDFValue_regularDatum β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) hβ hq0 hq1).smooth
  simpa only [parisiPhysicalValue, parisiCDFValue_eq_upstream, Nat.cast_ofNat] using
    h.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)

def actualSpatialRemainder (β v y z : ℝ) : ℝ :=
  spatialRemainder (parisiPhysicalValue β (parisiEquilibriumMeasure β))
    (actualParisiFullMagnetization β) (actualParisiFullCurvature β) v y z

theorem actualSpatialRemainder_bound (β : ℝ) (hβ : β ≠ 0) (v : ℝ)
    (hv : v ∈ Ico (0 : ℝ) (β ^ 2)) (y z : ℝ) :
    |actualSpatialRemainder β v y z| ≤
      (susceptibilityLipschitzConstant : ℝ) / 6 * |z - y| ^ 3 := by
  have hm : deriv (parisiPhysicalValue β (parisiEquilibriumMeasure β) v) =
      actualParisiFullMagnetization β v :=
    funext (fun y => (physicalValue_hasDerivAt β hβ v ⟨hv.1, hv.2.le⟩ y).deriv)
  have ha : deriv (actualParisiFullMagnetization β v) = actualParisiFullCurvature β v :=
    funext (fun y => (actualParisiFullMagnetization_hasDerivAt β v y).deriv)
  apply spatialRemainder_bound _ _ _ v _ (physicalValue_contDiff β hβ v hv) hm ha
  intro y
  have h3 : iteratedDeriv 3 (parisiPhysicalValue β (parisiEquilibriumMeasure β) v) =
      deriv (actualParisiFullCurvature β v) := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, hm, ha]
  rw [h3]
  simpa only [Real.norm_eq_abs] using
    (norm_deriv_le_of_lipschitz (actualParisiFullCurvature_lipschitz β v) (x₀ := y))

end SKConstants.Completion.J3B
