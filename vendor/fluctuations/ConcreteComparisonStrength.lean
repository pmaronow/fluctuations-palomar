module

public import ComparisonStrengthShape
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonMinimumRegularRawMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def laplaceComparisonStrength (d lam : ℝ) : ℝ → ℝ :=
  comparisonStrength laplaceComparisonShape d lam

theorem laplaceComparisonStrength_contDiff (d lam : ℝ) :
    ContDiff ℝ 1 (laplaceComparisonStrength d lam) := by
  change ContDiff ℝ 1 (fun r : ℝ => lam*laplaceComparisonShape (lam*r/d^3))
  exact contDiff_const.mul (laplaceComparisonShape_contDiff.comp
    ((contDiff_const.mul contDiff_id).div_const (d^3)))

theorem laplaceComparisonStrength_pos (d : ℝ) {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    0 < laplaceComparisonStrength d lam r :=
  mul_pos hlam (laplaceComparisonShape_pos _)

theorem laplaceComparisonStrength_le (d : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (r : ℝ) :
    laplaceComparisonStrength d lam r ≤ lam := by
  exact (mul_le_mul_of_nonneg_left (laplaceComparisonShape_le_one _) hlam).trans_eq (mul_one lam)

theorem laplaceComparisonStrength_logSlope {d lam : ℝ} (hd : d ≠ 0) (hlam : lam ≠ 0)
    (r : ℝ) :
    comparisonLogSlope (laplaceComparisonStrength d lam) r =
      laplaceComparisonSlope (lam*r/d^3) := by
  rw [laplaceComparisonStrength,comparisonLogSlope_strength hd hlam
    (laplaceComparisonShape_hasDerivAt _).differentiableAt
    (laplaceComparisonShape_pos _).ne',laplaceComparisonShape_logSlope]

theorem laplaceComparisonStrength_logSlope_mem {d lam : ℝ} (hd : d ≠ 0)
    (hlam : lam ≠ 0) (r : ℝ) :
    comparisonLogSlope (laplaceComparisonStrength d lam) r ∈ Ico (0:ℝ) 1 := by
  rw [laplaceComparisonStrength_logSlope hd hlam]
  exact laplaceComparisonSlope_mem_Ico _

theorem laplaceComparisonStrength_uniform_slope {N d lam : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    (1/3)/Real.log N ≤ 1-comparisonLogSlope (laplaceComparisonStrength d lam) r := by
  apply comparisonStrength_slope_bound hN hlog hd hnd hlam hld hr (by norm_num)
    (laplaceComparisonShape_hasDerivAt _).differentiableAt (laplaceComparisonShape_pos _).ne'
  rw [laplaceComparisonShape_logSlope]
  exact laplaceComparisonSlope_saving _
    (div_nonneg (mul_nonneg hlam.le hr.1) (pow_nonneg hd.le _))

theorem laplaceComparisonStrength_lower {d lam r : ℝ} (hd : 0 < d)
    (hlam : 0 < lam) (hr : 0 < r) :
    min lam (d^3/r) ≤ laplaceComparisonStrength d lam r := by
  have ht : 0 ≤ lam*r/d^3 :=
    div_nonneg (mul_nonneg hlam.le hr.le) (pow_nonneg hd.le _)
  have h := mul_le_mul_of_nonneg_left (laplaceComparisonShape_lower _ ht) hlam.le
  have he : lam*(1/(lam*r/d^3)) = d^3/r := by field_simp
  rw [mul_min_of_nonneg _ _ hlam.le,mul_one,he] at h
  exact h

theorem laplaceComparisonStrength_monotonicities {d lam r₀ : ℝ}
    (hd : d ≠ 0) (hlam : 0 < lam) (hr₀ : 0 ≤ r₀) :
    AntitoneOn (laplaceComparisonStrength d lam) (Icc r₀ 1) ∧
      MonotoneOn (fun r => laplaceComparisonStrength d lam r*r) (Icc r₀ 1) := by
  apply strength_monotonicities_of_logSlope hr₀ _
    (laplaceComparisonStrength_contDiff d lam).continuous
  · intro r _
    exact (laplaceComparisonStrength_contDiff d lam).differentiable (by norm_num) r
  · intro r _
    exact laplaceComparisonStrength_pos d hlam r
  · intro r _
    exact ⟨(laplaceComparisonStrength_logSlope_mem hd hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem hd hlam.ne' r).2.le⟩

theorem laplaceFinalStrength_eq {d : ℝ} (hd : d ≠ 0) (r : ℝ) :
    laplaceComparisonStrength d (d^2) r = d^2*laplaceComparisonShape (r/d) := by
  unfold laplaceComparisonStrength comparisonStrength
  congr 2
  field_simp

theorem laplaceFinalStrength_shell_lower {d C r : ℝ} (hd : 0 < d) (hC : 0 < C)
    (hr : 0 < r) (hrC : r ≤ C*d) :
    min 1 (1/C)*d^2 ≤ laplaceComparisonStrength d (d^2) r := by
  have hrl : d^2/C ≤ d^3/r := by
    apply (div_le_div_iff₀ hC hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrC (sq_nonneg d)]
  calc
    min 1 (1/C)*d^2 = min (d^2) (d^2/C) := by
      rw [min_mul_of_nonneg _ _ (sq_nonneg d)]
      simp only [one_mul]
      congr 1
      ring
    _ ≤ min (d^2) (d^3/r) := min_le_min le_rfl hrl
    _ ≤ laplaceComparisonStrength d (d^2) r :=
      laplaceComparisonStrength_lower hd (sq_pos_of_pos hd) hr

theorem concreteComparisonFloorCap_minimum
    {N δ U L E d lam : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hLU : L ≤ U) (hE : 0 < E) (hd : 0 < d) (hq : 2 ≤ N^δ)
    (hlam : 0 < lam) (b : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    let g := laplaceComparisonStrength d lam
    let hg := (laplaceComparisonStrength_contDiff d lam).continuous
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ := δ) hN hU (r₀ := 0) le_rfl
    let hkc := fun r (hri : r ∈ Icc (0:ℝ) 1) =>
      comparisonFloor_lower_on (δ := δ) hN hU (r₀ := 0) le_rfl hri
    let hm := comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd.le zero_le_one
    ∃ α : inverseIntegralConstraints 0 0 k M,
      ∀ β : inverseIntegralConstraints 0 0 k M,
        inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x α ≤
        inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x β := by
  dsimp only
  have hm := laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀ := 0) le_rfl
  exact comparisonFloorCap_fullMass_minimum hN hU hL hLU hE hd.le hq b hb
    (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
    hm.1 hm.2 (fun r _ => (laplaceComparisonStrength_pos d hlam r).le)
    (fun r _ => (laplaceComparisonStrength_le d hlam.le r).trans hlb) n hn x

end OAI.SKFluctuations.LaplaceWindowFormalization
