module

public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def initialShellMatrixClock (T epsilon s u : ℝ) : ℝ :=
  T - if u < s then epsilon else 0

theorem initialShellMatrixClock_monotone (T s : ℝ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) : Monotone (initialShellMatrixClock T epsilon s) := by
  intro u v huv
  by_cases hus : u < s
  · by_cases hvs : v < s
    · simp [initialShellMatrixClock, hus, hvs]
    · simpa [initialShellMatrixClock, hus, hvs] using sub_le_self T hepsilon
  · have hvs : ¬v < s := fun hv => hus (huv.trans_lt hv)
    simp [initialShellMatrixClock, hus, hvs]

theorem initialShellMatrixClock_zero (T epsilon : ℝ) {s : ℝ} (hs : 0 < s) :
    initialShellMatrixClock T epsilon s 0 = T - epsilon := by
  simp [initialShellMatrixClock, hs]

theorem strength_monotonicities_of_logSlope
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (g : ℝ → ℝ) (hg : Continuous g)
    (hdiff : ∀ r ∈ Ioo r₀ 1, DifferentiableAt ℝ g r)
    (hgpos : ∀ r ∈ Ioo r₀ 1, 0 < g r)
    (hp : ∀ r ∈ Ioo r₀ 1, comparisonLogSlope g r ∈ Icc (0 : ℝ) 1) :
    AntitoneOn g (Icc r₀ 1) ∧
      MonotoneOn (fun r => g r * r) (Icc r₀ 1) := by
  constructor
  · apply antitoneOn_of_deriv_nonpos (convex_Icc r₀ 1) hg.continuousOn
    · intro r hr
      exact (hdiff r (by simpa only [interior_Icc] using hr)).differentiableWithinAt
    · intro r hr
      have hri : r ∈ Ioo r₀ 1 := by simpa only [interior_Icc] using hr
      have hpos := hgpos r hri
      have hprod : 0 ≤ comparisonLogSlope g r * g r :=
        mul_nonneg (hp r hri).1 hpos.le
      have heq : comparisonLogSlope g r * g r = -r * deriv g r := by
        unfold comparisonLogSlope
        exact div_mul_cancel₀ _ hpos.ne'
      rw [heq] at hprod
      have hrpos : 0 < r := hr₀.trans_lt hri.1
      nlinarith
  · apply monotoneOn_of_deriv_nonneg (convex_Icc r₀ 1)
      (hg.mul continuous_id).continuousOn
    · intro r hr
      exact ((hdiff r (by simpa only [interior_Icc] using hr)).mul
        differentiableAt_id).differentiableWithinAt
    · intro r hr
      have hri : r ∈ Ioo r₀ 1 := by simpa only [interior_Icc] using hr
      change 0 ≤ deriv (fun t => g t * t) r
      rw [(hasDerivAt_radius_strength (hdiff r hri) (hgpos r hri).ne').deriv]
      exact mul_nonneg (sub_nonneg.mpr (hp r hri).2) (hgpos r hri).le

section

variable {r₀ c : ℝ} {k M : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hc : 0 < c) (hk : ContinuousOn k (Icc r₀ 1))
variable (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)

theorem fullMassCoefficient_eq
    (g : ℝ → ℝ) (hg : Continuous g)
    (α : inverseIntegralConstraints r₀ 0 k M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    omittedExtension zero_le_one
      (constrainedCoefficient hr hc hk hkc hm hM g hg α) u =
      g (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩) := by
  exact omittedExtension_on zero_le_one
    (constrainedCoefficient hr hc hk hkc hm hM g hg α) ⟨u, hu⟩

theorem fullMassCoefficient_monotone
    (g : ℝ → ℝ) (hg : Continuous g) (hgmono : MonotoneOn g (Icc r₀ 1))
    (α : inverseIntegralConstraints r₀ 0 k M) :
    MonotoneOn (omittedExtension zero_le_one
      (constrainedCoefficient hr hc hk hkc hm hM g hg α)) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  rw [fullMassCoefficient_eq hr hc hk hkc hm hM g hg α hu,
    fullMassCoefficient_eq hr hc hk hkc hm hM g hg α hv]
  exact hgmono
    (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩).property
    (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hv⟩).property
    ((inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv)

theorem fullMassCoefficient_antitone
    (g : ℝ → ℝ) (hg : Continuous g) (hganti : AntitoneOn g (Icc r₀ 1))
    (α : inverseIntegralConstraints r₀ 0 k M) :
    AntitoneOn (omittedExtension zero_le_one
      (constrainedCoefficient hr hc hk hkc hm hM g hg α)) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  rw [fullMassCoefficient_eq hr hc hk hkc hm hM g hg α hu,
    fullMassCoefficient_eq hr hc hk hkc hm hM g hg α hv]
  exact hganti
    (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩).property
    (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hv⟩).property
    ((inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv)

theorem fullMassComparison_minimum
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r₀ 0 k M).Nonempty)
    (hr₀ : 0 ≤ r₀) (b : ℝ → ℝ) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hganti : AntitoneOn g (Icc r₀ 1))
    (hgrmono : MonotoneOn (fun r => g r * r) (Icc r₀ 1))
    (hg0 : ∀ r ∈ Icc r₀ 1, 0 ≤ g r)
    (hgb : ∀ r ∈ Icc r₀ 1, g r ≤ b 0)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    ∃ α : inverseIntegralConstraints r₀ 0 k M,
      ∀ β : inverseIntegralConstraints r₀ 0 k M,
        inverseCompensatedPressure hr zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x α ≤
        inverseCompensatedPressure hr zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x β := by
  refine inverseCompensatedPressure_minimum hr zero_le_one hc hk hkc hm hM g hg
    hMc hne n hn b (fun _ => 0) ?_ ?_ ?_ ?_ x
  · intro α u hu v hv huv
    have hanti := fullMassCoefficient_antitone hr hc hk hkc hm hM g hg hganti α
    exact sub_le_sub (hb hu hv huv) (hanti hu hv huv)
  · intro α
    simpa only [zero_add] using fullMassCoefficient_monotone hr hc hk hkc hm hM
      (fun r => g r * r) (hg.mul continuous_id) hgrmono α
  · intro α
    rw [fullMassCoefficient_eq hr hc hk hkc hm hM g hg α (by norm_num)]
    exact sub_nonneg.mpr (hgb _
      (constrainedQuantile hr hc hk hkc hm hM α ⟨0, by norm_num⟩).property)
  · intro α
    simp only [zero_add]
    rw [fullMassCoefficient_eq hr hc hk hkc hm hM
      (fun r => g r * r) (hg.mul continuous_id) α (by norm_num)]
    exact mul_nonneg (hg0 _
      (constrainedQuantile hr hc hk hkc hm hM α ⟨0, by norm_num⟩).property)
      (hr₀.trans (constrainedQuantile hr hc hk hkc hm hM α ⟨0, by norm_num⟩).property.1)
end

theorem comparisonFloorCap_fullMass_minimum
    {N δ U L E d : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hLU : L ≤ U) (hE : 0 < E) (hd : 0 ≤ d) (hq : 2 ≤ N ^ δ)
    (b : ℝ → ℝ) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hganti : AntitoneOn g (Icc (0 : ℝ) 1))
    (hgrmono : MonotoneOn (fun r => g r * r) (Icc (0 : ℝ) 1))
    (hg0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ g r)
    (hgb : ∀ r ∈ Icc (0 : ℝ) 1, g r ≤ b 0)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hr : (0 : ℝ) ≤ 1 := zero_le_one
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ := δ) hN hU (r₀ := 0) le_rfl
    let hkc := fun r (hri : r ∈ Icc (0 : ℝ) 1) =>
      comparisonFloor_lower_on (δ := δ) hN hU (r₀ := 0) le_rfl hri
    let hm := comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd
      (show (0 : ℝ) ≤ 1 by norm_num)
    ∃ α : inverseIntegralConstraints 0 0 k M,
      ∀ β : inverseIntegralConstraints 0 0 k M,
        inverseCompensatedPressure hr zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x α ≤
        inverseCompensatedPressure hr zero_le_one hc hk hkc hm hM g hg
          n b (fun _ => 0) x β := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hk : ContinuousOn k (Icc (0 : ℝ) 1) :=
    comparisonFloor_continuousOn (δ := δ) hN hU le_rfl
  have hMc : Continuous M := comparisonCap_continuous N δ U L E d
  have hm : MonotoneOn M (Icc (0 : ℝ) 1) :=
    comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd
  have hM : 0 ≤ M 1 :=
    comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd (by norm_num)
  have hneD : (inverseDifferentialConstraints 0 0 k M).Nonempty :=
    comparisonConstraints_nonempty hN hU hL hLU hE hd hq (by norm_num) (by norm_num)
  rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hMc hm hM] at hneD
  exact fullMassComparison_minimum zero_le_one
    (comparisonFloor_pos hN hU (by norm_num)) hk
    (fun r hri => comparisonFloor_lower_on (δ := δ) hN hU le_rfl hri)
    hm hM hMc hneD le_rfl b hb g hg hganti hgrmono hg0 hgb n hn x

end OAI.SKFluctuations
