module

public import SKConstants.Completion.LBase.InverseProfile

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

lemma continuation_half_drop (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) (hwidth : T - S ≤ 1 / 4) :
    actualParisiContinuationR W β S / 2 ≤ actualParisiContinuationR W β T := by
  have H := actualParisiContinuationR_drop_le W β hβ S T hS hST
  have hr := (actualParisiContinuationR_pos W β S).le
  have hprod := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 2 * actualParisiContinuationR W β S by positivity)
  nlinarith

theorem continuation_unit_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    1 / (16 * β^2) ≤ actualParisiContinuationR W β v := by
  have h1 := continuation_half_drop W β hβ 0 (v / 4) le_rfl (by positivity) (by linarith)
  have h2 := continuation_half_drop W β hβ (v / 4) (v / 2) (by positivity) (by linarith) (by linarith)
  have h3 := continuation_half_drop W β hβ (v / 2) (3 * v / 4) (by positivity) (by linarith) (by linarith)
  have h4 := continuation_half_drop W β hβ (3 * v / 4) v (by positivity) (by linarith) (by linarith)
  rw [actualParisiContinuationR_zero W β hβ] at h1
  calc
    _ = (1 / β^2) / 16 := by ring
    _ ≤ _ := by linarith

def curvatureLowerConstant (β : ℝ) : ℝ :=
  min (1 / (16 * β^2))
    ((1 / 2 : ℝ) * scalarCompactTailConstant (actualParisiSeedCompactRadius β) / Real.sqrt (2 * Real.pi))

lemma curvatureLowerConstant_pos (β : ℝ) (hβ : 1 < β) : 0 < curvatureLowerConstant β := by
  unfold curvatureLowerConstant
  apply lt_min
  · positivity
  · exact div_pos (mul_pos (by norm_num) (scalarCompactTailConstant_pos _)) (by positivity)

theorem continuation_temperature_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : 0 ≤ v) :
    curvatureLowerConstant β * (Real.exp (-v / 2) / Real.sqrt (1 + v)) ≤
      actualParisiContinuationR W β v := by
  have hc := curvatureLowerConstant_pos β hβ
  have henv : 0 ≤ Real.exp (-v / 2) / Real.sqrt (1 + v) := by positivity
  by_cases hv1 : v ≤ 1
  · have he : Real.exp (-v / 2) / Real.sqrt (1 + v) ≤ 1 :=
      (div_le_self (Real.exp_pos _).le (Real.one_le_sqrt.mpr (by linarith))).trans
        (Real.exp_le_one_iff.mpr (by linarith))
    exact ((mul_le_of_le_one_right hc.le he).trans (min_le_left _ _)).trans
      (continuation_unit_lower W β hβ v hv hv1)
  · have hvge : 1 ≤ v := le_of_not_ge hv1
    have hvpos : 0 < v := by linarith
    let R := actualParisiSeedCompactRadius β
    let L := (1 / 2 : ℝ) * scalarCompactTailConstant R / Real.sqrt (2 * Real.pi)
    have hL : curvatureLowerConstant β ≤ L := min_le_right _ _
    have htail : L * (Real.exp (-v / 2) / Real.sqrt (1 + v)) ≤
        (1 / 2 : ℝ) * scalarCompactTailConstant R * scalarTailScale v.toNNReal := by
      calc
        _ = ((1 / 2 : ℝ) * scalarCompactTailConstant R * Real.exp (-v / 2)) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (1 + v)) := by dsimp [L]; ring
        _ ≤ ((1 / 2 : ℝ) * scalarCompactTailConstant R * Real.exp (-v / 2)) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt v) := by
          apply div_le_div_of_nonneg_left
          · exact mul_nonneg (mul_nonneg (by norm_num) (scalarCompactTailConstant_pos R).le) (Real.exp_pos _).le
          · positivity
          · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
        _ = _ := by
          unfold scalarTailScale
          norm_num only [Nat.cast_ofNat]
          rw [Real.coe_toNNReal v hv, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
          ring
    have hmass := actualParisiEndpointSeedLaw_compact_mass W β hβ
    calc
      _ ≤ L * (Real.exp (-v / 2) / Real.sqrt (1 + v)) := mul_le_mul_of_nonneg_right hL henv
      _ ≤ (1 / 2 : ℝ) * scalarCompactTailConstant R * scalarTailScale v.toNNReal := htail
      _ ≤ (actualParisiEndpointSeedLaw W β).real (Icc (-R) R) *
          scalarCompactTailConstant R * scalarTailScale v.toNNReal := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmass (scalarCompactTailConstant_pos R).le)
        unfold scalarTailScale
        positivity
      _ ≤ _ := scalarContinuationR_ge_compact_tail _ R (actualParisiSeedCompactRadius_nonneg β) v hvge

theorem actual_square_profile_temperature_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    curvatureLowerConstant β * (Real.exp (-t / 2) / Real.sqrt (1 + t)) ≤
      actualParisiFullSusceptibilitySquareExpected W β t := by
  rw [LQ.actual_square_profile_eq W β hβ t ht]
  by_cases hpre : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · rw [actualParisiContinuationR_nonpos_eq_zero W β _ (sub_nonpos.mpr hpre), actualParisiContinuationR_zero W β hβ]
    have he : Real.exp (-t / 2) / Real.sqrt (1 + t) ≤ 1 :=
      (div_le_self (Real.exp_pos _).le (Real.one_le_sqrt.mpr (by linarith))).trans
        (Real.exp_le_one_iff.mpr (by linarith))
    have hsmall : 1 / (16 * β^2) ≤ (1 : ℝ) / β^2 := by
      have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
      exact one_div_le_one_div_of_le hb (by nlinarith)
    exact ((mul_le_of_le_one_right (curvatureLowerConstant_pos β hβ).le he).trans
      (min_le_left _ _)).trans hsmall
  · have hv : 0 ≤ t - (parisiEquilibriumPhysicalEndpoint β : ℝ) := by linarith
    have henv : Real.exp (-t / 2) / Real.sqrt (1 + t) ≤
        Real.exp (-(t - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2) /
          Real.sqrt (1 + (t - (parisiEquilibriumPhysicalEndpoint β : ℝ))) := by
      have hE := (parisiEquilibriumPhysicalEndpoint β).coe_nonneg
      gcongr <;> linarith
    exact (mul_le_mul_of_nonneg_left henv (curvatureLowerConstant_pos β hβ).le).trans
      (continuation_temperature_lower W β hβ _ hv)

theorem actual_row_proxy_temperature_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    (actualParisiPosteriorRowMGFProxy W β H : ℝ) ≤
      (1 / curvatureLowerConstant β) * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ)) := by
  have hc := curvatureLowerConstant_pos β hβ
  have hr := actual_square_profile_pos W β hβ H H.coe_nonneg
  have he : (1 / curvatureLowerConstant β * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ))) *
      (curvatureLowerConstant β * (Real.exp (-(H : ℝ) / 2) / Real.sqrt (1 + (H : ℝ)))) = 1 := by
    have hs : Real.sqrt (1 + (H : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  have HB := mul_le_mul_of_nonneg_left (actual_square_profile_temperature_lower W β hβ H H.coe_nonneg)
    (show 0 ≤ 1 / curvatureLowerConstant β * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ)) by positivity)
  rw [he] at HB
  rw [actual_row_proxy_eq_inverse W β hβ H]
  exact (div_le_iff₀ hr).mpr HB

end SKConstants.Completion.LBase
