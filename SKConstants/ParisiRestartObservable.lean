module

public import SKConstants.ParisiFullMartingale
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem boundedDrift_restart_observable_test
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F) (C : ℝ)
    (hFC : ∀ p, |F p| ≤ C) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (M : ℝ) (hφM : ∀ x, |φ x| ≤ M) :
    (∫ w,F (boundedDriftPastPath W b a w)*φ (b.solution W.driver (a+v) w) ∂W.law)=
      ∫ past,F past*(∫ w,φ (past ⟨a,a.coe_nonneg,le_rfl⟩+
        (SKConstants.BoundedLipschitzDrift.translated b a (past ⟨a,a.coe_nonneg,le_rfl⟩)).solution W.driver v w) ∂W.law)
        ∂W.law.map (boundedDriftPastPath W b a) := by
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ :=
    fun p => F p.1*φ (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)
  have hH : Measurable H := (hF.comp measurable_fst).mul
    (hφ.comp ((ContinuousMap.measurable_eval _).comp measurable_snd))
  have hB (p : ScalarContinuousPath a × ScalarContinuousPath v) : |H p| ≤ C*M := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hFC p.1) (hφM _) (abs_nonneg _)
      ((abs_nonneg _).trans (hFC p.1)))
  have HE := boundedDrift_restart_integral W b a v H hH (C*M) hB
  have hE : (∫ w,F (boundedDriftPastPath W b a w)*φ (b.solution W.driver (a+v) w) ∂W.law)=
    ∫ w,H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w) ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftRestartPath_version W b a v] with w hw
    change _ = F (boundedDriftPastPath W b a w)*φ (boundedDriftRestartPath W b a v w ⟨v,v.coe_nonneg,le_rfl⟩)
    rw [hw]
    rfl
  rw [hE,HE]
  apply integral_congr_ae
  apply ae_of_all
  intro past
  change (∫ w,F past*φ (boundedDriftRestartCallback b a v (past,brownianFinitePath W v w)
    ⟨v,v.coe_nonneg,le_rfl⟩) ∂W.law)=_
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [boundedDriftRestartCallback_fresh_version W b a v past] with w hw
  rw [hw]
  rfl

lemma boundedDrift_past_observable_integral
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ w,F (boundedDriftPastPath W b a w)*φ (b.solution W.driver a w) ∂W.law)=
      ∫ past,F past*φ (past ⟨a,a.coe_nonneg,le_rfl⟩) ∂W.law.map (boundedDriftPastPath W b a) := by
  let J : ScalarContinuousPath a → ℝ := fun past => F past*φ (past ⟨a,a.coe_nonneg,le_rfl⟩)
  have hJ : Measurable J := hF.mul (hφ.comp (ContinuousMap.measurable_eval _))
  have HE : (∫ w,F (boundedDriftPastPath W b a w)*φ (b.solution W.driver a w) ∂W.law)=
      ∫ w,J (boundedDriftPastPath W b a w) ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftPastPath_version W b a] with w hw
    change _ = F (boundedDriftPastPath W b a w)*φ (boundedDriftPastPath W b a w ⟨a,a.coe_nonneg,le_rfl⟩)
    rw [hw]
    rfl
  exact HE.trans (integral_map (measurable_boundedDriftPastPath W b a).aemeasurable hJ.aestronglyMeasurable).symm

end SKConstants
