module

public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem theta_zero_changed_low_matrix (lam:ℝ) (hlam:0<lam)
    (hld:lam≤a.d^2) (alpha:a.Profile) {u:ℝ} (hu:u<a.s) :
    (a.thetaZeroShiftedParentData lam hlam hld).b u-
      (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha u=a.T-a.epsilon := by
  change wallBareMatrix a.T a.epsilon 0 a.s u-
    omittedStrengthCoefficient a.d a.s
      (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM alpha) lam u=a.T-a.epsilon
  simp [wallBareMatrix,omittedStrengthCoefficient,hu,not_le.mpr hu]

theorem theta_zero_changed_high_matrix (lam:ℝ) (hlam:0<lam)
    (hld:lam≤a.d^2) (alpha:a.Profile) {u:ℝ} (hu:a.s≤u) :
    a.T-lam ≤ (a.thetaZeroShiftedParentData lam hlam hld).b u-
      (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha u := by
  change a.T-lam ≤ wallBareMatrix a.T a.epsilon 0 a.s u-
    omittedStrengthCoefficient a.d a.s
      (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM alpha) lam u
  simp only [wallBareMatrix,not_lt.mpr hu,ite_false,
    omittedStrengthCoefficient,ite_eq_left hu]
  have H:=laplaceComparisonStrength_le a.d hlam.le
    (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha u)
  linarith only [H]

theorem theta_zero_fixed_margin_alternative (lam:ℝ) (hlam:0<lam)
    (hld:lam≤a.d^2) (alpha:a.Profile) (hd:a.d^2≤a.T/8) :
    (∀u∈Icc (0:ℝ) 1,5*a.T/8 ≤
      (a.thetaZeroShiftedParentData lam hlam hld).b u-
        (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha u) ∨
    ((∀u∈Icc a.s 1,7*a.T/8 ≤
      (a.thetaZeroShiftedParentData lam hlam hld).b u-
        (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha u) ∧
      ∀u∈Ico (0:ℝ) a.s,
        (a.thetaZeroShiftedParentData lam hlam hld).b u-
          (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha u+a.T/8 ≤
        (a.thetaZeroShiftedParentData lam hlam hld).b a.s-
          (a.thetaZeroShiftedParentData lam hlam hld).coefficient alpha a.s) := by
  have hT:0<a.T:=a.hepsilon.1.trans a.hepsilon.2
  rcases le_total a.epsilon (a.T/4) with heps|heps
  · left
    intro u hu
    by_cases hs:u<a.s
    · rw [a.theta_zero_changed_low_matrix lam hlam hld alpha hs]
      linarith only [heps,hT]
    · have H:=a.theta_zero_changed_high_matrix lam hlam hld alpha (le_of_not_gt hs)
      linarith only [H,hld,hd,hT]
  · right
    constructor
    · intro u hu
      have H:=a.theta_zero_changed_high_matrix lam hlam hld alpha hu.1
      linarith only [H,hld,hd]
    · intro u hu
      rw [a.theta_zero_changed_low_matrix lam hlam hld alpha hu.2]
      have H:=a.theta_zero_changed_high_matrix lam hlam hld alpha (le_refl a.s)
      linarith only [H,heps,hld,hd]

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
