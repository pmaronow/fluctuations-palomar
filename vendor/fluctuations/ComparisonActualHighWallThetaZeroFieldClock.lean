module

public import ComparisonActualHighWallThetaZeroDirectSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 7000000

namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem theta_zero_variable_strength_field_clock_budget
    (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) (alpha:a.Profile) :
    (let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
     let e:=omittedStrengthCoefficient a.d a.s R lam
     let hf:=fun u=>(a.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
     (hf 1:ℝ)-(hf 0:ℝ) ≤ a.T) := by
  dsimp only
  let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
  let e:=omittedStrengthCoefficient a.d a.s R lam
  have hR1:R 1∈Icc (0:ℝ) 1:=
    ⟨a.hrbounds.1.le.trans (omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha 1).1,
      (omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM alpha 1).2⟩
  have he1:0 ≤ e 1 ∧ e 1 ≤ lam:=by
    have hS:a.s≤(1:ℝ):=a.hs1
    change 0 ≤ omittedStrengthCoefficient a.d a.s R lam 1 ∧
      omittedStrengthCoefficient a.d a.s R lam 1 ≤ lam
    simp only [omittedStrengthCoefficient,ite_eq_left hS]
    exact ⟨(laplaceComparisonStrength_pos a.d hlam (R 1)).le,
      laplaceComparisonStrength_le a.d hlam.le (R 1)⟩
  have h0:e 0=0:=by
    have H:¬a.s≤(0:ℝ):=not_le.mpr a.hs.1
    simp only [e,omittedStrengthCoefficient,ite_eq_right H]
  have hfield:(a.thetaZeroHighOnlyData.h)=(fun _=>0):=rfl
  have hlow:(a.thetaZeroHighOnlyData.h 0+e 0*R 0).toNNReal=0:=by
    simp only [hfield,h0,zero_mul,add_zero,Real.toNNReal_zero]
  have hhigh:0≤a.thetaZeroHighOnlyData.h 1+e 1*R 1:=by
    rw [hfield]
    simpa only [zero_add] using mul_nonneg he1.1 hR1.1
  have hval:(↑((a.thetaZeroHighOnlyData.h 1+e 1*R 1).toNNReal):ℝ)=e 1*R 1:=by
    rw [Real.coe_toNNReal _ hhigh,hfield]
    simp only [zero_add]
  have heR:e 1*R 1≤e 1:=by
    nlinarith [mul_le_mul_of_nonneg_left hR1.2 he1.1]
  have hT:a.d^2≤a.T:=a.hdepsilon.trans a.hepsilon.2.le
  rw [hlow,hval]
  simp only [NNReal.coe_zero,sub_zero]
  linarith only [heR,he1.2,hld,hT]

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
