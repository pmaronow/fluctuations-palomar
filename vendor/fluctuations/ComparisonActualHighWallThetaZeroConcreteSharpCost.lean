module

public import ComparisonActualHighWallThetaZeroSharpCost
public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualHighWallData
variable {m : ℝ}

theorem eventually_concrete_theta_zero_original_wall_sharp_of_density
    (hm : 0 < m) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallData n (m/10000),
      a.E=wallHighError m n →
      (∀lam∈Ioo ((n:ℝ)^(-10:ℝ)) (a.d^2),∀alpha : a.Profile,
        omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
        omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam →
        a.thetaZeroOriginalSweepDensity lam alpha ≤ (n:ℝ)^(10*(m/10000))*a.E) →
      wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 0 ≤
        realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
          a.thetaZeroHighOnlyData.h 0+(n:ℝ)^(20*(m/10000))*a.E := by
  filter_upwards [eventually_theta_zero_sharp_original_wall_of_original_density
    (delta:=m/10000) hm (by positivity),eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro a hEa hD
  have hE : (n:ℝ)^(-(5:ℝ)/6+2*m) ≤ a.E := by
    rw [hEa,wallHighError_eq m (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
  exact hn a hE hD

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
