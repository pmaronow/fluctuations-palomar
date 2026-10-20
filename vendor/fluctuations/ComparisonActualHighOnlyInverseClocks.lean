module

public import ComparisonActualHighOnlyOverlapMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)

theorem coefficient_eq_original_high_only (alpha : a.Profile) (lam : ℝ) :
    a.coefficient alpha lam=omittedExtension a.hs1
      (constrainedCoefficient zero_le_one a.hc a.hk a.hkc a.hm a.hM
        (laplaceComparisonStrength a.d lam)
        (laplaceComparisonStrength_contDiff a.d lam).continuous alpha) :=
  omittedStrengthCoefficient_eq_original zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM a.d lam alpha

theorem fieldCoefficient_eq_original_high_only (alpha : a.Profile) (lam : ℝ) :
    omittedExtension a.hs1 (constrainedCoefficient zero_le_one a.hc a.hk a.hkc a.hm a.hM
      (fun r=>laplaceComparisonStrength a.d lam r*r)
      ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) alpha)=
        fun u=>a.coefficient alpha lam u*a.R alpha u := by
  ext u
  by_cases hu : a.s ≤ u <;>
    simp [coefficient,R,omittedStrengthCoefficient,omittedSweepQuantile,
      omittedExtension,IccExtend,constrainedCoefficient,constrainedQuantileMap,hu,Function.comp_def]

theorem original_clocks_admissible_high_only (alpha : a.Profile) {lam : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    let e:=omittedExtension a.hs1 (constrainedCoefficient zero_le_one a.hc a.hk a.hkc a.hm a.hM
      (laplaceComparisonStrength a.d lam) (laplaceComparisonStrength_contDiff a.d lam).continuous alpha)
    let q:=omittedExtension a.hs1 (constrainedCoefficient zero_le_one a.hc a.hk a.hkc a.hm a.hM
      (fun r=>laplaceComparisonStrength a.d lam r*r)
      ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) alpha)
    MonotoneOn (fun u=>a.b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>a.h u+q u) (Icc (0:ℝ) 1) ∧
      0 ≤ a.b 0-e 0 ∧ 0 ≤ a.h 0+q 0 :=
  omittedComparisonSweep_clocks_admissible le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM a.b a.h a.hd.ne' hlam.1 (hlam.2.trans a.hcut)
    (fun u hu=>by linarith [a.hcross u hu,hlam.2]) a.hb a.hb0 a.hh a.hh0 alpha

theorem original_clock_eq_high_only (alpha : a.Profile) (lam : ℝ) :
    (fun u=>(a.b u-omittedExtension a.hs1 (constrainedCoefficient zero_le_one a.hc a.hk
      a.hkc a.hm a.hM (laplaceComparisonStrength a.d lam)
      (laplaceComparisonStrength_contDiff a.d lam).continuous alpha) u).toNNReal)=a.bf alpha lam ∧
    (fun u=>(a.h u+omittedExtension a.hs1 (constrainedCoefficient zero_le_one a.hc a.hk
      a.hkc a.hm a.hM (fun r=>laplaceComparisonStrength a.d lam r*r)
      ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) alpha) u).toNNReal)=a.hf alpha lam := by
  rw [←a.coefficient_eq_original_high_only alpha lam,a.fieldCoefficient_eq_original_high_only alpha lam]
  exact ⟨rfl,rfl⟩

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
