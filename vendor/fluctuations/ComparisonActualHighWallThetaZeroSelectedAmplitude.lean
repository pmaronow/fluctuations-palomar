module

public import ComparisonActualHighWallThetaZeroPositiveAmplitude
public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

abbrev sweepRadius := omittedSweepQuantile M.data.hr
  ⟨M.data.hs.1.le,M.data.hs1⟩ M.data.hc M.data.hk M.data.hkc
  M.data.hm M.data.hM M.alpha
abbrev sweepCoefficient := omittedStrengthCoefficient M.data.d M.data.s
  M.sweepRadius M.lam
abbrev sweepBf : ℝ→ℝ≥0 :=
  fun u=>(M.data.thetaZeroHighOnlyData.b u-M.sweepCoefficient u).toNNReal
abbrev sweepHf : ℝ→ℝ≥0 :=
  fun u=>(M.data.thetaZeroHighOnlyData.h u+
    M.sweepCoefficient u*M.sweepRadius u).toNNReal

theorem sweep_bf_monotone : MonotoneOn M.sweepBf (Icc (0:ℝ) 1) := by
  have H:=(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).clockAdmissible M.alpha
  exact toNNReal_monotoneOn H.1

theorem sweep_hf_monotone : MonotoneOn M.sweepHf (Icc (0:ℝ) 1) := by
  have H:=(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).clockAdmissible M.alpha
  exact toNNReal_monotoneOn H.2.1

end ActualThetaZeroOverlapMinimum

theorem eventually_actual_theta_zero_selected_overlap_moment_normalized
    (ell:ℕ) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃K:ℝ,0 < K ∧ ∀ᶠn:ℕ in atTop,
      ∀M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
        pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf)
          (fun sigma tau=>|orderedOverlap (n+1) sigma tau|^(2*(ell+1))) u ≤
          K*(M.xs+u)^(2*(ell+1)) := by
  obtain ⟨K,hK,hamp⟩:=eventually_actual_theta_zero_positive_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp] with n hn
  intro M u hu
  have H:=hn M.data M.lam M.hlam M.hld M.alpha M.xs M.z M.minimum
    M.hxs M.hscale M.hsxs M.hz M.hzxs M.hdD M.hupper M.hlower
    M.htest M.regular M.field_clock_budget u hu
  exact H

theorem eventually_actual_theta_zero_selected_B_normalized
    (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃K:ℝ,0 < K ∧ ∀ᶠn:ℕ in atTop,
      ∀M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
        orderedPathB (n+1) M.sweepBf M.sweepHf u ≤ K*(M.xs+u)^2 := by
  obtain ⟨K,hK,hamp⟩:=eventually_actual_theta_zero_selected_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp] with n hn
  intro M u hu
  have H:=hn M u hu
  have hpair:=orderedPathPair_eq_completed (n+1) M.data.hn M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone
    (fun sigma tau=>(orderedOverlap (n+1) sigma tau)^2) hu
  have habs:(fun sigma tau:Spin (n+1)=>
      |orderedOverlap (n+1) sigma tau|^(2*(0+1)))=
      fun sigma tau=>(orderedOverlap (n+1) sigma tau)^2:=by
    funext sigma tau
    norm_num
  rw [habs,←hpair] at H
  simpa only [orderedPathB,Nat.zero_add,Nat.mul_one] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
