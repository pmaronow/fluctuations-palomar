module

public import SKConstants.SKModel
public import SKConstants.OptimizedRate

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

@[expose] def flowGood {n : ℕ} (beta epsilon B : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {W | ∀ S : Finset (Spin n), epsilon ≤ cutMass (gibbsProbability beta W) S →
    cutMass (gibbsProbability beta W) S ≤ 1 - epsilon →
      B < cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ}

theorem continuous_continuousHeatBathJumpRate {n : ℕ} (beta : ℝ) (x y : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => continuousHeatBathJumpRate beta W x y) := by
  unfold continuousHeatBathJumpRate
  split_ifs
  · exact continuous_const
  · exact (continuous_heatBathKernel_entry beta x y).const_mul (n : ℝ)

theorem continuous_continuousHeatBathEdgeFlow {n : ℕ} (beta : ℝ) (x y : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => continuousHeatBathEdgeFlow beta W x y) :=
  (continuous_gibbsProbability beta x).mul (continuous_continuousHeatBathJumpRate beta x y)

theorem continuous_cutMass_gibbsProbability {n : ℕ} (beta : ℝ) (S : Finset (Spin n)) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => cutMass (gibbsProbability beta W) S) :=
  continuous_finsetSum S (fun x _ => continuous_gibbsProbability beta x)

theorem continuous_cutFlow_continuousHeatBath {n : ℕ} (beta : ℝ)
    (S U : Finset (Spin n)) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ =>
      cutFlow (continuousHeatBathEdgeFlow beta W) S U) :=
  continuous_finsetSum S (fun x _ => continuous_finsetSum U
    (fun y _ => continuous_continuousHeatBathEdgeFlow beta x y))

theorem measurableSet_flowGood {n : ℕ} (beta epsilon B : ℝ) :
    MeasurableSet (flowGood (n := n) beta epsilon B) := by
  apply Measurable.setOf
  apply Measurable.forall
  intro S
  exact (measurableSet_setOfPred.mp (measurableSet_le measurable_const
    (continuous_cutMass_gibbsProbability beta S).measurable)).imp
    ((measurableSet_setOfPred.mp (measurableSet_le
      (continuous_cutMass_gibbsProbability beta S).measurable measurable_const)).imp
      (measurableSet_setOfPred.mp (measurableSet_lt measurable_const
        (continuous_cutFlow_continuousHeatBath beta S Sᶜ).measurable)))

theorem heatBath_card_bound_eq_numerical (c q d : ℝ) (n : ℕ) :
    (n : ℝ) * Real.sqrt (2 * Real.log 2) /
      (Real.exp (-((n : ℝ) ^ (1 - q))) *
        Real.sqrt (Real.exp ((n : ℝ) ^ (1 - c)))) + 2 * (n : ℝ) ^ (-d) =
      numericalFiniteChainBound c q d (Real.sqrt (2 * Real.log 2)) n := by
  rw [← Real.exp_half, ← Real.exp_add]
  unfold numericalFiniteChainBound
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  have hexp : -(-((n : ℝ) ^ (1 - q)) + (n : ℝ) ^ (1 - c) / 2) =
      (n : ℝ) ^ (1 - q) - (n : ℝ) ^ (1 - c) / 2 := by ring
  rw [hexp]
  ring

theorem continuousHeatBathAverageMixing_le_numerical_on_flowGood {n : ℕ}
    (hn : 0 < n) (beta c q d : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hepsilon : (n : ℝ) ^ (-d) < 1 / 3)
    (hW : W ∈ flowGood beta ((n : ℝ) ^ (-d))
      (Real.exp (-((n : ℝ) ^ (1 - q))))) :
    continuousHeatBathAverageMixing beta W (Real.exp ((n : ℝ) ^ (1 - c))) ≤
      numericalFiniteChainBound c q d (Real.sqrt (2 * Real.log 2)) n := by
  have h := continuousHeatBathAverageMixing_of_balanced_flow_card hn beta W
    ((n : ℝ) ^ (-d)) (Real.exp (-((n : ℝ) ^ (1 - q))))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hepsilon (Real.exp_pos _) hW
    (Real.exp ((n : ℝ) ^ (1 - c))) (Real.exp_pos _)
  rwa [heatBath_card_bound_eq_numerical] at h

theorem numericalFiniteChainBound_sqrt_nonneg (c q d : ℝ) (n : ℕ) :
    0 ≤ numericalFiniteChainBound c q d (Real.sqrt (2 * Real.log 2)) n := by
  unfold numericalFiniteChainBound
  positivity

theorem sk_joint_bad_start_bound_from_flow {n : ℕ} (hn : 0 < n)
    (beta c q d delta : ℝ) (hdelta : 0 < delta)
    (hepsilon : (n : ℝ) ^ (-d) < 1 / 3) :
    (skJointLaw n beta).real
      (continuousHeatBathBadStart beta (Real.exp ((n : ℝ) ^ (1 - c))) delta) ≤
      (skDisorderLaw n).real (flowGood beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))))ᶜ +
      numericalFiniteChainBound c q d (Real.sqrt (2 * Real.log 2)) n / delta := by
  exact continuousHeatBath_typical_start_bound hn beta (skDisorderLaw n)
    (Real.exp ((n : ℝ) ^ (1 - c))) (Real.exp_pos _).le
    (flowGood beta ((n : ℝ) ^ (-d)) (Real.exp (-((n : ℝ) ^ (1 - q)))))
    (measurableSet_flowGood beta _ _) _ delta
    (numericalFiniteChainBound_sqrt_nonneg c q d n) hdelta
    (fun W hW => continuousHeatBathAverageMixing_le_numerical_on_flowGood hn beta c q d W hepsilon hW)

theorem sk_joint_bad_start_decay_of_flow_decay (beta c q d delta : ℝ)
    (hcq : c < q) (hq : q < 1) (hd : 0 < d) (hdelta : 0 < delta)
    (hflow : Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (flowGood beta ((n : ℝ) ^ (-d)) (Real.exp (-((n : ℝ) ^ (1 - q)))))ᶜ)
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | delta < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (nhds 0) := by
  have hepslim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-d)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
  have hepssmall := hepslim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num))
  have hnum : Tendsto (numericalFiniteChainBound c q d (Real.sqrt (2 * Real.log 2)))
      atTop (nhds 0) := flow_bound_decay_nat c q d _ hcq hq hd
  have hlim := hflow.add (hnum.div_const delta)
  simp only [zero_div, zero_add] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ), hepssmall] with n hn heps
  exact sk_joint_bad_start_bound_from_flow hn beta c q d delta hdelta heps

theorem sk_optimized_joint_bad_start_decay_of_flow_decay (beta c delta : ℝ)
    (hc : 0 < c) (hquarter : c < 1 / 4) (hdelta : 0 < delta)
    (hflow : Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (flowGood beta ((n : ℝ) ^ (-(optimizedParameters c).d))
        (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))))ᶜ)
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | delta < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (nhds 0) := by
  obtain ⟨hcq, hq, hd⟩ := optimizedParameters_rate_margins c hc hquarter
  exact sk_joint_bad_start_decay_of_flow_decay beta c (optimizedParameters c).q
    (optimizedParameters c).d delta hcq hq hd hdelta hflow

@[expose] def OptimizedSKFlowProbabilityStatement : Prop :=
  ∀ (beta c : ℝ), 1 < beta → 0 < c → c < 1 / 4 →
    Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (flowGood beta ((n : ℝ) ^ (-(optimizedParameters c).d))
        (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))))ᶜ)
      atTop (nhds 0)

theorem optimizedSKTypicalStartStatement_of_flow_probability
    (hflow : OptimizedSKFlowProbabilityStatement) : OptimizedSKTypicalStartStatement := by
  intro beta c hbeta hc hquarter
  exact sk_optimized_joint_bad_start_decay_of_flow_decay beta c (1 / 4)
    hc hquarter (by norm_num) (hflow beta c hbeta hc hquarter)

end SKConstants
