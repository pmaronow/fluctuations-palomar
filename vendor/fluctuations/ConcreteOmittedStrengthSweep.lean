module

public import OmittedStrengthMinimum

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem concrete_omittedStrengthSweep_cost_analysis
    {N δ U L E d A r0 u0 : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hA : 0<A)
    (hr0 : r0∈Icc (0:ℝ) (1/2)) (hu0 : u0∈Icc (0:ℝ) (1/2))
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hAcut : A≤b u0) (hcross : ∀u∈Ico (0:ℝ) u0,b u+A≤b u0)
    (n : ℕ) (hn : 0<n) :
    let hr : r0≤1 := hr0.2.trans (by norm_num)
    let hu : u0∈Icc (0:ℝ) 1 := ⟨hu0.1,hu0.2.trans (by norm_num)⟩
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr0.1
    let hkc := fun r (hr : r∈Icc r0 1)=>comparisonFloor_lower_on (δ:=δ) hN hU hr0.1 hr
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
    let v := omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d
    LipschitzOnWith 1 v (Icc (0:ℝ) A) ∧
      MonotoneOn v (Icc (0:ℝ) A) ∧ v 0=0 ∧ (∀lam∈Icc (0:ℝ) A,0≤v lam) ∧
      ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) A),
        ∃α:inverseIntegralConstraints r0 u0 k M,
          omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α=
            omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam ∧
          let R := omittedSweepQuantile hr hu hc hk hkc hm hM α
          let e := omittedStrengthCoefficient d u0 R lam
          let bf := fun u=>(b u-e u).toNNReal
          let hf := fun u=>(h u+e u*R u).toNNReal
          lam*deriv v lam≤(1/4:ℝ)*(∫u in (0:ℝ)..1,e u*
            ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
              (orderedPathS n bf hf u-R u)^2)) := by
  dsimp only
  have hr : r0≤1 := hr0.2.trans (by norm_num)
  have hu : u0∈Icc (0:ℝ) 1 := ⟨hu0.1,hu0.2.trans (by norm_num)⟩
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hk : ContinuousOn k (Icc r0 1) := comparisonFloor_continuousOn (δ:=δ) hN hU hr0.1
  have hMc : Continuous M := comparisonCap_continuous N δ U L E d
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  have hM : 0≤M 1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hkc : ∀r∈Icc r0 1,k 1≤k r := fun r hr=>comparisonFloor_lower_on (δ:=δ) hN hU hr0.1 hr
  have hne : (inverseDifferentialConstraints r0 u0 k M).Nonempty :=
    comparisonConstraints_nonempty hN hU hL hLU hE hd.le hq hr0 hu0
  rw [inverseDifferentialConstraints_eq r0 u0 hr k M hk hMc hm hM] at hne
  exact ⟨omittedComparisonSweepCost_lipschitz hr0.1 hr hu hc hk hkc hm hM n hn b h hd.ne' hAcut hcross hb hb0 hh hh0 hMc hne,
    omittedComparisonSweepCost_monotone hr0.1 hr hu hc hk hkc hm hM n hn b h hd.ne' hAcut hcross hb hb0 hh hh0 hMc hne,
    omittedComparisonSweepCost_zero hr0.1 hr hu hc hk hkc hm hM n hn b h hd.ne' hb hb0 hh hh0 hMc hne,
    fun lam hlam=>omittedComparisonSweepCost_nonneg hr0.1 hr hu hc hk hkc hm hM n hn b h hd.ne' hAcut hcross hb hb0 hh hh0 hMc hne hlam,
    omittedComparisonSweepCost_ae_log_derivative_le hr0.1 hr hu hc hk hkc hm hM n hn b h hd.ne' hA hAcut hcross hb hb0 hh hh0 hMc hne⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
