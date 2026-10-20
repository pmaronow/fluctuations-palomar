module

public import VariableEndpointStrengthMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem concrete_variableEndpointStrengthSweep_cost_analysis
    {N δ U L E d A : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hA : 0<A)
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hAb : A≤b 0)
    (n : ℕ) (hn : 0<n) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU (r₀:=0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1)=>
      comparisonFloor_lower_on (δ:=δ) hN hU (r₀:=0) le_rfl hr
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
    let v := variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d
    LipschitzOnWith 1 v (Icc (0:ℝ) A) ∧
      MonotoneOn v (Icc (0:ℝ) A) ∧ v 0=0 ∧
      (∀ lam∈Icc (0:ℝ) A,0≤v lam) ∧
      ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) A),
        ∃ α : inverseIntegralConstraints 0 0 k M,
          variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
            variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam ∧
          let R := comparisonSweepQuantile hc hk hkc hm hM α
          let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
          let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
          lam*deriv v lam≤(1/4:ℝ)*(∫ u in (0:ℝ)..1,
            laplaceComparisonStrength d lam (R u)*
              ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
                (orderedPathS n bf hf u-R u)^2)) := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hk : ContinuousOn k (Icc (0:ℝ) 1) :=
    comparisonFloor_continuousOn (δ:=δ) hN hU le_rfl
  have hMc : Continuous M := comparisonCap_continuous N δ U L E d
  have hm : MonotoneOn M (Icc (0:ℝ) 1) :=
    comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  have hM : 0≤M 1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hkc : ∀ r∈Icc (0:ℝ) 1,k 1≤k r :=
    fun r hr=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
  have hne : (inverseDifferentialConstraints 0 0 k M).Nonempty :=
    comparisonConstraints_nonempty hN hU hL hLU hE hd.le hq (by norm_num) (by norm_num)
  rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hMc hm hM] at hne
  exact ⟨variableEndpointComparisonSweepCost_lipschitz hc hk hkc hm hM n hn b h hd.ne' hAb hb hh hh0 hMc hne,
    variableEndpointComparisonSweepCost_monotone hc hk hkc hm hM n hn b h hd.ne' hAb hb hh hh0 hMc hne,
    variableEndpointComparisonSweepCost_zero hc hk hkc hm hM n hn b h hd.ne' (hA.le.trans hAb) hb hh hh0 hMc hne,
    fun lam hlam=>variableEndpointComparisonSweepCost_nonneg hc hk hkc hm hM n hn b h hd.ne' hAb hb hh hh0 hMc hne hlam,
    variableEndpointComparisonSweepCost_ae_log_derivative_le hc hk hkc hm hM n hn b h hd.ne' hA hAb hb hh hh0 hMc hne⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
