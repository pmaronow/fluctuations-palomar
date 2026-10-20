module

public import ComparisonActualHighWallMacroscopicHighGapExclusion
public import ComparisonActualHighWallMacroscopicLowGapExclusion

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

def macroFixedMarginChildSweepCost
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0) : ℝ :=
  if M.data.epsilon < M.data.T/4 then M.macroAllMassChildSweepCost hc0
  else M.macroHighOnlyChildSweepCost hc0

theorem macro_fixed_margin_successful_child_literal_bad_witness_excluded
    {beta : ℝ≥0} (hbeta : 0 < beta) (hT : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      0 < m → 0 < delta → 0 < C0 →
      ∀hc0 : 0 < c0,c0^2 < (beta:ℝ)^2/4 → cl ≤ lower → upper ≤ cu →
      ∀N : ℕ→ℕ,Tendsto N atTop atTop →
      ∀M : (k:ℕ)→ActualHighWallOverlapMinimum (N k+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo : ℝ,0 < xlo → (∀k,(M k).xs∈Icc xlo 1) →
      (∀k,(M k).data.T=(beta:ℝ)^2) →
      Tendsto (fun k=>(M k).data.s) atTop (𝓝 0) →
      Tendsto (fun k=>(M k).data.g ((M k).xs)/(M k).xs^2) atTop (𝓝 0) →
      (∀ᶠk in atTop,(M k).macroFixedMarginChildSweepCost hc0 ≤ ((N k+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N k+1) delta c0 (M k).data.d ((M k).data.d^2) ((M k).xs)) →
      ∀ᶠk in atTop,cl*(M k).xs ≤ (M k).alpha.val.val (M k).xs ∧
        (M k).alpha.val.val (M k).xs ≤ cu*(M k).xs := by
  classical
  obtain ⟨lowerL,upperL,hLowerL,hUpperL,HL⟩ :=
    macro_low_gap_successful_child_literal_bad_witness_excluded hbeta hT
  obtain ⟨lowerH,upperH,hLowerH,hUpperH,HH⟩ :=
    macro_high_gap_successful_child_literal_bad_witness_excluded hbeta hT
  refine ⟨min lowerL lowerH,max upperL upperH,lt_min hLowerL hLowerH,
    hUpperL.trans_le (le_max_left _ _),?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T hclmargin hcumargin
    N hN M xlo hxlo hxs hTfix hs hweak hsuccess
  by_contra Hnot
  rw [eventually_atTop] at Hnot
  push Not at Hnot
  choose index hindex hbad using Hnot
  have hindexlim : Tendsto index atTop atTop := tendsto_atTop_mono hindex tendsto_id
  let dim := fun k=>N (index k)
  let P := fun k=>M (index k)
  have hdim : Tendsto dim atTop atTop := hN.comp hindexlim
  by_cases Hlow : ∀ᶠk in atTop,(P k).data.epsilon < (beta:ℝ)^2/4
  · have Hsuc : ∀ᶠk in atTop,(P k).macroAllMassChildSweepCost hc0 ≤ ((dim k+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim k+1) delta c0 (P k).data.d ((P k).data.d^2) ((P k).xs) := by
      filter_upwards [Hlow,hindexlim.eventually hsuccess] with k hk hsuc
      have he : (P k).data.epsilon < (P k).data.T/4 := by
        simpa only [P,hTfix] using hk
      change (P k).macroFixedMarginChildSweepCost hc0 ≤ _ at hsuc
      rw [macroFixedMarginChildSweepCost,ite_eq_left he] at hsuc
      exact hsuc
    have HG := HL m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T
      (hclmargin.trans (min_le_left _ _)) ((le_max_left _ _).trans hcumargin)
      dim hdim P xlo hxlo (fun k=>hxs (index k)) (fun k=>hTfix (index k))
      (hs.comp hindexlim) (hweak.comp hindexlim) (Hlow.mono fun k hk=>hk.le) Hsuc
    obtain ⟨k,hk⟩ := HG.exists
    exact (not_lt_of_ge hk.2) (hbad k hk.1)
  · rw [eventually_atTop] at Hlow
    push Not at Hlow
    choose highIndex hHighIndex hhigh using Hlow
    have hHighLim : Tendsto highIndex atTop atTop := tendsto_atTop_mono hHighIndex tendsto_id
    let theta := index ∘ highIndex
    let dimH := fun k=>N (theta k)
    let Q := fun k=>M (theta k)
    have htheta : Tendsto theta atTop atTop := hindexlim.comp hHighLim
    have hdimH : Tendsto dimH atTop atTop := hN.comp htheta
    have He : ∀ᶠk in atTop,(beta:ℝ)^2/4 ≤ (Q k).data.epsilon :=
      Eventually.of_forall fun k=>by simpa only [Q,theta,Function.comp_apply,P] using hhigh k
    have Hsuc : ∀ᶠk in atTop,(Q k).macroHighOnlyChildSweepCost hc0 ≤ ((dimH k+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dimH k+1) delta c0 (Q k).data.d ((Q k).data.d^2) ((Q k).xs) := by
      filter_upwards [He,htheta.eventually hsuccess] with k hk hsuc
      have he : ¬(Q k).data.epsilon < (Q k).data.T/4 := by
        rw [show (Q k).data.T=(beta:ℝ)^2 from hTfix (theta k)]
        exact not_lt_of_ge hk
      change (Q k).macroFixedMarginChildSweepCost hc0 ≤ _ at hsuc
      rw [macroFixedMarginChildSweepCost,ite_eq_right he] at hsuc
      exact hsuc
    have HG := HH m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T
      (hclmargin.trans (min_le_right _ _)) ((le_max_right _ _).trans hcumargin)
      dimH hdimH Q xlo hxlo (fun k=>hxs (theta k)) (fun k=>hTfix (theta k))
      (hs.comp htheta) (hweak.comp htheta) He Hsuc
    obtain ⟨k,hk⟩ := HG.exists
    have HB := hbad (highIndex k)
    change cl*(Q k).xs ≤ (Q k).alpha.val.val (Q k).xs →
      cu*(Q k).xs < (Q k).alpha.val.val (Q k).xs at HB
    exact (not_lt_of_ge hk.2) (HB hk.1)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
