module

public import ComparisonActualHighOnlyConditionalFiniteLeafBudget
public import ComparisonActualHighOnlyMassSlabScale

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem original_error_base_prefix_le_raw_high_only (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {R:ℝ} (hR:0 ≤ R) (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R) :
    (∫u in 0..min a.massCoverBase 1,a.comparisonErrorDensity u) ≤ R := by
  by_cases hUs:a.data.U ≤ a.data.s
  · rw [a.original_error_base_prefix_zero_of_U_le_s_high_only hUs]
    exact hR
  · have hsU:a.data.s ≤ a.data.U:=(lt_of_not_ge hUs).le
    rw [massCoverBase,max_eq_left hsU]
    have hsmall:min a.data.U 1∈Icc (0:ℝ) 1:=⟨le_min a.data.hU.le zero_le_one,min_le_right _ _⟩
    have hbig:min (16*a.data.U) 1∈Icc (0:ℝ) 1:=⟨le_min (by have HU:=a.data.hU;positivity) zero_le_one,min_le_right _ _⟩
    have hle:min a.data.U 1 ≤ min (16*a.data.U) 1:=min_le_min (by have HU:=a.data.hU;linarith) le_rfl
    have hi:=a.comparisonErrorDensity_intervalIntegrable.mono_set (by
      rw [uIcc_of_le hbig.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hbig.2)
    have H:=intervalIntegral.integral_mono_interval le_rfl hsmall.1 hle
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact a.comparisonErrorDensity_nonneg ⟨hu.1.le,hu.2.trans hbig.2⟩) hi
    exact H.trans hRaw

theorem Potential.conditional_finite_error_le_leaf_sum_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B R:ℝ} (hB:0 ≤ B) (hR:0 ≤ R)
    (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R)
    (hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ B)
    (hInit:a.data.U ≤ a.data.s → ∀t:F,(P.capFamily F t).left=0 → a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s →
      a.errorMaskIntegral (Ioo (P.capFamily F t).left (P.capFamily F t).right) ≤ B)
    (hOrd:∀j:ConditionalHighOrdinaryDyad a,
      a.errorMaskIntegral (P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val) ≤ B)
    (hBroad:∀p:RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1),
      a.errorMaskIntegral (actualBroadSlice (P.capFamily F) p.val) ≤ B) :
    a.errorMaskIntegral (Ioo (0:ℝ) 1∩((⋃t:F,Ioo (P.capFamily F t).left (P.capFamily F t).right)∪P.contactSet)) ≤
      4*R+(4+2*(Fintype.card (ConditionalHighOrdinaryDyad a):ℝ)+
        (Fintype.card (RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1)):ℝ))*B := by
  let O:=(Fintype.card (ConditionalHighOrdinaryDyad a):ℝ)*B
  have hO:0 ≤ O:=by dsimp only [O];positivity
  have HU:=P.conditional_high_ordinary_union_budget_high_only F hB hOrd
  have HC:=P.conditional_contact_budget_high_only F hB hR hO hRaw hWall HU
  have HQ:=P.conditional_comparable_budget_high_only F hB hR hO hRaw hWall HU
  have HS:=P.conditional_small_budget_high_only F hB hR hRaw hWall hInit
  have Hbase:=a.original_error_base_prefix_le_raw_high_only hR hRaw
  have HB:(∑p:RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1),
      a.errorMaskIntegral (actualBroadSlice (P.capFamily F) p.val)) ≤
      (Fintype.card (RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1)):ℝ)*B:=by
    calc _ ≤ ∑_p:RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1),B:=
           Finset.sum_le_sum (fun p _=>hBroad p)
         _=(Fintype.card (RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1)):ℝ)*B:=by simp
  have H:=local_finite_cap_conditional_error_cover (P.capFamily F) (Ioo (0:ℝ) 1) measurableSet_Ioo
  dsimp only [errorMaskIntegral,O] at HC HQ HS HB ⊢
  nlinarith only [H,HC,HQ,HS,HB,Hbase]

theorem Potential.conditional_finite_error_le_log_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B R:ℝ} (hB:0 ≤ B) (hR:0 ≤ R)
    (hN:1 ≤ a.data.N) (hlog:1 ≤ Real.log a.data.N) (hU1:a.data.U ≤ 1)
    (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R)
    (hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ B)
    (hInit:a.data.U ≤ a.data.s → ∀t:F,(P.capFamily F t).left=0 → a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s →
      a.errorMaskIntegral (Ioo (P.capFamily F t).left (P.capFamily F t).right) ≤ B)
    (hOrd:∀j:ConditionalHighOrdinaryDyad a,
      a.errorMaskIntegral (P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val) ≤ B)
    (hBroad:∀p:RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1),
      a.errorMaskIntegral (actualBroadSlice (P.capFamily F) p.val) ≤ B) :
    a.errorMaskIntegral (Ioo (0:ℝ) 1∩((⋃t:F,Ioo (P.capFamily F t).left (P.capFamily F t).right)∪P.contactSet)) ≤
      4*R+(4+6*(((1+Real.log (1+D^2))/Real.log 2)+2))*Real.log a.data.N*B := by
  have H:=P.conditional_finite_error_le_leaf_sum_high_only F hB hR hRaw hWall hInit hOrd hBroad
  let K:=(Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1
  have HO:(Fintype.card (ConditionalHighOrdinaryDyad a):ℝ) ≤ K:=by
    have H1:=Fintype.card_le_of_injective
      (Subtype.val:ConditionalHighOrdinaryDyad a→comparisonMassDyadicIndices a.data.U) Subtype.val_injective
    have H2:(comparisonMassDyadicIndices a.data.U).card ≤ Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1:=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have HC:(Fintype.card (ConditionalHighOrdinaryDyad a)) ≤ Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1:=
      H1.trans (by simpa only [Fintype.card_coe] using H2)
    dsimp only [K]
    exact_mod_cast HC
  have HB:(Fintype.card (RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1)):ℝ) ≤ 4*K:=by
    have HC:=relevant_broad_slice_card_le_original_log (P.capFamily F) (Ioo (0:ℝ) 1) (P.capFamily_disjoint F)
    dsimp only [K]
    exact_mod_cast HC
  have HK:=a.actual_mass_log_count_le hN hlog hU1
  have Hfactor:4+2*(Fintype.card (ConditionalHighOrdinaryDyad a):ℝ)+
      (Fintype.card (RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1)):ℝ) ≤
      (4+6*(((1+Real.log (1+D^2))/Real.log 2)+2))*Real.log a.data.N:=by
    dsimp only [K] at HO HB
    nlinarith only [HO,HB,HK,hlog]
  exact H.trans (by
    have HM:=mul_le_mul_of_nonneg_right Hfactor hB
    nlinarith only [HM])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
