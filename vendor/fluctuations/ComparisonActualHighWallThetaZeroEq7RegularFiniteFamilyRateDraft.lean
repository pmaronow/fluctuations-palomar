module

public import ComparisonActualHighWallThetaZeroEq7ExactBudgetJoinDraft
public import ComparisonActualHighWallThetaZeroEq7FinitePhysicalCalls
public import ComparisonActualHighWallThetaZeroEq7LowDyadCardinality
public import ComparisonActualHighWallThetaZeroEq7PostDyadCardinalityDraft
public import ComparisonOriginalQEq7BroadMaskFourLogDirectDraft
public import ComparisonActualHighWallThetaZeroEq7LowPostUniformRateDraft
public import ComparisonActualHighWallThetaZeroEq7BroadExactRegularRateDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

namespace OriginalQEq7RegularFamilyRateDraft

def ordinaryConstant (delta cl Az C q : ℝ) : ℝ :=
  comparisonEq7OrdinaryPieceConstant
    (comparisonEq7BinFactorConstant (30+10*delta)) C (1+16*C)
    (max 1 ((Az+1/cl)*(1+16*C))) q

def broadConstant (delta cl Az D C q : ℝ) : ℝ :=
  let beta := 30+10*delta
  let B := 2*C
  let Y := 1+16*B
  comparisonEq7BroadPieceConstant (max 1 ((Az+1/cl)*Y))
    (ActualThetaZeroOverlapMinimum.criticalBroadOriginLossFactor*(1025+25*(1+Real.log (1+D^2))))
    beta (comparisonEq7BroadTemperatureConstant beta) B
    (9*(2+Real.log (1+D^2))) Y q

def familyConstant (delta cl Az D C qLow qPost qBroad : ℝ) : ℝ :=
  6*ordinaryConstant delta cl Az C qLow+
    4*ordinaryConstant delta cl Az C qPost+
    16*broadConstant delta cl Az D C qBroad

end OriginalQEq7RegularFamilyRateDraft

namespace ActualThetaZeroOverlapMinimum

theorem Potential.eq7_inner_regular_finite_family_rate_draft
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (P : Q.Potential) (h : ℝ) (hhi : h ≤ 1)
    (ell : ℕ) (hell : 2 < ell) (qLow qPost qBroad eps C : ℝ)
    (hm : 0 ≤ m) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (horder : (14+3*delta)/((ell:ℝ)-1) ≤ eps)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hlogPow : Real.log Q.data.N ≤ Q.data.N^eps)
    (hdepth : 1/Q.data.N ≤ Q.data.d)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hlamFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam)
    (hC : 2 ≤ C) (hh : h ≤ C*Q.xs)
    (hYBN : 1+32*C ≤ Q.data.N) (hN3 : 72 ≤ Q.data.N^3)
    (hLcap : Q.data.N^(-(1:ℝ)) ≤
      comparisonConstraintLength Q.data.N Q.data.E Q.data.d)
    (hqLow : 1 ≤ qLow) (hqPost : 1 ≤ qPost) (hqBroad : 1 ≤ qBroad)
    (hKcutLow : qLow^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N)
    (hKcutPost : qPost^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N)
    (hLowPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (j : Eq7InnerLowDyad Q h),
      eq7InnerThermalPiece (P.capFamily F) h (.inr (.inl j)) ≤
        Q.eq7InnerLowExactBudget ell qLow
          ((30+10*delta)*Real.log Q.data.N)
          (Q.data.N^(-(30+10*delta))) j)
    (hPostPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (j : Eq7InnerPostDyad Q h),
      eq7InnerThermalPiece (P.capFamily F) h (.inr (.inr j)) ≤
        Q.eq7InnerPostExactBudget ell qPost
          ((30+10*delta)*Real.log Q.data.N)
          (Q.data.N^(-(30+10*delta))) j)
    (hBroadPhysical : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (b : Eq7InnerRelevantBroadSlice (P.capFamily F) h),
      eq7InnerThermalPiece (P.capFamily F) h (.inl b) ≤
        eq7InnerBroadExactBudget (P.capFamily F) ell qBroad
          ((30+10*delta)*Real.log Q.data.N)
          (Q.data.N^(-(30+10*delta))) b) :
    ∀ F : Finset (ordConnectedSection P.negativeSet),
      Q.lam*(∑ p : Eq7InnerCoverPiece (P.capFamily F) h,
        eq7InnerThermalPiece (P.capFamily F) h p) ≤
      OriginalQEq7RegularFamilyRateDraft.familyConstant
        delta cl Az D C qLow qPost qBroad*
        (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
  let Klow := OriginalQEq7RegularFamilyRateDraft.ordinaryConstant delta cl Az C qLow
  let Kpost := OriginalQEq7RegularFamilyRateDraft.ordinaryConstant delta cl Az C qPost
  let Kbroad := OriginalQEq7RegularFamilyRateDraft.broadConstant delta cl Az D C qBroad
  have hC0' : 0 ≤ C := by linarith only [hC]
  have hCN : C ≤ Q.data.N := by linarith only [hYBN,hC]
  have hYN : 1+16*C ≤ Q.data.N := by linarith only [hYBN,hC]
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hbeta : 0 ≤ 30+10*delta := by linarith only [hdelta]
  have hCbin : 0 ≤ comparisonEq7BinFactorConstant (30+10*delta) := by
    dsimp only [comparisonEq7BinFactorConstant,comparisonEq7BinTemperatureConstant]
    positivity
  have hY : 0 ≤ 1+16*C := by positivity
  have hK : 0 ≤ max 1 ((Az+1/cl)*(1+16*C)) :=
    zero_le_one.trans (le_max_left _ _)
  have hKlow : 0 ≤ Klow := by
    dsimp only [Klow,OriginalQEq7RegularFamilyRateDraft.ordinaryConstant,
      comparisonEq7OrdinaryPieceConstant]
    positivity
  have hKpost : 0 ≤ Kpost := by
    dsimp only [Kpost,OriginalQEq7RegularFamilyRateDraft.ordinaryConstant,
      comparisonEq7OrdinaryPieceConstant]
    positivity
  have hlogD : 0 ≤ Real.log (1+D^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg D])
  have hOrigin : 0 ≤ criticalBroadOriginLossFactor :=
    criticalBroadOriginLossFactor_pos.le
  have hB : 0 ≤ 2*C := by positivity
  have hYb : 0 ≤ 1+16*(2*C) := by positivity
  have hKbm : 0 ≤ max 1 ((Az+1/cl)*(1+16*(2*C))) :=
    zero_le_one.trans (le_max_left _ _)
  have hKbroad : 0 ≤ Kbroad := by
    dsimp only [Kbroad,OriginalQEq7RegularFamilyRateDraft.broadConstant,
      comparisonEq7BroadPieceConstant,comparisonEq7BroadTemperatureConstant]
    positivity
  obtain ⟨hLowRate,hPostRate⟩ :=
    Q.eq7_inner_low_post_uniform_exact_budget_rates_draft ell hell
      qLow qPost eps C h hm hdelta heps horder hcl hAz hC0
      hN hC0N hlog hlogPow hdepth hcarrier hUA hlamFloor hC hh
      hCN hYN hN3 hqLow hqPost hKcutLow hKcutPost
  have hBroadRate : ∀ (F : Finset (ordConnectedSection P.negativeSet))
      (b : Eq7InnerRelevantBroadSlice (P.capFamily F) h),
      Q.lam*eq7InnerBroadExactBudget (P.capFamily F) ell qBroad
          ((30+10*delta)*Real.log Q.data.N)
          (Q.data.N^(-(30+10*delta))) b ≤
        Kbroad*(Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E := by
    intro F b
    simpa only [Kbroad,OriginalQEq7RegularFamilyRateDraft.broadConstant] using
      Q.eq7_inner_regular_broad_exact_budget_rate_draft P h hhi ell hell
        qBroad eps C hm hdelta heps horder hcl hAz hC0 hN hC0N
        hlog hdepth hcarrier hUA hlamFloor hC1 hh hYBN hLcap hqBroad F b
  intro F
  have hLowCount := Q.eq7_inner_low_dyad_card_le_six h
  have Hpost := Q.eq7_inner_post_dyad_card_le_log h hN hlog
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at H
    exact H
  have hinv : (1:ℝ)/Real.log 2 ≤ 2 :=
    (div_le_iff₀ hlog2).mpr (by linarith only [hlog2half])
  have hcountCoeff : (1/Real.log 2+2:ℝ) ≤ 4 := by linarith only [hinv]
  have hPostCount : (Fintype.card (Eq7InnerPostDyad Q h):ℝ) ≤
      4*Real.log Q.data.N := Hpost.trans
    (mul_le_mul_of_nonneg_right hcountCoeff (by linarith only [hlog]))
  have Hbro := Potential.eq7_inner_relevant_broad_mask_card_le_sixteen_log_direct_draft Q P F h hlog
  have hBroadCount :
      (Fintype.card (Eq7InnerRelevantBroadSlice (P.capFamily F) h):ℝ) ≤
        4*(4:ℝ)*Real.log Q.data.N := by norm_num only at Hbro ⊢; exact Hbro
  have H := eq7_inner_finite_weighted_sum_of_exact_budgets_draft
    (P.capFamily F) h ell qLow qPost qBroad
    ((30+10*delta)*Real.log Q.data.N) (Q.data.N^(-(30+10*delta)))
    hlog hKlow hKpost hKbroad (by norm_num : (0:ℝ) ≤ 4)
    hLowCount hPostCount hBroadCount
    (fun j => by simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hLowPhysical F j)
    (fun j => by simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hPostPhysical F j)
    (fun b => by simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hBroadPhysical F b)
    (by simpa only [Klow,OriginalQEq7RegularFamilyRateDraft.ordinaryConstant] using hLowRate)
    (by simpa only [Kpost,OriginalQEq7RegularFamilyRateDraft.ordinaryConstant] using hPostRate)
    (hBroadRate F)
  simpa only [OriginalQEq7RegularFamilyRateDraft.familyConstant,Klow,Kpost,Kbroad,
    show (4:ℝ)*4 = 16 by norm_num] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
