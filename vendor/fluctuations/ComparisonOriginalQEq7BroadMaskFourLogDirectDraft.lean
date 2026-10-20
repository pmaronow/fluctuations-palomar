module

public import ComparisonOriginalQEq7BroadDyadicDirectDraft
public import ComparisonActualHighWallThetaZeroCapFamily

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_inner_broad_base_log_count_le_four_log_direct_draft
    (hlog : 1 ≤ Real.log Q.data.N) :
    ((Nat.ceil
      (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2):ℕ):ℝ)+1 ≤
        4*Real.log Q.data.N := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let base := Q.positiveOriginMassCoverBase
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hSqrtN : 1 ≤ Real.sqrt Q.data.N :=
    (Real.one_le_sqrt).mpr hN
  have hE1 : Q.data.E ≤ 1 := by
    have hdsq : Q.data.d^2 ≤ 1 :=
      pow_le_one₀ Q.data.hd.le Q.data.hd1
    have hEbound : Real.sqrt Q.data.N*Q.data.E ≤ 1 :=
      Q.hupper.trans hdsq
    have H := mul_le_mul_of_nonneg_right hSqrtN Q.data.hE.le
    have H' : Q.data.E ≤ Real.sqrt Q.data.N*Q.data.E := by
      simpa only [one_mul] using H
    exact H'.trans hEbound
  have hbase : 0 < base := Q.positiveOriginMassCoverBase_pos
  have hbaseU : U ≤ base := le_max_left _ _
  have hbase1 : base ≤ 1 := by
    dsimp only [base,positiveOriginMassCoverBase]
    exact max_le (Q.data.hsmall.trans Q.data.hd1) Q.data.hs1
  have hNE : Q.data.N*Q.data.E ≤ Q.data.N := by
    have H := mul_le_mul_of_nonneg_left hE1 Q.data.hN.le
    simpa only [mul_one] using H
  have hUinv : 1/U=Q.data.N*Q.data.E := by
    dsimp only [U]
    unfold comparisonSmallMass
    field_simp [Q.data.hN.ne',Q.data.hE.ne']
  have hbaseInv : 1/base ≤ Q.data.N := by
    have H := one_div_le_one_div_of_le Q.data.hU hbaseU
    exact H.trans (by rw [hUinv]; exact hNE)
  have hlogbase0 : 0 ≤ Real.log (1/base) :=
    Real.log_nonneg ((one_le_div hbase).mpr hbase1)
  have hlogbase : Real.log (1/base) ≤ Real.log Q.data.N :=
    Real.log_le_log (one_div_pos.mpr hbase) hbaseInv
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have Hratio := div_le_div_of_nonneg_right hlogbase hlog2.le
  have Hceil := Nat.ceil_lt_add_one
    (div_nonneg hlogbase0 hlog2.le)
  have hhalf : (1:ℝ)/2 ≤ Real.log 2 := by
    have H := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0:ℝ) < 2)
    norm_num at H
    exact H
  have hcoef : (1:ℝ)/Real.log 2+2 ≤ 4 := by
    have H : (1:ℝ)/Real.log 2 ≤ 2 :=
      (div_le_iff₀ hlog2).mpr (by linarith only [hhalf])
    linarith only [H]
  have hL0 : 0 ≤ Real.log Q.data.N := by linarith only [hlog]
  have htwo : (2:ℝ) ≤ 2*Real.log Q.data.N := by
    linarith only [hlog]
  have Hmain :
      ((Nat.ceil (Real.log (1/base)/Real.log 2):ℕ):ℝ)+1 ≤
      ((1:ℝ)/Real.log 2+2)*Real.log Q.data.N := by
    have Heq : Real.log Q.data.N/Real.log 2+
        2*Real.log Q.data.N =
        ((1:ℝ)/Real.log 2+2)*Real.log Q.data.N := by ring
    rw [←Heq]
    linarith only [Hratio,Hceil,htwo]
  have Hcoef := mul_le_mul_of_nonneg_right hcoef hL0
  exact Hmain.trans (by simpa only [mul_assoc] using Hcoef)

theorem Potential.eq7_inner_relevant_broad_mask_card_le_sixteen_log_direct_draft
    (P : Q.Potential)
    (F : Finset (ordConnectedSection P.negativeSet))
    (h : ℝ) (hlog : 1 ≤ Real.log Q.data.N) :
    (Fintype.card
      (Eq7InnerRelevantBroadSlice (P.capFamily F) h):ℝ) ≤
      16*Real.log Q.data.N := by
  have hd := P.capFamily_disjoint F
  have H := eq7_inner_relevant_broad_slice_card_le_base_log_direct_draft
    (P.capFamily F) h hd
  have Hreal :
      (Fintype.card (Eq7InnerRelevantBroadSlice (P.capFamily F) h):ℝ) ≤
      4*(((Nat.ceil
        (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2):ℕ):ℝ)+1) := by
    exact_mod_cast H
  have Hcount := Q.eq7_inner_broad_base_log_count_le_four_log_direct_draft hlog
  have Hmul := mul_le_mul_of_nonneg_left Hcount
    (by norm_num : (0:ℝ) ≤ 4)
  exact Hreal.trans (by nlinarith only [Hmul])

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
