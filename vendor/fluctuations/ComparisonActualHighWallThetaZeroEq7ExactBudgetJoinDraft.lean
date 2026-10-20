module

public import ComparisonActualHighWallThetaZeroEq7FiniteWeightedSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

def eq7InnerLowExactBudget (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Qraw Lside cut : ℝ) {h : ℝ}
    (j : Eq7InnerLowDyad Q h) : ℝ :=
  Q.ordinaryOptimizedBudgetPositiveOrigin ell Qraw 16 Lside cut
    (16*Q.eq7InnerDyadMass j.val.val) Q.data.s
    (Q.xs+Q.eq7InnerDyadRight j.val.val)
    (Q.eq7InnerDyadMass j.val.val) 16
    (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val))

def eq7InnerPostExactBudget (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Qraw Lside cut : ℝ) {h : ℝ}
    (j : Eq7InnerPostDyad Q h) : ℝ :=
  Q.ordinaryOptimizedBudget ell Qraw 16 Lside cut
    (16*Q.eq7InnerDyadMass j.val.val)
    (Q.eq7InnerWallStart j.val.val)
    (Q.xs+Q.eq7InnerDyadRight j.val.val)
    (Q.eq7InnerDyadMass j.val.val) 16
    (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val))

def eq7InnerBroadExactBudget {ι : Type*}
    (c : ι → ShiftedCapInterval Q P)
    (ell : ℕ) (Qraw Lside cut : ℝ) {h : ℝ}
    (b : Eq7InnerRelevantBroadSlice c h) : ℝ :=
  Q.criticalBroadMassBudget ell Qraw Lside cut
    ((eq7InnerBroadSampler c b.val.1).scale b.val.2)
    (∫r in eq7InnerBroadSlice c b.val, deriv Q.alpha.val.val r)

theorem eq7_inner_finite_weighted_sum_of_exact_budgets_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P) (h : ℝ)
    (ell : ℕ) (QrawLow QrawPost QrawBroad Lside cut : ℝ)
    {eps Klow Kpost Kbroad Kcount : ℝ}
    (hL : 1 ≤ Real.log Q.data.N)
    (hKlow : 0 ≤ Klow) (hKpost : 0 ≤ Kpost)
    (hKbroad : 0 ≤ Kbroad) (hKcount : 0 ≤ Kcount)
    (hLowCount : Fintype.card (Eq7InnerLowDyad Q h) ≤ 6)
    (hPostCount : (Fintype.card (Eq7InnerPostDyad Q h) : ℝ) ≤
      Kcount*Real.log Q.data.N)
    (hBroadCount :
      (Fintype.card (Eq7InnerRelevantBroadSlice c h) : ℝ) ≤
        4*Kcount*Real.log Q.data.N)
    (hLowPhysical : ∀ j : Eq7InnerLowDyad Q h,
      (∫u in 0..1, (eq7InnerLowSupport c j).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
      Q.eq7InnerLowExactBudget ell QrawLow Lside cut j)
    (hPostPhysical : ∀ j : Eq7InnerPostDyad Q h,
      (∫u in 0..1, (eq7InnerPostSupport c j).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
      Q.eq7InnerPostExactBudget ell QrawPost Lside cut j)
    (hBroadPhysical : ∀ b : Eq7InnerRelevantBroadSlice c h,
      (∫u in 0..1, (eq7InnerBroadSlice c b.val).indicator
        (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
        Q.shiftedNativeModel.thermal u) ≤
      eq7InnerBroadExactBudget c ell QrawBroad Lside cut b)
    (hLowRate : ∀ j : Eq7InnerLowDyad Q h,
      Q.lam*Q.eq7InnerLowExactBudget ell QrawLow Lside cut j ≤
        Klow*(Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E)
    (hPostRate : ∀ j : Eq7InnerPostDyad Q h,
      Q.lam*Q.eq7InnerPostExactBudget ell QrawPost Lside cut j ≤
        Kpost*(Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E)
    (hBroadRate : ∀ b : Eq7InnerRelevantBroadSlice c h,
      Q.lam*eq7InnerBroadExactBudget c ell QrawBroad Lside cut b ≤
        Kbroad*(Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E) :
    Q.lam*(∑ p : Eq7InnerCoverPiece c h,
      eq7InnerThermalPiece c h p) ≤
      (6*Klow+Kcount*Kpost+4*Kcount*Kbroad)*
        (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
  apply eq7_inner_finite_weighted_piece_sum_of_rates_draft c h hL
    hKlow hKpost hKbroad hKcount hLowCount hPostCount hBroadCount
  · intro j
    have hp := mul_le_mul_of_nonneg_left (hLowPhysical j) Q.hlam.le
    have hp' : Q.lam*eq7InnerThermalPiece c h (.inr (.inl j)) ≤
        Q.lam*Q.eq7InnerLowExactBudget ell QrawLow Lside cut j := by
      simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hp
    exact hp'.trans (hLowRate j)
  · intro j
    have hp := mul_le_mul_of_nonneg_left (hPostPhysical j) Q.hlam.le
    have hp' : Q.lam*eq7InnerThermalPiece c h (.inr (.inr j)) ≤
        Q.lam*Q.eq7InnerPostExactBudget ell QrawPost Lside cut j := by
      simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hp
    exact hp'.trans (hPostRate j)
  · intro b
    have hp := mul_le_mul_of_nonneg_left (hBroadPhysical b) Q.hlam.le
    have hp' : Q.lam*eq7InnerThermalPiece c h (.inl b) ≤
        Q.lam*eq7InnerBroadExactBudget c ell QrawBroad Lside cut b := by
      simpa only [eq7InnerThermalPiece,eq7InnerCoverSupport] using hp
    exact hp'.trans (hBroadRate b)

theorem Potential.eq7_inner_post_weighted_thermal_of_finite_piece_prices_draft
    (P : Q.Potential) {h B : ℝ}
    (hprefix : Q.eq7InnerPrefixEnd ≤ h) (hhi : h ≤ 1)
    (hprices : ∀F : Finset (ordConnectedSection P.negativeSet),
      Q.lam*(∑p : Eq7InnerCoverPiece (P.capFamily F) h,
        eq7InnerThermalPiece (P.capFamily F) h p) ≤ B) :
    Q.lam*(∫u in 0..1,
      (Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h ∩
        (P.negativeSet ∪ P.contactSet)).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ B := by
  have hraw : ∀F : Finset (ordConnectedSection P.negativeSet),
      (∑p : Eq7InnerCoverPiece (P.capFamily F) h,
        eq7InnerThermalPiece (P.capFamily F) h p) ≤ B/Q.lam := by
    intro F
    exact (le_div_iff₀ Q.hlam).2 (by simpa only [mul_comm] using hprices F)
  have hthermal := P.eq7_inner_post_thermal_le_of_finite_piece_prices
    hprefix hhi hraw
  have hweighted := mul_le_mul_of_nonneg_left hthermal Q.hlam.le
  calc
    _ ≤ Q.lam*(B/Q.lam) := hweighted
    _ = B := by field_simp [Q.hlam.ne']

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
