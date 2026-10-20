module

public import ComparisonActualHighWallThetaZeroEq7FinitePhysicalCalls
public import ComparisonActualHighWallThetaZeroEq7FiniteThermalAssembly

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

def eq7InnerThermalPiece {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (h : ℝ) (p : Eq7InnerCoverPiece c h) : ℝ :=
  ∫u in 0..1,
    (eq7InnerCoverSupport c h p).indicator (fun _ => (1:ℝ))
      (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u

theorem eq7_inner_finite_weighted_piece_sum_of_rates_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P) (h : ℝ)
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
    (hLow : ∀ j : Eq7InnerLowDyad Q h,
      Q.lam*eq7InnerThermalPiece c h (.inr (.inl j)) ≤
        Klow*(Real.log Q.data.N)^5*
          Q.data.N^(2*delta+eps)*Q.data.E)
    (hPost : ∀ j : Eq7InnerPostDyad Q h,
      Q.lam*eq7InnerThermalPiece c h (.inr (.inr j)) ≤
        Kpost*(Real.log Q.data.N)^5*
          Q.data.N^(2*delta+eps)*Q.data.E)
    (hBroad : ∀ b : Eq7InnerRelevantBroadSlice c h,
      Q.lam*eq7InnerThermalPiece c h (.inl b) ≤
        Kbroad*(Real.log Q.data.N)^5*
          Q.data.N^(2*delta+eps)*Q.data.E) :
    Q.lam*(∑ p : Eq7InnerCoverPiece c h,
      eq7InnerThermalPiece c h p) ≤
      (6*Klow+Kcount*Kpost+4*Kcount*Kbroad)*
        (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
  let L := Real.log Q.data.N
  let X := Q.data.N^(2*delta+eps)*Q.data.E
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith only [hL]
  have hX : 0 ≤ X := by
    have hN := Q.data.hN
    have hE := Q.data.hE
    dsimp only [X]
    positivity
  have hLowCardR : (Fintype.card (Eq7InnerLowDyad Q h) : ℝ) ≤ 6 := by
    exact_mod_cast hLowCount
  have hLowCardL : (Fintype.card (Eq7InnerLowDyad Q h) : ℝ) ≤ 6*L := by
    linarith only [hLowCardR,hL]
  have hLowSum :
      (∑ j : Eq7InnerLowDyad Q h,
        Q.lam*eq7InnerThermalPiece c h (.inr (.inl j))) ≤
      (Fintype.card (Eq7InnerLowDyad Q h) : ℝ)*(Klow*L^5*X) := by
    calc
      _ ≤ ∑ _j : Eq7InnerLowDyad Q h, Klow*L^5*X := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [L,X,mul_assoc] using hLow j
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hPostSum :
      (∑ j : Eq7InnerPostDyad Q h,
        Q.lam*eq7InnerThermalPiece c h (.inr (.inr j))) ≤
      (Fintype.card (Eq7InnerPostDyad Q h) : ℝ)*(Kpost*L^5*X) := by
    calc
      _ ≤ ∑ _j : Eq7InnerPostDyad Q h, Kpost*L^5*X := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [L,X,mul_assoc] using hPost j
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hBroadSum :
      (∑ b : Eq7InnerRelevantBroadSlice c h,
        Q.lam*eq7InnerThermalPiece c h (.inl b)) ≤
      (Fintype.card (Eq7InnerRelevantBroadSlice c h) : ℝ)*
        (Kbroad*L^5*X) := by
    calc
      _ ≤ ∑ _b : Eq7InnerRelevantBroadSlice c h, Kbroad*L^5*X := by
        apply Finset.sum_le_sum
        intro b hb
        simpa only [L,X,mul_assoc] using hBroad b
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hLowPaid :
      (Fintype.card (Eq7InnerLowDyad Q h) : ℝ)*(Klow*L^5*X) ≤
        6*Klow*L^6*X := by
    calc
      _ ≤ (6*L)*(Klow*L^5*X) :=
        mul_le_mul_of_nonneg_right hLowCardL (by positivity)
      _ = _ := by ring
  have hPostPaid :
      (Fintype.card (Eq7InnerPostDyad Q h) : ℝ)*(Kpost*L^5*X) ≤
        Kcount*Kpost*L^6*X := by
    calc
      _ ≤ (Kcount*L)*(Kpost*L^5*X) :=
        mul_le_mul_of_nonneg_right (by simpa only [L] using hPostCount)
          (by positivity)
      _ = _ := by ring
  have hBroadPaid :
      (Fintype.card (Eq7InnerRelevantBroadSlice c h) : ℝ)*
          (Kbroad*L^5*X) ≤ 4*Kcount*Kbroad*L^6*X := by
    calc
      _ ≤ (4*Kcount*L)*(Kbroad*L^5*X) :=
        mul_le_mul_of_nonneg_right (by simpa only [L] using hBroadCount)
          (by positivity)
      _ = _ := by ring
  have hsplit :
      (∑ p : Eq7InnerCoverPiece c h,
        Q.lam*eq7InnerThermalPiece c h p) =
      (∑ b : Eq7InnerRelevantBroadSlice c h,
        Q.lam*eq7InnerThermalPiece c h (.inl b))+
      (∑ j : Eq7InnerLowDyad Q h,
        Q.lam*eq7InnerThermalPiece c h (.inr (.inl j)))+
      (∑ j : Eq7InnerPostDyad Q h,
        Q.lam*eq7InnerThermalPiece c h (.inr (.inr j))) := by
    simp only [Eq7InnerCoverPiece,Fintype.sum_sum_type]
    ring
  calc
    _ = (∑ b : Eq7InnerRelevantBroadSlice c h,
          Q.lam*eq7InnerThermalPiece c h (.inl b))+
        (∑ j : Eq7InnerLowDyad Q h,
          Q.lam*eq7InnerThermalPiece c h (.inr (.inl j)))+
        (∑ j : Eq7InnerPostDyad Q h,
          Q.lam*eq7InnerThermalPiece c h (.inr (.inr j))) := by
            rw [Finset.mul_sum]
            exact hsplit
    _ ≤ (Fintype.card (Eq7InnerRelevantBroadSlice c h) : ℝ)*
          (Kbroad*L^5*X)+
        (Fintype.card (Eq7InnerLowDyad Q h) : ℝ)*(Klow*L^5*X)+
        (Fintype.card (Eq7InnerPostDyad Q h) : ℝ)*(Kpost*L^5*X) :=
          add_le_add (add_le_add hBroadSum hLowSum) hPostSum
    _ ≤ 4*Kcount*Kbroad*L^6*X+6*Klow*L^6*X+
          Kcount*Kpost*L^6*X :=
          add_le_add (add_le_add hBroadPaid hLowPaid) hPostPaid
    _ = (6*Klow+Kcount*Kpost+4*Kcount*Kbroad)*
          (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
          dsimp only [L,X]
          ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
