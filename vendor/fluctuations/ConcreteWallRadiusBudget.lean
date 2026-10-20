module

public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wallHighRadius_bounds {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    (n:ℝ)^(-(1:ℝ)/6-55*m-m/10000)/12 ≤ 
      concreteWallRadius (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n) ∧
    concreteWallRadius (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n) ≤ 
      (n:ℝ)^(-(1:ℝ)/6-55*m-m/10000)/4 := by
  have hn0 : 0 < n := by omega
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  let U := comparisonSmallMass (n:ℝ) (wallHighError m n)
  let C := concreteWallCap (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n)
  let P := (n:ℝ)^(30*m+m/10000)
  have hU : 0 < U := concreteWallSmallMass_pos hN (wallHighError_pos m hn0)
  have hP : 0 < P := Real.rpow_pos_of_pos hN _
  have hb := wallHighCap_bounds hm hn
  have hC : 0 < C := (by positivity : 0 < 2*P).trans_le hb.1
  have he (K:ℝ) : U/(K*P)=((n:ℝ)^(-(1:ℝ)/6-55*m-m/10000))/K := by
    dsimp [U,P]
    rw [wallHighSmallMass_eq m hn0]
    calc
      _ = ((n:ℝ)^(-(1:ℝ)/6-25*m)/(n:ℝ)^(30*m+m/10000))/K := by ring
      _ = _ := by rw [←Real.rpow_sub hN]; congr 2; ring
  change _ ≤ U/(2*C) ∧ U/(2*C) ≤ _
  constructor
  · rw [←he 12]
    exact div_le_div_of_nonneg_left hU.le (by positivity : 0 < 2*C) (by linarith [hb.2])
  · rw [←he 4]
    exact div_le_div_of_nonneg_left hU.le (by positivity : 0 < 4*P) (by linarith [hb.1])

theorem wallHighRadius_noise_budget {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    wallHighD m n/((n:ℝ)*wallHighMass m n*
      concreteWallRadius (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n)) ≤ 
        12*(n:ℝ)^(-(5:ℝ)/6+65*m+m/10000) := by
  have hn0 : 0 < n := by omega
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hS : 0 < wallHighMass m n := wallHighMass_pos m hn0
  have hD : 0 < wallHighD m n := wallHighD_pos m hn0
  let R := (n:ℝ)^(-(1:ℝ)/6-55*m-m/10000)
  have hR : 0 < R := Real.rpow_pos_of_pos hN _
  have hr := (wallHighRadius_bounds hm hn).1
  have hratio := div_le_div_of_nonneg_left hD.le (by positivity : 0 < (n:ℝ)*wallHighMass m n*(R/12))
    (mul_le_mul_of_nonneg_left hr (mul_pos hN hS).le)
  have hden : (n:ℝ)*wallHighMass m n*R=(n:ℝ)^((2:ℝ)/3-50*m-m/10000) := by
    dsimp [wallHighMass,R]
    have hfirst := (Real.rpow_add hN (1:ℝ) (-(1:ℝ)/6+5*m)).symm
    rw [Real.rpow_one] at hfirst
    rw [hfirst,←Real.rpow_add hN]
    congr 1
    ring
  have heq : wallHighD m n/((n:ℝ)*wallHighMass m n*(R/12))=
      12*(n:ℝ)^(-(5:ℝ)/6+65*m+m/10000) := by
    calc
      _ = 12*(wallHighD m n/((n:ℝ)*wallHighMass m n*R)) := by ring
      _ = _ := by
        rw [hden]
        unfold wallHighD
        rw [←Real.rpow_sub hN]
        congr 2
        ring
  exact hratio.trans_eq heq

end OAI.SKFluctuations.LaplaceWindowFormalization
