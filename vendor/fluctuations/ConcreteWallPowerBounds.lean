module

public import ConcreteWallPowers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wallHighError_eq (m:ℝ) {n:ℕ} (hn:0 < n) :
    wallHighError m n=(n:ℝ)^(-(5:ℝ)/6+25*m) := by
  unfold wallHighError wallHighD
  rw [←Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem wallHighLowerScale_eq (m:ℝ) {n:ℕ} (hn:0 < n) :
    comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n)=
      (n:ℝ)^(-(1:ℝ)/6+10*m) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < wallHighD m n := wallHighD_pos m hn
  calc
    _ = Real.sqrt (n:ℝ)*(n:ℝ)^(-(2:ℝ)/3+10*m) := by
      unfold comparisonLowerScale wallHighError
      field_simp [hd.ne']
    _ = (n:ℝ)^((1:ℝ)/2+(-(2:ℝ)/3+10*m)) := by
      rw [Real.sqrt_eq_rpow]
      exact (Real.rpow_add hN ((1:ℝ)/2) (-(2:ℝ)/3+10*m)).symm
    _ = _ := by congr 1; ring

theorem wallHighLengthRatio_eq (m:ℝ) {n:ℕ} (hn:0 < n) :
    (comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n))^3/(wallHighD m n)^2=
      (n:ℝ)^(-(1:ℝ)/6) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  rw [wallHighLowerScale_eq m hn]
  unfold wallHighD
  rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_mul hN.le,
    ←Real.rpow_sub hN]
  congr 1
  ring

theorem wallHighConstraintLength_eq {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    comparisonConstraintLength (n:ℝ) (wallHighError m n) (wallHighD m n)=
      comparisonSmallMass (n:ℝ) (wallHighError m n) := by
  unfold comparisonConstraintLength
  apply min_eq_left
  rw [wallHighLengthRatio_eq m (by omega),wallHighSmallMass_eq m (by omega)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem wallHighMass_div_smallMass (m:ℝ) {n:ℕ} (hn:0 < n) :
    wallHighMass m n/comparisonSmallMass (n:ℝ) (wallHighError m n)=(n:ℝ)^(30*m) := by
  rw [wallHighSmallMass_eq m hn]
  unfold wallHighMass
  rw [←Real.rpow_sub (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem wallHighCapSecondTerm_eq (m:ℝ) {n:ℕ} (hn:0 < n) :
    (wallHighD m n)^3/wallHighError m n*(wallHighMass m n)^2=(n:ℝ)^(30*m) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  rw [wallHighError_eq m hn]
  unfold wallHighD wallHighMass
  rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_mul hN.le,
    ←Real.rpow_sub hN,←Real.rpow_add hN]
  congr 1
  ring

theorem wallHighCap_bounds {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    2*(n:ℝ)^(30*m+m/10000) ≤ 
      concreteWallCap (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n) ∧
    concreteWallCap (n:ℝ) (m/10000) (wallHighError m n) (wallHighD m n) (wallHighMass m n) ≤ 
      6*(n:ℝ)^(30*m+m/10000) := by
  have hn0 : 0 < n := by omega
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  let U := comparisonSmallMass (n:ℝ) (wallHighError m n)
  let S := wallHighMass m n
  let d := wallHighD m n
  let E := wallHighError m n
  let t := (n:ℝ)^(30*m)
  have hU : 0 < U := concreteWallSmallMass_pos hN (wallHighError_pos m hn0)
  have hS : 0 < S := wallHighMass_pos m hn0
  have hd : 0 < d := wallHighD_pos m hn0
  have hE : 0 < E := wallHighError_pos m hn0
  have hUS : U ≤ S := by
    dsimp [U,S]
    rw [wallHighSmallMass_eq m hn0]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have hfirst : S/U=t := wallHighMass_div_smallMass m hn0
  have hsecond : d^3/E*S^2=t := wallHighCapSecondTerm_eq m hn0
  have hq : 0 < (n:ℝ)^(m/10000) := Real.rpow_pos_of_pos hN _
  have hfirstBounds : t ≤ (S+U)/U ∧ (S+U)/U ≤ 2*t := by
    constructor
    · rw [←hfirst]
      exact div_le_div_of_nonneg_right (by linarith) hU.le
    · rw [←hfirst]
      calc
        (S+U)/U ≤ (2*S)/U := div_le_div_of_nonneg_right (by linarith) hU.le
        _ = _ := by ring
  have hsecondBounds : t ≤ d^3/E*(S+U)^2 ∧ d^3/E*(S+U)^2 ≤ 4*t := by
    constructor
    · rw [←hsecond]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    · rw [←hsecond]
      have hsq : (S+U)^2 ≤ 4*S^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ d^3/E)]
  have hexp : (n:ℝ)^(m/10000)*t=(n:ℝ)^(30*m+m/10000) := by
    dsimp [t]
    rw [←Real.rpow_add hN]
    congr 1
    ring
  unfold concreteWallCap comparisonCap
  rw [wallHighConstraintLength_eq hm hn]
  change 2*(n:ℝ)^(30*m+m/10000) ≤ (n:ℝ)^(m/10000)*((S+U)/U+d^3/E*(S+U)^2) ∧
    (n:ℝ)^(m/10000)*((S+U)/U+d^3/E*(S+U)^2) ≤ 6*(n:ℝ)^(30*m+m/10000)
  constructor  <;> rw [←hexp]  <;>
    nlinarith [mul_le_mul_of_nonneg_left hfirstBounds.1 hq.le,
      mul_le_mul_of_nonneg_left hfirstBounds.2 hq.le,
      mul_le_mul_of_nonneg_left hsecondBounds.1 hq.le,
      mul_le_mul_of_nonneg_left hsecondBounds.2 hq.le]

end OAI.SKFluctuations.LaplaceWindowFormalization
