module

public import ConcreteWallStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def wallHighMass (m : ℝ) (n:ℕ) : ℝ := (n:ℝ)^(-(1:ℝ)/6+5*m)
def wallHighD (m : ℝ) (n:ℕ) : ℝ := (n:ℝ)^(-(1:ℝ)/6+15*m)
def wallHighError (m : ℝ) (n:ℕ) : ℝ := (n:ℝ)^(-(2:ℝ)/3+10*m)*wallHighD m n

theorem wallHighMass_pos (m:ℝ) {n:ℕ} (hn:0 < n) : 0 < wallHighMass m n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
theorem wallHighD_pos (m:ℝ) {n:ℕ} (hn:0 < n) : 0 < wallHighD m n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
theorem wallHighError_pos (m:ℝ) {n:ℕ} (hn:0 < n) : 0 < wallHighError m n :=
  mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) (wallHighD_pos m hn)

theorem wallHighSmallMass_eq (m:ℝ) {n:ℕ} (hn:0 < n) :
    comparisonSmallMass (n:ℝ) (wallHighError m n)=(n:ℝ)^(-(1:ℝ)/6-25*m) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have he : (n:ℝ)*wallHighError m n=(n:ℝ)^((1:ℝ)/6+25*m) := by
    unfold wallHighError wallHighD
    have hmul := (Real.rpow_add hN (-(2:ℝ)/3+10*m) (-(1:ℝ)/6+15*m)).symm
    have hone := (Real.rpow_add hN (1:ℝ) ((-(2:ℝ)/3+10*m)+(-(1:ℝ)/6+15*m))).symm
    rw [Real.rpow_one] at hone
    calc
      _ = (n:ℝ)*(n:ℝ)^((-(2:ℝ)/3+10*m)+(-(1:ℝ)/6+15*m)) := by rw [hmul]
      _ = (n:ℝ)^((1:ℝ)+((-(2:ℝ)/3+10*m)+(-(1:ℝ)/6+15*m))) := hone
      _ = _ := by congr 1; ring
  unfold comparisonSmallMass
  rw [he,one_div,← Real.rpow_neg hN.le]
  congr 1
  ring

theorem wallHighSmallMass_le_d {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    comparisonSmallMass (n:ℝ) (wallHighError m n) ≤ wallHighD m n := by
  rw [wallHighSmallMass_eq m (by omega)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem wallHighD_sq_le_initial {m:ℝ} (hm:0 ≤ m) {n:ℕ} (hn:1 ≤ n) :
    (wallHighD m n)^2 ≤ PositiveLaplaceAssembly.upperInitialEpsilon m n := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  unfold wallHighD PositiveLaplaceAssembly.upperInitialEpsilon
  rw [← Real.rpow_natCast,← Real.rpow_mul hN.le]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem wallHighParameters_eventually {m:ℝ} (hm:0 < m) (hmmax:m < 1/300) :
    ∀ᶠ n:ℕ in atTop,
      0 < wallHighD m n ∧ wallHighD m n ≤ 1 ∧
      wallHighMass m n∈Ioc (0:ℝ) (1/2) ∧
      2 ≤ (n:ℝ)^(m/10000) ∧
      comparisonSmallMass (n:ℝ) (wallHighError m n) ≤ wallHighD m n ∧
      (wallHighD m n)^2 ≤ PositiveLaplaceAssembly.upperInitialEpsilon m n := by
  have hDlim : Tendsto (wallHighD m) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)/6-15*m)).comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    dsimp [wallHighD,Function.comp_apply]
    congr 1
    ring
  have hSlim : Tendsto (wallHighMass m) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)/6-5*m)).comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    dsimp [wallHighMass,Function.comp_apply]
    congr 1
    ring
  have hQlim : Tendsto (fun n:ℕ => (n:ℝ)^(m/10000)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < m/10000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hDlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)),
      hSlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2)),
      hQlim.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with n hd hs hq hn
  exact ⟨wallHighD_pos m (by omega),hd.le,⟨wallHighMass_pos m (by omega),hs.le⟩,hq,
    wallHighSmallMass_le_d hm.le hn,wallHighD_sq_le_initial hm.le hn⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter Set Hierarchy
open scoped Topology NNReal

theorem wallHighConstraints_eventually {m:ℝ} (hm:0 < m) (hmmax:m < 1/300) :
    ∀ᶠ n:ℕ in atTop,
      let s := wallHighMass m n
      let d := wallHighD m n
      let E := wallHighError m n
      let rmin := concreteWallRadius (n:ℝ) (m/10000) E d s
      (inverseIntegralConstraints rmin s (concreteWallFloor (n:ℝ) (m/10000) E)
        (concreteWallCap (n:ℝ) (m/10000) E d)).Nonempty ∧
      laplaceComparisonStrength d (d^2) rmin=d^2 := by
  filter_upwards [wallHighParameters_eventually hm hmmax,eventually_ge_atTop (1:ℕ)] with n hn hn1
  dsimp only
  have hN : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hE : 0<wallHighError m n := wallHighError_pos m (by omega)
  exact ⟨concreteWallConstraints_nonempty hN hE hn.1 hn.2.1
      ⟨hn.2.2.1.1.le,hn.2.2.1.2⟩ hn.2.2.2.1 hn.2.2.2.2.1,
    concreteWallStrength_initial hN hE hn.1 hn.2.1 hn.2.2.1.1.le hn.2.2.2.1 hn.2.2.2.2.1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
