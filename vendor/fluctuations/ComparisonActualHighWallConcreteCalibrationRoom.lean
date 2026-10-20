module

public import ConcreteHighWallInputs
public import ComparisonActualHighWallDirectOmittedMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter LaplaceWindowFormalization PositiveLaplaceAssembly
open scoped Topology
set_option maxHeartbeats 12000000

 theorem actual_wall_high_square_div_initial_epsilon_eq
    (m : ℝ) {n : ℕ} (hn : 0 < n) :
    (wallHighD m n)^2/upperInitialEpsilon m n=(n:ℝ)^(-10*m) := by
  have hN : 0 < (n:ℝ):=Nat.cast_pos.mpr hn
  unfold wallHighD upperInitialEpsilon
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_sub hN]
  congr 1
  ring

 theorem eventually_actual_concrete_high_wall_defect_calibration_room
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) (Bclock Cd : ℝ) :
    ∀ᶠn : ℕ in atTop,∀epsilon : ℝ,upperInitialEpsilon m n ≤ epsilon →
      (Cd+1)*(wallHighD m n)^2 ≤ 1/2 ∧
      4*Bclock*(Cd+1)*(wallHighD m n)^2 ≤ epsilon := by
  have Hsmall:=eventually_coefficient_rpow_le (c:=Cd+1) (d:=1/2)
    (q:=2*(-(1:ℝ)/6+15*m)) (r:=0) (by norm_num) (by linarith)
  have Hroom:=eventually_coefficient_rpow_le (c:=4*Bclock*(Cd+1)) (d:=1)
    (q:=-10*m) (r:=0) zero_lt_one (by linarith)
  filter_upwards [Hsmall,Hroom,eventually_gt_atTop (0:ℕ)] with n hnSmall hnRoom hn
  intro epsilon heps
  have hN : 0 < (n:ℝ):=Nat.cast_pos.mpr hn
  have HDsquare : (wallHighD m n)^2=(n:ℝ)^(2*(-(1:ℝ)/6+15*m)):=by
    unfold wallHighD
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    congr 1
    ring
  have HS : (Cd+1)*(wallHighD m n)^2 ≤ 1/2:=by
    rw [HDsquare]
    simpa only [Real.rpow_zero,mul_one] using hnSmall
  have HEpositive : 0 < upperInitialEpsilon m n:=by unfold upperInitialEpsilon;positivity
  have HR : (4*Bclock*(Cd+1)*(wallHighD m n)^2)/upperInitialEpsilon m n ≤ 1:=by
    rw [mul_div_assoc,actual_wall_high_square_div_initial_epsilon_eq m hn]
    simpa only [Real.rpow_zero,mul_one] using hnRoom
  exact ⟨HS,((div_le_one₀ HEpositive).mp HR).trans heps⟩

 theorem eventually_actual_concrete_high_wall_defect_calibration_room_along
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) (Bclock Cd : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,∀epsilon : ℝ,upperInitialEpsilon m (dim n+1) ≤ epsilon →
      (Cd+1)*(wallHighD m (dim n+1))^2 ≤ 1/2 ∧
      4*Bclock*(Cd+1)*(wallHighD m (dim n+1))^2 ≤ epsilon :=
  ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_actual_concrete_high_wall_defect_calibration_room hm hmmax Bclock Cd)

end OAI.SKFluctuations.Cavity
