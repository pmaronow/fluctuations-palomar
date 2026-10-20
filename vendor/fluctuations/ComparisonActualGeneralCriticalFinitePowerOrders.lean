module

public import ComparisonActualGeneralFinitePowerFamilyResidualIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open scoped BigOperators
set_option autoImplicit false

def criticalFinitePowerOrder (depth : ℕ) :
    Sum (Fin 2) (Fin depth) → ℕ
  | .inl i => if i.val=0 then 8 else 4
  | .inr j => 2*(j.val+2)

theorem criticalFinitePowerOrder_pos (depth : ℕ)
    (j : Sum (Fin 2) (Fin depth)) :
    0 < criticalFinitePowerOrder depth j := by
  rcases j with i|i
  · by_cases hi : i.val=0 <;> simp [criticalFinitePowerOrder,hi]
  · simp [criticalFinitePowerOrder]

theorem criticalFinitePowerOrder_pred_succ (depth : ℕ)
    (j : Sum (Fin 2) (Fin depth)) :
    criticalFinitePowerOrder depth j-1+1=criticalFinitePowerOrder depth j := by
  have H:=criticalFinitePowerOrder_pos depth j
  omega

end OAI.SKFluctuations.Cavity
