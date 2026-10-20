module

public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter

theorem actual_high_wall_category_orders
    {m delta : ℝ} (hm : 0 < m) (hdelta : 0 < delta) :
    ∃p : ℝ,∃dOrder : ℕ,∃eta : ℝ,
      2 < p ∧ 0 < dOrder ∧ p/(p-2) ≤ (dOrder:ℝ) ∧
      1 ≤ 4/p ∧ 4/p ≤ 2 ∧
      2-4/p ≤ actualMassSavingExponent m delta/128 ∧
      0 < eta ∧ 2*eta < 6*m := by
  let gamma:=actualMassSavingExponent m delta
  let p:=2+gamma/512
  let dOrder:=Nat.ceil (p/(p-2))+1
  let eta:=gamma/1024
  have hg : 0 < gamma:=actualMassSavingExponent_pos hm hdelta
  have hb:=actualMassSavingExponent_bounds m delta
  have hp : 2 < p:=by dsimp only [p];linarith only [hg]
  have hp0 : 0 < p:=by linarith only [hp]
  have hp4 : p ≤ 4:=by dsimp only [p,gamma];linarith only [hb.1]
  have horder : p/(p-2) ≤ (dOrder:ℝ):=by
    have H:=Nat.le_ceil (p/(p-2))
    dsimp only [dOrder]
    exact H.trans (by exact_mod_cast (Nat.le_succ (Nat.ceil (p/(p-2)))))
  refine ⟨p,dOrder,eta,hp,by dsimp only [dOrder];omega,horder,?_,?_,?_,?_,?_⟩
  · exact (le_div_iff₀ hp0).mpr (by linarith only [hp4])
  · exact (div_le_iff₀ hp0).mpr (by linarith only [hp])
  · have H : 2-gamma/128 ≤ 4/p:=by
      apply (le_div_iff₀ hp0).mpr
      dsimp only [p]
      nlinarith only [hg]
    change 2-4/p ≤ gamma/128
    linarith only [H]
  · dsimp only [eta];positivity
  · dsimp only [eta,gamma]
    linarith only [hb.2.1,hm]

end OAI.SKFluctuations.LaplaceWindowFormalization
