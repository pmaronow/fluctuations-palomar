module

public import ComparisonNativeActualSelectedBadHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock cl' cu' Az' Ct' D' Bclock' : ℝ}

def weakenConstants {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    NativeOverlapMinimum n m delta cl' cu' Az' C0 Ct' D' Bclock' where
  context := M.context
  lam := M.lam
  hlam := M.hlam
  hld := M.hld
  alpha := M.alpha
  b := M.b
  h := M.h
  hb := M.hb
  hlb := M.hlb
  hh := M.hh
  hh0 := M.hh0
  minimum := M.minimum
  xs := M.xs
  z := M.z
  hxs := M.hxs
  hscale := M.hscale
  hz := M.hz
  hzxs := M.hzxs.trans (mul_le_mul_of_nonneg_right hAz M.hxs.le)
  hdD := M.hdD.trans hD
  hupper := M.hupper
  hlower := M.hlower
  htest := M.htest.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCt (laplaceComparisonStrength_pos M.context.d M.hlam M.xs).le)
    (sq_nonneg M.xs))
  regular := by
    intro r hr
    have Hr : 0 ≤ r := M.hz.1.trans hr.1
    exact ⟨(mul_le_mul_of_nonneg_right hcl Hr).trans (M.regular r hr).1,
      (M.regular r hr).2.trans (mul_le_mul_of_nonneg_right hcu Hr)⟩
  clockBudget := M.clockBudget.trans hB

theorem ActualSelectedBadHistoryChain.weaken_constants
    {N : ℕ→ℕ} {c0 : ℝ}
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualSelectedBadHistoryChain c0
      (fun n=>(root n).weakenConstants hcl hcu hAz hCt hD hB)
      (fun n=>(M n).weakenConstants hcl hcu hAz hCt hD hB) := by
  induction Hhistory with
  | root => exact .root
  | @child P M history x hx hxlim htarget hcap hweak hd hE hb hh ih =>
    apply ActualSelectedBadHistoryChain.child ih x hx hxlim htarget ?_ hweak hd hE hb hh
    filter_upwards [hcap] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right hAz (hx n).le)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
