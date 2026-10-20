module

public import ComparisonActualHighOnlyWeakenConstants
public import ComparisonActualHighOnlyComparableContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock cl' cu' Az' Ct' D' Bclock' c0 T : ℝ} {dim : ℕ → ℕ}

theorem ActualWeakHighOnlyHistoryChain.weaken_constants
    {root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualWeakHighOnlyHistoryChain c0
      (fun n => (root n).weakenConstants hcl hcu hAz hCt hD hB)
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) := by
  induction H with
  | root => exact .root
  | @child P M history x hx hxunit htarget hcap hweak hd hE hs hb hh ih =>
    apply ActualWeakHighOnlyHistoryChain.child ih x hx hxunit htarget ?_ hweak hd hE hs hb hh
    filter_upwards [hcap] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right hAz (hx n).le)

def HighOnlyActualComparableBandContext.weaken_constants
    {M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : HighOnlyActualComparableBandContext M T)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    HighOnlyActualComparableBandContext
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) T where
  hT := G.hT
  xs_zero := G.xs_zero
  omission_ratio := G.omission_ratio
  pullback := G.pullback
  total_root := G.total_root
  Cf := G.Cf
  hCf := G.hCf
  source := G.source
  comparable := G.comparable

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
