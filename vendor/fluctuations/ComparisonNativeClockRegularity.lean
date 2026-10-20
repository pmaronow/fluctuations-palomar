module

public import ComparisonNativeShellHistoryContactTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

def NativePullbackClockRegularity (alpha b h : ℝ → ℝ) (a z : ℝ) : Prop :=
  (∃Kb Kh : ℝ≥0,
    LipschitzOnWith Kb (fun r=>b (alpha r)) (Icc a z) ∧
    LipschitzOnWith Kh (fun r=>h (alpha r)) (Icc a z)) ∨
  ∃s : ℝ,∀l r,a ≤ l → l ≤ r → r ≤ z → (r < s ∨ s ≤ l) →
    ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun t=>b (alpha t)) (Icc l r) ∧
      LipschitzOnWith Kh (fun t=>h (alpha t)) (Icc l r)

namespace NativePullbackClockRegularity

theorem smooth {alpha b h : ℝ → ℝ} {a z : ℝ} (Kb Kh : ℝ≥0)
    (hb : LipschitzOnWith Kb (fun r=>b (alpha r)) (Icc a z))
    (hh : LipschitzOnWith Kh (fun r=>h (alpha r)) (Icc a z)) :
    NativePullbackClockRegularity alpha b h a z := Or.inl ⟨Kb,Kh,hb,hh⟩

theorem restrict {alpha b h : ℝ → ℝ} {a z l r : ℝ}
    (H : NativePullbackClockRegularity alpha b h a z) (hal : a ≤ l) (hrz : r ≤ z) :
    NativePullbackClockRegularity alpha b h l r := by
  rcases H with ⟨Kb,Kh,hb,hh⟩|⟨s,hs⟩
  · exact Or.inl ⟨Kb,Kh,hb.mono (Icc_subset_Icc hal hrz),hh.mono (Icc_subset_Icc hal hrz)⟩
  · exact Or.inr ⟨s,fun p q hlp hpq hqr hside=>hs p q (hal.trans hlp) hpq
      (hqr.trans hrz) hside⟩

theorem of_shell_history {c : ℝ} {k M : ℝ → ℝ}
    (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (alpha : inverseIntegralConstraints 0 0 k M)
    (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm)
    (b h : ℝ → ℝ) (hb : ∀u,b u=historyMatrixClock T epsilon shell ts u)
    (hh : ∀u,h u=historyFieldClock ts u)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
    NativePullbackClockRegularity alpha.val.val b h a z := by
  obtain ⟨s,_,hs⟩:=inherited_shell_history_exists_clock_cut hc hk hkc hm hM alpha
    T epsilon shell ts b h hb hh ha haz hz
  exact Or.inr ⟨s,hs⟩

end NativePullbackClockRegularity
end OAI.SKFluctuations.LaplaceWindowFormalization
