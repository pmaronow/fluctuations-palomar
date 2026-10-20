module

public import ComparisonActualHighOnlyOmittedCapEnvelopes

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem actual_high_only_downward_clipped_radius_after {A B c H b s : ℝ} {M : ℝ→ℝ}
    (hs : s∈Icc (0:ℝ) 1) (hA : 0<A) (hB : 0<B) (hc : 0<c)
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1) (hb : b∈Icc (0:ℝ) 1)
    (alpha : inverseIntegralConstraints 0 s (reciprocalSquareFloor A B) M)
    {u : ℝ} (hu : u∈Icc s 1) (huafter : b+reciprocalFloorTime A B 1 ≤ u) :
    min (omittedSweepQuantile zero_le_one hs hc (reciprocalSquareFloor_continuousOn hB)
      hkc hm (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha u) (downwardRampBarrier A B M H b u)=
      omittedSweepQuantile zero_le_one hs hc (reciprocalSquareFloor_continuousOn hB)
        hkc hm (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha u := by
  rw [downwardRampBarrier_after hA hB hMc hm hMp hH hHroom hb ⟨hs.1.trans hu.1,hu.2⟩ huafter]
  exact min_eq_left (actual_high_only_omitted_quantile_cap_envelopes hs hc
    (reciprocalSquareFloor_continuousOn hB) hkc hMc hm hMp alpha hu).2

end OAI.SKFluctuations.LaplaceWindowFormalization
