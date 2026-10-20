module

public import ComparisonActualHighOnlyOverlapMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy
set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem inverse_radius_outer_threshold
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (houter : cu*M.z ≤ u) : M.z ≤ M.R u := by
  have hzupper := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
  have H := omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
    (hzupper.trans houter)
  have hzspec := omittedSweepQuantile_inverse zero_le_one
    ⟨M.data.hs.1,M.data.hs1⟩ M.data.hc M.data.hk M.data.hkc M.data.hm
    M.data.hM M.alpha M.hz
  exact hzspec.symm.trans_le H

theorem inverse_radius_outer_lower_bound
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (houter : cu*M.z ≤ u) : u/cu ≤ M.R u := by
  have hzupper := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
  have hzMass : M.data.s ≤ M.alpha.val.val M.z := by
    have H := M.alpha.val.property.2 M.hz.1
    rw [M.alpha.property.1] at H
    exact H
  have huHigh : u∈Icc M.data.s 1 :=
    ⟨hzMass.trans (hzupper.trans houter),hu.2⟩
  have hR := omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u
  have hspec := omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha huHigh
  have H := (M.regular (M.R u) ⟨M.inverse_radius_outer_threshold houter,hR.2⟩).2
  change M.alpha.val.val (M.R u) ≤ cu*M.R u at H
  rw [hspec] at H
  exact (div_le_iff₀ hcu).mpr (by nlinarith only [H])

theorem inverse_radius_outer_band_lower_bound_of_parent_scale
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {u left x y : ℝ} (hu : u∈Icc (0:ℝ) 1) (hxs : M.xs ≤ x)
    (hband : left*y ≤ u) (houter : cu*Az*x ≤ left*y) :
    left*y/cu ≤ M.R u := by
  have Houter : cu*M.z ≤ u :=
    (mul_le_mul_of_nonneg_left M.hzxs hcu.le).trans (by
      have H := mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
      nlinarith only [H,houter,hband])
  exact (div_le_div_of_nonneg_right hband hcu.le).trans
    (M.inverse_radius_outer_lower_bound hcu hu Houter)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
