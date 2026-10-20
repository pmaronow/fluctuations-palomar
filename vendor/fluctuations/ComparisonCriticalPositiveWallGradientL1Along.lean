module

public import ComparisonCriticalPositiveWallGradientL1

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000

theorem critical_positive_wall_gradient_L1_of_eventual_spin_and_radius_defect
    {m delta cl cu Az C0 Ct D Bclock a b K : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hspinBound : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).actualScaledRadiusSpin t∈Icc (0:ℝ) K)
    (s : NonnegativeMassProfile)
    (hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t)))
    (hdefect : Tendsto (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
      (M n).wallRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-
        comparisonScaledStationarity (laplaceComparisonShape t)
          (laplaceComparisonSlope t) t (s.mass t)|) atTop (𝓝 0) := by
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp hspinBound
  have H := critical_positive_wall_gradient_L1_of_spin_and_radius_defect
    ha hab (fun n=>dim (n+n0)) (fun n=>M (n+n0))
    (fun n=>hfixed (n+n0))
    (fun n t ht=>Hn0 (n+n0) (by omega) t ht) s
    (fun t ht=>(hspin t ht).comp (tendsto_add_atTop_nat n0))
    (hdefect.comp (tendsto_add_atTop_nat n0))
  exact (tendsto_add_atTop_iff_nat n0).mp H

theorem critical_positive_wall_gradient_L1_of_spin_profile_and_radius_defect
    {m delta cl cu Az C0 Ct D Bclock a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (s : NonnegativeMassProfile)
    (hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t)))
    (hdefect : Tendsto (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
      (M n).wallRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-
        comparisonScaledStationarity (laplaceComparisonShape t)
          (laplaceComparisonSlope t) t (s.mass t)|) atTop (𝓝 0) := by
  let K := s.mass b+1
  have hb : b∈Icc a b := ⟨hab,le_rfl⟩
  have Hbs : ∀ᶠn in atTop,(M n).actualScaledRadiusSpin b ≤ K :=
    (hspin b hb).eventually (gt_mem_nhds (by dsimp only [K];linarith))
      |>.mono (fun n hn=>hn.le)
  have Hbound : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).actualScaledRadiusSpin t∈Icc (0:ℝ) K := by
    filter_upwards [Hbs] with n hn t ht
    exact ⟨div_nonneg ((M n).full_radius_moments.2.2 _).1.1 (M n).hxs.le,
      ((M n).actual_scaled_radius_spin_monotone ht.2).trans hn⟩
  exact critical_positive_wall_gradient_L1_of_eventual_spin_and_radius_defect
    ha hab dim M hfixed Hbound s hspin hdefect

end OAI.SKFluctuations.LaplaceWindowFormalization
