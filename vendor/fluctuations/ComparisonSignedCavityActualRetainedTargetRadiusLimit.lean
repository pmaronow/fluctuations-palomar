module

public import ComparisonSignedCavitySharpOriginalLowRadius
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem native_original_retained_target_low_radius_tendsto
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeOriginalCutLowErrorRadius n bf hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))) atTop
      (𝓝 (Real.sqrt (orderedPathB (n+1) bf hf u.val-(orderedPathS (n+1) bf hf u.val)^2))) := by
  have H:=(nativeRetainedCenteredMoment_one_tendsto n bf hf hb hh us hus u hu).sqrt
  convert H using 1
  funext j
  unfold nativeOriginalCutLowErrorRadius
  rw [native_original_retained_star_low_second n bf hf hb hh (finiteCutMasses us j)
    (finiteCutMasses_ordered us hus j) u (finiteCutMasses_nodes us j hu)]

theorem actual_original_retained_target_low_radius_tendsto
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))) atTop
      (𝓝 (Real.sqrt (orderedPathB (n+1) M.bf M.hf u.val-(orderedPathS (n+1) M.bf M.hf u.val)^2))) :=
  native_original_retained_target_low_radius_tendsto n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone us hus u hu

theorem actual_original_retained_target_low_radius_with_site_tendsto
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))+1/(n+1:ℕ)) atTop
      (𝓝 (Real.sqrt (orderedPathB (n+1) M.bf M.hf u.val-(orderedPathS (n+1) M.bf M.hf u.val)^2)+
        1/(n+1:ℕ))) :=
  (actual_original_retained_target_low_radius_tendsto M us hus u hu).add_const _

theorem actual_original_retained_target_low_radius_refinement
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠj in atTop,|nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))-
      Real.sqrt (orderedPathB (n+1) M.bf M.hf u.val-(orderedPathS (n+1) M.bf M.hf u.val)^2)|<epsilon := by
  have H:=Metric.tendsto_nhds.mp (actual_original_retained_target_low_radius_tendsto M us hus u hu)
    epsilon hepsilon
  simpa only [Real.dist_eq] using H

end OAI.SKFluctuations.Cavity
