module

public import ComparisonActualHighWallThetaZeroWholeCapSamplerPositiveOrigin
public import ComparisonShiftedNativeRadiusWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
namespace PositiveOriginWholeCapBroadSampler
variable {cap : ShiftedCapInterval a P}

theorem actual_cover_ae (f : PositiveOriginWholeCapBroadSampler cap) :
    ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      a.shiftedNativeModel.R u ∈ Ioo cap.left cap.right →
      u ≤ min a.positiveOriginMassCoverBase 1 ∨
        ∃ i : Fin f.count, a.shiftedNativeModel.R u ∈ f.slice i := by
  let m:=a.shiftedNativeModel
  have hfinite : (Set.range (fun i : Fin f.count=>f.node (i.val+1))).Countable:=
    (Set.finite_range _).countable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hfinite.ae_notMem (volume.restrict (Icc (0:ℝ) 1))] with u hu hcuts hcap
  have huHigh : u∈Icc a.data.s 1:=⟨(m.R_high_mass (cap.hleft.trans_lt hcap.1)).le,hu.2⟩
  have hr:=m.R_bounds u
  have hs:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
  have hA:=hs ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩ hr hcap.1
  have hB:=hs hr ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩ hcap.2
  rw [m.R_spec huHigh] at hA hB
  by_cases hlow : u≤a.positiveOriginMassCoverBase
  · exact Or.inl (le_min hlow hu.2)
  · have hret : u∈Ioc (max (a.alpha.val.val cap.left) a.positiveOriginMassCoverBase)
        (a.alpha.val.val cap.right):=⟨max_lt hA (lt_of_not_ge hlow),hB.le⟩
    obtain ⟨i,hi⟩:=nativeBroadSlice_cover a.positiveOriginMassCoverBase
      (max (a.alpha.val.val cap.left) a.positiveOriginMassCoverBase)
      (a.alpha.val.val cap.right) f.hgap hret
    refine Or.inr ⟨i,?_⟩
    exact (m.massSlice_quantile_mem (f.nodes_mem i).1 (f.nodes_mem i).2 hu).mpr
      ⟨hi.1,lt_of_le_of_ne hi.2 (fun he=>hcuts ⟨i,he.symm⟩)⟩

end PositiveOriginWholeCapBroadSampler
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
