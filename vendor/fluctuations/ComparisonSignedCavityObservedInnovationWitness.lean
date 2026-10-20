module

public import ComparisonSignedCavityObservedRestInnovation

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem physical_homogeneous_field_finite_clock (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (i₀ : Fin n)
    (hhom : ∀st∈steps,∀i : Fin n,st.2 (Sum.inl i)=st.2 (Sum.inl i₀)) :
    ∃d : Fin steps.length → ℝ,
      (∀j,0 ≤ d j) ∧
      (∑j,d j)=physicalFieldDuration (fun st=>st.2 (Sum.inl i₀)) steps ∧
      (∀j i,(hierarchyClocks steps j (Sum.inl i):ℝ)=d j) := by
  let d : Fin steps.length → ℝ:=fun j=>((steps.get j).2 (Sum.inl i₀):ℝ)
  refine ⟨d,fun j=>NNReal.coe_nonneg _,?_,?_⟩
  · dsimp only [d,physicalFieldDuration]
    rw [←NNReal.coe_sum]
    congr 1
    rw [←List.sum_ofFn]
    conv_rhs => rw [←List.ofFn_get steps,List.map_ofFn]
    rfl
  · intro j i
    rw [hierarchyClocks_get]
    exact congrArg NNReal.toReal (hhom _ (List.get_mem _ _) i)

theorem cutSlice_append_cutSlice_eq {α : Type*} (steps : List α)
    {low pre high : ℕ} (hlp : low ≤ pre) (hph : pre ≤ high) :
    cutSlice steps low pre ++ cutSlice steps pre high=cutSlice steps low high := by
  have H:=List.take_add (l:=steps.drop low) (i:=pre-low) (j:=high-pre)
  have he : pre-low+(high-pre)=high-low := by omega
  simpa only [cutSlice,he,List.drop_drop,Nat.add_sub_of_le hlp] using H.symm

theorem native_observed_innovation_finite_witness
    (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i₀ : Fin n) {a : ℝ} (ha : 0 ≤ a) {low pre high : ℕ}
    (hlp : low ≤ pre) (hph : pre ≤ high) (hhigh : high ≤ as.length)
    (hmass : a ≤ partitionPoint 0 as pre) :
    let steps:=nativeSampledPhysicalSteps n b h as
    let innovation:=cutSlice steps pre high
    let skip:=cutSlice steps low pre
    (steps.drop low).take (high-low)=skip++innovation ∧
    (steps.drop low).drop (high-low)=steps.drop high ∧
    OrderedSteps a (innovation++steps.drop high) ∧
    ∃d : Fin innovation.length → ℝ,
      (∀j,0 ≤ d j) ∧
      (∑j,d j)=physicalFieldDuration (fun st=>st.2 (Sum.inl i₀)) innovation ∧
      (∀j i,(hierarchyClocks innovation j (Sum.inl i):ℝ)=d j) := by
  dsimp only
  let steps:=nativeSampledPhysicalSteps n b h as
  have hs : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hm : a ≤ physicalCutMass 0 steps pre := by
    simpa only [steps,nativeSampledPhysicalSteps,
      physicalCutMass_sampleClockSteps _ _ _ pre (hph.trans hhigh)] using hmass
  refine ⟨(cutSlice_append_cutSlice_eq steps hlp hph).symm,?_,?_,?_⟩
  · rw [List.drop_drop,Nat.add_sub_of_le (hlp.trans hph)]
  · rw [cutSlice_append_drop steps hph]
    exact (orderedSteps_drop_cutMass steps hs pre).lower ha hm
  · apply physical_homogeneous_field_finite_clock n _ i₀
    intro st hst i
    exact native_sampled_field_homogeneous n b h as i₀ st
      (List.mem_of_mem_drop (List.mem_of_mem_take hst)) i

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Cavity

theorem exists_observed_rest_finite_innovation
    (n : ℕ) (hn : 0<n) {m delta cl cu Az C0 Ct D Bclock mesh v : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hlog : 1 ≤ Real.log M.context.N) (hnd : 1/M.context.N ≤ M.context.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0<v) (hsmall : mesh/M.context.floor ≤ v/16)
    {low high : ℕ} (hhigh : high ≤ as.length)
    (hvr : M.R (partitionPoint 0 as high)=v)
    (hlow : M.R (partitionPoint 0 as low) ≤ v/2) (hz : M.z ≤ v/2) :
    let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
    ∃pre : ℕ,low ≤ pre ∧ pre ≤ high ∧ cl*v/2 ≤ partitionPoint 0 as pre ∧
      let innovation:=cutSlice steps pre high
      let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) innovation
      0<duration ∧ laplaceComparisonStrength M.context.d M.lam v*v/
        (12*Real.log M.context.N) ≤ duration ∧ duration ≤ Bclock ∧
      (steps.drop low).take (high-low)=cutSlice steps low pre++innovation ∧
      (steps.drop low).drop (high-low)=steps.drop high ∧
      OrderedSteps (cl*v/2) (innovation++steps.drop high) ∧
      ∃d : Fin innovation.length → ℝ,
        (∀j,0 ≤ d j) ∧ (∑j,d j)=duration ∧
        (∀j i,(hierarchyClocks innovation j (Sum.inl i):ℝ)=d j) := by
  obtain ⟨pre,hlp,hph,hmass,hpos,hlower,hupper,-,-⟩:=
    exists_observed_rest_pre_high_innovation n hn M hcl hlog hnd as ho hmesh hpart hv hsmall
      hhigh (w:=high) le_rfl (by omega) hvr hlow hz
  have H:=native_observed_innovation_finite_witness n M.bf M.hf as ho ⟨0,hn⟩
    (by positivity : 0 ≤ cl*v/2) hlp hph hhigh hmass
  exact ⟨pre,hlp,hph,hmass,hpos,hlower,hupper,H⟩

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
