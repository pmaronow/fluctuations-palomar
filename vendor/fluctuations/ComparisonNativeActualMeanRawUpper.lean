module

public import ComparisonNativeCavityConcentrationRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mass_mean_nonneg
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    0 ≤ orderedPathS (n+1) M.bf M.hf u := by
  by_cases hu0 : u = 0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero,le_refl]
  · let c := M.context
    have had := comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
      M.b M.h c.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
    have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
    have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
    exact (orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf hbf hhf
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).1

theorem mass_mean_monotone
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn (orderedPathS (n+1) M.bf M.hf) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  by_cases hu0 : u = 0
  · subst u
    simpa only [orderedPathS,orderedPathPair_zero] using M.mass_mean_nonneg hv
  · let c := M.context
    have had := comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
      M.b M.h c.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
    have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
    have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    exact (orderedPath_SK_monotone (n+1) (by omega) M.bf M.hf hbf hhf).1
      ⟨huPos,hu.2⟩ ⟨huPos.trans_le huv,hv.2⟩ huv

end NativeOverlapMinimum

theorem eventually_actual_minimum_mass_mean_upper
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,orderedPathS (n+1) M.bf M.hf u ≤ B*(M.xs+u) := by
  obtain ⟨C,hC,hraw⟩ := eventually_native_minimum_original_boundary_raw
    1 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hshift.eventually hraw] with n hnraw
  intro M u hu
  let up : PositiveMass := ⟨u,hu.1⟩
  obtain ⟨us,hus,huretain,_,hQ⟩ := hnraw M up hu.2 [] (by simp)
  let as := finiteCutMasses us
  let mesh := fun j:ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j : MassOrdered 0 (as j) := finiteCutMasses_ordered us hus j
  have he j : partitionEnd 0 (as j)=1 := finiteCutMasses_end us hus j
  have hmesh j : PartitionMesh (mesh j) 0 (as j) := finiteCutMasses_mesh us hus j
  have hQ' : ∀ᶠj : ℕ in atTop,
      (physicalRawRatio (n+1) 2 (sampleClockSteps (completedPathClock (n+1) M.bf M.hf) 0 (as j))
        0 M.xs (Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) M.bf M.hf 0 i))
        id measurable_id)^2 ≤ 2*C := by
    filter_upwards [hQ] with j hj
    exact hj.1
  let c := M.context
  have had := comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    M.b M.h c.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hretain j : ∃i≤(as j).length,partitionPoint 0 (as j) i=u :=
    cavity_partitionPoint_exists_of_mem (as j) (finiteCutMasses_nodes us j huretain) 0
  exact orderedPathS_le_retained_native_raw n 2 (by norm_num) M.bf M.hf hbf hhf
    as mesh ho he hmesh uniformMasses_mesh_tendsto hu.1 M.hxs hretain hQ'

end OAI.SKFluctuations.LaplaceWindowFormalization
