module

public import ComparisonSignedCavityActualMinimumResampling
public import ComparisonSignedCavityLocalInnovation

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Cavity

theorem exists_observed_rest_pre_high_innovation
    (n : ℕ) (hn : 0<n) {m delta cl cu Az C0 Ct D Bclock mesh v : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hlog : 1 ≤ Real.log M.context.N) (hnd : 1/M.context.N ≤ M.context.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0<v) (hsmall : mesh/M.context.floor ≤ v/16)
    {low high w : ℕ} (hhigh : high ≤ as.length) (hhw : high ≤ w) (hw : w ≤ as.length+1)
    (hvr : M.R (partitionPoint 0 as high)=v)
    (hlow : M.R (partitionPoint 0 as low) ≤ v/2) (hz : M.z ≤ v/2) :
    let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
    ∃ pre : ℕ,low ≤ pre ∧ pre ≤ high ∧ cl*v/2 ≤ partitionPoint 0 as pre ∧
      let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
        (cutSlice steps pre high)
      0<duration ∧ laplaceComparisonStrength M.context.d M.lam v*v/
        (12*Real.log M.context.N) ≤ duration ∧ duration ≤ Bclock ∧
      PhysicalProjectionClock n steps low high w (cl*v/2) duration ∧
      PhysicalProjectionClock n (steps.drop low) 0 (high-low) (w-low) (cl*v/2) duration := by
  have hN : 1 ≤ M.context.N := by
    change (1:ℝ) ≤ ((n+1:ℕ):ℝ)
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hreg : ∀r∈Icc (v/2) v,cl*r ≤ M.alpha.val.val r := by
    intro r hr
    apply (M.regular r ⟨hz.trans hr.1,?_⟩).1
    exact hr.2.trans (by rw [←hvr];exact (comparisonSweepQuantile_bounds M.context.hc
      M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha _).2)
  obtain ⟨pre,hafter,hbefore,hmass,hpos,hdr,hclock⟩ :=
    exists_actual_comparison_pre_high_innovation n hn M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha M.b M.h M.hb M.hlb M.hh M.hh0
      hN hlog M.context.hd hnd M.hlam M.hld as ho hmesh hpart hv hsmall hcl
      hhigh hhw hw hvr hlow hreg
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb
    M.hb M.hh M.hh0 M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1):=toNNReal_monotoneOn had.1
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1):=toNNReal_monotoneOn had.2.1
  let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
  let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre high)
  have he : duration=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
      (cutSlice (sampleClockSteps (completedPathClock n M.bf M.hf) 0 as) pre high) := by
    rw [actual_completed_sample_field_duration_slice n hn M.bf M.hf hbf hhf as ho hbefore hhigh]
    exact native_sampled_field_duration_slice n M.bf M.hf hbf hhf as ho ⟨0,hn⟩ hbefore hhigh
  have hDB : duration ≤ Bclock := by
    dsimp only [duration,steps]
    rw [native_sampled_field_duration_slice n M.bf M.hf hbf hhf as ho ⟨0,hn⟩ hbefore hhigh]
    have Hhigh:=hhf (partitionPoint_mem as ho high) (by simp : (1:ℝ)∈Icc 0 1)
      (partitionPoint_mem as ho high).2
    have Hpre:=hhf (by simp : (0:ℝ)∈Icc 0 1) (partitionPoint_mem as ho pre)
      (partitionPoint_mem as ho pre).1
    have Hbudget : (M.hf 1:ℝ)-(M.hf 0:ℝ) ≤ Bclock:=M.clockBudget
    have HhighR : (M.hf (partitionPoint 0 as high):ℝ) ≤ (M.hf 1:ℝ) := by exact_mod_cast Hhigh
    have HpreR : (M.hf 0:ℝ) ≤ (M.hf (partitionPoint 0 as pre):ℝ) := by exact_mod_cast Hpre
    linarith
  have hc : PhysicalProjectionClock n steps low high w (cl*v/2) duration :=
    native_sampled_field_layer_projection_clock n M.bf M.hf as ho ⟨0,hn⟩ (by positivity)
      hafter hbefore hhw hhigh hw hmass
  refine ⟨pre,hafter,hbefore,hmass,?_,?_,hDB,hc,actual_physical_projection_clock_suffix hc⟩
  · change 0<duration
    rw [he]
    exact hpos
  · change laplaceComparisonStrength M.context.d M.lam v*v/
      (12*Real.log M.context.N) ≤ duration
    rw [he]
    exact hdr

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
