module

public import PhysicalOverlapClockIncrement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _=>Classical.propDecidable _
set_option maxHeartbeats 1000000

theorem physicalOrderedPathS_increment_le_clock (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u v : ℝ} (hu : u∈Ioc (0:ℝ) 1) (hv : v∈Ioc (0:ℝ) 1) (huv : u ≤ v) :
    orderedPathS (n+1) b h v-orderedPathS (n+1) b h u ≤
      physicalOverlapEnergyConstant (n+1)*∑ k,
        ((completedPathClock (n+1) b h v k:ℝ)-(completedPathClock (n+1) b h u k:ℝ)) := by
  let q := completedPathClock (n+1) b h
  let u' : PositiveMass := ⟨u,hu.1⟩
  let v' : PositiveMass := ⟨v,hv.1⟩
  let as := twoCutMasses u' v'
  have hq := completedPathClock_monotone (n+1) hb hh
  have ho (j : ℕ) : MassOrdered 0 (as j) := twoCutMasses_ordered u' v' hu.2 hv.2 j
  have hm (j : ℕ) : PartitionMesh (((j+1:ℕ):ℝ)⁻¹) 0 (as j) :=
    twoCutMasses_mesh u' v' hu.2 hv.2 j
  have he (j : ℕ) : partitionEnd 0 (as j)=1 :=
    insertMass_end u' _ hu.2 (insertMass_end v' _ hv.2 (uniformMasses_end j))
  have h₁ := retainedMoment_tendsto_all (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    q hq as _ ho hm he uniformMasses_mesh_tendsto u' hu.2
    (fun j=>(twoCutMasses_nodes u' v' j).1) (orderedOverlap (n+1))
  have h₂ := retainedMoment_tendsto_all (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    q hq as _ ho hm he uniformMasses_mesh_tendsto v' hv.2
    (fun j=>(twoCutMasses_nodes u' v' j).2) (orderedOverlap (n+1))
  have hlimit := h₂.sub h₁
  rw [←orderedPathPair_eq_completed (n+1) (by omega) b h hb hh _ hv,
    ←orderedPathPair_eq_completed (n+1) (by omega) b h hb hh _ hu] at hlimit
  apply le_of_tendsto hlimit
  apply Eventually.of_forall
  intro j
  have hi := physicalFiniteOverlap_increment_le_clock (n+1) d (by omega) e (q 0)
    (sampleClockSteps q 0 (as j)) (sampleClockSteps_ordered q _ (ho j)) huv
  have hvnode (k : FeatureIndex (n+1)) :
      partitionSample (fun r=>(q r k:ℝ)) 0 (as j) v=(q v k:ℝ) :=
    partitionSample_at_node _ _ (ho j) (twoCutMasses_nodes u' v' j).2
  have hunode (k : FeatureIndex (n+1)) :
      partitionSample (fun r=>(q r k:ℝ)) 0 (as j) u=(q u k:ℝ) :=
    partitionSample_at_node _ _ (ho j) (twoCutMasses_nodes u' v' j).1
  simp_rw [sampleClockSteps_function q hq _ (ho j),hvnode,hunode] at hi
  exact hi

theorem physicalOrderedPathS_abs_sub_le_clock (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u v : ℝ} (hu : u∈Ioc (0:ℝ) 1) (hv : v∈Ioc (0:ℝ) 1) :
    |orderedPathS (n+1) b h v-orderedPathS (n+1) b h u| ≤
      physicalOverlapEnergyConstant (n+1)*∑ k,
        |(completedPathClock (n+1) b h v k:ℝ)-(completedPathClock (n+1) b h u k:ℝ)| := by
  have hmono := (orderedPath_SK_monotone (n+1) (by omega) b h hb hh).1
  have hq := completedPathClock_monotone (n+1) hb hh
  rcases le_total u v with huv|hvu
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hu hv huv))]
    have hi := physicalOrderedPathS_increment_le_clock n d e b h hb hh hu hv huv
    have he (k : FeatureIndex (n+1)) :
        |(completedPathClock (n+1) b h v k:ℝ)-(completedPathClock (n+1) b h u k:ℝ)|=
        (completedPathClock (n+1) b h v k:ℝ)-(completedPathClock (n+1) b h u k:ℝ) :=
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hq k (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hv) huv))
    simp_rw [he]
    exact hi
  · rw [abs_sub_comm]
    have hi := physicalOrderedPathS_increment_le_clock n d e b h hb hh hv hu hvu
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono hv hu hvu))]
    have he (k : FeatureIndex (n+1)) :
        |(completedPathClock (n+1) b h v k:ℝ)-(completedPathClock (n+1) b h u k:ℝ)|=
        (completedPathClock (n+1) b h u k:ℝ)-(completedPathClock (n+1) b h v k:ℝ) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hq k (Ioc_subset_Icc_self hv) (Ioc_subset_Icc_self hu) hvu))
    simp_rw [he]
    exact hi

theorem physicalOrderedPathS_comp_lipschitzOn (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (R : ℝ→ℝ) (A : Set ℝ) (K : ℝ≥0)
    (hR : MapsTo R A (Ioc (0:ℝ) 1))
    (hclock : ∀k,LipschitzOnWith K (fun r=>(completedPathClock (n+1) b h (R r) k:ℝ)) A) :
    LipschitzOnWith ((physicalOverlapEnergyConstant (n+1)).toNNReal*K*
      (Fintype.card (FeatureIndex (n+1)):ℝ≥0))
      (fun r=>orderedPathS (n+1) b h (R r)) A := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  have hi := physicalOrderedPathS_abs_sub_le_clock n d e b h hb hh (hR hy) (hR hx)
  apply hi.trans
  have hc : 0 ≤ physicalOverlapEnergyConstant (n+1) := physicalOverlapEnergyConstant_nonneg _
  have hs : (∑ k : FeatureIndex (n+1),
      |(completedPathClock (n+1) b h (R x) k:ℝ)-(completedPathClock (n+1) b h (R y) k:ℝ)|) ≤
      ∑ k : FeatureIndex (n+1),(K:ℝ)*dist x y := by
    apply Finset.sum_le_sum
    intro k _
    simpa only [Real.dist_eq] using (hclock k).dist_le_mul x hx y hy
  have hh' := mul_le_mul_of_nonneg_left hs hc
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh'
  simp only [NNReal.coe_mul,NNReal.coe_natCast,Real.coe_toNNReal', max_eq_left hc]
  convert hh' using 1 <;> ring

theorem physicalOrderedPathS_comp_absolutelyContinuous (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (R : ℝ→ℝ) {a z : ℝ} (K : ℝ≥0)
    (hR : MapsTo R (uIcc a z) (Ioc (0:ℝ) 1))
    (hclock : ∀k,LipschitzOnWith K (fun r=>(completedPathClock (n+1) b h (R r) k:ℝ)) (uIcc a z)) :
    AbsolutelyContinuousOnInterval (fun r=>orderedPathS (n+1) b h (R r)) a z :=
  (physicalOrderedPathS_comp_lipschitzOn n d e b h hb hh R _ K hR hclock).absolutelyContinuousOnInterval

end OAI.SKFluctuations.LaplaceWindowFormalization
