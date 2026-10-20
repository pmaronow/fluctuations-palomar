module

public import ChildMovementGain
public import ContinuousPartitionSum

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology

theorem actual_path_cumulative_chord (n : ℕ) (hn : 0<n) (b h b' h' : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (hba : ∀u∈Icc (0:ℝ) 1,b u ≤ b' u)
    (hzero : ∀u∈Icc (0:ℝ) 1,b u=b' u → h u=h' u)
    (hcost : ContinuousOn (fun u=>(h u-h' u)^2/(b' u-b u)) (Icc (0:ℝ) 1))
    (x : OrderedFeatureIndex n→ℝ) :
    realOrderedSKPathPressure n b' h' x ≤ realOrderedSKPathPressure n b h x+
      (1/4:ℝ)*(∫u in (0:ℝ)..1,(h u-h' u)^2/(b' u-b u)) := by
  apply le_of_tendsto_of_tendsto (orderedSKPressure_samples_tendsto n hn b' h' hb' hh' hb0' hh0' x)
    ((orderedSKPressure_samples_tendsto n hn b h hb hh hb0 hh0 x).add
      ((continuous_partitionSum_tendsto hcost).const_mul (1/4:ℝ)))
  apply Eventually.of_forall
  intro k
  let as := uniformMasses k
  have ha : MassOrdered 0 as := uniformMasses_ordered k
  exact orderedSK_cumulative_chord n hn as ha.pairwise ha.members_le_one
    (fun j=>b (partitionPoint 0 as j)) (fun j=>h (partitionPoint 0 as j))
    (fun j=>b' (partitionPoint 0 as j)) (fun j=>h' (partitionPoint 0 as j))
    (comp_partitionPoint_monotone hb as ha) (comp_partitionPoint_monotone hh as ha)
    (comp_partitionPoint_monotone hb' as ha) (comp_partitionPoint_monotone hh' as ha)
    (by simpa [partitionPoint] using hb0) (by simpa [partitionPoint] using hh0)
    (by simpa [partitionPoint] using hb0') (by simpa [partitionPoint] using hh0')
    (fun j _=>hba _ (partitionPoint_mem as ha j))
    (fun j _ he=>hzero _ (partitionPoint_mem as ha j) he) x

theorem actual_path_movement_gain
    (n : ℕ) (hn : 0<n) (b h e r D z eh rhat omega : ℝ→ℝ)
    (he : ∀u∈Icc (0:ℝ) 1,0 ≤ e u) (hD : ∀u∈Icc (0:ℝ) 1,0<D u)
    (hw0 : ∀u∈Icc (0:ℝ) 1,0 ≤ omega u)
    (hw : ∀u∈Icc (0:ℝ) 1,omega u<D u/(e u+D u))
    (hehat : ∀u∈Icc (0:ℝ) 1,eh u ≤ e u/(1-omega u))
    (hrhat : ∀u∈Icc (0:ℝ) 1,rhat u=r u+omega u*(z u-r u))
    (hec : ContinuousOn e (Icc (0:ℝ) 1)) (hDc : ContinuousOn D (Icc (0:ℝ) 1))
    (hehc : ContinuousOn eh (Icc (0:ℝ) 1)) (hrc : ContinuousOn r (Icc (0:ℝ) 1))
    (hzc : ContinuousOn z (Icc (0:ℝ) 1)) (hrhc : ContinuousOn rhat (Icc (0:ℝ) 1))
    (hqb : MonotoneOn (fun u=>b u-e u-D u) (Icc (0:ℝ) 1))
    (hqh : MonotoneOn (fun u=>h u+e u*r u+D u*z u) (Icc (0:ℝ) 1))
    (htb : MonotoneOn (fun u=>b u-eh u) (Icc (0:ℝ) 1))
    (hth : MonotoneOn (fun u=>h u+eh u*rhat u) (Icc (0:ℝ) 1))
    (hqb0 : 0 ≤ b 0-e 0-D 0) (hqh0 : 0 ≤ h 0+e 0*r 0+D 0*z 0)
    (htb0 : 0 ≤ b 0-eh 0) (hth0 : 0 ≤ h 0+eh 0*rhat 0)
    (x : OrderedFeatureIndex n→ℝ) :
    (∫u in (0:ℝ)..1,e u*(rhat u-r u)*(z u-r u)) ≤
      4*(pathCompensatedPressure n b h e r x-pathCompensatedPressure n b h eh rhat x+
        pathCompensatedPressure n (fun u=>b u-e u) (fun u=>h u+e u*r u) D z x-
          realOrderedSKPathPressure n (fun u=>b u-e u) (fun u=>h u+e u*r u) x) := by
  let cost := fun u=>(e u*r u+D u*z u-eh u*rhat u)^2/(e u+D u-eh u)
  have hpos (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : 0<e u+D u-eh u :=
    (movement_strength_positive (he u hu) (hD u hu) (hw0 u hu) (hw u hu) (hehat u hu)).2
  have hcost : ContinuousOn cost (Icc (0:ℝ) 1) :=
    (((hec.mul hrc).add (hDc.mul hzc)).sub (hehc.mul hrhc)).pow 2 |>.div
      ((hec.add hDc).sub hehc) (fun u hu=>(hpos u hu).ne')
  have hcost' : ContinuousOn (fun u=>(h u+e u*r u+D u*z u-(h u+eh u*rhat u))^2/
      (b u-eh u-(b u-e u-D u))) (Icc (0:ℝ) 1) := by
    convert hcost using 1
    ext u
    congr 1 <;> ring
  have hchord := actual_path_cumulative_chord n hn
    (fun u=>b u-e u-D u) (fun u=>h u+e u*r u+D u*z u)
    (fun u=>b u-eh u) (fun u=>h u+eh u*rhat u)
    hqb hqh htb hth hqb0 hqh0 htb0 hth0
    (fun u hu=>by linarith [hpos u hu])
    (fun u hu hz=>by exfalso;linarith [hpos u hu]) hcost' x
  have hid (u : ℝ) : (h u+e u*r u+D u*z u-(h u+eh u*rhat u))^2/
      (b u-eh u-(b u-e u-D u))=cost u := by dsimp [cost];congr 1 <;> ring
  simp_rw [hid] at hchord
  have hiE : IntervalIntegrable (fun u=>e u*(r u)^2) volume 0 1 :=
    (hec.mul (hrc.pow 2)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hiD : IntervalIntegrable (fun u=>D u*(z u)^2) volume 0 1 :=
    (hDc.mul (hzc.pow 2)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hiH : IntervalIntegrable (fun u=>eh u*(rhat u)^2) volume 0 1 :=
    (hehc.mul (hrhc.pow 2)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hiC := hcost.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hiG : IntervalIntegrable (fun u=>e u*(rhat u-r u)*(z u-r u)) volume 0 1 :=
    (hec.mul (hrhc.sub hrc) |>.mul (hzc.sub hrc)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hbound : (∫u in (0:ℝ)..1,e u*(rhat u-r u)*(z u-r u)) ≤
      ∫u in (0:ℝ)..1,e u*(r u)^2+D u*(z u)^2-eh u*(rhat u)^2-cost u := by
    apply intervalIntegral.integral_mono_on zero_le_one hiG (((hiE.add hiD).sub hiH).sub hiC)
    intro u hu
    change e u*(rhat u-r u)*(z u-r u) ≤ e u*(r u)^2+D u*(z u)^2-eh u*(rhat u)^2-cost u
    have hs := movement_pointwise_gain (r := r u) (z := z u)
      (he u hu) (hD u hu) (hw0 u hu) (hw u hu) (hehat u hu)
    rw [←hrhat u hu] at hs
    have hid : e u*(rhat u-r u)*(z u-r u)=e u*omega u*(z u-r u)^2 := by
      rw [hrhat u hu]
      ring
    rw [hid]
    exact hs
  rw [intervalIntegral.integral_sub ((hiE.add hiD).sub hiH) hiC,
    intervalIntegral.integral_sub (hiE.add hiD) hiH,
    intervalIntegral.integral_add hiE hiD] at hbound
  unfold pathCompensatedPressure
  dsimp only
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
