module

public import ComparisonNativeMasterCapFibre

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
theorem comparison_retained_cap_unit_endpoint_geometry_master {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ)
    {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (haz : a<z)
    (haD : α.val.val a∈D) (hzD : α.val.val z∈D)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps clock 0
      (finiteCutMasses us m)).length+1)))
    (unit : Fin ((sampleClockSteps clock 0
      (finiteCutMasses us m)).length+1)→Fin K) (u : Fin K)
    (hfilter : J.filter (fun i=>unit i=u)=
      (completeMassCapCells (sampleClockSteps clock 0
        (finiteCutMasses us m)) (α.val.val a) (α.val.val z)).erase
          (finiteBoundaryClockCell clock (finiteCutMasses us m) (α.val.val a)))
    (p q : Fin ((sampleClockSteps clock 0
      (finiteCutMasses us m)).length+1))
    (hp : p∈J) (hq : q∈J) (hpu : unit p=u) (hqu : unit q=u)
    (hfirst : ∀j∈J,unit j=u→p ≤ j) (hlast : ∀j∈J,unit j=u→j ≤ q) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps clock 0 as
    let mesh : ℝ := ((m+1:ℕ):ℝ)⁻¹
    p.val < as.length ∧ q.val < as.length ∧
    α.val.val a ≤ physicalCutMass 0 steps p.val ∧
    physicalCutMass 0 steps (q.val+1) ≤ α.val.val z ∧
    α.val.val z-α.val.val a-mesh ≤ physicalSelectedUnitMass steps J unit u ∧
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as p.val)-a| ≤ mesh/c ∧
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (q.val+1))-z| ≤ mesh/c := by
  dsimp only
  let as := finiteCutMasses us m
  let steps := sampleClockSteps clock 0 as
  let mesh : ℝ := ((m+1:ℕ):ℝ)⁻¹
  have hnode := hnodes
  have ho : MassOrdered 0 as := finiteCutMasses_ordered _ hnode m
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property ha hz haz
  have hleftnode := masterBoundaryMassIndex_exact clock D hD us hnodes hretain m haD
  have hrightnode := masterBoundaryMassIndex_exact clock D hD us hnodes hretain m hzD
  change physicalCutMass 0 steps (finiteBoundaryMassIndex (α.val.val a) as)=α.val.val a at hleftnode
  change physicalCutMass 0 steps (finiteBoundaryMassIndex (α.val.val z) as)=α.val.val z at hrightnode
  have hidxBound : finiteBoundaryMassIndex (α.val.val z) as ≤ as.length := by
    unfold finiteBoundaryMassIndex
    split_ifs
    · omega
    · exact retainedMassPrefixIndex_le_length _ _
  have hrow (i : Fin (steps.length+1)) (hi : i∈J) (hiu : unit i=u) :
      i.val < as.length ∧ α.val.val a ≤ physicalCutMass 0 steps i.val ∧
        physicalCutMass 0 steps (i.val+1) ≤ α.val.val z := by
    have hif : i∈J.filter (fun j=>unit j=u) := Finset.mem_filter.mpr ⟨hi,hiu⟩
    rw [hfilter] at hif
    have hic := (Finset.mem_erase.mp hif).2
    obtain ⟨hip,him⟩ := (Finset.mem_filter.mp hic).2
    have hiidx : finiteBoundaryMassIndex (α.val.val a) as ≤ i.val ∧
        i.val < finiteBoundaryMassIndex (α.val.val z) as := by
      rw [←hleftnode,←hrightnode] at him
      exact (physicalCellMassMidpoint_mem_iff_interval steps hs _ _ i hip).mp him
    refine ⟨hiidx.2.trans_le hidxBound,?_,?_⟩
    · rw [←hleftnode]
      exact physicalCutMass_monotone steps hs hiidx.1
    · rw [←hrightnode]
      exact physicalCutMass_monotone steps hs (by omega)
  have hpr := hrow p hp hpu
  have hqr := hrow q hq hqu
  have hfull : α.val.val z-α.val.val a-mesh ≤ physicalSelectedUnitMass steps J unit u := by
    rw [physicalSelectedUnitMass_eq_window_filter,hfilter,
      masterBoundaryMass_cap_erase_initial_mass clock D hD us hnodes hretain m haD hzD hstrict]
    have hm := sampled_physicalMass_mesh clock as (finiteCutMasses_mesh _ hnode m)
      (finiteBoundaryClockCell clock as (α.val.val a))
    rw [←pathMassDifferences_eq_cutMass] at hm
    linarith
  have hb := comparison_selected_unit_endpoint_radius_bounds hc hk hkc hm hM clock α
    as ho J unit p q hp hq (hpu.trans hqu.symm) hpr.1 hqr.1
    (fun j hj hu=>hfirst j hj (hu.trans hpu)) (fun j hj hu=>hlast j hj (hu.trans hqu))
    ha hz hpr.2.1 hqr.2.2 (by simpa only [hpu] using hfull)
  exact ⟨hpr.1,hqr.1,hpr.2.1,hqr.2.2,hfull,hb.1,hb.2⟩

theorem comparison_retained_cap_unit_endpoint_coordinates_tendsto_master {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us)
    (ms : ℕ→ℕ) (hms : Tendsto ms atTop atTop)
    {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (haz : a<z)
    (haD : α.val.val a∈D) (hzD : α.val.val z∈D)
    (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps clock 0
      (finiteCutMasses us (ms j))).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps clock 0
      (finiteCutMasses us (ms j))).length+1)→Fin (K j))
    (u : ∀j,Fin (K j)) (x : ℕ→ℕ→ℝ) (h0 : ∀j,x j 0=0)
    (hmass : ∀j,∀v : Fin (K j),physicalSelectedUnitMass (sampleClockSteps clock 0
      (finiteCutMasses us (ms j))) (J j) (unit j) v=
        x j (v.val+1)-x j v.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set _))
    (hfilter : ∀j,(J j).filter (fun i=>unit j i=u j)=
      (completeMassCapCells (sampleClockSteps clock 0
        (finiteCutMasses us (ms j))) (α.val.val a) (α.val.val z)).erase
          (finiteBoundaryClockCell clock (finiteCutMasses us (ms j)) (α.val.val a)))
    (p q : ∀j,Fin ((sampleClockSteps clock 0
      (finiteCutMasses us (ms j))).length+1))
    (hp : ∀j,p j∈J j) (hq : ∀j,q j∈J j)
    (hpu : ∀j,unit j (p j)=u j) (hqu : ∀j,unit j (q j)=u j)
    (hfirst : ∀m,∀j∈J m,unit m j=u m→p m ≤ j)
    (hlast : ∀m,∀j∈J m,unit m j=u m→j ≤ q m)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM clock α
      (finiteCutMasses us (ms j))
      (finiteCutMasses_ordered _ (hnodes) (ms j))
      (J j)) atTop (𝓝 f)) :
    Tendsto (fun j=>x j (u j).val) atTop (𝓝 (f ⟨a,ha⟩)) ∧
    Tendsto (fun j=>x j ((u j).val+1)) atTop (𝓝 (f ⟨z,hz⟩)) ∧
    f ⟨z,hz⟩-f ⟨a,ha⟩=α.val.val z-α.val.val a ∧ f ⟨a,ha⟩ < f ⟨z,hz⟩ := by
  let as := fun j=>finiteCutMasses us (ms j)
  have hnode := hnodes
  let ho := fun j=>finiteCutMasses_ordered _ hnode (ms j)
  let mesh := fun j=>(((ms j)+1:ℕ):ℝ)⁻¹
  have hmeshlim : Tendsto mesh atTop (𝓝 0) := uniformMasses_mesh_tendsto.comp hms
  have hg j := comparison_retained_cap_unit_endpoint_geometry_master hc hk hkc hm hM clock α
    D hD us hnodes hretain (ms j) ha hz haz haD hzD (J j) (unit j) (u j) (hfilter j)
    (p j) (q j) (hp j) (hq j) (hpu j) (hqu j) (hfirst j) (hlast j)
  have hcoords := comparison_selected_unit_endpoint_coordinates_tendsto hc hk hkc hm hM
    clock α as ho (fun j=>finiteCutMasses_end _ hnode (ms j)) K J unit x h0 hmass horder
    p q hp hq (fun j=>(hpu j).trans (hqu j).symm) (fun j=>(hg j).1)
    (fun j=>(hg j).2.1) (fun m j hj hu=>hfirst m j hj (hu.trans (hpu m)))
    (fun m j hj hu=>hlast m j hj (hu.trans (hqu m))) ha hz mesh hmeshlim
    (fun j=>(hg j).2.2.1) (fun j=>(hg j).2.2.2.1)
    (fun j=>by simpa only [hpu j] using (hg j).2.2.2.2.1) f huniform
  have hleftlim : Tendsto (fun j=>x j (u j).val) atTop (𝓝 (f ⟨a,ha⟩)) := by
    simpa only [hpu] using hcoords.1
  have hrightlim : Tendsto (fun j=>x j ((u j).val+1)) atTop (𝓝 (f ⟨z,hz⟩)) := by
    simpa only [hpu] using hcoords.2
  let mu := fun j=>physicalSelectedUnitMass (sampleClockSteps clock 0 (as j)) (J j) (unit j) (u j)
  have hmuUpper j : mu j ≤ α.val.val z-α.val.val a := by
    have hh := physicalSelectedUnitMass_le_endpoint_span (sampleClockSteps clock 0 (as j))
      (sampleClockSteps_ordered clock (as j) (ho j)) (J j) (unit j)
      (p j) (q j) (hp j) (hq j) ((hpu j).trans (hqu j).symm)
      (fun i hi hu=>hfirst j i hi (hu.trans (hpu j)))
      (fun i hi hu=>hlast j i hi (hu.trans (hqu j)))
    simp only [hpu j] at hh
    linarith [(hg j).2.2.1,(hg j).2.2.2.1]
  have hmuAbs j : |mu j-(α.val.val z-α.val.val a)| ≤ mesh j := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hmuUpper j))]
    linarith [(hg j).2.2.2.2.1]
  have hmuLim : Tendsto mu atTop (𝓝 (α.val.val z-α.val.val a)) := by
    have ht := squeeze_zero (fun _=>abs_nonneg _) hmuAbs hmeshlim
    have hs : Tendsto (fun j=>mu j-(α.val.val z-α.val.val a)) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using ht)
    simpa only [sub_add_cancel,zero_add] using hs.add_const (α.val.val z-α.val.val a)
  have hmuCoord : (fun j=>x j ((u j).val+1)-x j (u j).val)=mu := by
    funext j
    exact (hmass j (u j)).symm
  have hsep : f ⟨z,hz⟩-f ⟨a,ha⟩=α.val.val z-α.val.val a := by
    have hh := hrightlim.sub hleftlim
    rw [hmuCoord] at hh
    exact tendsto_nhds_unique hh hmuLim
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property ha hz haz
  exact ⟨hleftlim,hrightlim,hsep,by linarith⟩

end

end OAI.SKFluctuations.LaplaceWindowFormalization
