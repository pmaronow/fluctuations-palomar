module

public import ComparisonSelectedCumulativeCoordinates
public import ComparisonCapInteriorCutTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Filter Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 2400000

theorem selected_effective_coordinate_eq_mass_through_unit {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (x : ℕ→ℝ) (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (u : Fin K) :
    x (u.val+1)=∑i : Fin (steps.length+1),pathMassDifferences steps 0 i*
      (if i∈J ∧ unit i ≤ u then 1 else 0) := by
  have hx := finite_unit_coordinate_eq_cumulative x (physicalSelectedUnitMass steps J unit)
    h0 (fun v=>(hmass v).symm) (u.val+1) (by omega)
  have hg := selected_mass_grouping steps J unit (fun v=>if v ≤ u then 1 else 0)
  have he : (∑i : Fin (steps.length+1),pathMassDifferences steps 0 i*
      (if i∈J ∧ unit i ≤ u then 1 else 0))=
      ∑v : Fin K,if v.val< u.val+1 then physicalSelectedUnitMass steps J unit v else 0 := by
    calc
      _=∑i : Fin (steps.length+1),pathMassDifferences steps 0 i*
          (if i∈J then (if unit i ≤ u then 1 else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i∈J <;> simp [hi]
      _=∑v : Fin K,physicalSelectedUnitMass steps J unit v*(if v ≤ u then 1 else 0) := hg
      _=_ := by
        apply Finset.sum_congr rfl
        intro v _
        have hv : v ≤ u ↔ v.val< u.val+1 := by simp only [Fin.le_def];omega
        simp only [hv,mul_ite,mul_one,mul_zero]
  exact hx.trans he.symm

theorem selected_first_coordinate_eq_mass_before_row {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (x : ℕ→ℝ) (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin (steps.length+1))))
    (i : Fin (steps.length+1)) (hi : i∈J)
    (hfirst : ∀j∈J,unit j=unit i→i ≤ j) :
    x (unit i).val=∑j : Fin (steps.length+1),pathMassDifferences steps 0 j*
      (if j∈J ∧ j.val< i.val then 1 else 0) := by
  rw [selected_effective_coordinate_eq_mass_before_unit steps J unit x h0 hmass]
  apply Finset.sum_congr rfl
  intro j _
  have he : (j∈J ∧ unit j< unit i)↔(j∈J ∧ j.val< i.val) := by
    constructor
    · intro hj
      refine ⟨hj.1,?_⟩
      by_contra hno
      have hle := horder hi hj.1 (Fin.le_def.mpr (by omega))
      exact (not_le_of_gt hj.2) hle
    · intro hj
      have hji : j< i := Fin.lt_def.mpr hj.2
      refine ⟨hj.1,lt_of_le_of_ne (horder hj.1 hi hji.le) ?_⟩
      intro heq
      exact (not_le_of_gt hji) (hfirst j hj.1 heq)
  simp only [he]

theorem selected_last_coordinate_eq_mass_through_row {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (x : ℕ→ℝ) (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin (steps.length+1))))
    (i : Fin (steps.length+1)) (hi : i∈J)
    (hlast : ∀j∈J,unit j=unit i→j ≤ i) :
    x ((unit i).val+1)=∑j : Fin (steps.length+1),pathMassDifferences steps 0 j*
      (if j∈J ∧ j.val< i.val+1 then 1 else 0) := by
  rw [selected_effective_coordinate_eq_mass_through_unit steps J unit x h0 hmass]
  apply Finset.sum_congr rfl
  intro j _
  have he : (j∈J ∧ unit j ≤ unit i)↔(j∈J ∧ j.val< i.val+1) := by
    constructor
    · intro hj
      refine ⟨hj.1,?_⟩
      by_contra hno
      have hij : i< j := Fin.lt_def.mpr (by omega)
      have hle := horder hi hj.1 hij.le
      have heq : unit j=unit i := le_antisymm hj.2 hle
      exact (not_le_of_gt hij) (hlast j hj.1 heq)
    · intro hj
      exact ⟨hj.1,horder hj.1 hi (Fin.le_def.mpr (by omega))⟩
  simp only [he]

theorem selected_unit_first_last_exist {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (u : Fin K)
    (hpos : 0 < physicalSelectedUnitMass steps J unit u) :
    ∃p q : Fin (steps.length+1),p∈J ∧ q∈J ∧ unit p=u ∧ unit q=u ∧
      (∀j∈J,unit j=u→p ≤ j) ∧ (∀j∈J,unit j=u→j ≤ q) := by
  classical
  let F := J.filter (fun i=>unit i=u)
  have hF : F.Nonempty := by
    by_contra hno
    have hn : ∀i,¬(i∈J ∧ unit i=u) := by
      intro i hi
      exact hno ⟨i,Finset.mem_filter.mpr hi⟩
    have hz : physicalSelectedUnitMass steps J unit u=0 := by
      unfold physicalSelectedUnitMass
      simp only [hn,ite_false,Finset.sum_const_zero]
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  let p := F.min' hF
  let q := F.max' hF
  have hp := Finset.mem_filter.mp (Finset.min'_mem F hF)
  have hq := Finset.mem_filter.mp (Finset.max'_mem F hF)
  exact ⟨p,q,hp.1,hq.1,hp.2,hq.2,
    fun j hj hu=>Finset.min'_le F j (Finset.mem_filter.mpr ⟨hj,hu⟩),
    fun j hj hu=>Finset.le_max' F j (Finset.mem_filter.mpr ⟨hj,hu⟩)⟩

theorem physicalSelectedUnitMass_le_endpoint_span {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    (p q : Fin (steps.length+1)) (_hp : p∈J) (hq : q∈J) (hu : unit p=unit q)
    (hfirst : ∀j∈J,unit j=unit p→p ≤ j)
    (hlast : ∀j∈J,unit j=unit q→j ≤ q) :
    physicalSelectedUnitMass steps J unit (unit p) ≤
      physicalCutMass 0 steps (q.val+1)-physicalCutMass 0 steps p.val := by
  classical
  rw [physicalSelectedUnitMass_eq_window_filter]
  have hpq : p ≤ q := hfirst q hq hu.symm
  have hsub : J.filter (fun j=>unit j=unit p)⊆physicalIntervalCells steps p.val (q.val+1) := by
    intro j hj
    have hh := Finset.mem_filter.mp hj
    exact (mem_physicalIntervalCells steps _ _ j).mpr
      ⟨hfirst j hh.1 hh.2,Nat.lt_succ_of_le (hlast j hh.1 (hh.2.trans hu))⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _=>pathMassDifferences_nonneg steps ha j)
  change physicalWindowMass steps 0 (J.filter (fun j=>unit j=unit p)) ≤
    physicalWindowMass steps 0 (physicalIntervalCells steps p.val (q.val+1)) at hh
  rw [physicalIntervalMass steps 0 (show p.val ≤ q.val+1 by omega)
    (Nat.succ_le_of_lt q.isLt)] at hh
  exact hh

end OAI.SKFluctuations.WholeUnitSideKernel

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 2400000

theorem selectedCumulative_uniform_moving_eval_tendsto
    (F : ℕ→(Icc (0:ℝ) 1 →ᵇ ℝ)) (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (hF : Tendsto F atTop (𝓝 f)) (r : ℕ→Icc (0:ℝ) 1)
    (a : Icc (0:ℝ) 1) (hr : Tendsto r atTop (𝓝 a)) :
    Tendsto (fun j=>F j (r j)) atTop (𝓝 (f a)) := by
  exact (continuous_eval.tendsto (f,a)).comp (hF.prodMk_nhds hr)

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_selected_first_coordinate_eq_cumulative {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps clock 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set _))
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) (hi : i∈J)
    (hfirst : ∀j∈J,unit j=unit i→i ≤ j) :
    x (unit i).val=cumulativeCellMass
      (comparisonSelectedMassDensity hc hk hkc hm hM clock α as J)
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val)) := by
  rw [comparison_selected_cumulative_at_cut hc hk hkc hm hM clock α as ho he J]
  exact selected_first_coordinate_eq_mass_before_row _ J unit x h0 hmass horder i hi hfirst

theorem comparison_selected_last_coordinate_eq_cumulative {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps clock 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set _))
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) (hi : i∈J)
    (hlast : ∀j∈J,unit j=unit i→j ≤ i) :
    x ((unit i).val+1)=cumulativeCellMass
      (comparisonSelectedMassDensity hc hk hkc hm hM clock α as J)
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))) := by
  rw [comparison_selected_cumulative_at_cut hc hk hkc hm hM clock α as ho he J]
  exact selected_last_coordinate_eq_mass_through_row _ J unit x h0 hmass horder i hi hlast

theorem comparison_selected_unit_endpoint_radius_bounds {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K)
    (p q : Fin ((sampleClockSteps clock 0 as).length+1)) (hp : p∈J) (hq : q∈J)
    (hu : unit p=unit q) (hpl : p.val < as.length) (hql : q.val < as.length)
    (hfirst : ∀j∈J,unit j=unit p→p ≤ j)
    (hlast : ∀j∈J,unit j=unit q→j ≤ q)
    {a z loss : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (hleft : α.val.val a ≤ physicalCutMass 0 (sampleClockSteps clock 0 as) p.val)
    (hright : physicalCutMass 0 (sampleClockSteps clock 0 as) (q.val+1) ≤ α.val.val z)
    (hfull : α.val.val z-α.val.val a-loss ≤
      physicalSelectedUnitMass (sampleClockSteps clock 0 as) J unit (unit p)) :
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as p.val)-a| ≤ loss/c ∧
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (q.val+1))-z| ≤ loss/c := by
  let steps := sampleClockSteps clock 0 as
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hspan := physicalSelectedUnitMass_le_endpoint_span steps hs J unit p q hp hq hu hfirst hlast
  have hleftgap : |physicalCutMass 0 steps p.val-α.val.val a| ≤ loss := by
    rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
    linarith
  have hrightgap : |physicalCutMass 0 steps (q.val+1)-α.val.val z| ≤ loss := by
    rw [abs_of_nonpos (sub_nonpos.mpr hright)]
    linarith
  have hLp := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul
    (physicalCutMass 0 steps p.val) (α.val.val a)
  have hLq := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul
    (physicalCutMass 0 steps (q.val+1)) (α.val.val z)
  simp only [Real.dist_eq,comparisonSweepQuantile_at_profile hc hk hkc hm hM α ha,
    comparisonSweepQuantile_at_profile hc hk hkc hm hM α hz] at hLp hLq
  rw [physicalCutMass_sampleClockSteps clock 0 as p.val hpl.le] at hLp
  rw [physicalCutMass_sampleClockSteps clock 0 as (q.val+1) (by omega)] at hLq
  rw [physicalCutMass_sampleClockSteps clock 0 as p.val hpl.le] at hleftgap
  rw [physicalCutMass_sampleClockSteps clock 0 as (q.val+1) (by omega)] at hrightgap
  change |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as p.val)-a| ≤
    (1/c)*|partitionPoint 0 as p.val-α.val.val a| at hLp
  change |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (q.val+1))-z| ≤
    (1/c)*|partitionPoint 0 as (q.val+1)-α.val.val z| at hLq
  rw [one_div] at hLp hLq
  constructor
  · exact hLp.trans (by simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hleftgap (show 0 ≤ c⁻¹ by positivity))
  · exact hLq.trans (by simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hrightgap (show 0 ≤ c⁻¹ by positivity))

theorem comparison_selected_unit_endpoint_coordinates_tendsto {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps clock 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps clock 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (h0 : ∀j,x j 0=0)
    (hmass : ∀j,∀u : Fin (K j),physicalSelectedUnitMass
      (sampleClockSteps clock 0 (as j)) (J j) (unit j) u=x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set _))
    (p q : ∀j,Fin ((sampleClockSteps clock 0 (as j)).length+1))
    (hp : ∀j,p j∈J j) (hq : ∀j,q j∈J j) (hu : ∀j,unit j (p j)=unit j (q j))
    (hpl : ∀j,(p j).val < (as j).length) (hql : ∀j,(q j).val < (as j).length)
    (hfirst : ∀m,∀j∈J m,unit m j=unit m (p m)→p m ≤ j)
    (hlast : ∀m,∀j∈J m,unit m j=unit m (q m)→j ≤ q m)
    {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (loss : ℕ→ℝ) (hloss : Tendsto loss atTop (𝓝 0))
    (hleft : ∀j,α.val.val a ≤ physicalCutMass 0 (sampleClockSteps clock 0 (as j)) (p j).val)
    (hright : ∀j,physicalCutMass 0 (sampleClockSteps clock 0 (as j)) ((q j).val+1) ≤ α.val.val z)
    (hfull : ∀j,α.val.val z-α.val.val a-loss j ≤ physicalSelectedUnitMass
      (sampleClockSteps clock 0 (as j)) (J j) (unit j) (unit j (p j)))
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
      clock α (as j) (ho j) (J j)) atTop (𝓝 f)) :
    Tendsto (fun j=>x j (unit j (p j)).val) atTop (𝓝 (f ⟨a,ha⟩)) ∧
    Tendsto (fun j=>x j ((unit j (p j)).val+1)) atTop (𝓝 (f ⟨z,hz⟩)) := by
  let lefts := fun j=>comparisonSweepQuantile hc hk hkc hm hM α
    (partitionPoint 0 (as j) (p j).val)
  let rights := fun j=>comparisonSweepQuantile hc hk hkc hm hM α
    (partitionPoint 0 (as j) ((q j).val+1))
  have hbounds j := comparison_selected_unit_endpoint_radius_bounds hc hk hkc hm hM
    clock α (as j) (ho j) (J j) (unit j) (p j) (q j) (hp j) (hq j) (hu j)
    (hpl j) (hql j) (hfirst j) (hlast j) ha hz (hleft j) (hright j) (hfull j)
  have herror : Tendsto (fun j=>loss j/c) atTop (𝓝 0) := by
    simpa only [zero_div] using hloss.div_const c
  have hl : Tendsto lefts atTop (𝓝 a) := by
    have ht := squeeze_zero (fun _=>abs_nonneg _) (fun j=>(hbounds j).1) herror
    have hs : Tendsto (fun j=>lefts j-a) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using ht)
    simpa only [sub_add_cancel,zero_add] using hs.add_const a
  have hr : Tendsto rights atTop (𝓝 z) := by
    have ht := squeeze_zero (fun _=>abs_nonneg _) (fun j=>(hbounds j).2) herror
    have hs : Tendsto (fun j=>rights j-z) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using ht)
    simpa only [sub_add_cancel,zero_add] using hs.add_const z
  have hlI : Tendsto (fun j=>(⟨lefts j,comparisonSweepQuantile_bounds hc hk hkc hm hM α _⟩ :
      Icc (0:ℝ) 1)) atTop (𝓝 ⟨a,ha⟩) := tendsto_subtype_rng.mpr hl
  have hrI : Tendsto (fun j=>(⟨rights j,comparisonSweepQuantile_bounds hc hk hkc hm hM α _⟩ :
      Icc (0:ℝ) 1)) atTop (𝓝 ⟨z,hz⟩) := tendsto_subtype_rng.mpr hr
  have hleval := selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨a,ha⟩ hlI
  have hreval := selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨z,hz⟩ hrI
  have hleq : (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM clock α
      (as j) (ho j) (J j) ⟨lefts j,comparisonSweepQuantile_bounds hc hk hkc hm hM α _⟩)=
      (fun j=>x j (unit j (p j)).val) := by
    funext j
    exact (comparison_selected_first_coordinate_eq_cumulative hc hk hkc hm hM clock α
      (as j) (ho j) (he j) (J j) (unit j) (x j) (h0 j) (hmass j) (horder j)
      (p j) (hp j) (hfirst j)).symm
  have hreq : (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM clock α
      (as j) (ho j) (J j) ⟨rights j,comparisonSweepQuantile_bounds hc hk hkc hm hM α _⟩)=
      (fun j=>x j ((unit j (p j)).val+1)) := by
    funext j
    have hh := (comparison_selected_last_coordinate_eq_cumulative hc hk hkc hm hM clock α
      (as j) (ho j) (he j) (J j) (unit j) (x j) (h0 j) (hmass j) (horder j)
      (q j) (hq j) (hlast j)).symm
    change comparisonSelectedCumulativeMap hc hk hkc hm hM clock α (as j) (ho j) (J j)
      ⟨rights j,comparisonSweepQuantile_bounds hc hk hkc hm hM α _⟩=
        x j ((unit j (q j)).val+1) at hh
    simpa only [←hu j] using hh
  rw [hleq] at hleval
  rw [hreq] at hreval
  exact ⟨hleval,hreval⟩

theorem comparison_retained_cap_unit_endpoint_geometry {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (haz : a<z)
    (haD : α.val.val a∈D) (hzD : α.val.val z∈D)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) m)).length+1)))
    (unit : Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) m)).length+1)→Fin K) (u : Fin K)
    (hfilter : J.filter (fun i=>unit i=u)=
      (completeMassCapCells (sampleClockSteps clock 0
        (finiteCutMasses (finiteBoundaryMassNodes D) m)) (α.val.val a) (α.val.val z)).erase
          (finiteBoundaryClockCell clock (finiteCutMasses (finiteBoundaryMassNodes D) m) (α.val.val a)))
    (p q : Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) m)).length+1))
    (hp : p∈J) (hq : q∈J) (hpu : unit p=u) (hqu : unit q=u)
    (hfirst : ∀j∈J,unit j=u→p ≤ j) (hlast : ∀j∈J,unit j=u→j ≤ q) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let mesh : ℝ := ((m+1:ℕ):ℝ)⁻¹
    p.val < as.length ∧ q.val < as.length ∧
    α.val.val a ≤ physicalCutMass 0 steps p.val ∧
    physicalCutMass 0 steps (q.val+1) ≤ α.val.val z ∧
    α.val.val z-α.val.val a-mesh ≤ physicalSelectedUnitMass steps J unit u ∧
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as p.val)-a| ≤ mesh/c ∧
    |comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (q.val+1))-z| ≤ mesh/c := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  let mesh : ℝ := ((m+1:ℕ):ℝ)⁻¹
  have hnode := finiteBoundaryMassNodes_bound D (fun d hd=>(hD d hd).2)
  have ho : MassOrdered 0 as := finiteCutMasses_ordered _ hnode m
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property ha hz haz
  have hleftnode := finiteBoundaryMassIndex_exact clock D hD m haD
  have hrightnode := finiteBoundaryMassIndex_exact clock D hD m hzD
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
      finiteBoundaryMass_cap_erase_initial_mass clock D hD m haD hzD hstrict]
    have hm := sampled_physicalMass_mesh clock as (finiteCutMasses_mesh _ hnode m)
      (finiteBoundaryClockCell clock as (α.val.val a))
    rw [←pathMassDifferences_eq_cutMass] at hm
    linarith
  have hb := comparison_selected_unit_endpoint_radius_bounds hc hk hkc hm hM clock α
    as ho J unit p q hp hq (hpu.trans hqu.symm) hpr.1 hqr.1
    (fun j hj hu=>hfirst j hj (hu.trans hpu)) (fun j hj hu=>hlast j hj (hu.trans hqu))
    ha hz hpr.2.1 hqr.2.2 (by simpa only [hpu] using hfull)
  exact ⟨hpr.1,hqr.1,hpr.2.1,hqr.2.2,hfull,hb.1,hb.2⟩

theorem comparison_retained_cap_unit_endpoint_coordinates_tendsto {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (ms : ℕ→ℕ) (hms : Tendsto ms atTop atTop)
    {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (haz : a<z)
    (haD : α.val.val a∈D) (hzD : α.val.val z∈D)
    (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))).length+1)→Fin (K j))
    (u : ∀j,Fin (K j)) (x : ℕ→ℕ→ℝ) (h0 : ∀j,x j 0=0)
    (hmass : ∀j,∀v : Fin (K j),physicalSelectedUnitMass (sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))) (J j) (unit j) v=
        x j (v.val+1)-x j v.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set _))
    (hfilter : ∀j,(J j).filter (fun i=>unit j i=u j)=
      (completeMassCapCells (sampleClockSteps clock 0
        (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))) (α.val.val a) (α.val.val z)).erase
          (finiteBoundaryClockCell clock (finiteCutMasses (finiteBoundaryMassNodes D) (ms j)) (α.val.val a)))
    (p q : ∀j,Fin ((sampleClockSteps clock 0
      (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))).length+1))
    (hp : ∀j,p j∈J j) (hq : ∀j,q j∈J j)
    (hpu : ∀j,unit j (p j)=u j) (hqu : ∀j,unit j (q j)=u j)
    (hfirst : ∀m,∀j∈J m,unit m j=u m→p m ≤ j)
    (hlast : ∀m,∀j∈J m,unit m j=u m→j ≤ q m)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM clock α
      (finiteCutMasses (finiteBoundaryMassNodes D) (ms j))
      (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D (fun d hd=>(hD d hd).2)) (ms j))
      (J j)) atTop (𝓝 f)) :
    Tendsto (fun j=>x j (u j).val) atTop (𝓝 (f ⟨a,ha⟩)) ∧
    Tendsto (fun j=>x j ((u j).val+1)) atTop (𝓝 (f ⟨z,hz⟩)) ∧
    f ⟨z,hz⟩-f ⟨a,ha⟩=α.val.val z-α.val.val a ∧ f ⟨a,ha⟩ < f ⟨z,hz⟩ := by
  let as := fun j=>finiteCutMasses (finiteBoundaryMassNodes D) (ms j)
  have hnode := finiteBoundaryMassNodes_bound D (fun d hd=>(hD d hd).2)
  let ho := fun j=>finiteCutMasses_ordered _ hnode (ms j)
  let mesh := fun j=>(((ms j)+1:ℕ):ℝ)⁻¹
  have hmeshlim : Tendsto mesh atTop (𝓝 0) := uniformMasses_mesh_tendsto.comp hms
  have hg j := comparison_retained_cap_unit_endpoint_geometry hc hk hkc hm hM clock α
    D hD (ms j) ha hz haz haD hzD (J j) (unit j) (u j) (hfilter j)
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
