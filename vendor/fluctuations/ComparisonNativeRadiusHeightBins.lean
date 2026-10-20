module

public import ComparisonNativeVarianceBinGeometry
public import ComparisonNativeRadiusCellAverages
public import ComparisonSelectedUnitEndpointCoordinates
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable

namespace NativeRadiusHeight

def leftMass {N : ℕ} (v : Fin N→ℝ) (i : Fin N) : ℝ :=
  ∑j : Fin N,if j< i then v j else 0

def rightMass {N : ℕ} (v : Fin N→ℝ) (i : Fin N) : ℝ :=
  ∑j : Fin N,if i< j then v j else 0

def retainedRows {N : ℕ} (v : Fin N→ℝ) (δ : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i=>δ ≤ leftMass v i ∧ δ ≤ rightMass v i)

theorem leftMass_nonneg {N : ℕ} (v : Fin N→ℝ) (hv : ∀i,0 ≤ v i) (i : Fin N) :
    0 ≤ leftMass v i := Finset.sum_nonneg (fun j _=>by split_ifs;exact hv j;exact le_rfl)

theorem rightMass_nonneg {N : ℕ} (v : Fin N→ℝ) (hv : ∀i,0 ≤ v i) (i : Fin N) :
    0 ≤ rightMass v i := Finset.sum_nonneg (fun j _=>by split_ifs;exact hv j;exact le_rfl)

theorem leftMass_add_row {N : ℕ} (v : Fin N→ℝ) (q : Fin N) :
    (∑i : Fin N,if i ≤ q then v i else 0)=leftMass v q+v q := by
  have he : (∑i : Fin N,if i=q then v i else 0)=v q := by simp
  calc
    _=∑i : Fin N,((if i< q then v i else 0)+(if i=q then v i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i< q
      · simp [hi,hi.ne,hi.le]
      · by_cases heq : i=q
        · subst i;simp
        · simp [hi,heq,show ¬i ≤ q by exact fun hh=>heq (le_antisymm hh (le_of_not_gt hi))]
    _=_ := by rw [Finset.sum_add_distrib,he];rfl

theorem row_add_rightMass {N : ℕ} (v : Fin N→ℝ) (q : Fin N) :
    (∑i : Fin N,if q ≤ i then v i else 0)=v q+rightMass v q := by
  have he : (∑i : Fin N,if i=q then v i else 0)=v q := by simp
  calc
    _=∑i : Fin N,((if i=q then v i else 0)+(if q< i then v i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : q< i
      · simp [hi,hi.ne',hi.le]
      · by_cases heq : i=q
        · subst i;simp
        · simp [hi,heq,show ¬q ≤ i by exact fun hh=>heq (le_antisymm (le_of_not_gt hi) hh)]
    _=_ := by rw [Finset.sum_add_distrib,he];rfl

theorem left_strip_mass_le {N : ℕ} (v : Fin N→ℝ) (hv : ∀i,0 ≤ v i)
    {δ mesh : ℝ} (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh) (hb : ∀i,v i ≤ mesh) :
    (∑i : Fin N,if leftMass v i< δ then v i else 0) ≤ δ+mesh := by
  let F := Finset.univ.filter (fun i=>leftMass v i< δ ∧ 0< v i)
  by_cases hn : F.Nonempty
  · let q := F.max' hn
    have hq := (Finset.mem_filter.mp (Finset.max'_mem F hn)).2
    have hsum : (∑i : Fin N,if leftMass v i< δ then v i else 0) ≤
        ∑i : Fin N,if i ≤ q then v i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : leftMass v i< δ
      · by_cases hp : 0< v i
        · have him : i∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hp⟩
          have hil : i ≤ q := Finset.le_max' F i him
          simp only [hi,hil,ite_true];exact le_rfl
        · have hz : v i=0 := le_antisymm (le_of_not_gt hp) (hv i)
          simp only [hi,ite_true,hz];split_ifs <;> exact le_rfl
      · simp only [hi,ite_false];split_ifs;exact hv i;exact le_rfl
    rw [leftMass_add_row] at hsum
    linarith [hb q]
  · have hzero i : leftMass v i< δ → v i=0 := by
      intro hi
      have hnot : ¬0< v i := fun hp=>hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hp⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hv i)
    have hs : (∑i : Fin N,if leftMass v i< δ then v i else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact hzero i hi
      · rfl
    rw [hs];exact add_nonneg hδ hmesh

theorem right_strip_mass_le {N : ℕ} (v : Fin N→ℝ) (hv : ∀i,0 ≤ v i)
    {δ mesh : ℝ} (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh) (hb : ∀i,v i ≤ mesh) :
    (∑i : Fin N,if rightMass v i< δ then v i else 0) ≤ δ+mesh := by
  let F := Finset.univ.filter (fun i=>rightMass v i< δ ∧ 0< v i)
  by_cases hn : F.Nonempty
  · let q := F.min' hn
    have hq := (Finset.mem_filter.mp (Finset.min'_mem F hn)).2
    have hsum : (∑i : Fin N,if rightMass v i< δ then v i else 0) ≤
        ∑i : Fin N,if q ≤ i then v i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : rightMass v i< δ
      · by_cases hp : 0< v i
        · have him : i∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hp⟩
          have hil : q ≤ i := Finset.min'_le F i him
          simp only [hi,hil,ite_true];exact le_rfl
        · have hz : v i=0 := le_antisymm (le_of_not_gt hp) (hv i)
          simp only [hi,ite_true,hz];split_ifs <;> exact le_rfl
      · simp only [hi,ite_false];split_ifs;exact hv i;exact le_rfl
    rw [row_add_rightMass] at hsum
    linarith [hb q]
  · have hzero i : rightMass v i< δ → v i=0 := by
      intro hi
      have hnot : ¬0< v i := fun hp=>hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hp⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hv i)
    have hs : (∑i : Fin N,if rightMass v i< δ then v i else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact hzero i hi
      · rfl
    rw [hs];exact add_nonneg hδ hmesh

theorem omitted_radius_mass_le {N : ℕ} (v : Fin N→ℝ) (hv : ∀i,0 ≤ v i)
    {δ mesh : ℝ} (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh) (hb : ∀i,v i ≤ mesh) :
    (∑i : Fin N,if i∉retainedRows v δ then v i else 0) ≤ 2*δ+2*mesh := by
  have hs : (∑i : Fin N,if i∉retainedRows v δ then v i else 0) ≤
      (∑i : Fin N,if leftMass v i< δ then v i else 0)+
      (∑i : Fin N,if rightMass v i< δ then v i else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hl : leftMass v i< δ <;> by_cases hr : rightMass v i< δ <;>
      simp [retainedRows,hl,hr,not_le_of_gt,le_of_not_gt,hv i]
  linarith [left_strip_mass_le v hv hδ hmesh hb,right_strip_mass_le v hv hδ hmesh hb]

theorem retained_side_lengths {N : ℕ} (v : Fin N→ℝ) (δ : ℝ)
    {i : Fin N} (hi : i∈retainedRows v δ) : δ ≤ leftMass v i ∧ δ ≤ rightMass v i :=
  (Finset.mem_filter.mp hi).2

def bin {N bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N)) (w : ℝ) (b : Fin bins) :
    Finset (Fin N) := J.filter (fun i=>heightBin bins w (S i)=b.val)

theorem bin_partition {N bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (w : ℝ) (hk : 0< bins) {i : Fin N} (hi : i∈J) :
    ∃!b : Fin bins,i∈bin S J w b := by
  let b : Fin bins := ⟨heightBin bins w (S i),heightBin_lt hk _ _⟩
  exact ⟨b,Finset.mem_filter.mpr ⟨hi,rfl⟩,fun j hj=>Fin.ext (Finset.mem_filter.mp hj).2.symm⟩

theorem bin_profile_abs_le {N bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    {w : ℝ} (hw : 0< w) (hS : ∀i∈J,S i∈Icc (0:ℝ) ((bins:ℝ)*w))
    (b : Fin bins) {i j : Fin N} (hi : i∈bin S J w b) (hj : j∈bin S J w b) :
    |S j-S i| ≤ w := by
  have hiJ := (Finset.mem_filter.mp hi).1
  have hjJ := (Finset.mem_filter.mp hj).1
  exact sameHeightBin_abs_le (Nat.zero_lt_of_lt b.isLt) hw (hS j hjJ) (hS i hiJ)
    ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hi).2.symm)

theorem bin_between {N bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (hS : MonotoneOn S (J:Set (Fin N))) {w : ℝ} (hw : 0< w) (b : Fin bins)
    {i j t : Fin N} (hi : i∈bin S J w b) (hj : j∈bin S J w b)
    (ht : t∈J) (hit : i ≤ t) (htj : t ≤ j) : t∈bin S J w b := by
  have hlo := heightBin_monotone (k:=bins) hw (hS (Finset.mem_filter.mp hi).1 ht hit)
  have hhi := heightBin_monotone (k:=bins) hw (hS ht (Finset.mem_filter.mp hj).1 htj)
  rw [(Finset.mem_filter.mp hi).2] at hlo
  rw [(Finset.mem_filter.mp hj).2] at hhi
  exact Finset.mem_filter.mpr ⟨ht,le_antisymm hhi hlo⟩

theorem bin_eq_selected_index_interval {N bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (hS : MonotoneOn S (J:Set (Fin N))) {w : ℝ} (hw : 0< w) (b : Fin bins)
    (hn : (bin S J w b).Nonempty) :
    ∃p q : Fin N,p∈bin S J w b ∧ q∈bin S J w b ∧
      bin S J w b=J.filter (fun i=>p ≤ i ∧ i ≤ q) := by
  let F := bin S J w b
  let p := F.min' hn
  let q := F.max' hn
  have hp := Finset.min'_mem F hn
  have hq := Finset.max'_mem F hn
  refine ⟨p,q,hp,hq,?_⟩
  ext i
  constructor
  · intro hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
      Finset.min'_le F i hi,Finset.le_max' F i hi⟩
  · intro hi
    obtain ⟨hi,hpi,hiq⟩ := Finset.mem_filter.mp hi
    exact bin_between S J hS hw b hp hq hi hpi hiq

def clippedRadiusCut (a z r : ℝ) : ℝ := max a (min z r)

theorem clippedRadiusCut_monotone (a z : ℝ) : Monotone (clippedRadiusCut a z) := by
  intro r s hrs
  exact max_le_max_left a (min_le_min_left z hrs)

private theorem clipped_cell_length {a z l r : ℝ} (haz : a ≤ z) (hlr : l ≤ r) :
    max (min z r-max a l) 0=clippedRadiusCut a z r-clippedRadiusCut a z l := by
  unfold clippedRadiusCut
  simp only [max_def,min_def]
  split_ifs <;> linarith

theorem volume_clipped_radius_cell {a z l r : ℝ} (haz : a ≤ z) (hlr : l ≤ r) :
    volume.real (Ioo a z∩Ioc l r)=clippedRadiusCut a z r-clippedRadiusCut a z l := by
  by_cases hzr : z ≤ r
  · rw [Ioo_inter_Ioc_of_left_le hzr,Real.volume_real_Ioo]
    simpa only [min_eq_left hzr] using clipped_cell_length haz hlr
  · have hrz : r < z := lt_of_not_ge hzr
    rw [Ioo_inter_Ioc_of_right_lt hrz,Real.volume_real_Ioc]
    simpa only [min_eq_right hrz.le] using clipped_cell_length haz hlr

theorem clipped_radius_cell_mass_le {a z l r : ℝ} (_haz : a ≤ z) (hlr : l ≤ r) :
    0 ≤ volume.real (Ioo a z∩Ioc l r) ∧ volume.real (Ioo a z∩Ioc l r) ≤ r-l := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have hf : volume (Ioc l r)≠⊤ := by rw [Real.volume_Ioc];exact ENNReal.ofReal_ne_top
  have hh : volume.real (Ioo a z∩Ioc l r) ≤ volume.real (Ioc l r) :=
    ENNReal.toReal_mono hf (measure_mono (inter_subset_right : Ioo a z∩Ioc l r⊆Ioc l r))
  rw [Real.volume_real_Ioc_of_le hlr] at hh
  exact hh

theorem finite_cell_prefix_sum {N : ℕ} (cuts : ℕ→ℝ) (j : ℕ) (hj : j ≤ N) :
    (∑i : Fin N,if i.val< j then cuts (i.val+1)-cuts i.val else 0)=cuts j-cuts 0 := by
  have hh := WholeUnitSideKernel.finite_unit_coordinate_eq_cumulative (fun i=>cuts i-cuts 0)
    (fun i : Fin N=>cuts (i.val+1)-cuts i.val) (by ring) (fun _=>by ring) j hj
  exact hh.symm

theorem finite_interval_side_mass {N : ℕ} (cuts : ℕ→ℝ) (p q i : Fin N)
    (hpi : p ≤ i) (hiq : i ≤ q) :
    let v := fun j : Fin N=>if p ≤ j ∧ j ≤ q then cuts (j.val+1)-cuts j.val else 0
    leftMass v i=cuts i.val-cuts p.val ∧
      rightMass v i=cuts (q.val+1)-cuts (i.val+1) := by
  dsimp only
  have hpN : p.val ≤ N := p.isLt.le
  have hiN : i.val ≤ N := i.isLt.le
  have hi1N : i.val+1 ≤ N := Nat.succ_le_of_lt i.isLt
  have hq1N : q.val+1 ≤ N := Nat.succ_le_of_lt q.isLt
  constructor
  · have he : leftMass (fun j : Fin N=>if p ≤ j ∧ j ≤ q then cuts (j.val+1)-cuts j.val else 0) i=
        (∑j : Fin N,if j.val< i.val then cuts (j.val+1)-cuts j.val else 0)-
        (∑j : Fin N,if j.val< p.val then cuts (j.val+1)-cuts j.val else 0) := by
      rw [leftMass,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.lt_def,Fin.le_def]
      split_ifs <;> first | omega | ring
    rw [he,finite_cell_prefix_sum cuts i.val hiN,finite_cell_prefix_sum cuts p.val hpN]
    ring
  · have he : rightMass (fun j : Fin N=>if p ≤ j ∧ j ≤ q then cuts (j.val+1)-cuts j.val else 0) i=
        (∑j : Fin N,if j.val< q.val+1 then cuts (j.val+1)-cuts j.val else 0)-
        (∑j : Fin N,if j.val< i.val+1 then cuts (j.val+1)-cuts j.val else 0) := by
      rw [rightMass,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.lt_def,Fin.le_def]
      split_ifs <;> first | omega | ring
    rw [he,finite_cell_prefix_sum cuts (q.val+1) hq1N,finite_cell_prefix_sum cuts (i.val+1) hi1N]
    ring

end NativeRadiusHeight

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonNativeRadiusRowMass {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) : ℝ :=
  if i∈J then volume.real (Ioo a z∩Ioc
    (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val))
    (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) (i.val+1)))) else 0

theorem comparisonNativeRadiusRowMass_nonneg {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1)) :
    0 ≤ comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as J a z i := by
  unfold comparisonNativeRadiusRowMass
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem comparisonNativeRadiusRowMass_zero_of_zero_mass {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps clock 0 as).length+1))
    (hi : pathMassDifferences (sampleClockSteps clock 0 as) 0 i=0) :
    comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as J a z i=0 := by
  rw [pathMassDifferences_eq_cutMass] at hi
  have he := sub_eq_zero.mp hi
  simp only [comparisonNativeRadiusRowMass,he,Ioc_self,inter_empty,measureReal_empty,ite_self]

theorem comparisonNativeRadiusRowMass_le_mesh {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    {a z : ℝ} (haz : a ≤ z) (i : Fin ((sampleClockSteps clock 0 as).length+1)) :
    comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as J a z i ≤ mesh/c := by
  let steps := sampleClockSteps clock 0 as
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hmass : physicalCutMass 0 steps i.val ≤ physicalCutMass 0 steps (i.val+1) :=
    physicalCutMass_monotone steps hs (Nat.le_succ _)
  have hR : R (physicalCutMass 0 steps i.val) ≤ R (physicalCutMass 0 steps (i.val+1)) :=
    comparisonSweepQuantile_monotone hc hk hkc hm hM α hmass
  have hLip := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul
    (physicalCutMass 0 steps (i.val+1)) (physicalCutMass 0 steps i.val)
  change dist (R (physicalCutMass 0 steps (i.val+1))) (R (physicalCutMass 0 steps i.val)) ≤
    (1/c)*dist (physicalCutMass 0 steps (i.val+1)) (physicalCutMass 0 steps i.val) at hLip
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hR),
    abs_of_nonneg (sub_nonneg.mpr hmass)] at hLip
  have hbound := sampled_physicalMass_mesh clock as hmesh i
  have hwidth : R (physicalCutMass 0 steps (i.val+1))-R (physicalCutMass 0 steps i.val) ≤ mesh/c :=
    hLip.trans (by simpa only [steps,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
      mul_le_mul_of_nonneg_left hbound (show 0 ≤ (1/c:ℝ) by positivity))
  unfold comparisonNativeRadiusRowMass
  split_ifs
  · exact (NativeRadiusHeight.clipped_radius_cell_mass_le haz hR).2.trans hwidth
  · exact div_nonneg hmesh0 hc.le

theorem comparisonNativeRadiusRows_strip_budget {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh δ a z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hδ : 0 ≤ δ) (haz : a ≤ z)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1))) :
    let v := comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as J a z
    (∑i,if i∉NativeRadiusHeight.retainedRows v δ then v i else 0) ≤ 2*δ+2*(mesh/c) ∧
      (∀i∈NativeRadiusHeight.retainedRows v δ,
        δ ≤ NativeRadiusHeight.leftMass v i ∧ δ ≤ NativeRadiusHeight.rightMass v i) := by
  dsimp only
  refine ⟨NativeRadiusHeight.omitted_radius_mass_le _
    (comparisonNativeRadiusRowMass_nonneg hc hk hkc hm hM clock α as J a z)
    hδ (div_nonneg hmesh0 hc.le)
    (comparisonNativeRadiusRowMass_le_mesh hc hk hkc hm hM clock α as ho hmesh hmesh0 J haz),?_⟩
  intro i hi
  exact NativeRadiusHeight.retained_side_lengths _ δ hi

theorem comparisonNativeRadiusRowMass_total {ι : Type} (clock : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
    (∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as Finset.univ a z i)=z-a := by
  let steps := sampleClockSteps clock 0 as
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let cuts := fun j=>NativeRadiusHeight.clippedRadiusCut a z (R (physicalCutMass 0 steps j))
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hcutsMono : Monotone (physicalCutMass 0 steps) := physicalCutMass_monotone steps hs
  have hR : Monotone R := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hv (i : Fin (steps.length+1)) :
      comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as Finset.univ a z i=
        cuts (i.val+1)-cuts i.val := by
    simpa only [comparisonNativeRadiusRowMass,Finset.mem_univ,ite_true] using
      NativeRadiusHeight.volume_clipped_radius_cell haz (hR (hcutsMono (Nat.le_succ i.val)))
  have hh := NativeRadiusHeight.finite_cell_prefix_sum cuts (steps.length+1) le_rfl
  simp only [Fin.is_lt,ite_true] at hh
  have he := comparisonSweepQuantile_endpoints hc hk hkc hm hM α
  have hstart : cuts 0=a := by
    simp only [cuts,R,physicalCutMass,he.1,NativeRadiusHeight.clippedRadiusCut,
      min_eq_right (ha.trans haz),max_eq_left ha]
  have hend : cuts (steps.length+1)=z := by
    change NativeRadiusHeight.clippedRadiusCut a z (R (physicalCutMass 0 steps (steps.length+1)))=z
    rw [physicalCutMass_terminal]
    simp only [R,he.2,NativeRadiusHeight.clippedRadiusCut,min_eq_left hz,max_eq_right haz]
  simp_rw [hv]
  rw [hh,hstart,hend]

theorem comparisonNativeRadiusHeightBins_mass_partition {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (S : Fin ((sampleClockSteps clock 0 as).length+1)→ℝ) {bins : ℕ} (hk0 : 0<bins)
    (w a z : ℝ) :
    (∑b : Fin bins,∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as
      (NativeRadiusHeight.bin S J w b) a z i)=
      ∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as J a z i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold comparisonNativeRadiusRowMass NativeRadiusHeight.bin
  simp only [Finset.mem_filter]
  by_cases hi : i∈J
  · let b0 : Fin bins := ⟨heightBin bins w (S i),heightBin_lt hk0 _ _⟩
    have hb (b : Fin bins) : heightBin bins w (S i)=b.val ↔ b=b0 := by
      constructor
      · intro he;exact Fin.ext he.symm
      · intro he;subst b;rfl
    simp only [hi,true_and,ite_true]
    simp_rw [hb]
    simp
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero]

theorem comparisonNativeRadiusHeightBins_strip_budget {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh δ a z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hδ : 0 ≤ δ) (haz : a ≤ z)
    (J : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (S : Fin ((sampleClockSteps clock 0 as).length+1)→ℝ) (bins : ℕ) (w : ℝ) :
    (∑b : Fin bins,
      let v := comparisonNativeRadiusRowMass hc hk hkc hm hM clock α as
        (NativeRadiusHeight.bin S J w b) a z
      ∑i,if i∉NativeRadiusHeight.retainedRows v δ then v i else 0) ≤
      2*(bins:ℝ)*δ+2*(bins:ℝ)*(mesh/c) := by
  have hh := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin bins))) (fun b _=>
    (comparisonNativeRadiusRows_strip_budget hc hk hkc hm hM clock α as ho
      hmesh hmesh0 hδ haz (NativeRadiusHeight.bin S J w b)).1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  convert hh using 1; ring

end
end OAI.SKFluctuations.LaplaceWindowFormalization
