module

public import ComparisonTwoSidedNativeReverseMovement
public import ComparisonTwoSidedNativeRawRetention
public import ComparisonSelectedCapOrder
public import ComparisonWholeCapHeightBins
public import ComparisonCapSideTraceTerminal
public import ComparisonCapBoundaryRowDiscard
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalForkSumMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

namespace NativeUnitHeight

def height {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N)) (unit : Fin N→Fin K) (u : Fin K) : ℝ :=
  if hn : (J.filter (fun i=>unit i=u)).Nonempty then
    (J.filter (fun i=>unit i=u)).sup' hn S else 0

theorem row_le_height {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) {i : Fin N} (hi : i ∈ J) : S i ≤ height S J unit (unit i) := by
  have hmem : i ∈ J.filter (fun j=>unit j=unit i) := Finset.mem_filter.mpr ⟨hi,rfl⟩
  have hn : (J.filter (fun j=>unit j=unit i)).Nonempty := ⟨i,hmem⟩
  rw [height,dite_eq_left hn]
  exact Finset.le_sup' S hmem

theorem height_le_of_rows {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) {Y : ℝ} (hY : 0 ≤ Y) (hrows : ∀i ∈ J,S i ≤ Y) (u : Fin K) :
    height S J unit u ≤ Y := by
  unfold height
  split_ifs with hn
  · exact Finset.sup'_le _ _ (fun i hi=>hrows i (Finset.mem_filter.mp hi).1)
  · exact hY

theorem height_nonneg {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (hrows : ∀i ∈ J,0 ≤ S i) (u : Fin K) : 0 ≤ height S J unit u := by
  unfold height
  split_ifs with hn
  · obtain ⟨i,hi⟩ := hn
    exact (hrows i (Finset.mem_filter.mp hi).1).trans (Finset.le_sup' S hi)
  · exact le_rfl

theorem height_le_row_add {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) {i : Fin N} (hi : i ∈ J) {L : ℝ}
    (hunit : ∀j ∈ J,unit j=unit i→S j ≤ S i+L) : height S J unit (unit i) ≤ S i+L := by
  have hmem : i ∈ J.filter (fun j=>unit j=unit i) := Finset.mem_filter.mpr ⟨hi,rfl⟩
  have hn : (J.filter (fun j=>unit j=unit i)).Nonempty := ⟨i,hmem⟩
  rw [height,dite_eq_left hn]
  exact Finset.sup'_le _ _ (fun j hj=>hunit j (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hj).2)

def bin {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N)) (unit : Fin N→Fin K)
    (bins : ℕ) (w : ℝ) (b : Fin bins) : Finset (Fin N) :=
  J.filter (fun i=>heightBin bins w (height S J unit (unit i))=b.val)

theorem bin_same_unit {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (w : ℝ) (b : Fin bins) {i j : Fin N}
    (hi : i ∈ bin S J unit bins w b) (hj : j ∈ J) (he : unit j=unit i) :
    j ∈ bin S J unit bins w b := by
  exact Finset.mem_filter.mpr ⟨hj,by rw [he];exact (Finset.mem_filter.mp hi).2⟩

theorem bin_profile_abs_le {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) {w L : ℝ} (hw : 0<w) (hrows : ∀i ∈ J,S i ∈ Icc (0:ℝ) ((bins:ℝ)*w))
    (hunit : ∀i ∈ J,∀j ∈ J,unit j=unit i→S j ≤ S i+L)
    (b : Fin bins) {i j : Fin N} (hi : i ∈ bin S J unit bins w b)
    (hj : j ∈ bin S J unit bins w b) : |S j-S i| ≤ w+L := by
  have hiJ := (Finset.mem_filter.mp hi).1
  have hjJ := (Finset.mem_filter.mp hj).1
  have hk : 0<bins := Nat.zero_lt_of_lt b.isLt
  have hY : 0 ≤ (bins:ℝ)*w := mul_nonneg (Nat.cast_nonneg _) hw.le
  have hiH : height S J unit (unit i) ∈ Icc (0:ℝ) ((bins:ℝ)*w) :=
    ⟨height_nonneg S J unit (fun i hi=>(hrows i hi).1) _,
      height_le_of_rows S J unit hY (fun i hi=>(hrows i hi).2) _⟩
  have hjH : height S J unit (unit j) ∈ Icc (0:ℝ) ((bins:ℝ)*w) :=
    ⟨height_nonneg S J unit (fun i hi=>(hrows i hi).1) _,
      height_le_of_rows S J unit hY (fun i hi=>(hrows i hi).2) _⟩
  have hsame : heightBin bins w (height S J unit (unit i))=
      heightBin bins w (height S J unit (unit j)) :=
    (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  have hH := abs_le.mp (sameHeightBin_abs_le hk hw hiH hjH hsame)
  have hli := row_le_height S J unit hiJ
  have hlj := row_le_height S J unit hjJ
  have hui := height_le_row_add S J unit hiJ (hunit i hiJ)
  have huj := height_le_row_add S J unit hjJ (hunit j hjJ)
  apply abs_le.mpr
  constructor <;> linarith

theorem height_monotoneOn_selected {N K : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (hS : Monotone S) (hunit : MonotoneOn unit (J:Set (Fin N))) :
    MonotoneOn (fun i=>height S J unit (unit i)) (J:Set (Fin N)) := by
  intro i hi j hj hij
  dsimp only
  by_cases he : unit i=unit j
  · rw [he]
  have hlt : unit i<unit j := lt_of_le_of_ne (hunit hi hj hij) he
  have hmem : i ∈ J.filter (fun a=>unit a=unit i) := Finset.mem_filter.mpr ⟨hi,rfl⟩
  have hn : (J.filter (fun a=>unit a=unit i)).Nonempty := ⟨i,hmem⟩
  rw [height,dite_eq_left hn]
  apply Finset.sup'_le
  intro a ha
  have haJ := (Finset.mem_filter.mp ha).1
  have hae := (Finset.mem_filter.mp ha).2
  have haj : a ≤ j := by
    by_contra hno
    have hu := hunit hj haJ (le_of_lt (lt_of_not_ge hno))
    rw [hae] at hu
    exact (not_le_of_gt hlt) hu
  exact (hS haj).trans (row_le_height S J unit hj)

theorem bin_label_monotoneOn_selected {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (hS : Monotone S) (hunit : MonotoneOn unit (J:Set (Fin N)))
    {w : ℝ} (hw : 0<w) :
    MonotoneOn (fun i=>heightBin bins w (height S J unit (unit i))) (J:Set (Fin N)) := by
  intro i hi j hj hij
  exact heightBin_monotone hw (height_monotoneOn_selected S J unit hS hunit hi hj hij)

theorem bin_between_selected {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (hS : Monotone S) (hunit : MonotoneOn unit (J:Set (Fin N)))
    {w : ℝ} (hw : 0<w) (b : Fin bins) {i j t : Fin N}
    (hi : i ∈ bin S J unit bins w b) (hj : j ∈ bin S J unit bins w b)
    (ht : t ∈ J) (hit : i ≤ t) (htj : t ≤ j) : t ∈ bin S J unit bins w b := by
  have hiJ := (Finset.mem_filter.mp hi).1
  have hjJ := (Finset.mem_filter.mp hj).1
  have hm := bin_label_monotoneOn_selected (bins:=bins) S J unit hS hunit hw
  have hlo := hm hiJ ht hit
  have hup := hm ht hjJ htj
  dsimp only at hlo hup
  rw [(Finset.mem_filter.mp hi).2] at hlo
  rw [(Finset.mem_filter.mp hj).2] at hup
  exact Finset.mem_filter.mpr ⟨ht,le_antisymm hup hlo⟩

theorem bin_partition {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (w : ℝ) (hk : 0<bins) {i : Fin N} (hi : i ∈ J) :
    ∃!b:Fin bins,i ∈ bin S J unit bins w b := by
  let b : Fin bins := ⟨heightBin bins w (height S J unit (unit i)),heightBin_lt hk _ _⟩
  refine ⟨b,Finset.mem_filter.mpr ⟨hi,rfl⟩,?_⟩
  intro a ha
  apply Fin.ext
  exact (Finset.mem_filter.mp ha).2.symm

theorem bin_eq_selected_index_interval {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (hS : Monotone S) (hunit : MonotoneOn unit (J:Set (Fin N)))
    {w : ℝ} (hw : 0<w) (b : Fin bins) (hn : (bin S J unit bins w b).Nonempty) :
    ∃lo hi:Fin N,lo ∈ bin S J unit bins w b ∧ hi ∈ bin S J unit bins w b ∧
      bin S J unit bins w b=J.filter (fun i=>lo ≤ i ∧ i ≤ hi) := by
  let B := bin S J unit bins w b
  let lo := B.min' hn
  let hi := B.max' hn
  have hlo : lo ∈ B := Finset.min'_mem B hn
  have hhi : hi ∈ B := Finset.max'_mem B hn
  refine ⟨lo,hi,hlo,hhi,?_⟩
  ext i
  constructor
  · intro hiB
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiB).1,
      Finset.min'_le _ _ hiB,Finset.le_max' _ _ hiB⟩
  · intro hiJ
    obtain ⟨hiJ,hloi,hihi⟩ := Finset.mem_filter.mp hiJ
    exact bin_between_selected S J unit hS hunit hw b hlo hhi hiJ hloi hihi

end NativeUnitHeight

theorem physicalProfile_second_le_raw_ratio (n l : ℕ) (hl : 0<l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {xs : ℝ} (hxs : 0<xs) {i : ℕ} (hi : i  ≤  steps.length+1) :
    physicalPathSecondMoment n steps q0 i ≤ 
      (physicalRawRatio n l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id)^2*
        (xs+physicalCutMass 0 steps i) := by
  let mu := Measure.pi fun k=>gaussianReal 0 (q0 k)
  let : IsProbabilityMeasure mu := by dsimp only [mu];infer_instance
  let nu := physicalPathLaw mu n steps id measurable_id
  have hprob := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  let : IsProbabilityMeasure nu := by
    simpa only [nu,mu,rootedHierarchyPathLaw_eq_physical] using hprob
  have hpow := integral_pow_le_mass nu
    (Eventually.of_forall (fun z=>sq_nonneg ‖actualSpinPath n steps id i z‖))
    (physicalCutNormPower_integrable n steps ha mu id measurable_id i 2) hl
    (by simpa only [←pow_mul] using physicalCutNormPower_integrable n steps ha mu id measurable_id i (2*l))
  have hraw := physicalRawRatio_half_moment n l hl steps ha hxs mu id measurable_id hi
  have he : ((physicalRawRatio n l steps 0 xs mu id measurable_id)^2*
      (xs+physicalCutMass 0 steps i))^l=
      (physicalRawRatio n l steps 0 xs mu id measurable_id)^(2*l)*(xs+physicalCutMass 0 steps i)^l := by
    rw [mul_pow,←pow_mul]
  have hb : 0 ≤ (physicalRawRatio n l steps 0 xs mu id measurable_id)^2*
      (xs+physicalCutMass 0 steps i) := mul_nonneg (sq_nonneg _)
        (add_nonneg hxs.le (physicalCutMass_mem steps ha i).1)
  rw [←he] at hraw
  have hbound := le_of_pow_le_pow_left₀ hl.ne' hb (hpow.trans (by
    simpa only [nu,←pow_mul,Measure.real,measure_univ,ENNReal.toReal_one,one_pow,one_mul] using hraw))
  change (∫z,‖actualSpinPath n steps id i z‖^2 ∂nu) ≤ _ at hbound
  simpa only [physicalPathSecondMoment,nu,mu,←rootedHierarchyPathLaw_eq_physical] using hbound

theorem physicalCutMass_strictOn_positive_selected {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1)))
    (hpos : ∀i ∈ J,0<pathMassDifferences steps 0 i) :
    StrictMonoOn (fun i:Fin (steps.length+1)=>physicalCutMass 0 steps i.val) (J:Set _) := by
  intro i hi j hj hij
  have hp := hpos i hi
  rw [pathMassDifferences_eq_cutMass] at hp
  have hm := physicalCutMass_monotone steps ha (show i.val+1 ≤ j.val by exact_mod_cast hij)
  dsimp only
  linarith

theorem physicalProfile_monotone_on_rows (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) :
    Monotone (fun i:Fin (steps.length+1)=>physicalPathSecondMoment n steps q0 i.val) := by
  intro i j hij
  exact physicalPathSecondMoment_mono n steps ha q0 hij (by omega)

theorem physicalFineCoupling_mem_selected {n K : ℕ}
    (steps : List (GaussianStep (FeatureIndex n))) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (P : Fin K→Fin K→ℝ)
    {i j : Fin (steps.length+1)}
    (hP : fineCoupling (physicalSelectedCellMass steps J) unit P i j ≠ 0) : i ∈ J ∧ j ∈ J := by
  constructor
  all_goals
    by_contra hno
    apply hP
    simp [fineCoupling,physicalSelectedCellMass,hno]

theorem physical_native_unit_bins_profile_diameter (n l : ℕ) (hl : 0<l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {K bins : ℕ}
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    {xs y w L : ℝ} (hxs : 0<xs) (hw : 0<w)
    (hmass : ∀i ∈ J,xs+physicalCutMass 0 steps i.val ≤ y)
    (hwidth : (physicalRawRatio n l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id)^2*y ≤ (bins:ℝ)*w)
    (hunit : ∀i ∈ J,∀j ∈ J,unit j=unit i→
      physicalPathSecondMoment n steps q0 j.val ≤ physicalPathSecondMoment n steps q0 i.val+L)
    (b : Fin bins) {i j : Fin (steps.length+1)}
    (hi : i ∈ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment n steps q0 i.val) J unit bins w b)
    (hj : j ∈ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment n steps q0 i.val) J unit bins w b) :
    |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ w+L := by
  apply NativeUnitHeight.bin_profile_abs_le _ J unit hw _ hunit b hi hj
  intro a haJ
  refine ⟨physicalPathSecondMoment_nonneg n steps q0 _,?_⟩
  exact (physicalProfile_second_le_raw_ratio n l hl steps ha q0 hxs (by omega)).trans
    ((mul_le_mul_of_nonneg_left (hmass a haJ) (sq_nonneg _)).trans hwidth)

theorem physical_native_bins_mass_partition {n K bins : ℕ}
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n→ℝ≥0)
    (A : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    (w : ℝ) (hk : 0<bins) (i : Fin (steps.length+1)) :
    (∑b:Fin bins,physicalSelectedCellMass steps
      (NativeUnitHeight.bin (fun i=>physicalPathSecondMoment n steps q0 i.val) A unit bins w b) i)=
      physicalSelectedCellMass steps A i := by
  by_cases hi:i ∈ A
  · obtain ⟨b,hb,hunique⟩ := NativeUnitHeight.bin_partition (fun i=>physicalPathSecondMoment n steps q0 i.val) A unit w hk hi
    rw [Finset.sum_eq_single b]
    · simp only [physicalSelectedCellMass,hb,hi,ite_true]
    · intro c hc hcb
      have hic : i ∉ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment n steps q0 i.val) A unit bins w c :=
        fun hic=>hcb (hunique c hic)
      simp only [physicalSelectedCellMass,hic,ite_false]
    · simp
  · have hn b : i ∉ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment n steps q0 i.val) A unit bins w b :=
      fun hib=>hi (Finset.mem_filter.mp hib).1
    simp only [physicalSelectedCellMass,hi,hn,ite_false,Finset.sum_const_zero]

theorem nativeReverseBudget_le_of_raw_square {l : ℕ} (hl : 2<l)
    {D Q C s y : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hQ : Q^2 ≤ 2*C) (hsy : s ≤ y) :
    D^(((l:ℝ)-2)/((l:ℝ)-1))*((2*Q)^(2*l)*s^l)^(1/((l:ℝ)-1)) ≤ 
      D^(((l:ℝ)-2)/((l:ℝ)-1))*((8*C*y)^l)^(1/((l:ℝ)-1)) := by
  have hy : 0 ≤ y := hs.trans hsy
  have hlR : (2:ℝ)<l := by exact_mod_cast hl
  have hp : 0 ≤ 1/((l:ℝ)-1) := div_nonneg zero_le_one (by linarith)
  have he : (2*Q)^(2*l)*s^l=(4*Q^2*s)^l := by
    rw [pow_mul,mul_pow,mul_pow]
    norm_num
    ring
  have hb : 4*Q^2*s ≤ 8*C*y := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hs,mul_le_mul_of_nonneg_left hsy hC]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4*Q^2*s) hb l
  rw [he]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hpow hp) (Real.rpow_nonneg hD _)

namespace NativeCapClosure

def close {N K : ℕ} (P A : Finset (Fin N)) (unit : Fin N→Fin K) : Finset (Fin N) :=
  P.filter (fun i=>∃j ∈ A,unit j=unit i)

theorem subset_close {N K : ℕ} (P A : Finset (Fin N)) (unit : Fin N→Fin K)
    (hAP : A⊆P) : A⊆close P A unit := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨hAP hi,i,hi,rfl⟩

theorem close_same_unit {N K : ℕ} (P A : Finset (Fin N)) (unit : Fin N→Fin K)
    {i j : Fin N} (hi : i ∈ close P A unit) (hj : j ∈ P) (he : unit j=unit i) :
    j ∈ close P A unit := by
  obtain ⟨_,a,ha,hea⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hj,a,ha,hea.trans he.symm⟩

theorem added_row_is_cap {N K : ℕ} (P A : Finset (Fin N)) (unit : Fin N→Fin K)
    (hAP : A⊆P) (U : Set ℝ) (r : Fin N→ℝ) (hr : StrictMonoOn r (P:Set _))
    (hclass : ∀i ∈ P,∀j ∈ P,unit i=unit j↔wholeUnit U (r i)=wholeUnit U (r j))
    {i : Fin N} (hi : i ∈ close P A unit\A) : r i ∈ U := by
  obtain ⟨hiC,hiA⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hiP,j,hjA,hji⟩ := Finset.mem_filter.mp hiC
  have he := (hclass i hiP j (hAP hjA)).mp hji.symm
  have hjr : r j ∈ wholeUnit U (r i) := he.symm ▸ self_mem_wholeUnit U (r j)
  by_contra hno
  have hrij : r j=r i := by simpa [wholeUnit,hno] using hjr
  have hji : j=i := hr.injOn (hAP hjA) hiP hrij
  exact hiA (hji ▸ hjA)

theorem added_mass_le_cap_tail {N K : ℕ} (P A : Finset (Fin N)) (unit : Fin N→Fin K)
    (hAP : A⊆P) (U : Set ℝ) (r : Fin N→ℝ) (hr : StrictMonoOn r (P:Set _))
    (hclass : ∀i ∈ P,∀j ∈ P,unit i=unit j↔wholeUnit U (r i)=wholeUnit U (r j))
    (F : Finset (Fin K)) (hretained : ∀i ∈ P,unit i ∈ F→i ∈ A)
    (mass : Fin N→ℝ) (hmass : ∀i ∈ P,0 ≤ mass i) :
    (∑i ∈ close P A unit\A,mass i) ≤ ∑i ∈ P.filter (fun i=>r i ∈ U ∧ unit i ∉ F),mass i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨hiC,hiA⟩ := Finset.mem_sdiff.mp hi
    have hiP := (Finset.mem_filter.mp hiC).1
    exact Finset.mem_filter.mpr ⟨hiP,added_row_is_cap P A unit hAP U r hr hclass hi,
      fun hiF=>hiA (hretained i hiP hiF)⟩
  · intro i hi _
    exact hmass i (Finset.mem_filter.mp hi).1

end NativeCapClosure

theorem partitionMesh_nonneg_of_ordered {a mesh : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hm : PartitionMesh mesh a as) : 0 ≤ mesh := by
  induction as generalizing a with
  | nil=>exact (sub_nonneg.mpr (massOrdered_bounds ho).2).trans hm
  | cons b bs ih=>exact ih ho.2.2 hm.2

theorem physicalSelectedUnitMass_le_left_cut_span {ι : Type} {K : ℕ}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (A : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K) (u : Fin K)
    {a b : ℝ} (hab : a ≤ b)
    (hcuts : ∀i ∈ A,unit i=u→physicalCutMass 0 (sampleClockSteps clock 0 as) i.val ∈ Ioo a b) :
    physicalSelectedUnitMass (sampleClockSteps clock 0 as) A unit u ≤ b-a+mesh := by
  let steps := sampleClockSteps clock 0 as
  let B := A.filter (fun i=>unit i=u)
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have he : physicalSelectedUnitMass steps A unit u=physicalWindowMass steps 0 B := by
    simp only [physicalSelectedUnitMass,physicalWindowMass,B,ite_and]
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    exact (Finset.sum_filter (s:=A) (fun i=>unit i=u) (fun i=>pathMassDifferences steps 0 i)).symm
  rw [he]
  by_cases hn : B.Nonempty
  · let p := B.min' hn
    let q := B.max' hn
    have hp := Finset.min'_mem B hn
    have hq := Finset.max'_mem B hn
    have hpq : p ≤ q := Finset.min'_le _ _ hq
    have hB : B⊆physicalIntervalCells steps p.val (q.val+1) := by
      intro i hi
      apply (mem_physicalIntervalCells steps _ _ i).mpr
      exact ⟨Finset.min'_le _ _ hi,by have h := Finset.le_max' _ _ hi;exact Nat.lt_succ_of_le h⟩
    have hsum : physicalWindowMass steps 0 B ≤ physicalWindowMass steps 0 (physicalIntervalCells steps p.val (q.val+1)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hB (fun i _ _=>pathMassDifferences_nonneg steps hs i)
    rw [physicalIntervalMass steps 0 (show p.val ≤ q.val+1 by omega) (show q.val+1 ≤ steps.length+1 from Nat.succ_le_of_lt q.isLt)] at hsum
    have hpl := (hcuts p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2).1
    have hqr := (hcuts q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2
    have hcell := sampled_physicalMass_mesh clock as hmesh q
    change physicalCutMass 0 steps (q.val+1)-physicalCutMass 0 steps q.val ≤ mesh at hcell
    linarith
  · have heB : B=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [heB]
    simp only [physicalWindowMass,Finset.sum_empty]
    exact add_nonneg (sub_nonneg.mpr hab) (partitionMesh_nonneg_of_ordered as ho hmesh)

theorem physicalSelectedUnitMass_le_mesh_of_straddling {ι : Type} {K : ℕ}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (A : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K) (u : Fin K)
    (t : ℝ) (hstraddle : ∀i ∈ A,unit i=u→
      physicalCutMass 0 (sampleClockSteps clock 0 as) i.val<t ∧
        t ≤ physicalCutMass 0 (sampleClockSteps clock 0 as) (i.val+1)) :
    physicalSelectedUnitMass (sampleClockSteps clock 0 as) A unit u ≤ mesh := by
  let steps := sampleClockSteps clock 0 as
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  by_cases hn : ∃i ∈ A,unit i=u
  · obtain ⟨i,hi,hiu⟩ := hn
    have hunique (j : Fin (steps.length+1)) (hj : j ∈ A) (hju : unit j=u) : j=i := by
      rcases lt_trichotomy j i with hji|heq|hij
      · have hm := physicalCutMass_monotone steps hs (show j.val+1 ≤ i.val by exact_mod_cast hji)
        have hp := hstraddle j hj hju
        have hq := hstraddle i hi hiu
        linarith
      · exact heq
      · have hm := physicalCutMass_monotone steps hs (show i.val+1 ≤ j.val by exact_mod_cast hij)
        have hp := hstraddle i hi hiu
        have hq := hstraddle j hj hju
        linarith
    have he : physicalSelectedUnitMass steps A unit u=pathMassDifferences steps 0 i := by
      unfold physicalSelectedUnitMass
      rw [Finset.sum_eq_single i]
      · simp only [hi,hiu,and_self,ite_true]
      · intro j hj hji
        have hn : ¬(j ∈ A ∧ unit j=u) := fun h=>hji (hunique j h.1 h.2)
        simp only [hn,ite_false]
      · simp
    rw [he,pathMassDifferences_eq_cutMass]
    exact sampled_physicalMass_mesh clock as hmesh i
  · have he : physicalSelectedUnitMass steps A unit u=0 := by
      unfold physicalSelectedUnitMass
      apply Finset.sum_eq_zero
      intro i hi
      have hh : ¬(i ∈ A ∧ unit i=u) := fun h=>hn ⟨i,h.1,h.2⟩
      simp only [hh,ite_false]
    rw [he]
    exact partitionMesh_nonneg_of_ordered as ho hmesh

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonSweepQuantile_strictMono_native_geometry
    (α : inverseIntegralConstraints 0 0 k M) :
    StrictMonoOn (comparisonSweepQuantile hc hk hkc hm hM α) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hle := comparisonSweepQuantile_monotone hc hk hkc hm hM α huv.le
  have hne : comparisonSweepQuantile hc hk hkc hm hM α u ≠ comparisonSweepQuantile hc hk hkc hm hM α v := by
    intro he
    have ht := congrArg α.val.val he
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α hu,
      comparisonSweepQuantile_spec hc hk hkc hm hM α hv] at ht
    exact huv.ne ht
  exact lt_of_le_of_ne hle hne

theorem comparison_sampled_contact_cap_unit_mass_le_mesh
    (α : inverseIntegralConstraints 0 0 k M) {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0) {K : ℕ}
    (A : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) j.val)))
    {i : Fin ((sampleClockSteps clock 0 as).length+1)} (hi : i ∈ A)
    (hiU : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val) ∈ U)
    (hmeet : ∀j ∈ A,unit j=unit i→∃t ∈ Icc
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) j.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) (j.val+1))),H t=0) :
    physicalSelectedUnitMass (sampleClockSteps clock 0 as) A unit (unit i) ≤ mesh := by
  let steps := sampleClockSteps clock 0 as
  let ri := comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps i.val)
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  obtain ⟨hlo,hls,hsz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen
    (hU.trans Ioo_subset_Icc_self) hiU
  have haI : sInf (ordConnectedComponent U ri) ∈ Icc (0:ℝ) 1 := ⟨hlo,by linarith⟩
  have hzI : sSup (ordConnectedComponent U ri) ∈ Icc (0:ℝ) 1 := ⟨by linarith,hhi⟩
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  apply physicalSelectedUnitMass_le_mesh_of_straddling clock as ho hmesh A unit (unit i)
    (α.val.val (sSup (ordConnectedComponent U ri)))
  intro j hj hji
  have heunit := (hclass i hi j hj).mp hji.symm
  have hjr : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val) ∈
      ordConnectedComponent U ri := by
    have hmem := heunit.symm ▸ self_mem_wholeUnit U
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val))
    simpa only [wholeUnit,ite_eq_left hiU] using hmem
  have hjI := heq ▸ hjr
  obtain ⟨t,ht,hzero⟩ := hmeet j hj hji
  have hzt : sSup (ordConnectedComponent U ri) ≤ t := by
    by_contra hno
    have htI : t ∈ Ioo (sInf (ordConnectedComponent U ri)) (sSup (ordConnectedComponent U ri)) :=
      ⟨hjI.1.trans_le ht.1,lt_of_not_ge hno⟩
    have hnt := hneg t (ordConnectedComponent_subset (heq.symm ▸ htI))
    rw [hzero] at hnt
    exact lt_irrefl _ hnt
  have hjrI := comparisonSweepQuantile_bounds hc hk hkc hm hM α (physicalCutMass 0 steps j.val)
  have hjnextI := comparisonSweepQuantile_bounds hc hk hkc hm hM α (physicalCutMass 0 steps (j.val+1))
  have hs1 := comparisonSweepQuantile_spec hc hk hkc hm hM α (physicalCutMass_mem steps hs j.val)
  have hs2 := comparisonSweepQuantile_spec hc hk hkc hm hM α (physicalCutMass_mem steps hs (j.val+1))
  constructor
  · rw [←hs1]
    exact hstrict hjrI hzI hjI.2
  · rw [←hs2]
    exact hstrict.monotoneOn hzI hjnextI (hzt.trans ht.2)

theorem comparison_sampled_unit_mass_le_component
    (α : inverseIntegralConstraints 0 0 k M) {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1) {K : ℕ}
    (A : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) j.val)))
    {i : Fin ((sampleClockSteps clock 0 as).length+1)} (hi : i ∈ A)
    (hiU : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val) ∈ U) :
    let ri := comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val)
    physicalSelectedUnitMass (sampleClockSteps clock 0 as) A unit (unit i) ≤
      α.val.val (sSup (ordConnectedComponent U ri))-α.val.val (sInf (ordConnectedComponent U ri))+mesh := by
  dsimp only
  let steps := sampleClockSteps clock 0 as
  let ri := comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps i.val)
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  obtain ⟨hlo,hls,hsz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen
    (hU.trans Ioo_subset_Icc_self) hiU
  have haI : sInf (ordConnectedComponent U ri) ∈ Icc (0:ℝ) 1 := ⟨hlo,by linarith⟩
  have hzI : sSup (ordConnectedComponent U ri) ∈ Icc (0:ℝ) 1 := ⟨by linarith,hhi⟩
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  apply physicalSelectedUnitMass_le_left_cut_span clock as ho hmesh A unit (unit i)
    (hstrict.monotoneOn haI hzI (by linarith))
  intro j hj hji
  have heunit := (hclass i hi j hj).mp hji.symm
  have hjr : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val) ∈
      ordConnectedComponent U ri := by
    have hmem := heunit.symm ▸ self_mem_wholeUnit U
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val))
    simpa only [wholeUnit,ite_eq_left hiU] using hmem
  have hjI := heq ▸ hjr
  have hjrI := comparisonSweepQuantile_bounds hc hk hkc hm hM α (physicalCutMass 0 steps j.val)
  have hspec := comparisonSweepQuantile_spec hc hk hkc hm hM α (physicalCutMass_mem steps hs j.val)
  rw [←hspec]
  exact ⟨hstrict haI hjrI hjI.1,hstrict hjrI hzI hjI.2⟩

theorem comparison_sampled_contact_unit_mass_le_mesh
    (α : inverseIntegralConstraints 0 0 k M) {ι : Type}
    (clock : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (U : Set ℝ) {K : ℕ}
    (A : Finset (Fin ((sampleClockSteps clock 0 as).length+1)))
    (unit : Fin ((sampleClockSteps clock 0 as).length+1)→Fin K)
    (hpos : ∀i ∈ A,0<pathMassDifferences (sampleClockSteps clock 0 as) 0 i)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) j.val)))
    {i : Fin ((sampleClockSteps clock 0 as).length+1)} (hi : i ∈ A)
    (hiU : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val) ∉ U) :
    physicalSelectedUnitMass (sampleClockSteps clock 0 as) A unit (unit i) ≤ mesh := by
  let steps := sampleClockSteps clock 0 as
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered clock as ho
  have hcstrict := physicalCutMass_strictOn_positive_selected steps hs A hpos
  have heunit (j : Fin (steps.length+1)) (hj : j ∈ A) (hji : unit j=unit i) : j=i := by
    have he := (hclass i hi j hj).mp hji.symm
    have hmem := he.symm ▸ self_mem_wholeUnit U
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val))
    have hr : comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps j.val)=
        comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 steps i.val) := by
      simpa only [wholeUnit,ite_eq_right hiU,Set.mem_singleton_iff] using hmem
    have hmassEq := congrArg α.val.val hr
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α (physicalCutMass_mem steps hs j.val),
      comparisonSweepQuantile_spec hc hk hkc hm hM α (physicalCutMass_mem steps hs i.val)] at hmassEq
    exact hcstrict.injOn hj hi hmassEq
  have he : physicalSelectedUnitMass steps A unit (unit i)=pathMassDifferences steps 0 i := by
    unfold physicalSelectedUnitMass
    rw [Finset.sum_eq_single i]
    · simp only [hi,and_self,ite_true]
    · intro j hj hji
      have hn : ¬(j ∈ A ∧ unit j=unit i) := fun h=>hji (heunit j h.1 h.2)
      simp only [hn,ite_false]
    · simp
  rw [he,pathMassDifferences_eq_cutMass]
  exact sampled_physicalMass_mesh clock as hmesh i

abbrev comparisonNativeClock (n : ℕ) (b h : ℝ→ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (d lam : ℝ) :=
  completedPathClock (n+1)
    (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
    (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*
      comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)

theorem actual_comparison_component_increment
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d)
    (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r ∈ Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {delta Ucap Lcap E : ℝ} (hUcap : 0<Ucap) (hLcap : 0<Lcap) (hE : 0<E)
    (hbang : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→H r<0→deriv α.val.val r=
      comparisonCap N delta Ucap Lcap E d (α.val.val r))
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (hcontact : ∀r ∈ U,H (sInf (ordConnectedComponent U r))=0 ∧
      (H (sSup (ordConnectedComponent U r))=0 ∨ sSup (ordConnectedComponent U r)=1))
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ ordConnectedComponent U s) (hst : s ≤ t) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    S t-S s ≤ 9*Real.log N*((Lcap/N^delta)*Real.log ((1+Ucap)/Ucap)) := by
  dsimp only
  obtain ⟨hlo,hls,hsz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen
    (hU.trans Ioo_subset_Icc_self) hs
  have hsI : s ∈ Ioo (sInf (ordConnectedComponent U s)) (sSup (ordConnectedComponent U s)) := ⟨hls,hsz⟩
  have htI : t ∈ Ioo (sInf (ordConnectedComponent U s)) (sSup (ordConnectedComponent U s)) := heq ▸ ht
  have hnegI : ∀r ∈ Ioo (sInf (ordConnectedComponent U s)) (sSup (ordConnectedComponent U s)),H r<0 := by
    intro r hr
    exact hneg r (ordConnectedComponent_subset (heq.symm ▸ hr))
  have hlip := inverseIntegralConstraints_lipschitz hm hM α.property
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  have htravel := potential_comparison_cap_interval_travel (zero_lt_one.trans_le hN)
    hUcap hLcap hE hd hlip hstrict (fun r _=>α.val.property.1 r) hbang
    hlo hhi (hls.trans hsz).le hnegI
  have hinc :
      orderedPathS (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*
          comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal) (α.val.val t)-
      orderedPathS (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*
          comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal) (α.val.val s) ≤ 
      9*Real.log N*(sSup (ordConnectedComponent U s)-sInf (ordConnectedComponent U s)) := by
    rcases (hcontact s hs).2 with hzH|hz1
    · exact (actual_variableEndpoint_comparison_cap_interior_geometry hc hk hkc hm hM
        hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
        hlo hhi hsI htI hst (hcontact s hs).1 hzH (hneg s hs)
        (hneg t (ordConnectedComponent_subset ht))).1
    · rw [hz1] at hsI htI ⊢
      exact actual_variableEndpoint_comparison_terminal_cap_increment hc hk hkc hm hM
        hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
        hlo hsI htI hst (hcontact s hs).1 (hneg s hs)
        (hneg t (ordConnectedComponent_subset ht))
  exact hinc.trans (mul_le_mul_of_nonneg_left htravel.2.1 (by linarith : 0 ≤ 9*Real.log N))

theorem actual_comparison_sampled_component_increment
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d)
    (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r ∈ Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {delta Ucap Lcap E : ℝ} (hUcap : 0<Ucap) (hLcap : 0<Lcap) (hE : 0<E)
    (hbang : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→H r<0→deriv α.val.val r=
      comparisonCap N delta Ucap Lcap E d (α.val.val r))
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (hcontact : ∀r ∈ U,H (sInf (ordConnectedComponent U r))=0 ∧
      (H (sSup (ordConnectedComponent U r))=0 ∨ sSup (ordConnectedComponent U r)=1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ as.length) (hui : 0<partitionPoint 0 as i)
    (hs : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i) ∈ U)
    (ht : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j) ∈ 
      ordConnectedComponent U (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i))) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 as
    physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i ≤ 
      9*Real.log N*((Lcap/N^delta)*Real.log ((1+Ucap)/Ucap))+
      2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hmass := partitionPoint_mono as ho hij
  have hrad := comparisonSweepQuantile_monotone hc hk hkc hm hM α hmass
  have hinc := actual_comparison_component_increment hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact hs ht hrad
  have herr := physicalSampledNodeSecondMoment_increment_le n bf hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    as ho he hmesh (hij.trans hj) hj hui (hui.trans_le hmass)
  rw [←comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho i),
    ←comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho j)] at herr
  dsimp only [R,bf,hf,q] at herr hinc ⊢
  linarith

theorem actual_comparison_sampled_component_reverse_fourth
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d)
    (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r ∈ Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {delta Ucap Lcap E : ℝ} (hUcap : 0<Ucap) (hLcap : 0<Lcap) (hE : 0<E)
    (hbang : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→H r<0→deriv α.val.val r=
      comparisonCap N delta Ucap Lcap E d (α.val.val r))
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (hcontact : ∀r ∈ U,H (sInf (ordConnectedComponent U r))=0 ∧
      (H (sSup (ordConnectedComponent U r))=0 ∨ sSup (ordConnectedComponent U r)=1))
    (l : ℕ) (hl : 2<l)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ as.length) (hui : 0<partitionPoint 0 as i)
    (hs : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i) ∈ U)
    (ht : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j) ∈ 
      ordConnectedComponent U (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)))
    {xs : ℝ} (hxs : 0<xs) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 as
    let D := 9*Real.log N*((Lcap/N^delta)*Real.log ((1+Ucap)/Ucap))+
      2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q))
    physicalSideMovementMoment (n+1) steps (q 0) i j ≤ D^(((l:ℝ)-2)/((l:ℝ)-1))*
      ((2*physicalRawRatio (n+1) l steps 0 xs (Measure.pi fun v=>gaussianReal 0 (q 0 v)) id measurable_id)^(2*l)*
        (xs+physicalCutMass 0 steps j)^l)^(1/((l:ℝ)-1)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  have hsteps : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  have hinc := actual_comparison_sampled_component_increment hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh hij hj hui hs ht
  have hbase : 0 ≤ physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i := by
    rw [←physical_movement_second_eq_profile_increment (n+1) steps hsteps (q 0) hij]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hlR : (2:ℝ)<l := by exact_mod_cast hl
  have hp : 0 ≤ ((l:ℝ)-2)/((l:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hpow := Real.rpow_le_rpow hbase hinc hp
  have hraw := physical_movement_fourth_le_raw_interpolation (n+1) l hl steps hsteps (q 0)
    hxs hij (by simp only [steps,sampleClockSteps_length];omega)
  have hQ0 : 0 ≤ physicalRawRatio (n+1) l steps 0 xs
      (Measure.pi fun v=>gaussianReal 0 (q 0 v)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le (n+1) l steps 0 xs _ id measurable_id)
  have hmass0 : 0 ≤ xs+physicalCutMass 0 steps j :=
    add_nonneg hxs.le (physicalCutMass_mem steps hsteps j).1
  exact hraw.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQ0) _) (pow_nonneg hmass0 _)) _))

section NativeAssembly
variable
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d)
    (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r ∈ Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {delta Ucap Lcap E : ℝ} (hUcap : 0<Ucap) (hLcap : 0<Lcap) (hE : 0<E)
    (hbang : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→H r<0→deriv α.val.val r=
      comparisonCap N delta Ucap Lcap E d (α.val.val r))
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (hcontact : ∀r ∈ U,H (sInf (ordConnectedComponent U r))=0 ∧
      (H (sSup (ordConnectedComponent U r))=0 ∨ sSup (ordConnectedComponent U r)=1))
variable (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
variable {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
local notation "Rc" => comparisonSweepQuantile hc hk hkc hm hM α
local notation "qc" => comparisonNativeClock hc hk hkc hm hM n b h α d lam
local notation "sc" => sampleClockSteps qc 0 as
local notation "Dc" => 9*Real.log N*((Lcap/N^delta)*Real.log ((1+Ucap)/Ucap))+
  2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) qc))
local notation "rad" => (fun i:Fin ((sc).length+1)=>Rc (physicalCutMass 0 sc (i:ℕ)))

include hN hlog hd hlam hb hlb hh hh0 hUcap hLcap ho hmesh in
theorem comparisonNativeDiameter_nonneg : 0 ≤ Dc := by
  have hnp : 0<N := zero_lt_one.trans_le hN
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hratio : 1 ≤ (1+Ucap)/Ucap := (le_div_iff₀ hUcap).mpr (by linarith)
  have hell : 0 ≤ (Lcap/N^delta)*Real.log ((1+Ucap)/Ucap) :=
    mul_nonneg (div_nonneg hLcap.le (Real.rpow_nonneg hnp.le _)) (Real.log_nonneg hratio)
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hclock := clockVariationBound_nonneg (physicalFeatureCoordinateBound n) qc
    (completedPathClock_monotone (n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1))
  exact add_nonneg (mul_nonneg (by positivity) hell)
    (mul_nonneg (by norm_num) (mul_nonneg (partitionMesh_nonneg_of_ordered as ho hmesh)
      (mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg 2 0 0)) hclock)))

include ho in
theorem comparisonNativeRadius_strictOn_positive_selected
    (A : Finset (Fin ((sc).length+1))) (hpos : ∀i ∈ A,0<pathMassDifferences sc 0 i) :
    StrictMonoOn rad (A:Set _) := by
  have hs : OrderedSteps 0 sc := sampleClockSteps_ordered qc as ho
  have hcuts := physicalCutMass_strictOn_positive_selected sc hs A hpos
  intro i hi j hj hij
  exact comparisonSweepQuantile_strictMono_native_geometry hc hk hkc hm hM α
    (physicalCutMass_mem sc hs i.val) (physicalCutMass_mem sc hs j.val) (hcuts hi hj hij)

include hN hlog hd hnd hlam hld hb hlb hh hh0 hH hJ hD hUcap hLcap hE hbang hopen hU hneg hcontact ho he hmesh

theorem actual_comparison_native_pair_geometry
    (l : ℕ) (hl : 2<l) {xs : ℝ} (hxs : 0<xs)
    {i j : Fin ((sc).length+1)} (hij : i<j)
    (hpi : 0<pathMassDifferences sc 0 i) (hui : 0<physicalCutMass 0 sc i.val)
    (hunit : wholeUnit U (rad i)=wholeUnit U (rad j)) :
    |physicalPathSecondMoment (n+1) sc (qc 0) j.val-
      physicalPathSecondMoment (n+1) sc (qc 0) i.val| ≤ Dc ∧
    physicalSideMovementMoment (n+1) sc (qc 0) i.val j.val ≤ Dc^(((l:ℝ)-2)/((l:ℝ)-1))*
      ((2*physicalRawRatio (n+1) l sc 0 xs (Measure.pi fun v=>gaussianReal 0 (qc 0 v)) id measurable_id)^(2*l)*
        (xs+physicalCutMass 0 sc j.val)^l)^(1/((l:ℝ)-1)) := by
  have hs : OrderedSteps 0 sc := sampleClockSteps_ordered qc as ho
  have hmass : physicalCutMass 0 sc i.val<physicalCutMass 0 sc j.val := by
    rw [pathMassDifferences_eq_cutMass] at hpi
    have hm := physicalCutMass_monotone sc hs (show i.val+1 ≤ j.val by exact_mod_cast hij)
    linarith
  have hrad := comparisonSweepQuantile_strictMono_native_geometry hc hk hkc hm hM α
    (physicalCutMass_mem sc hs i.val) (physicalCutMass_mem sc hs j.val) hmass
  obtain ⟨hiU,hjU⟩ := equal_wholeUnits_of_strict_points_is_cap U hunit hrad
  have hi : i.val ≤ as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt
  have hj : j.val ≤ as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ j.isLt
  have hci := physicalCutMass_sampleClockSteps qc 0 as i.val hi
  have hcj := physicalCutMass_sampleClockSteps qc 0 as j.val hj
  have hui' : 0<partitionPoint 0 as i.val := by simpa only [hci,sub_zero] using hui
  have hiU' : Rc (partitionPoint 0 as i.val) ∈ U := by simpa only [hci,sub_zero] using hiU
  have hjU' : Rc (partitionPoint 0 as j.val) ∈ ordConnectedComponent U (Rc (partitionPoint 0 as i.val)) := by
    simpa only [hci,hcj,sub_zero] using hjU
  have hinc := actual_comparison_sampled_component_increment hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh hij.le hj hui' hiU' hjU'
  have hmove := actual_comparison_sampled_component_reverse_fourth hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact l hl as ho he hmesh hij.le hj hui' hiU' hjU' hxs
  have hmono := physicalPathSecondMoment_mono (n+1) sc hs (qc 0) hij.le (by omega)
  exact ⟨by rw [abs_of_nonneg (sub_nonneg.mpr hmono)];exact hinc,hmove⟩

theorem actual_comparison_native_unit_oscillation
    (l : ℕ) (hl : 2<l) {xs : ℝ} (hxs : 0<xs)
    {K : ℕ} (A : Finset (Fin ((sc).length+1))) (unit : Fin ((sc).length+1)→Fin K)
    (hpos : ∀i ∈ A,0<pathMassDifferences sc 0 i)
    (hstart : ∀i ∈ A,0<physicalCutMass 0 sc i.val)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔wholeUnit U (rad i)=wholeUnit U (rad j)) :
    ∀i ∈ A,∀j ∈ A,unit j=unit i→
      physicalPathSecondMoment (n+1) sc (qc 0) j.val ≤ physicalPathSecondMoment (n+1) sc (qc 0) i.val+Dc := by
  intro i hi j hj hji
  rcases lt_trichotomy i j with hij|heq|hji'
  · have hpair := actual_comparison_native_pair_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
      hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs
      hij (hpos i hi) (hstart i hi) ((hclass i hi j hj).mp hji.symm)
    have hh := (abs_le.mp hpair.1).2
    linarith
  · subst j
    have hD0 := comparisonNativeDiameter_nonneg (delta:=delta) hc hk hkc hm hM hN hlog hd hlam n b h hb hlb hh hh0 α hUcap hLcap as ho hmesh
    linarith
  · have hpair := actual_comparison_native_pair_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
      hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs
      hji' (hpos j hj) (hstart j hj) ((hclass j hj i hi).mp hji)
    have hh := (abs_le.mp hpair.1).1
    linarith

theorem actual_comparison_native_reverse_contracts
    (l : ℕ) (hl : 2<l) {xs : ℝ} (hxs : 0<xs)
    {K : ℕ} (A : Finset (Fin ((sc).length+1))) (unit : Fin ((sc).length+1)→Fin K)
    (hpos : ∀i ∈ A,0<pathMassDifferences sc 0 i)
    (hstart : ∀i ∈ A,0<physicalCutMass 0 sc i.val)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔wholeUnit U (rad i)=wholeUnit U (rad j))
    (horder : MonotoneOn unit (A:Set _)) (x : ℕ→ℝ)
    (hx : ∀u:Fin K,x u.val<x (u.val+1)) (a b0 p q : ℝ) :
    (∀i j:Fin ((sc).length+1),i < j → 
      fineCoupling (physicalSelectedCellMass sc A) unit (fun u v=>coarseLeft x a p q u.val v.val) i j ≠ 0→
      physicalSideMovementMoment (n+1) sc (qc 0) i.val j.val ≤ Dc^(((l:ℝ)-2)/((l:ℝ)-1))*
        ((2*physicalRawRatio (n+1) l sc 0 xs (Measure.pi fun v=>gaussianReal 0 (qc 0 v)) id measurable_id)^(2*l)*
          (xs+physicalCutMass 0 sc j.val)^l)^(1/((l:ℝ)-1))) ∧
    (∀i j:Fin ((sc).length+1),j < i → 
      fineCoupling (physicalSelectedCellMass sc A) unit (fun u v=>coarseRight x b0 p q u.val v.val) i j ≠ 0→
      physicalSideMovementMoment (n+1) sc (qc 0) i.val j.val ≤ Dc^(((l:ℝ)-2)/((l:ℝ)-1))*
        ((2*physicalRawRatio (n+1) l sc 0 xs (Measure.pi fun v=>gaussianReal 0 (qc 0 v)) id measurable_id)^(2*l)*
          (xs+physicalCutMass 0 sc i.val)^l)^(1/((l:ℝ)-1))) := by
  constructor
  · intro i j hij hP
    obtain ⟨hi,hj⟩ := physicalFineCoupling_mem_selected sc A unit _ hP
    have heunit := nonzero_fineCoarseLeft_reverse_same_unit (physicalSelectedCellMass sc A) unit A
      horder x hx a p q hi hj hij hP
    exact (actual_comparison_native_pair_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
      hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs
      hij (hpos i hi) (hstart i hi) ((hclass i hi j hj).mp heunit)).2
  · intro i j hji hP
    obtain ⟨hi,hj⟩ := physicalFineCoupling_mem_selected sc A unit _ hP
    have heunit := nonzero_fineCoarseRight_reverse_same_unit (physicalSelectedCellMass sc A) unit A
      horder x hx b0 p q hi hj hji hP
    rw [physicalSideMovementMoment_comm (n+1) sc (qc 0) i.val j.val]
    exact (actual_comparison_native_pair_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
      hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs
      hji (hpos j hj) (hstart j hj) ((hclass j hj i hi).mp heunit.symm)).2

theorem actual_comparison_native_bins_height_contract
    (l : ℕ) (hl : 2<l) {xs y w : ℝ} (hxs : 0<xs) (hw : 0<w)
    {K bins : ℕ} (A : Finset (Fin ((sc).length+1))) (unit : Fin ((sc).length+1)→Fin K)
    (hpos : ∀i ∈ A,0<pathMassDifferences sc 0 i)
    (hstart : ∀i ∈ A,0<physicalCutMass 0 sc i.val)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔wholeUnit U (rad i)=wholeUnit U (rad j))
    (hmass : ∀i ∈ A,xs+physicalCutMass 0 sc i.val ≤ y)
    (hwidth : (physicalRawRatio (n+1) l sc 0 xs (Measure.pi fun k=>gaussianReal 0 (qc 0 k)) id measurable_id)^2*y ≤ (bins:ℝ)*w) :
    ∀b:Fin bins,∀i ∈ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment (n+1) sc (qc 0) i.val) A unit bins w b,
      ∀j ∈ NativeUnitHeight.bin (fun i=>physicalPathSecondMoment (n+1) sc (qc 0) i.val) A unit bins w b,
      |physicalPathSecondMoment (n+1) sc (qc 0) j.val-
        physicalPathSecondMoment (n+1) sc (qc 0) i.val| ≤ w+Dc := by
  have hosc := actual_comparison_native_unit_oscillation hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs A unit hpos hstart hclass
  intro z i hi j hj
  exact physical_native_unit_bins_profile_diameter (n+1) l (by omega) sc
    (sampleClockSteps_ordered qc as ho) (qc 0) A unit hxs hw hmass hwidth hosc z hi hj

end NativeAssembly

end
end OAI.SKFluctuations.LaplaceWindowFormalization
