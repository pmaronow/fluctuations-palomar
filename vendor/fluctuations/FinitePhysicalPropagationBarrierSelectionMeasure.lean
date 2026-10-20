module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Set
open scoped BigOperators ENNReal
set_option maxHeartbeats 2500000

def physicalPropagationThresholdCell (R Z : ℝ → ℝ) (a b lo hi : ℝ) : Set ℝ :=
  {u | u ∈ Icc a b ∧ R u ≤ lo ∧ hi ≤ Z u}

theorem physical_propagation_threshold_cell_interval
    {R Z : ℝ → ℝ} (hR : Monotone R) (hZ : Monotone Z)
    (hRc : Continuous R) (hZc : Continuous Z)
    {a b lo hi L : ℝ}
    (hmeasure : ENNReal.ofReal L < volume (physicalPropagationThresholdCell R Z a b lo hi)) :
    ∃ left right : ℝ,left ∈ Icc a b ∧ right ∈ Icc a b ∧
      L < right-left ∧ ∀ u ∈ Icc left right,R u ≤ lo ∧ hi ≤ Z u := by
  let S := physicalPropagationThresholdCell R Z a b lo hi
  have hmeasureS : ENNReal.ofReal L < volume S := hmeasure
  have hclosed : IsClosed S :=
    isClosed_Icc.inter ((isClosed_le hRc continuous_const).inter
      (isClosed_le continuous_const hZc))
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun u hu => hu.1)
  have hnonempty : S.Nonempty := by
    by_contra hnot
    have hempty : S=∅ := Set.not_nonempty_iff_eq_empty.mp hnot
    have hzero : volume S=0 := by rw [hempty,measure_empty]
    exact not_lt_of_ge (show (0:ℝ≥0∞) ≤ ENNReal.ofReal L from bot_le)
      (by simpa only [hzero] using hmeasureS)
  obtain ⟨left,hleft⟩ := hcompact.exists_isLeast hnonempty
  obtain ⟨right,hright⟩ := hcompact.exists_isGreatest hnonempty
  have hinterval : S=Icc left right := by
    apply Set.Subset.antisymm
    · intro u hu
      exact ⟨hleft.2 hu,hright.2 hu⟩
    · intro u hu
      refine ⟨⟨hleft.1.1.1.trans hu.1,hu.2.trans hright.1.1.2⟩,?_,?_⟩
      · exact (hR hu.2).trans hright.1.2.1
      · exact hleft.1.2.2.trans (hZ hu.1)
  have hwidth : L < right-left := by
    have hvol : ENNReal.ofReal L < ENNReal.ofReal (right-left) := by
      simpa only [hinterval,Real.volume_Icc] using hmeasureS
    by_contra hnot
    have hh := ENNReal.ofReal_le_ofReal (le_of_not_gt hnot)
    exact not_lt_of_ge hh hvol
  exact ⟨left,right,hleft.1.1,hright.1.1,hwidth,
    fun u hu => (show u ∈ S from hinterval.symm ▸ hu).2⟩

theorem physical_propagation_upward_disagreement_value_cover
    (J : ℕ) (R Z : ℝ → ℝ) {a b step : ℝ} (hstep : 0 < step)
    (hRrange : ∀ u ∈ Icc a b,3*step ≤ Z u-R u →
      0 ≤ R u ∧ R u ≤ (J:ℝ)*step) :
    {u | u ∈ Icc a b ∧ 3*step ≤ Z u-R u} ⊆
      ⋃ j : Fin (J+1),physicalPropagationThresholdCell R Z a b
        (((((j:ℕ):ℝ)+1))*step) (((((j:ℕ):ℝ)+2))*step) := by
  intro u hu
  have hratio0 : 0 ≤ R u/step := div_nonneg (hRrange u hu.1 hu.2).1 hstep.le
  have hratioJ : R u/step ≤ (J:ℝ) :=
    (div_le_iff₀ hstep).mpr (hRrange u hu.1 hu.2).2
  let j := Nat.floor (R u/step)
  have hj : j ≤ J := Nat.floor_le_of_le hratioJ
  have hfloor := Nat.floor_le hratio0
  have hceil := Nat.lt_floor_add_one (R u/step)
  have hlower : (j:ℝ)*step ≤ R u := (le_div_iff₀ hstep).mp hfloor
  have hupper : R u < ((j:ℝ)+1)*step := (div_lt_iff₀ hstep).mp hceil
  refine mem_iUnion.mpr ⟨⟨j,Nat.lt_succ_of_le hj⟩,?_,hupper.le,?_⟩
  · exact hu.1
  · change ((j:ℝ)+2)*step ≤ Z u
    nlinarith only [hlower,hu.2,hstep]

theorem physical_propagation_upward_disagreement_selects_interval
    (J : ℕ) {R Z : ℝ → ℝ} (hR : Monotone R) (hZ : Monotone Z)
    (hRc : Continuous R) (hZc : Continuous Z)
    {a b step L : ℝ} (hstep : 0 < step)
    (hRrange : ∀ u ∈ Icc a b,3*step ≤ Z u-R u →
      0 ≤ R u ∧ R u ≤ (J:ℝ)*step)
    (hbadmass : (J+1:ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc a b ∧ 3*step ≤ Z u-R u}) :
    ∃ j : Fin (J+1),∃ left right : ℝ,
      left ∈ Icc a b ∧ right ∈ Icc a b ∧ L < right-left ∧
      ∀ u ∈ Icc left right,
        R u ≤ (((j:ℕ):ℝ)+1)*step ∧ (((j:ℕ):ℝ)+2)*step ≤ Z u := by
  classical
  let cell := fun j : Fin (J+1) => physicalPropagationThresholdCell R Z a b
    ((((j:ℕ):ℝ)+1)*step) (((((j:ℕ):ℝ)+2))*step)
  have hcover := physical_propagation_upward_disagreement_value_cover J R Z hstep hRrange
  have hsum : volume {u | u ∈ Icc a b ∧ 3*step ≤ Z u-R u} ≤ ∑ j,volume (cell j) :=
    (measure_mono hcover).trans (measure_iUnion_fintype_le volume cell)
  have hexists : ∃ j,ENNReal.ofReal L < volume (cell j) := by
    by_contra hnot
    have hbound : ∀ j,volume (cell j) ≤ ENNReal.ofReal L := by
      intro j
      by_contra hlarge
      exact hnot ⟨j,lt_of_not_ge hlarge⟩
    have hsumsmall : (∑ j,volume (cell j)) ≤ (J+1:ℝ≥0∞)*ENNReal.ofReal L := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (J+1)))) => hbound j)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one] using hh
    exact not_lt_of_ge (hsum.trans hsumsmall) hbadmass
  obtain ⟨j,hj⟩ := hexists
  obtain ⟨left,right,hleftrange,hrightrange,hlength,hseparation⟩ :=
    physical_propagation_threshold_cell_interval hR hZ hRc hZc hj
  exact ⟨j,left,right,hleftrange,hrightrange,hlength,hseparation⟩

theorem physical_propagation_downward_disagreement_selects_interval
    (J : ℕ) {R Z : ℝ → ℝ} (hR : Monotone R) (hZ : Monotone Z)
    (hRc : Continuous R) (hZc : Continuous Z)
    {a b step L : ℝ} (hstep : 0 < step)
    (hRupper : ∀ u ∈ Icc a b,R u ≤ (J:ℝ)*step)
    (hZ0 : ∀ u ∈ Icc a b,0 ≤ Z u)
    (hbadmass : (J+1:ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc a b ∧ 3*step ≤ R u-Z u}) :
    ∃ j : Fin (J+1),∃ left right : ℝ,
      left ∈ Icc a b ∧ right ∈ Icc a b ∧ L < right-left ∧
      ∀ u ∈ Icc left right,
        Z u ≤ (((j:ℕ):ℝ)+1)*step ∧ (((j:ℕ):ℝ)+2)*step ≤ R u := by
  apply physical_propagation_upward_disagreement_selects_interval J hZ hR hZc hRc hstep _ hbadmass
  intro u hu hgap
  refine ⟨hZ0 u hu,?_⟩
  have hZR : Z u ≤ R u := by nlinarith only [hgap,hstep]
  exact hZR.trans (hRupper u hu)

theorem physical_propagation_absolute_disagreement_selects_interval
    (J : ℕ) {R Z : ℝ → ℝ} (hR : Monotone R) (hZ : Monotone Z)
    (hRc : Continuous R) (hZc : Continuous Z)
    {a b step L : ℝ} (hstep : 0 < step)
    (hRrange : ∀ u ∈ Icc a b,0 ≤ R u ∧ R u ≤ (J:ℝ)*step)
    (hZ0 : ∀ u ∈ Icc a b,0 ≤ Z u)
    (hbadmass : 2*(J+1:ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc a b ∧ 3*step ≤ |Z u-R u|}) :
    ∃ j : Fin (J+1),∃ left right : ℝ,
      left ∈ Icc a b ∧ right ∈ Icc a b ∧ L < right-left ∧
      ((∀ u ∈ Icc left right,
        R u ≤ (((j:ℕ):ℝ)+1)*step ∧ (((j:ℕ):ℝ)+2)*step ≤ Z u) ∨
       (∀ u ∈ Icc left right,
        Z u ≤ (((j:ℕ):ℝ)+1)*step ∧ (((j:ℕ):ℝ)+2)*step ≤ R u)) := by
  classical
  let up : Set ℝ := {u | u ∈ Icc a b ∧ 3*step ≤ Z u-R u}
  let down : Set ℝ := {u | u ∈ Icc a b ∧ 3*step ≤ R u-Z u}
  have hcover : {u | u ∈ Icc a b ∧ 3*step ≤ |Z u-R u|} ⊆ up∪down := by
    intro u hu
    rcases le_total (R u) (Z u) with h | h
    · left
      exact ⟨hu.1,by simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hu.2⟩
    · right
      refine ⟨hu.1,?_⟩
      have hh := hu.2
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
      linarith
  have hmeasure := (measure_mono (μ := volume) hcover).trans
    (measure_union_le (μ := volume) up down)
  have horientation : (J+1:ℝ≥0∞)*ENNReal.ofReal L < volume up ∨
      (J+1:ℝ≥0∞)*ENNReal.ofReal L < volume down := by
    by_contra hnot
    push_neg at hnot
    have hsum := add_le_add hnot.1 hnot.2
    have heq : (J+1:ℝ≥0∞)*ENNReal.ofReal L+(J+1:ℝ≥0∞)*ENNReal.ofReal L=
        2*(J+1:ℝ≥0∞)*ENNReal.ofReal L := by
      rw [two_mul]
      exact (add_mul _ _ _).symm
    rw [heq] at hsum
    exact not_lt_of_ge (hmeasure.trans hsum) hbadmass
  rcases horientation with hup | hdown
  · obtain ⟨j,left,right,hleftrange,hrightrange,hlength,hsep⟩ :=
      physical_propagation_upward_disagreement_selects_interval J hR hZ hRc hZc hstep
        (fun u hu _ => hRrange u hu) hup
    exact ⟨j,left,right,hleftrange,hrightrange,hlength,Or.inl hsep⟩
  · obtain ⟨j,left,right,hleftrange,hrightrange,hlength,hsep⟩ :=
      physical_propagation_downward_disagreement_selects_interval J hR hZ hRc hZc hstep
        (fun u hu => (hRrange u hu).2) hZ0 hdown
    exact ⟨j,left,right,hleftrange,hrightrange,hlength,Or.inr hsep⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
