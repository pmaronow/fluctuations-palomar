module

public import ComparisonWholeCapRetainedCells
public import ComparisonSelectedFineCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coarseLeft_zero_of_unit_lt (x : ℕ → ℝ) {K : ℕ}
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (a p q : ℝ)
    {u v : Fin K} (huv : u < v) : coarseLeft x a p q u.val v.val=0 := by
  have hmono := unitPoints_monotoneOn x (fun i hi => (hx ⟨i,hi⟩).le)
  have hright : x (u.val+1) ≤ x v.val := hmono
    ⟨by omega,by omega⟩ ⟨by omega,v.is_lt.le⟩ (by exact_mod_cast huv)
  unfold coarseLeft
  have he (t : ℝ) : (Ico (x u.val) (x (u.val+1))).indicator
      (left a (x v.val) (x (v.val+1))) t=0 := by
    by_cases ht:t∈Ico (x u.val) (x (u.val+1))
    · rw [indicator_of_mem ht]
      have htv : t ≤ x v.val := ht.2.le.trans hright
      simp [left,leftFraction,min_eq_left htv,min_eq_left (htv.trans (hx v).le)]
    · exact indicator_of_notMem ht _
  simp_rw [he]
  simp

theorem coarseRight_zero_of_unit_lt (x : ℕ → ℝ) {K : ℕ}
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (b p q : ℝ)
    {u v : Fin K} (hvu : v < u) : coarseRight x b p q u.val v.val=0 := by
  have hmono := unitPoints_monotoneOn x (fun i hi => (hx ⟨i,hi⟩).le)
  have hleft : x (v.val+1) ≤ x u.val := hmono
    ⟨by omega,by omega⟩ ⟨by omega,u.is_lt.le⟩ (by exact_mod_cast hvu)
  unfold coarseRight
  have he (t : ℝ) : (Ico (x u.val) (x (u.val+1))).indicator
      (right b (x v.val) (x (v.val+1))) t=0 := by
    by_cases ht:t∈Ico (x u.val) (x (u.val+1))
    · rw [indicator_of_mem ht]
      have hvt : x (v.val+1) ≤ t := hleft.trans ht.1
      simp [right,rightFraction,max_eq_left hvt,max_eq_left ((hx v).le.trans hvt)]
    · exact indicator_of_notMem ht _
  simp_rw [he]
  simp

theorem nonzero_fineCoarseLeft_reverse_same_unit {N K : ℕ}
    (mass : Fin N → ℝ) (unit : Fin N → Fin K) (J : Finset (Fin N))
    (hm : MonotoneOn unit (J:Set (Fin N))) (x : ℕ → ℝ)
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (a p q : ℝ)
    {i j : Fin N} (hi:i∈J) (hj:j∈J) (hij:i < j)
    (hP : fineCoupling mass unit (fun u v => coarseLeft x a p q u.val v.val) i j≠0) :
    unit i=unit j := by
  have hle := hm hi hj hij.le
  by_contra hne
  have hlt : unit i < unit j := lt_of_le_of_ne hle hne
  have hz := coarseLeft_zero_of_unit_lt x hx a p q hlt
  apply hP
  simp only [fineCoupling,hz,mul_zero]

theorem nonzero_fineCoarseRight_reverse_same_unit {N K : ℕ}
    (mass : Fin N → ℝ) (unit : Fin N → Fin K) (J : Finset (Fin N))
    (hm : MonotoneOn unit (J:Set (Fin N))) (x : ℕ → ℝ)
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (b p q : ℝ)
    {i j : Fin N} (hi:i∈J) (hj:j∈J) (hji:j < i)
    (hP : fineCoupling mass unit (fun u v => coarseRight x b p q u.val v.val) i j≠0) :
    unit i=unit j := by
  have hle := hm hj hi hji.le
  by_contra hne
  have hlt : unit j < unit i := lt_of_le_of_ne hle (Ne.symm hne)
  have hz := coarseRight_zero_of_unit_lt x hx b p q hlt
  apply hP
  simp only [fineCoupling,hz,mul_zero]

theorem equal_wholeUnits_of_strict_points_is_cap (U : Set ℝ) {r t : ℝ}
    (he : wholeUnit U r=wholeUnit U t) (hrt:r < t) :
    r∈U ∧ t∈ordConnectedComponent U r := by
  have ht : t∈wholeUnit U r := he.symm ▸ self_mem_wholeUnit U t
  have hrU:r∈U := by
    by_contra hr
    have htr : t=r := by simpa [wholeUnit,hr] using ht
    exact hrt.ne htr.symm
  exact ⟨hrU,by simpa [wholeUnit,hrU] using ht⟩

theorem physicalCellMassMidpoint_strict_order {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    {i j : Fin (steps.length+1)} (hij:i < j)
    (hi:0 < pathMassDifferences steps 0 i) (hj:0 < pathMassDifferences steps 0 j) :
    physicalCellMassMidpoint steps i < physicalCellMassMidpoint steps j := by
  have hm := physicalCutMass_monotone steps ha (show i.val+1 ≤ j.val by exact_mod_cast hij)
  exact (physicalCellMassMidpoint_strict_inside steps i hi).2.trans_le hm |>.trans
    (physicalCellMassMidpoint_strict_inside steps j hj).1

theorem nonzero_fineCoarseLeft_reverse_same_cap {N K : ℕ}
    (mass : Fin N → ℝ) (unit : Fin N → Fin K) (J : Finset (Fin N))
    (hm : MonotoneOn unit (J:Set (Fin N))) (x : ℕ → ℝ)
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (a p q : ℝ)
    (U : Set ℝ) (r : Fin N → ℝ) (hr : StrictMonoOn r (J:Set (Fin N)))
    (hclass : ∀i∈J,∀j∈J,unit i=unit j ↔ wholeUnit U (r i)=wholeUnit U (r j))
    {i j : Fin N} (hi:i∈J) (hj:j∈J) (hij:i < j)
    (hP : fineCoupling mass unit (fun u v => coarseLeft x a p q u.val v.val) i j≠0) :
    unit i=unit j ∧ r i∈U ∧ r j∈ordConnectedComponent U (r i) := by
  have he := nonzero_fineCoarseLeft_reverse_same_unit mass unit J hm x hx a p q hi hj hij hP
  exact ⟨he,equal_wholeUnits_of_strict_points_is_cap U ((hclass i hi j hj).mp he) (hr hi hj hij)⟩

theorem nonzero_fineCoarseRight_reverse_same_cap {N K : ℕ}
    (mass : Fin N → ℝ) (unit : Fin N → Fin K) (J : Finset (Fin N))
    (hm : MonotoneOn unit (J:Set (Fin N))) (x : ℕ → ℝ)
    (hx : ∀u:Fin K,x u.val < x (u.val+1)) (b p q : ℝ)
    (U : Set ℝ) (r : Fin N → ℝ) (hr : StrictMonoOn r (J:Set (Fin N)))
    (hclass : ∀i∈J,∀j∈J,unit i=unit j ↔ wholeUnit U (r i)=wholeUnit U (r j))
    {i j : Fin N} (hi:i∈J) (hj:j∈J) (hji:j < i)
    (hP : fineCoupling mass unit (fun u v => coarseRight x b p q u.val v.val) i j≠0) :
    unit i=unit j ∧ r j∈U ∧ r i∈ordConnectedComponent U (r j) := by
  have he := nonzero_fineCoarseRight_reverse_same_unit mass unit J hm x hx b p q hi hj hji hP
  exact ⟨he,equal_wholeUnits_of_strict_points_is_cap U ((hclass j hj i hi).mp he.symm) (hr hj hi hji)⟩

end OAI.SKFluctuations.WholeUnitSideKernel
