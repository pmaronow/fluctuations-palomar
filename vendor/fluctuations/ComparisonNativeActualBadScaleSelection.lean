module

public import ComparisonNativeActualSelectedScaleMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

theorem comparison_exists_bad_scale_with_regular_outer
    (alpha : ℝ→ℝ) {A cl cu : ℝ} (hA : 0 < A)
    (hcl : cl ≤ 1) (hcu : 1 ≤ cu) (hterminal : alpha 1=1)
    (hbad : ∃r∈Icc (min A 1) 1,alpha r < cl*r ∨ cu*r < alpha r) :
    ∃x∈Icc A 1,(alpha x < cl*x ∨ cu*x < alpha x) ∧
      ∀r∈Icc (min (2*x) 1) 1,cl*r ≤ alpha r ∧ alpha r ≤ cu*r := by
  classical
  have hterminalGood : cl*1 ≤ alpha 1 ∧ alpha 1 ≤ cu*1 := by
    simpa only [hterminal,mul_one] using And.intro hcl hcu
  have hA1 : A < 1 := by
    by_contra hn
    obtain ⟨r,hr,hbad⟩ := hbad
    rw [min_eq_right (le_of_not_gt hn)] at hr
    have he : r=1 := le_antisymm hr.2 hr.1
    subst r
    rcases hbad with hbad|hbad
    · exact (not_lt_of_ge hterminalGood.1) hbad
    · exact (not_lt_of_ge hterminalGood.2) hbad
  let bad : Set ℝ := {r | r∈Icc A 1 ∧ (alpha r < cl*r ∨ cu*r < alpha r)}
  have hne : bad.Nonempty := by
    obtain ⟨r,hr,hb⟩ := hbad
    exact ⟨r,by simpa only [min_eq_left hA1.le] using hr,hb⟩
  have hbounded : BddAbove bad := ⟨1,fun _ hr=>hr.1.2⟩
  have hsup : 0 < sSup bad := by
    obtain ⟨r,hr⟩ := hne
    exact (hA.trans_le hr.1.1).trans_le (le_csSup hbounded hr)
  obtain ⟨x,hx,hxnear⟩ := exists_lt_of_lt_csSup hne
    (show sSup bad/2 < sSup bad by linarith)
  refine ⟨x,hx.1,hx.2,?_⟩
  intro r hr
  by_cases h2 : 2*x ≤ 1
  · rw [min_eq_left h2] at hr
    by_contra hnot
    have hbadR : alpha r < cl*r ∨ cu*r < alpha r := by
      by_cases hlo : cl*r ≤ alpha r
      · exact Or.inr (lt_of_not_ge (fun hup=>hnot ⟨hlo,hup⟩))
      · exact Or.inl (lt_of_not_ge hlo)
    have hxr : x ≤ r := by linarith only [hr.1,hA,hx.1.1]
    have hsupR := le_csSup hbounded (show r∈bad from ⟨⟨hx.1.1.trans hxr,hr.2⟩,hbadR⟩)
    linarith only [hr.1,hxnear,hsupR]
  · rw [min_eq_right (le_of_not_ge h2)] at hr
    have he : r=1 := le_antisymm hr.2 hr.1
    simpa only [he] using hterminalGood

end OAI.SKFluctuations.LaplaceWindowFormalization
