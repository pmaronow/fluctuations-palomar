module

public import ComparisonCapSideVarianceComposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem fixedCapContactWeight_equiv_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι≃κ)
    (a z weight : κ→ℝ) (A : Set ℝ) (w : ℝ→ℝ) :
    fixedCapContactWeight (a∘e) (z∘e) (weight∘e) A w=
      fixedCapContactWeight a z weight A w := by
  funext r
  unfold fixedCapContactWeight
  congr 1
  simpa only [Function.comp_apply] using
    e.sum_comp (fun t=>(Ioo (a t) (z t)).indicator (fun _=>weight t) r)

theorem fixedCapContactWeight_contact_restrict
    {ι : Type*} [Fintype ι] (a z weight : ι→ℝ) (A I : Set ℝ) (w : ℝ→ℝ) :
    fixedCapContactWeight a z weight A (I.indicator w)=
      fixedCapContactWeight a z weight (A∩I) w := by
  funext r
  unfold fixedCapContactWeight
  congr 1
  by_cases hA : r∈A <;> by_cases hI : r∈I <;> simp [hA,hI]

theorem fixedCapContactWeight_equiv_contact_restrict
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι≃κ)
    (a z weight : κ→ℝ) (A I : Set ℝ) (w : ℝ→ℝ) :
    fixedCapContactWeight (a∘e) (z∘e) (weight∘e) A (I.indicator w)=
      fixedCapContactWeight a z weight (A∩I) w := by
  rw [fixedCapContactWeight_equiv_reindex e,
    fixedCapContactWeight_contact_restrict a z weight A I w]

end OAI.SKFluctuations.LaplaceWindowFormalization
