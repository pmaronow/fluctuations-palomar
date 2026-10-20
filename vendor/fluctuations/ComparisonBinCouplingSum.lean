module

public import ComparisonActualIntegratedDefect

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open scoped BigOperators

theorem bin_coupling_sum_marginals {B I : Type*} [Fintype B] [Fintype I]
    (P : B → I → I → ℝ) (mass : B → I → ℝ) {L : ℝ}
    (hP : ∀b i j,0 ≤ P b i j)
    (hrow : ∀b i,(∑j,P b i j) ≤ mass b i)
    (hcol : ∀b j,(∑i,P b i j) ≤ L*mass b j) :
    (∀i j,0 ≤ ∑b,P b i j) ∧
    (∀i,(∑j,∑b,P b i j) ≤ ∑b,mass b i) ∧
    (∀j,(∑i,∑b,P b i j) ≤ L*(∑b,mass b j)) := by
  refine ⟨fun i j=>Finset.sum_nonneg (fun b _=>hP b i j),?_,?_⟩
  · intro i
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun b _=>hrow b i)
  · intro j
    rw [Finset.sum_comm,Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _=>hcol b j)

theorem bin_joint_cost_sum_eq {B I : Type*} [Fintype B] [Fintype I]
    (P : B → I → I → ℝ) (cost : I → I → ℝ) :
    (∑b,∑i,∑j,P b i j*cost i j)=(∑i,∑j,(∑b,P b i j)*cost i j) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext i
  exact Finset.sum_comm

theorem bin_mass_cost_sum_eq {B I : Type*} [Fintype B] [Fintype I]
    (mass : B → I → ℝ) (cost : I → ℝ) :
    (∑b,∑i,mass b i*cost i)=(∑i,(∑b,mass b i)*cost i) := by
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem bin_sum_support {B : Type*} [Fintype B] (P : B → ℝ)
    (hP : (∑b,P b)≠0) : ∃b,P b≠0 := by
  obtain ⟨b,_,hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  exact ⟨b,hb⟩

end OAI.SKFluctuations.WholeUnitSideKernel
