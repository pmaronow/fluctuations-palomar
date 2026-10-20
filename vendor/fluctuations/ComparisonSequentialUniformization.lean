module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter
open scoped Topology
set_option autoImplicit false

theorem eventual_uniform_bound_of_every_cofinal_sequence
    (A : ℕ → Type*) (Bound : ℝ → (n : ℕ) → A n → Prop)
    (hmono : ∀C C' n (a : A n),C≤C' → Bound C n a → Bound C' n a)
    (hseq : ∀dim : ℕ → ℕ,Tendsto dim atTop atTop →
      ∀a : (j : ℕ) → A (dim j),
        ∃C : ℝ,0<C ∧ ∀ᶠj in atTop,Bound C (dim j) (a j)) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,∀a : A n,Bound C n a := by
  classical
  by_contra Hnot
  have hbad (j : ℕ) :
      ∃n,j≤n ∧ ∃a : A n,¬ Bound ((j:ℝ)+1) n a := by
    by_contra H
    have Hgood : ∀ᶠn in atTop,∀a : A n,Bound ((j:ℝ)+1) n a :=
      eventually_atTop.mpr ⟨j,by
        intro n hn a
        by_contra hno
        exact H ⟨n,hn,a,hno⟩⟩
    exact Hnot ⟨(j:ℝ)+1,by positivity,Hgood⟩
  choose dim hdim a ha using hbad
  have hdimTop : Tendsto dim atTop atTop :=
    tendsto_atTop_mono hdim tendsto_id
  obtain ⟨C,hC,Hseq⟩ := hseq dim hdimTop a
  have Hlarge : ∀ᶠj : ℕ in atTop,C≤(j:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop C
  obtain ⟨j,hj⟩ := (Hseq.and Hlarge).exists
  have Hnew : Bound ((j:ℝ)+1) (dim j) (a j) :=
    hmono C ((j:ℝ)+1) (dim j) (a j) (by linarith only [hj.2]) hj.1
  exact (ha j) Hnew

end OAI.SKFluctuations.LaplaceWindowFormalization
