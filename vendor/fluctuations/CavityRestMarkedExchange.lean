module

public import CavityRestMarkedPlacement

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem identical_fork_expect_swap (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) :
    (T.fork T).expect w φ q (fun σ=>Q σ.1 σ.2) x=
      (T.fork T).expect w φ q (fun σ=>Q σ.2 σ.1) x := by
  simp only [expect,weight_fork,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem single_full_rest_exchange {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement (single (S := S×B) as)) (hp : p∈(single as).markedAttach a)
    (q : ℕ → ι → ℝ≥0) (Q : S → S → ℝ) (x : ι → ℝ) :
    p.tree.cavityLeft.expect w φ q (fun σ=>
      Q (p.tree.cavityLeft.atSlot σ
          (cavityLeftSlot p.tree (p.embed (singleSlot as))))
        (p.tree.cavityLeft.atSlot σ (cavityLeftSlot p.tree p.mark))) x=
    p.tree.cavityLeft.expect w φ q (fun σ=>
      Q (p.tree.cavityLeft.atSlot σ (cavityLeftSlot p.tree p.mark))
        (p.tree.cavityLeft.atSlot σ
          (cavityLeftSlot p.tree (p.embed (singleSlot as))))) x := by
  induction as generalizing a x q with
  | nil =>
    rcases List.mem_cons.mp hp with rfl|hp
    · rfl
    · obtain rfl:=List.mem_singleton.mp hp
      exact identical_fork_expect_swap w φ leaf q Q x
  | cons m as ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact identical_fork_expect_swap w φ (single (S := S×B) (m::as)).cavityLeft q
        (fun σ τ=>Q
          ((single (S := S×B) (m::as)).cavityLeft.atSlot σ
            (cavityLeftSlot (single (S := S×B) (m::as)) (singleSlot (m::as))))
          ((single (S := S×B) (m::as)).cavityLeft.atSlot τ
            (cavityLeftSlot (single (S := S×B) (m::as)) (singleSlot (m::as))))) x
    · obtain ⟨z,hz,hpz⟩:=List.mem_map.mp hp
      subst p
      change (z.tree.cavityLeft.step m).expect w φ q
        (fun σ=>Q (z.tree.cavityLeft.atSlot σ
          (cavityLeftSlot z.tree (z.embed (singleSlot as))))
          (z.tree.cavityLeft.atSlot σ (cavityLeftSlot z.tree z.mark))) x=
        (z.tree.cavityLeft.step m).expect w φ q (fun σ=>
          Q (z.tree.cavityLeft.atSlot σ (cavityLeftSlot z.tree z.mark))
            (z.tree.cavityLeft.atSlot σ
              (cavityLeftSlot z.tree (z.embed (singleSlot as))))) x
      rw [expect_step hw φ m z.tree.cavityLeft ho.2.2 q,
        expect_step hw φ m z.tree.cavityLeft ho.2.2 q]
      congr 1
      funext y
      exact ih ho.2.2 z hz (fun j=>q (j+1)) y

theorem single_full_rest_external_exchange {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (E : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement (single (S := S×B) as)) (hp : p∈(single as).markedAttach a)
    (q : ℕ → ι → ℝ≥0) (Q : E.Assignment → S → S → ℝ) (x : ι → ℝ) :
    (E.fork p.tree.cavityLeft).expect w φ q (fun σ=>
      Q σ.1 (p.tree.cavityLeft.atSlot σ.2
          (cavityLeftSlot p.tree (p.embed (singleSlot as))))
        (p.tree.cavityLeft.atSlot σ.2 (cavityLeftSlot p.tree p.mark))) x=
    (E.fork p.tree.cavityLeft).expect w φ q (fun σ=>
      Q σ.1 (p.tree.cavityLeft.atSlot σ.2 (cavityLeftSlot p.tree p.mark))
        (p.tree.cavityLeft.atSlot σ.2
          (cavityLeftSlot p.tree (p.embed (singleSlot as))))) x := by
  rw [expect_fork,expect_fork]
  congr 1
  funext σ
  exact single_full_rest_exchange hw φ as ho p hp q (Q σ) x

end OAI.SKFluctuations.Hierarchy.ClockTree
