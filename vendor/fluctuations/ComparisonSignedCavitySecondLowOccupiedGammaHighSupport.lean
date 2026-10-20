module

public import ComparisonSignedCavitySecondLowObservedOccupiedGammaLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowChronologicalTargets {α : Type} (j : Fin 8) (a v z : α) : Fin 4 → α :=
  match j.val with
  | 0 => ![a,v,v,z]
  | 1 => ![a,v,z,v]
  | 2 => ![v,a,v,z]
  | 3 => ![v,a,z,v]
  | 4 => ![v,z,a,v]
  | 5 => ![z,v,a,v]
  | 6 => ![v,z,v,a]
  | _ => ![z,v,v,a]

def nativeSecondLowFinalWordMarks {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n × Bool) as} (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : Fin 4 → t.tree.Slot :=
  ![t.embed (s.embed (r.embed p.mark)),t.embed (s.embed r.mark),t.embed s.mark,t.mark]

theorem native_second_low_occupied_gamma_word_final_high_support
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a v z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (Hv : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
      (nativeSecondLowWordMiddle p r s t j))
    (HZ : nativeSecondLowGammaWordValue n q U b h K P a z j p r s t ≠ 0) :
    ∀ k : Fin 4, U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z k)))))
      (nativeSecondLowFinalWordMarks p r s t k) := by
  have HG : nativeSecondLowPathGamma t.tree U K
      (t.embed (s.embed (r.embed (p.embed a)))) (t.embed (s.embed (r.embed (p.embed z))))
      (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark)) (t.embed s.mark) t.mark j ≠ 0 :=
    (mul_ne_zero_iff.mp HZ).2
  let B := t.tree.cutBlock U hU
  have HB (u w : t.tree.Slot) (H : fullScalarCutGamma t.tree U K u w ≠ 0) : B u = B w := by
    apply (t.tree.cutBlock_eq_iff U hU u w).mpr
    by_contra HH
    exact H (fullScalarCutGamma_cross_zero t.tree ho U K u w hU (lt_of_not_ge HH))
  have HV : B (t.embed (s.embed (r.embed (p.embed v)))) = B (nativeSecondLowWordMiddle p r s t j) :=
    (t.tree.cutBlock_eq_iff U hU _ _).mpr Hv
  intro k
  rw [←t.tree.cutBlock_eq_iff U hU]
  fin_cases j
  all_goals dsimp only [nativeSecondLowPathGamma] at HG
  all_goals rcases mul_ne_zero_iff.mp HG with ⟨HAB,H3⟩
  all_goals rcases mul_ne_zero_iff.mp HAB with ⟨H1,H2⟩
  all_goals have H1B := HB _ _ H1
  all_goals have H2B := HB _ _ H2
  all_goals have H3B := HB _ _ H3
  all_goals fin_cases k
  all_goals simp_all [nativeSecondLowChronologicalTargets,nativeSecondLowFinalWordMarks,
    nativeSecondLowWordMiddle,nativeSecondLowPathMiddle,B]

theorem native_second_low_occupied_gamma_word_current_high_support
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a v z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (_hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0)
    (Hv : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
      (nativeSecondLowWordMiddle p r s t j))
    (HZ : nativeSecondLowGammaWordValue n q U b h K P a z j p r s t ≠ 0) :
    let A := nativeSecondLowChronologicalTargets j a v z
    U ≤ p.tree.splitIndex (p.embed (A 0)) p.mark ∧
    U ≤ r.tree.splitIndex (r.embed (p.embed (A 1))) r.mark ∧
    U ≤ s.tree.splitIndex (s.embed (r.embed (p.embed (A 2)))) s.mark ∧
    U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed (A 3))))) t.mark := by
  have H := native_second_low_occupied_gamma_word_final_high_support n q U b h K T ho hU P a v z j p r s t Hv HZ
  have H0 := H 0
  have H1 := H 1
  have H2 := H 2
  have H3 := H 3
  change U ≤ t.tree.splitIndex
    (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 0)))))
    (t.embed (s.embed (r.embed p.mark))) at H0
  change U ≤ t.tree.splitIndex
    (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 1)))))
    (t.embed (s.embed r.mark)) at H1
  change U ≤ t.tree.splitIndex
    (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 2)))))
    (t.embed s.mark) at H2
  change U ≤ t.tree.splitIndex
    (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 3))))) t.mark at H3
  rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
    (r.tree.markedAttach_embed_preserves 0 s hs).2,
    (p.tree.markedAttach_embed_preserves 0 r hr).2] at H0
  rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
    (r.tree.markedAttach_embed_preserves 0 s hs).2] at H1
  rw [(s.tree.markedAttach_embed_preserves 0 t ht).2] at H2
  exact ⟨H0,H1,H2,H3⟩

end OAI.SKFluctuations.Cavity
