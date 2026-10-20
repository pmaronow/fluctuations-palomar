module

public import ComparisonSignedCavitySecondLowOccupiedGammaHighSupport
public import ComparisonSignedCavityHighRowsSupportReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowFourMarkedSum {S : Type} {as : List PositiveMass}
    (T : ClockTree S as)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      ((r.tree.markedAttach 0).map (fun s=>s.coeff*
        ((s.tree.markedAttach 0).map (fun t=>t.coeff*F p r s t)).sum)).sum)).sum)).sum

def nativeSecondLowFourHighSum {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (A : Fin 4 → T.Slot) (high : ℕ)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ) : ℝ :=
  ((nativeHighMarkedRows T (A 0) high 0).map (fun p=>p.coeff*
    ((nativeHighMarkedRows p.tree (p.embed (A 1)) high 0).map (fun r=>r.coeff*
      ((nativeHighMarkedRows r.tree (r.embed (p.embed (A 2))) high 0).map (fun s=>s.coeff*
        ((nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed (A 3)))) high 0).map
          (fun t=>t.coeff*F p r s t)).sum)).sum)).sum)).sum

theorem native_second_low_four_high_sum_congr {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (A : Fin 4 → T.Slot) (high : ℕ)
    (F G : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    (h : ∀p∈nativeHighMarkedRows T (A 0) high 0,
      ∀r∈nativeHighMarkedRows p.tree (p.embed (A 1)) high 0,
      ∀s∈nativeHighMarkedRows r.tree (r.embed (p.embed (A 2))) high 0,
      ∀t∈nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed (A 3)))) high 0,
        F p r s t=G p r s t) :
    nativeSecondLowFourHighSum T A high F=nativeSecondLowFourHighSum T A high G := by
  unfold nativeSecondLowFourHighSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [h p hp r hr s hs t ht]

theorem native_second_low_four_high_sum_eq_full_of_support {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (A : Fin 4 → T.Slot) (high : ℕ)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    (h : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,F p r s t≠0 →
        high<p.tree.splitIndex (p.embed (A 0)) p.mark ∧
        high<r.tree.splitIndex (r.embed (p.embed (A 1))) r.mark ∧
        high<s.tree.splitIndex (s.embed (r.embed (p.embed (A 2)))) s.mark ∧
        high<t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed (A 3))))) t.mark) :
    nativeSecondLowFourHighSum T A high F=nativeSecondLowFourMarkedSum T F := by
  let H:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    ((r.tree.markedAttach 0).map (fun s=>s.coeff*
      ((s.tree.markedAttach 0).map (fun t=>t.coeff*F p r s t)).sum)).sum
  have Hinner (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      ((nativeHighMarkedRows r.tree (r.embed (p.embed (A 2))) high 0).map (fun s=>s.coeff*
        ((nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed (A 3)))) high 0).map
          (fun t=>t.coeff*F p r s t)).sum)).sum=H p r := by
    apply native_two_high_nested_full_of_support
    · intro s hs t ht Hno
      by_contra HF
      exact Hno (h p hp r hr s hs t ht HF).2.2.1
    · intro s hs t ht Hno
      by_contra HF
      exact Hno (h p hp r hr s hs t ht HF).2.2.2
  have Hzero (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
      (Hno : ¬high<p.tree.splitIndex (p.embed (A 0)) p.mark ∨
        ¬high<r.tree.splitIndex (r.embed (p.embed (A 1))) r.mark) : H p r=0 := by
    dsimp only [H]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hx
    have Ht : ((s.tree.markedAttach 0).map (fun t=>t.coeff*F p r s t)).sum=0 := by
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hy
      have HF : F p r s t=0 := by
        by_contra HV
        rcases Hno with Hno|Hno
        · exact Hno (h p hp r hr s hs t ht HV).1
        · exact Hno (h p hp r hr s hs t ht HV).2.1
      rw [HF,mul_zero]
    rw [Ht,mul_zero]
  have Houter:=native_two_high_nested_full_of_support T (A 0) (A 1) high 0 H
    (fun p hp r hr Hno=>Hzero p hp r hr (Or.inl Hno))
    (fun p hp r hr Hno=>Hzero p hp r hr (Or.inr Hno))
  unfold nativeSecondLowFourHighSum nativeSecondLowFourMarkedSum
  change _=((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*H p r)).sum)).sum
  rw [←Houter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [Hinner p ((mem_nativeHighMarkedRows T (A 0) high 0 p).mp hp).1
    r ((mem_nativeHighMarkedRows p.tree (p.embed (A 1)) high 0 r).mp hr).1]

private theorem native_second_low_double_double_average_eq_four_sum
    {S : Type} {as : List PositiveMass} (T : ClockTree S as)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ) :
    nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree (F p r))=
      nativeSecondLowFourMarkedSum T F/4 := by
  unfold nativeSecondLowDoubleAverage nativeSecondLowFourMarkedSum
  simp only [div_eq_mul_inv,←mul_assoc,List.sum_map_mul_right]
  ring

theorem native_second_low_chronological_high_middle_support
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (a v z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (_hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (H0 : U ≤ p.tree.splitIndex (p.embed (nativeSecondLowChronologicalTargets j a v z 0)) p.mark)
    (H1 : U ≤ r.tree.splitIndex (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 1))) r.mark)
    (H2 : U ≤ s.tree.splitIndex (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 2)))) s.mark)
    (H3 : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 3))))) t.mark) :
    U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v)))) (nativeSecondLowWordMiddle p r s t j) := by
  have H0' : U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 0)))))
      (t.embed (s.embed (r.embed p.mark))) := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2]
    exact H0
  have H1' : U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 1)))))
      (t.embed (s.embed r.mark)) := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
    exact H1
  have H2' : U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 2)))))
      (t.embed s.mark) := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2]
    exact H2
  fin_cases j
  all_goals simp [nativeSecondLowChronologicalTargets,nativeSecondLowWordMiddle,nativeSecondLowPathMiddle]
    at H0' H1' H2' H3 ⊢
  all_goals first | exact H0' | exact H1' | exact H2' | exact H3

def nativeSecondLowOccupiedGammaHighPathLedger
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU) : ℝ :=
  nativeSecondLowFourHighSum T
    (nativeSecondLowChronologicalTargets j a (nativeSecondLowOccupiedBlockRepresentative T U hU B) z) (U-1)
    (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z j p r s t)/4

theorem native_second_low_occupied_gamma_path_ledger_eq_high_rows
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=
      nativeSecondLowOccupiedGammaHighPathLedger n q U b h K T hU P a z j B := by
  let v:=nativeSecondLowOccupiedBlockRepresentative T U hU B
  let A:=nativeSecondLowChronologicalTargets j a v z
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)=>
      if U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v)))) (nativeSecondLowWordMiddle p r s t j)
      then nativeSecondLowGammaWordValue n q U b h K P a z j p r s t else 0
  have Hsupport : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,F p r s t≠0 →
        U-1<p.tree.splitIndex (p.embed (A 0)) p.mark ∧
        U-1<r.tree.splitIndex (r.embed (p.embed (A 1))) r.mark ∧
        U-1<s.tree.splitIndex (s.embed (r.embed (p.embed (A 2)))) s.mark ∧
        U-1<t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed (A 3))))) t.mark := by
    intro p hp r hr s hs t ht HF
    have Hv : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
        (nativeSecondLowWordMiddle p r s t j) := by
      by_contra HV
      exact HF (by simp only [F,HV,ite_false])
    have HG : nativeSecondLowGammaWordValue n q U b h K P a z j p r s t≠0 := by
      simpa only [F,Hv,ite_true] using HF
    have H:=native_second_low_occupied_gamma_word_current_high_support n q U b h K T ho hU
      P a v z j p hp r hr s hs t ht Hv HG
    change U ≤ p.tree.splitIndex (p.embed (A 0)) p.mark ∧
      U ≤ r.tree.splitIndex (r.embed (p.embed (A 1))) r.mark ∧
      U ≤ s.tree.splitIndex (s.embed (r.embed (p.embed (A 2)))) s.mark ∧
      U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed (A 3))))) t.mark at H
    exact ⟨by omega,by omega,by omega,by omega⟩
  have Hprune:=native_second_low_four_high_sum_eq_full_of_support T A (U-1) F Hsupport
  have Hremove : nativeSecondLowFourHighSum T A (U-1) F=
      nativeSecondLowFourHighSum T A (U-1)
        (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z j p r s t) := by
    apply native_second_low_four_high_sum_congr
    intro p hp r hr s hs t ht
    obtain ⟨hp',H0⟩:=(mem_nativeHighMarkedRows T (A 0) (U-1) 0 p).mp hp
    obtain ⟨hr',H1⟩:=(mem_nativeHighMarkedRows p.tree (p.embed (A 1)) (U-1) 0 r).mp hr
    obtain ⟨hs',H2⟩:=(mem_nativeHighMarkedRows r.tree (r.embed (p.embed (A 2))) (U-1) 0 s).mp hs
    obtain ⟨ht',H3⟩:=(mem_nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed (A 3)))) (U-1) 0 t).mp ht
    dsimp only [A] at H0 H1 H2 H3
    have Hv:=native_second_low_chronological_high_middle_support T U a v z j
      p hp' r hr' s hs' t ht' (by omega) (by omega) (by omega) (by omega)
    exact ite_eq_left Hv
  calc
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=
        nativeSecondLowFourMarkedSum T F/4:=native_second_low_double_double_average_eq_four_sum T F
    _=nativeSecondLowFourHighSum T A (U-1) F/4:=congrArg (fun x : ℝ=>x/4) Hprune.symm
    _=nativeSecondLowOccupiedGammaHighPathLedger n q U b h K T hU P a z j B:=by
      rw [Hremove]
      rfl

end OAI.SKFluctuations.Cavity
