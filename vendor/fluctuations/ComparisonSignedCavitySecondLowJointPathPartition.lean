module

public import ComparisonSignedCavitySecondLowActualPathBudget
public import ComparisonSignedCavitySecondLowPathPartition
public import ComparisonSignedCavityHighOutsideCommutation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeSecondLowWordValue (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
    fullScalarCutMoment t.tree U K (insertedSiteSlots (insertedSiteSlots [a,z] p r) s t)

def nativeSecondLowWordPath {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (U : ℕ) (hU : U≤as.length) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) (j : Fin 8) : Prop :=
  let B:=t.tree.cutBlock U hU
  nativeSecondLowBlockPath j
    (B (t.embed (s.embed (r.embed (p.embed a))))) (B (t.embed (s.embed (r.embed (p.embed z)))))
    (B (t.embed (s.embed (r.embed p.mark)))) (B (t.embed (s.embed r.mark)))
    (B (t.embed s.mark)) (B t.mark)

def nativeSecondLowWordMiddle {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) (j : Fin 8) : t.tree.Slot :=
  nativeSecondLowPathMiddle j (t.embed (s.embed (r.embed p.mark)))
    (t.embed (s.embed r.mark)) (t.embed s.mark) t.mark

def nativeSecondLowWordObserved {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (U : ℕ) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) (j : Fin 8) : Prop :=
  ∃v : T.Slot,U≤t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
    (nativeSecondLowWordMiddle p r s t j)

theorem native_second_low_word_value_eq_paths (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z<U)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    nativeSecondLowWordValue n q U b h K P a z p r s t=
      ∑j : Fin 8,if nativeSecondLowWordPath U hU a z p r s t j
        then nativeSecondLowWordValue n q U b h K P a z p r s t else 0 := by
  classical
  let V:=nativeSecondLowWordValue n q U b h K P a z p r s t
  by_cases HV : V=0
  · change V=∑j : Fin 8,if nativeSecondLowWordPath U hU a z p r s t j then V else 0
    simp [HV]
  have Hf : r.tree.splitIndex (r.embed p.mark) r.mark<U := by
    by_contra HH
    have HZ:=native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t (not_lt.mp HH)
    apply HV
    dsimp only [V,nativeSecondLowWordValue]
    rw [HZ]
    simp [ClockTree.disorderExpect]
  have He : t.tree.splitIndex (t.embed s.mark) t.mark<U := by
    by_contra HH
    have HZ:=native_second_low_joint_rest_test_zero_of_second_high n U b h K P p r s t (not_lt.mp HH)
    apply HV
    dsimp only [V,nativeSecondLowWordValue]
    rw [HZ]
    simp [ClockTree.disorderExpect]
  have Ha : t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed a))))
      (t.embed (s.embed (r.embed (p.embed z))))<U := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have Hf' : t.tree.splitIndex (t.embed (s.embed (r.embed p.mark)))
      (t.embed (s.embed r.mark))<U := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
    exact Hf
  have Hne (u v : t.tree.Slot) (H : t.tree.splitIndex u v<U) :
      t.tree.cutBlock U hU u≠t.tree.cutBlock U hU v := by
    intro HH
    have HL:=(t.tree.cutBlock_eq_iff U hU u v).mp HH
    omega
  apply native_second_low_path_partition _ _ _ _ _ _ (Hne _ _ Ha) (Hne _ _ Hf') (Hne _ _ He)
  intro _
  have HH:=native_second_low_joint_nonzero_path n q U b h K T ho hU P a z haz
    p hp r hr s hs t ht HV
  dsimp only [NativeSecondLowPathSupport] at HH
  have HB (u v : t.tree.Slot) (H : U≤t.tree.splitIndex u v) :
      t.tree.cutBlock U hU u=t.tree.cutBlock U hU v := (t.tree.cutBlock_eq_iff U hU u v).mpr H
  rcases HH with ⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|
    ⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩
  · exact ⟨0,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨1,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨2,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨3,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨4,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨5,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨6,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
  · exact ⟨7,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩

theorem native_second_low_list_sum_univ {α ι : Type*} [Fintype ι]
    (L : List α) (F : ι→α→ℝ) :
    (L.map (fun a=>∑j,F j a)).sum=∑j,(L.map (F j)).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih,Finset.sum_add_distrib]

theorem native_second_low_double_average_univ {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) {ι : Type*} [Fintype ι]
    (F : ι→(p : MarkedPlacement T)→MarkedPlacement p.tree→ℝ) :
    nativeSecondLowDoubleAverage T (fun p r=>∑j,F j p r)=
      ∑j,nativeSecondLowDoubleAverage T (F j) := by
  unfold nativeSecondLowDoubleAverage
  dsimp only
  simp only [Finset.mul_sum,native_second_low_list_sum_univ,Finset.sum_div]

def nativeSecondLowPathLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree (fun s t=>
    if nativeSecondLowWordPath U hU a z p r s t j
      then nativeSecondLowWordValue n q U b h K P a z p r s t else 0))

theorem native_second_low_joint_ledger_half_eq_eight_paths (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z<U) :
    nativeSecondLowJointLedger n q U b h K T P [a,z]/2=
      ∑j : Fin 8,nativeSecondLowPathLedger n q U b h K T hU P a z j/2 := by
  have Hinner (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      nativeSecondLowDoubleAverage r.tree (fun s t=>nativeSecondLowWordValue n q U b h K P a z p r s t)=
      ∑j : Fin 8,nativeSecondLowDoubleAverage r.tree (fun s t=>
        if nativeSecondLowWordPath U hU a z p r s t j
          then nativeSecondLowWordValue n q U b h K P a z p r s t else 0) := by
    rw [←native_second_low_double_average_univ]
    apply native_second_low_double_average_congr
    intro s hs t ht
    exact native_second_low_word_value_eq_paths n q U b h K T ho hU P a z haz p hp r hr s hs t ht
  have H:=native_second_low_double_average_congr T _ _ Hinner
  rw [native_second_low_double_average_univ] at H
  unfold nativeSecondLowJointLedger nativeSecondLowPathLedger
  rw [←Finset.sum_div]
  exact congrArg (fun a : ℝ=>a/2) H

end OAI.SKFluctuations.Cavity
