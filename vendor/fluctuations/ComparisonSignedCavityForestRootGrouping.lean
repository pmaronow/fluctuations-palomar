module

public import ComparisonSignedCavityGeneratedResourcesForks
public import ComparisonSignedCavityExteriorForestDisorder

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

def nativeFirstSlot : {as : List PositiveMass} → (T : ClockTree S as) → T.Slot
  | _,.leaf=>()
  | _,.step _ T=>nativeFirstSlot T
  | _,.fork T _=>Sum.inl (nativeFirstSlot T)

def NativeRootForkFree : {as : List PositiveMass} → ClockTree S as → Prop
  | _,.leaf=>True
  | _,.step _ _=>True
  | _,.fork _ _=>False

structure NativeRootForestGrouping {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) where
  exterior : ClockTree S as
  occupied : ClockTree S as
  target : occupied.Slot
  read : exterior.Assignment → occupied.Assignment → T.Assignment
  embed : T.Slot → (exterior.fork occupied).Slot
  occupiedEmbed : occupied.Slot → T.Slot
  target_eq : occupiedEmbed target=s
  occupied_embed : ∀c,embed (occupiedEmbed c)=Sum.inr c
  read_at : ∀η σ c,T.atSlot (read η σ) c=(exterior.fork occupied).atSlot (η,σ) (embed c)
  old_splits : ∀c d,(exterior.fork occupied).splitIndex (embed c) (embed d)=T.splitIndex c d
  occupied_splits : ∀c d,T.splitIndex (occupiedEmbed c) (occupiedEmbed d)=occupied.splitIndex c d
  root_free : NativeRootForkFree occupied

namespace NativeRootForestGrouping

def trivial {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (h : NativeRootForkFree T) : NativeRootForestGrouping T s where
  exterior:=single as
  occupied:=T
  target:=s
  read:=fun _ σ=>σ
  embed:=Sum.inr
  occupiedEmbed:=id
  target_eq:=rfl
  occupied_embed:=fun _=>rfl
  read_at:=fun _ _ _=>rfl
  old_splits:=fun _ _=>rfl
  occupied_splits:=fun _ _=>rfl
  root_free:=h

def leftEmbed {as : List PositiveMass} {T : ClockTree S as} {s : T.Slot}
    (g : NativeRootForestGrouping T s) (V : ClockTree S as) :
    (T.fork V).Slot → ((V.fork g.exterior).fork g.occupied).Slot
  | Sum.inl c=>match g.embed c with
    | Sum.inl e=>Sum.inl (Sum.inr e)
    | Sum.inr d=>Sum.inr d
  | Sum.inr v=>Sum.inl (Sum.inl v)

def left {as : List PositiveMass} {T : ClockTree S as} {s : T.Slot}
    (g : NativeRootForestGrouping T s) (V : ClockTree S as) :
    NativeRootForestGrouping (T.fork V) (Sum.inl s) where
  exterior:=V.fork g.exterior
  occupied:=g.occupied
  target:=g.target
  read:=fun η σ=>(g.read η.2 σ,η.1)
  embed:=g.leftEmbed V
  occupiedEmbed:=fun c=>Sum.inl (g.occupiedEmbed c)
  target_eq:=congrArg Sum.inl g.target_eq
  occupied_embed:=by intro c;simp [leftEmbed,g.occupied_embed]
  read_at:=by
    intro η σ c
    cases c with
    | inl c=>
      have H:=g.read_at η.2 σ c
      cases he:g.embed c <;> simpa [leftEmbed,he,atSlot] using H
    | inr c=>rfl
  old_splits:=by
    intro c d
    cases c with
    | inl c=>
      cases d with
      | inl d=>
        have H:=g.old_splits c d
        cases hc:g.embed c <;> cases hd:g.embed d <;>
          simpa [leftEmbed,hc,hd,splitIndex] using H
      | inr d=>cases hc:g.embed c <;> simp [leftEmbed,hc,splitIndex]
    | inr c=>
      cases d with
      | inl d=>cases hd:g.embed d <;> simp [leftEmbed,hd,splitIndex]
      | inr d=>rfl
  occupied_splits:=g.occupied_splits
  root_free:=g.root_free

def rightEmbed {as : List PositiveMass} (T : ClockTree S as) {V : ClockTree S as} {s : V.Slot}
    (g : NativeRootForestGrouping V s) :
    (T.fork V).Slot → ((T.fork g.exterior).fork g.occupied).Slot
  | Sum.inl t=>Sum.inl (Sum.inl t)
  | Sum.inr c=>match g.embed c with
    | Sum.inl e=>Sum.inl (Sum.inr e)
    | Sum.inr d=>Sum.inr d

def right {as : List PositiveMass} (T : ClockTree S as) {V : ClockTree S as} {s : V.Slot}
    (g : NativeRootForestGrouping V s) : NativeRootForestGrouping (T.fork V) (Sum.inr s) where
  exterior:=T.fork g.exterior
  occupied:=g.occupied
  target:=g.target
  read:=fun η σ=>(η.1,g.read η.2 σ)
  embed:=g.rightEmbed T
  occupiedEmbed:=fun c=>Sum.inr (g.occupiedEmbed c)
  target_eq:=congrArg Sum.inr g.target_eq
  occupied_embed:=by intro c;simp [rightEmbed,g.occupied_embed]
  read_at:=by
    intro η σ c
    cases c with
    | inl c=>rfl
    | inr c=>
      have H:=g.read_at η.2 σ c
      cases he:g.embed c <;> simpa [rightEmbed,he,atSlot] using H
  old_splits:=by
    intro c d
    cases c with
    | inl c=>
      cases d with
      | inl d=>rfl
      | inr d=>cases hd:g.embed d <;> simp [rightEmbed,hd,splitIndex]
    | inr c=>
      cases d with
      | inl d=>cases hc:g.embed c <;> simp [rightEmbed,hc,splitIndex]
      | inr d=>
        have H:=g.old_splits c d
        cases hc:g.embed c <;> cases hd:g.embed d <;>
          simpa [rightEmbed,hc,hd,splitIndex] using H
  occupied_splits:=g.occupied_splits
  root_free:=g.root_free

end NativeRootForestGrouping

theorem NativeRootForestGrouping.read_target {as : List PositiveMass} {T : ClockTree S as}
    {s : T.Slot} (g : NativeRootForestGrouping T s) (η : g.exterior.Assignment)
    (σ : g.occupied.Assignment) : T.atSlot (g.read η σ) s=g.occupied.atSlot σ g.target := by
  calc
    _=T.atSlot (g.read η σ) (g.occupiedEmbed g.target):=
      congrArg (T.atSlot (g.read η σ)) g.target_eq.symm
    _=g.occupied.atSlot σ g.target:=by rw [g.read_at,g.occupied_embed];rfl

theorem NativeRootForestGrouping.read_high_relative {as : List PositiveMass} {T : ClockTree S as}
    {s : T.Slot} (g : NativeRootForestGrouping T s) (c : T.Slot) (h : 0<T.splitIndex s c) :
    ∃d : g.occupied.Slot,
      (∀η σ,T.atSlot (g.read η σ) c=g.occupied.atSlot σ d) ∧
      g.occupied.splitIndex g.target d=T.splitIndex s c := by
  have he : g.embed s=Sum.inr g.target := by
    calc
      _=g.embed (g.occupiedEmbed g.target):=congrArg g.embed g.target_eq.symm
      _=Sum.inr g.target:=g.occupied_embed g.target
  have H:=g.old_splits s c
  rw [he] at H
  cases hc:g.embed c with
  | inl e=>
    simp only [hc,splitIndex,Sum.elim_inr,Sum.elim_inl] at H
    omega
  | inr d=>
    refine ⟨d,?_,?_⟩
    · intro η σ
      rw [g.read_at,hc]
      rfl
    · simpa only [hc,splitIndex,Sum.elim_inr] using H

def nativeGroupRootForest : {as : List PositiveMass} → (T : ClockTree S as) →
    (s : T.Slot) → NativeRootForestGrouping T s
  | _,.leaf,s=>.trivial .leaf s trivial
  | _,.step b T,s=>.trivial (T.step b) s trivial
  | _,.fork T V,s=>match s with
    | Sum.inl s=>(nativeGroupRootForest T s).left V
    | Sum.inr s=>(nativeGroupRootForest V s).right T

variable {ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_expect_nested_commute {as : List PositiveMass} (T V : ClockTree S as)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (Q : T.Assignment → V.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ=>V.expect w φ q (Q σ) x) x=
      V.expect w φ q (fun τ=>T.expect w φ q (fun σ=>Q σ τ) x) x := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem nativeGroupRootForest_expect {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ q Q x=
      ((nativeGroupRootForest T s).exterior.fork (nativeGroupRootForest T s).occupied).expect w φ q
        (fun σ=>(Q ((nativeGroupRootForest T s).read σ.1 σ.2))) x := by
  induction T generalizing a with
  | leaf=>
    change _=((single []).fork (leaf (S:=S))).expect w φ q (fun σ=>Q σ.2) x
    rw [expect_fork]
    exact (expect_const hw φ (single []) ho q ((leaf (S:=S)).expect w φ q Q x) x).symm
  | @step b tail T ih=>
    change _=((single (b::tail)).fork (T.step b)).expect w φ q (fun σ=>Q σ.2) x
    rw [expect_fork]
    exact (expect_const hw φ (single (b::tail)) ho q ((T.step b).expect w φ q Q x) x).symm
  | @fork tail T V ihT ihV=>
    cases s with
    | inl s=>
      change _=(((V.fork (nativeGroupRootForest T s).exterior).fork
        (nativeGroupRootForest T s).occupied)).expect w φ q
        (fun σ=>Q ((nativeGroupRootForest T s).read σ.1.2 σ.2,σ.1.1)) x
      simp only [expect_fork]
      rw [native_expect_nested_commute T V]
      apply congrArg (fun F=>V.expect w φ q F x)
      funext τ
      rw [ihT s ho (fun σ=>Q (σ,τ)),expect_fork]
    | inr s=>
      change _=(((T.fork (nativeGroupRootForest V s).exterior).fork
        (nativeGroupRootForest V s).occupied)).expect w φ q
        (fun σ=>Q (σ.1.1,(nativeGroupRootForest V s).read σ.1.2 σ.2)) x
      simp only [expect_fork]
      apply congrArg (fun F=>T.expect w φ q F x)
      funext τ
      rw [ihV s ho (fun σ=>Q (τ,σ)),expect_fork]

end OAI.SKFluctuations.Hierarchy.ClockTree
