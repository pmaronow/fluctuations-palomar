module

public import ComparisonSignedCavityActualDummyScalarModel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
set_option maxHeartbeats 7000000
variable {S : Type*}
universe u v

def withDummy : {as : List PositiveMass}→ClockTree S as→ClockTree (S×Bool) as
  | _,.leaf=>.leaf
  | _,.step a T=>.step a T.withDummy
  | _,.fork T R=>.fork T.withDummy R.withDummy

def withDummySlot : {as : List PositiveMass}→(T : ClockTree S as)→T.Slot≃T.withDummy.Slot
  | _,.leaf=>Equiv.refl _
  | _,.step _ T=>T.withDummySlot
  | _,.fork T R=>T.withDummySlot.sumCongr R.withDummySlot

theorem withDummy_cavityLeft {as : List PositiveMass} (T : ClockTree S as) :
    T.withDummy.cavityLeft=T := by
  induction T with
  | leaf=>rfl
  | step a T ih=>exact congrArg (ClockTree.step a) ih
  | fork T R ihT ihR=>exact congrArg₂ ClockTree.fork ihT ihR

def withDummyPhysical {as : List PositiveMass} (T : ClockTree S as) :
    T.withDummy.Assignment→T.Assignment := fun σ=>
  cast (congrArg ClockTree.Assignment T.withDummy_cavityLeft) (T.withDummy.cavityAssignment σ).1

theorem disorderExpect_cast_tree [Fintype S] {ι : Type*} [Fintype ι]
    {as : List PositiveMass} {R T : ClockTree S as} (h : R=T)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (P : T.Assignment→ℝ) (x : ι→ℝ) :
    R.disorderExpect w φ v q (fun σ=>P (cast (congrArg ClockTree.Assignment h) σ)) x=
      T.disorderExpect w φ v q P x := by
  subst T
  rfl

theorem atSlot_cast_tree {as : List PositiveMass} {R T : ClockTree S as} (h : R=T)
    (σ : R.Assignment) (s : R.Slot) :
    T.atSlot (cast (congrArg ClockTree.Assignment h) σ) (cast (congrArg ClockTree.Slot h) s)=
      R.atSlot σ s := by
  subst T
  rfl

theorem dummy_cast_sum_inl {A A' : Type u} {B B' : Type v} (ha : A=A') (hb : B=B')
    (h : Sum A B=Sum A' B') (x : A) : cast h (Sum.inl x)=Sum.inl (cast ha x) := by
  subst A';subst B';rfl

theorem dummy_cast_sum_inr {A A' : Type u} {B B' : Type v} (ha : A=A') (hb : B=B')
    (h : Sum A B=Sum A' B') (x : B) : cast h (Sum.inr x)=Sum.inr (cast hb x) := by
  subst A';subst B';rfl

theorem withDummy_leftSlot {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) :
    cast (congrArg ClockTree.Slot T.withDummy_cavityLeft)
      (T.withDummy.cavityLeftSlot (T.withDummySlot s))=s := by
  induction T with
  | leaf=>rfl
  | step a T ih=>exact ih s
  | fork T R ihT ihR=>
    cases s with
    | inl s=>
      change cast _ (Sum.inl (T.withDummy.cavityLeftSlot (T.withDummySlot s)))=Sum.inl s
      exact (dummy_cast_sum_inl (congrArg ClockTree.Slot T.withDummy_cavityLeft)
        (congrArg ClockTree.Slot R.withDummy_cavityLeft) _ _).trans (congrArg Sum.inl (ihT s))
    | inr s=>
      change cast _ (Sum.inr (R.withDummy.cavityLeftSlot (R.withDummySlot s)))=Sum.inr s
      exact (dummy_cast_sum_inr (congrArg ClockTree.Slot T.withDummy_cavityLeft)
        (congrArg ClockTree.Slot R.withDummy_cavityLeft) _ _).trans (congrArg Sum.inr (ihR s))

theorem withDummyPhysical_atSlot {as : List PositiveMass} (T : ClockTree S as)
    (σ : T.withDummy.Assignment) (s : T.Slot) :
    T.atSlot (T.withDummyPhysical σ) s=(T.withDummy.atSlot σ (T.withDummySlot s)).1 := by
  have H:=atSlot_cast_tree T.withDummy_cavityLeft (T.withDummy.cavityAssignment σ).1
    (T.withDummy.cavityLeftSlot (T.withDummySlot s))
  rw [T.withDummy_leftSlot] at H
  exact H.trans (T.withDummy.atSlot_cavityLeft σ (T.withDummySlot s))

theorem splitIndex_withDummy {as : List PositiveMass} (T : ClockTree S as) (s t : T.Slot) :
    T.withDummy.splitIndex (T.withDummySlot s) (T.withDummySlot t)=T.splitIndex s t := by
  induction T with
  | leaf=>rfl
  | step a T ih=>exact congrArg (1+·) (ih s t)
  | fork T R ihT ihR=>cases s <;> cases t <;> first | rfl | exact ihT _ _ | exact ihR _ _

theorem withDummy_cavityRight {as : List PositiveMass} (T : ClockTree (S×Bool) as) :
    T.withDummy.cavityRight=T.cavityRight := by
  induction T with
  | leaf=>rfl
  | step a T ih=>exact congrArg (ClockTree.step a) ih
  | fork T R ihT ihR=>exact congrArg₂ ClockTree.fork ihT ihR

def withDummyScalar {as : List PositiveMass} (T : ClockTree (S×Bool) as) :
    T.withDummy.Assignment→T.cavityRight.Assignment := fun σ=>
  cast (congrArg ClockTree.Assignment T.withDummy_cavityRight) (T.withDummy.cavityAssignment σ).2

theorem withDummy_rightSlot {as : List PositiveMass} (T : ClockTree (S×Bool) as) (s : T.Slot) :
    cast (congrArg ClockTree.Slot T.withDummy_cavityRight)
      (T.withDummy.cavityRightSlot (T.withDummySlot s))=T.cavityRightSlot s := by
  induction T with
  | leaf=>rfl
  | step a T ih=>exact ih s
  | fork T R ihT ihR=>
    cases s with
    | inl s=>
      change cast _ (Sum.inl (T.withDummy.cavityRightSlot (T.withDummySlot s)))=Sum.inl (T.cavityRightSlot s)
      exact (dummy_cast_sum_inl (congrArg ClockTree.Slot T.withDummy_cavityRight)
        (congrArg ClockTree.Slot R.withDummy_cavityRight) _ _).trans (congrArg Sum.inl (ihT s))
    | inr s=>
      change cast _ (Sum.inr (R.withDummy.cavityRightSlot (R.withDummySlot s)))=Sum.inr (R.cavityRightSlot s)
      exact (dummy_cast_sum_inr (congrArg ClockTree.Slot T.withDummy_cavityRight)
        (congrArg ClockTree.Slot R.withDummy_cavityRight) _ _).trans (congrArg Sum.inr (ihR s))

theorem withDummyScalar_atSlot {as : List PositiveMass} (T : ClockTree (S×Bool) as)
    (σ : T.withDummy.Assignment) (s : T.Slot) :
    T.cavityRight.atSlot (T.withDummyScalar σ) (T.cavityRightSlot s)=
      (T.withDummy.atSlot σ (T.withDummySlot s)).2 := by
  have H:=atSlot_cast_tree T.withDummy_cavityRight (T.withDummy.cavityAssignment σ).2
    (T.withDummy.cavityRightSlot (T.withDummySlot s))
  rw [T.withDummy_rightSlot] at H
  exact H.trans (T.withDummy.atSlot_cavityRight σ (T.withDummySlot s))

end OAI.SKFluctuations.Hierarchy.ClockTree
