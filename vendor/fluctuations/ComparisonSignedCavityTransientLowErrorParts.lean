module

public import ComparisonSignedCavityTransientMixedAllocation
public import ComparisonSignedCavityActualResourceHistories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

inductive NativeTransientLowErrorPart where
  | initial
  | star
  | moving
deriving DecidableEq

def nativeTransientLowErrorPartKernel {S : Type*} (i star : ℕ)
    (A : ℕ→S→S→ℝ) : NativeTransientLowErrorPart→ℕ→S→S→ℝ
  | .initial,j,σ,τ=>if j=i then A j σ τ else 0
  | .star,j,σ,τ=>if j≠i ∧ j=star then A j σ τ else 0
  | .moving,j,σ,τ=>if j≠i ∧ j≠star then A j σ τ else 0

theorem native_transient_low_error_kernel_partition {S : Type*} (i star : ℕ)
    (A : ℕ→S→S→ℝ) :
    A=fun j σ τ=>nativeTransientLowErrorPartKernel i star A .initial j σ τ+
      nativeTransientLowErrorPartKernel i star A .star j σ τ+
      nativeTransientLowErrorPartKernel i star A .moving j σ τ := by
  funext j σ τ
  by_cases hi : j=i <;> by_cases hs : j=star <;>
    simp_all [nativeTransientLowErrorPartKernel]

def nativeTransientLowErrorPartJet (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i star U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (part : NativeTransientLowErrorPart) (k : ℕ) (l t : ℝ) : ℝ :=
  ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))++
      [nativeTransientLowErrorPartKernel i star
        (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)) part]) T P

theorem native_transient_low_error_jet_partition (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i star U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t : ℝ) :
    nativeTransientLowErrorJet n q U b h K T P x k l t=
      nativeTransientLowErrorPartJet n q i star U b h K T P x .initial k l t+
      nativeTransientLowErrorPartJet n q i star U b h K T P x .star k l t+
      nativeTransientLowErrorPartJet n q i star U b h K T P x .moving k l t := by
  unfold nativeTransientLowErrorJet nativeTransientLowErrorPartJet
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil]
  conv_lhs => rw [native_transient_low_error_kernel_partition i star
    (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K))]
  rw [ClockTree.native_profileJets_add_kernel (pre:=List.replicate k _ ) (post:=[]),
    ClockTree.native_profileJets_add_kernel (pre:=List.replicate k _ ) (post:=[])]

theorem native_transient_productJet3_add (g f h : Fin 4→ℝ) (k : Fin 4) :
    productJet3 g (fun i=>f i+h i) k=productJet3 g f k+productJet3 g h k := by
  fin_cases k <;> simp only [productJet3] <;> ring

def nativeTransientCenteredLowErrorPart (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i star U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (Q : T.cavityRight.Assignment→ℝ) (x : ActiveCoordinate n→ℝ)
    (part : NativeTransientLowErrorPart) (l t : ℝ) : ℝ :=
  let g:=fun j : Fin 4=>cutLowJet n q U b h K T
    (fun σ=>Q (T.cavityAssignment σ).2) (cavityEmbed x) j l 0
  let D:=fun J k=>nativeTransientLowErrorPartJet n q i star U b h K T J (cavityEmbed x) part k l t
  let J:=fun σ=>P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2
  let A:=fun σ=>P (T.cavityAssignment σ).1
  l*(D J 3-productJet3 g (fun j=>D A j) 3)+
    3*(D J 2-productJet3 g (fun j=>D A j) 2)

theorem native_transient_centered_low_error_parts
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (Q : T.cavityRight.Assignment→ℝ) (x : ActiveCoordinate n→ℝ)
    (l t : ℝ) :
    let g:=fun j : Fin 4=>cutLowJet n q U b h K T
      (fun σ=>Q (T.cavityAssignment σ).2) (cavityEmbed x) j l 0
    let D:=fun J k=>nativeTransientLowErrorJet n q U b h K T J (cavityEmbed x) k l t
    let J:=fun σ=>P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2
    let A:=fun σ=>P (T.cavityAssignment σ).1
    l*(D J 3-productJet3 g (fun j=>D A j) 3)+
      3*(D J 2-productJet3 g (fun j=>D A j) 2)=
      nativeTransientCenteredLowErrorPart n q i star U b h K T P Q x .initial l t+
      nativeTransientCenteredLowErrorPart n q i star U b h K T P Q x .star l t+
      nativeTransientCenteredLowErrorPart n q i star U b h K T P Q x .moving l t := by
  dsimp only
  unfold nativeTransientCenteredLowErrorPart
  dsimp only
  simp_rw [native_transient_low_error_jet_partition n q i star U b h K T,
    native_transient_productJet3_add]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity

def nativeTransientLowFirstSlot {S : Type*} : {as : List PositiveMass}→(T : ClockTree S as)→T.Slot
  | _,.leaf=>()
  | _,.step _ T=>nativeTransientLowFirstSlot T
  | _,.fork T _=>Sum.inl (nativeTransientLowFirstSlot T)

theorem native_transient_forkCost_zero_of_pair_splits {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (f : ℕ→ℝ)
    (hf : ∀c d : T.Slot,c≠d→f (T.splitIndex c d)=0) : T.forkCost f=0 := by
  induction T generalizing f with
  | leaf=>rfl
  | step a T ih=>exact ih _ hf
  | fork T V ihT ihV=>
    have Hz : f 0=0:=hf (Sum.inl (nativeTransientLowFirstSlot T))
      (Sum.inr (nativeTransientLowFirstSlot V)) (by simp)
    have HT:=ihT f (by intro c d hcd;exact hf (Sum.inl c) (Sum.inl d) (by simpa))
    have HV:=ihV f (by intro c d hcd;exact hf (Sum.inr c) (Sum.inr d) (by simpa))
    simp only [forkCost,Hz,HT,HV,add_zero]

theorem native_persistent_moving_low_profile_forkCost_zero {S : Type*} {as : List PositiveMass}
    {i star U : ℕ} (T : ClockTree S as) (hT : NativePersistentLowForks i star U T)
    (f : ℕ→ℝ) (hhigh : ∀j,U≤j→f j=0) :
    T.forkCost (fun j=>if j≠i ∧ j≠star then f j else 0)=0 := by
  apply native_transient_forkCost_zero_of_pair_splits
  intro c d hcd
  rcases hT c d with hi|hs|hh
  · simp only [hi,ne_eq,not_true_eq_false,false_and,ite_false]
  · simp only [hs,ne_eq,not_true_eq_false,and_false,ite_false]
  · rw [hhigh _ hh]
    simp only [ite_self]

end OAI.SKFluctuations.Hierarchy.ClockTree
