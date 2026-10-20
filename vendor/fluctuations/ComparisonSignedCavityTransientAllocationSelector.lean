module

public import ComparisonSignedCavityTransientMixedAllocation
public import CavityFiniteProfileClipping
public import CavityAllDiagonalCancellation

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

def nativeLowAllocationWords (Lsmall Llarge : ℕ → S → S → ℝ) :
    ℕ → List (List (ℕ → S → S → ℝ))
  | 0 => [[]]
  | k+1 => (nativeLowAllocationWords Lsmall Llarge k).map (List.cons Lsmall) ++
      (nativeLowAllocationWords Lsmall Llarge k).map (List.cons Llarge)

theorem native_profileJets_low_word_sum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (pre : List (ℕ → S → S → ℝ)) (Lsmall Llarge : ℕ → S → S → ℝ)
    (k : ℕ) (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x
      (pre++List.replicate k (fun j σ τ => Lsmall j σ τ+Llarge j σ τ)) T P =
      ((nativeLowAllocationWords Lsmall Llarge k).map
        (fun word => disorderProfileJets w φ v q x (pre++word) T P)).sum := by
  induction k generalizing pre with
  | zero => simp only [List.replicate_zero,List.append_nil,nativeLowAllocationWords,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  | succ k ih =>
    simp only [List.replicate_succ]
    rw [native_profileJets_add_kernel]
    have hs := ih (pre++[Lsmall])
    have hl := ih (pre++[Llarge])
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hs hl
    rw [hs,hl]
    simp only [nativeLowAllocationWords,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,List.append_assoc,List.cons_append,List.nil_append]

theorem nativeLowAllocationWords_length (Lsmall Llarge : ℕ → S → S → ℝ)
    (k : ℕ) (word : List (ℕ → S → S → ℝ))
    (hword : word∈nativeLowAllocationWords Lsmall Llarge k) : word.length=k := by
  induction k generalizing word with
  | zero =>
    have H : word=[] := List.mem_singleton.mp hword
    simpa only [H,List.length_nil]
  | succ k ih =>
    rcases List.mem_append.mp hword with H | H
    all_goals
      obtain ⟨word,hw,rfl⟩ := List.mem_map.mp H
      simp only [List.length_cons,ih word hw]

theorem nativeLowAllocationWords_dichotomy (Lsmall Llarge : ℕ → S → S → ℝ)
    (k : ℕ) (word : List (ℕ → S → S → ℝ))
    (hword : word∈nativeLowAllocationWords Lsmall Llarge k) :
    word=List.replicate k Llarge ∨ Lsmall∈word := by
  induction k generalizing word with
  | zero => exact Or.inl (List.mem_singleton.mp hword)
  | succ k ih =>
    rcases List.mem_append.mp hword with H | H
    · obtain ⟨word,hw,rfl⟩ := List.mem_map.mp H
      exact Or.inr List.mem_cons_self
    · obtain ⟨word,hw,rfl⟩ := List.mem_map.mp H
      rcases ih word hw with H | H
      · exact Or.inl (by simp only [H,List.replicate_succ])
      · exact Or.inr (List.mem_cons_of_mem Llarge H)

theorem native_profileJets_allOffDiagonal_without_budget {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (A : ι → ℝ) (hA : ∀ σ i,(φ σ (Pi.single i 1))^2=A i)
    (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (hq : ∀ i,Monotone (fun j => q j i))
    (hq0 : ∀ i,v i ≤ q 0 i) (Ds : List (ℕ → ι → ℝ))
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderOffDiagonalJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P := by
  obtain ⟨B,hB,hDs⟩ := native_finite_directions_bounded as.length Ds
  rw [disorderProfileJets_eq_clipDirections w φ v q x Ds T P,
    disorderOffDiagonalJets_eq_clipDirections w φ v q x Ds T P]
  exact disorderProfileJets_eq_allOffDiagonal hw φ A hA ho v q hq hq0
    (Ds.map (clipDirection as.length)) hB (clipDirection_bounded as.length Ds hB hDs) T P x

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeCoordinateCutPart {ι : Type*} (pred : ℕ → Prop) [DecidablePred pred]
    (D : ℕ → ι → ℝ) : ℕ → ι → ℝ := fun j i => if pred j then D j i else 0

theorem nativeCoordinateCutPart_partition {ι : Type*} (pred : ℕ → Prop) [DecidablePred pred]
    (D : ℕ → ι → ℝ) :
    D=fun j i => nativeCoordinateCutPart pred D j i+nativeCoordinateCutPart (fun j => ¬pred j) D j i := by
  funext j i
  by_cases H : pred j <;> simp only [nativeCoordinateCutPart,H,not_true_eq_false,
    not_false_eq_true,↓reduceIte,zero_add,add_zero]

theorem native_cutLowError_atom_partition (n U i star : ℕ) (b h K : ℕ → ℝ) :
    cutLowError n U b h K=fun j z =>
      nativeCoordinateCutPart (fun j => j=i) (cutLowError n U b h K) j z+
      nativeCoordinateCutPart (fun j => j≠i ∧ j=star) (cutLowError n U b h K) j z+
      nativeCoordinateCutPart (fun j => j≠i ∧ j≠star) (cutLowError n U b h K) j z := by
  funext j z
  by_cases hi : j=i <;> by_cases hs : j=star <;>
    simp_all [nativeCoordinateCutPart]

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
  (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
  (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
include ho hq0 hq hb hh hK hbm hhm hKm

theorem nativeTransientLowErrorJet_errorFirst (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (k : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientLowErrorJet n q U b h K T P x k l t=
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((cutLowError n U b h K::List.replicate k (cutLSlope n U t b h K)).map
          (ReplicaTree.coordinateProfile (fullFeature n))) T P := by
  unfold nativeTransientLowErrorJet
  apply ClockTree.native_profileJets_perm_without_budget (fullWeight_pos n) (fullFeature n) T ho
    0 (cutFullVariance n q U l t b h K)
    (fun i => cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 i)
  simpa only [List.append_nil] using (List.perm_middle (a:=cutLowError n U b h K)
    (l₁:=List.replicate k (cutLSlope n U t b h K)) (l₂:=[]))

theorem nativeTransientHighJet_errorFirst (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (k : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientHighJet n q U b h K T P x k l t=
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((cutTSlope n U 0 b h K::List.replicate k (cutLSlope n U t b h K)).map
          (ReplicaTree.coordinateProfile (fullFeature n))) T P := by
  unfold nativeTransientHighJet
  apply ClockTree.native_profileJets_perm_without_budget (fullWeight_pos n) (fullFeature n) T ho
    0 (cutFullVariance n q U l t b h K)
    (fun i => cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 i)
  simpa only [List.append_nil] using (List.perm_middle (a:=cutTSlope n U 0 b h K)
    (l₁:=List.replicate k (cutLSlope n U t b h K)) (l₂:=[]))

end
end OAI.SKFluctuations.Cavity
