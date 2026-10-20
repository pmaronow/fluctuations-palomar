module

public import CavityDiagonalHigherJets
public import CavityPhysicalJetBounds

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 def disorderOffDiagonalJets (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    List (ℕ → S → S → ℝ) → (T : ClockTree S as) → (T.Assignment → ℝ) → ℝ
  | [], T, P => T.disorderExpect w φ v q P x
  | K::Ks, T, P => ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ks r.tree (profilePairTest P K p r)).sum).sum/2

 theorem coordinateProfile_self_of_square (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : ι → ℝ) (hA : ∀ σ i, (φ σ (Pi.single i 1))^2=A i)
    (D : ℕ → ι → ℝ) (j : ℕ) (σ : S) :
    ReplicaTree.coordinateProfile φ D j σ σ = ∑ i, D j i*A i := by
  classical
  unfold ReplicaTree.coordinateProfile
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc,←pow_two,hA]

 theorem disorderProfileJets_eq_allOffDiagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : ι → ℝ)
    (hA : ∀ σ i, (φ σ (Pi.single i 1))^2=A i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (Ds : List (ℕ → ι → ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B) (T : ClockTree S as)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderOffDiagonalJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P := by
  induction Ds generalizing T with
  | nil => rfl
  | cons D Ds ih =>
    have hOld : ∀ E ∈ Ds, ∀ j i, |E j i| ≤ B :=
      fun E hE => hDs E (List.mem_cons_of_mem _ hE)
    have hd (σ : S) : ReplicaTree.coordinateProfile φ D as.length σ σ =
        ∑ i, D as.length i*A i := coordinateProfile_self_of_square φ A hA D as.length σ
    simp only [List.map_cons]
    rw [T.disorderProfileJets_errorFirst_eq_offDiagonal hw φ ho v q hq hq0 Ds hB hOld P hd x]
    simp only [disorderOffDiagonalProfileJets,disorderOffDiagonalJets]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [ih hOld r.tree (profilePairTest P (ReplicaTree.coordinateProfile φ D) p r)]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem fullFeature_coordinateProfile_self (n : ℕ) (D : ℕ → FullCoordinate n → ℝ)
    (j : ℕ) (σ : Spin n × Bool) :
    ReplicaTree.coordinateProfile (fullFeature n) D j σ σ =
      ∑ i, D j i*(fullAmplitude n i)^2 := by
  classical
  apply ClockTree.coordinateProfile_self_of_square
  intro τ i
  rw [fullFeature_single_any_decidable]
  simpa only [fullFeature_single] using fullFeature_square n τ i

end OAI.SKFluctuations.Cavity
