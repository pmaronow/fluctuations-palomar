module

public import CavityTwoErrorActualBudget
public import CavityAllDiagonalCancellation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_twoErrorFirst_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::A::Ds, ∀ j i, |D j i| ≤ B)
    {C M rho p : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hrho : 0 < rho) (hp : 2 < p)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ)
    (hA : ∀ j σ τ, |ReplicaTree.coordinateProfile φ A j σ τ| ≤ M)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j (pairSpin as j σ).1
        (pairSpin as j σ).2|^((p/(p-2))*(Ds.length:ℝ))) x ≤ rho^((p/(p-2))*(Ds.length:ℝ))) :
    |disorderProfileJets w φ v q x ((A::A::Ds).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*pairForkVariation (r+2)*absJetVariation (r+4) Ds.length*C*
        M^((p-2)/p)*M^((p-2)/p)*rho^Ds.length*
        (T.forkCost (fun j => D j^(4/p))+(∫ u, edgeDensity 0 as (fun j => D j^(4/p)) u)) := by
  rw [T.disorderProfileJets_eq_allOffDiagonal hw φ F hF ho v q hq hq0
    (A::A::Ds) hB hDs P x]
  simp only [List.map_cons]
  let Ks := Ds.map (fun L => (ReplicaTree.coordinateProfile φ L,rho))
  have hKs : Ks.map Prod.fst=Ds.map (ReplicaTree.coordinateProfile φ) := by
    simp only [Ks,List.map_map,Function.comp_def]
  have hprod : (Ks.map Prod.snd).prod=rho^Ds.length := by
    simp [Ks,List.map_map,Function.comp_def]
  have H := disorderOffDiagonalJets_markedTest_twoError_L2 hw φ ho v q x Ks 0 Ds.length
    (by simp only [Ks,List.length_map,zero_add]) hC hM hp T hT P hP
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) Fin.elim0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)
    (by intro K hK; obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK; exact hrho)
    (ReplicaTree.coordinateProfile φ A) hA hD hsecond
    (by intro K hK j; obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK; exact hmoment L hL j)
  simpa only [hKs,hprod,Ks,List.length_map,Fin.prod_univ_zero,mul_one] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
