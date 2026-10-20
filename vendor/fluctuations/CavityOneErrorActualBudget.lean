module

public import CavityOneErrorJetMoments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_errorFirst_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ)) (hk : 0 < Ds.length)
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::Ds, ∀ j i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*Ds.length)) x ≤ rho^(2*Ds.length)) :
    |disorderProfileJets w φ v q x
      ((A::Ds).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*absJetVariation (r+2) Ds.length*C*rho^Ds.length*
        (T.forkCost D + (∫ u, edgeDensity 0 as D u)) := by
  rw [T.disorderProfileJets_eq_allOffDiagonal hw φ F hF ho v q hq hq0
    (A::Ds) hB hDs P x]
  simp only [List.map_cons]
  have H := disorderOffDiagonalJets_oneError_L2 hw φ ho v q x
    (Ds.map (ReplicaTree.coordinateProfile φ)) (by simpa only [List.length_map] using hk)
    hC hrho T hT P hP (ReplicaTree.coordinateProfile φ A) hD hsecond (by
      intro K hK j
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK
      simpa only [List.length_map] using hmoment L hL j)
  simpa only [List.length_map] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
