module

public import CavityProfileJetPermutation
public import CavityFiniteOneErrorBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem actual_profileJets_perm_finite {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    {Ds Es : List (ℕ → ι → ℝ)} {B : ℝ} (hB : 0 ≤ B) (hperm : Ds.Perm Es)
    (hDs : ∀ D ∈ Ds, ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderProfileJets w φ v q x (Es.map (ReplicaTree.coordinateProfile φ)) T P := by
  rw [disorderProfileJets_eq_clipDirections w φ v q x Ds T P,
    disorderProfileJets_eq_clipDirections w φ v q x Es T P]
  exact T.actual_profileJets_perm hw φ ho v q hq hq0 hB
    (hperm.map (clipDirection as.length)) (clipDirection_bounded as.length Ds hB hDs) P x

 theorem disorderProfileJets_oneError_finite_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (pre post : List (ℕ → ι → ℝ)) (hk : 0 < (pre++post).length)
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ pre++A::post, ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ pre++post, ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*(pre++post).length)) x ≤ rho^(2*(pre++post).length)) :
    |disorderProfileJets w φ v q x
      ((pre++A::post).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*absJetVariation (r+2) (pre++post).length*C*rho^(pre++post).length*
        (T.forkCost D + (∫ u, edgeDensity 0 as D u)) := by
  have hperm : (pre++A::post).Perm (A::(pre++post)) := List.perm_middle
  rw [T.actual_profileJets_perm_finite hw φ ho v q hq hq0 hB hperm hDs P x]
  exact T.disorderProfileJets_errorFirst_finite_moment_L2 hw φ F hF ho v q hq hq0 A (pre++post) hk
    hB (fun L hL => hDs L (hperm.mem_iff.mpr hL)) hC hrho hT P hP x hD hsecond hmoment

end OAI.SKFluctuations.Hierarchy.ClockTree
