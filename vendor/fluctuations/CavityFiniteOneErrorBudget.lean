module

public import CavityOneErrorActualBudget
public import CavityFiniteProfileClipping

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_errorFirst_finite_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ)) (hk : 0 < Ds.length)
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::Ds, ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*Ds.length)) x ≤ rho^(2*Ds.length)) :
    |disorderProfileJets w φ v q x
      ((A::Ds).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*absJetVariation (r+2) Ds.length*C*rho^Ds.length*
        (T.forkCost D + (∫ u, edgeDensity 0 as D u)) := by
  rw [disorderProfileJets_eq_clipDirections w φ v q x (A::Ds) T P]
  simp only [List.map_cons]
  have hbounds := clipDirection_bounded as.length (A::Ds) hB hDs
  simp only [List.map_cons] at hbounds
  have hs : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ (clipDirection as.length A) j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2 := by
    intro j
    by_cases hj : j ≤ as.length
    · simp only [coordinateProfile_clip_below φ as.length A hj]
      exact hsecond j hj
    · simp only [coordinateProfile_clip_above φ as.length A hj,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ) ≠ 0),
        disorderExpect,mul_zero,Finset.sum_const_zero]
      exact sq_nonneg (D j)
  have hm : ∀ L ∈ Ds.map (clipDirection as.length), ∀ j,
      (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*(Ds.map (clipDirection as.length)).length)) x
        ≤ rho^(2*(Ds.map (clipDirection as.length)).length) := by
    intro L hL j
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hL
    by_cases hj : j ≤ as.length
    · simpa only [coordinateProfile_clip_below φ as.length K hj,List.length_map] using hmoment K hK j hj
    · simp only [coordinateProfile_clip_above φ as.length K hj,Pi.zero_apply,abs_zero,List.length_map,
        zero_pow (by omega : 2*Ds.length ≠ 0),disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho _
  have H := T.disorderProfileJets_errorFirst_moment_L2 hw φ F hF ho v q hq hq0
    (clipDirection as.length A) (Ds.map (clipDirection as.length))
    (by simpa only [List.length_map] using hk) hB hbounds hC hrho hT P hP x hD hs hm
  simpa only [List.map_cons,List.length_map] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
