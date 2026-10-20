module

public import ComparisonSignedCavityWholeLawTwoErrorJets
public import CavityFiniteProfilePermutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_errorFirst_wholeLaw_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι→ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ)) (hk : 0 < Ds.length)
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::Ds, ∀ j i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^4) x ≤ C^4)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(4*Ds.length)) x ≤ rho^(4*Ds.length)) :
    |disorderProfileJets w φ v q x
      ((A::Ds).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*absJetVariation (r+2) Ds.length*C*rho^Ds.length*
        (T.forkCost D + (∫ u, edgeDensity 0 as D u)) := by
  rw [T.disorderProfileJets_eq_allOffDiagonal hw φ F hF ho v q hq hq0
    (A::Ds) hB hDs P x]
  simp only [List.map_cons]
  let Ks:=Ds.map (fun L=>(ReplicaTree.coordinateProfile φ L,rho))
  have hKs : Ks.map Prod.fst=Ds.map (ReplicaTree.coordinateProfile φ):=by simp [Ks,List.map_map,Function.comp_def]
  have hprod : (Ks.map Prod.snd).prod=rho^Ds.length:=by simp [Ks,List.map_map,Function.comp_def]
  have H:=disorderOffDiagonalJets_markedTest_oneError_wholeLaw_L2 hw φ ho v q x
    Ks 0 Ds.length hk (by simp only [Ks,List.length_map,zero_add]) hC T hT P hP
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i=>Fin.elim0 i) Fin.elim0 (fun i=>Fin.elim0 i)
    (fun i=>Fin.elim0 i)
    (by intro K hK;obtain ⟨L,hL,rfl⟩:=List.mem_map.mp hK;exact hrho)
    (ReplicaTree.coordinateProfile φ A) hD hsecond
    (by intro K hK j;obtain ⟨L,hL,rfl⟩:=List.mem_map.mp hK;exact hmoment L hL j)
  simpa only [hKs,hprod,Ks,List.length_map,Fin.prod_univ_zero,mul_one] using H

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_errorFirst_finite_wholeLaw_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι→ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ)) (hk : 0 < Ds.length)
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::Ds, ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^4) x ≤ C^4)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(4*Ds.length)) x ≤ rho^(4*Ds.length)) :
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
        (pairSpin as j σ).1 (pairSpin as j σ).2|^(4*(Ds.map (clipDirection as.length)).length)) x
        ≤ rho^(4*(Ds.map (clipDirection as.length)).length) := by
    intro L hL j
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hL
    by_cases hj : j ≤ as.length
    · simpa only [coordinateProfile_clip_below φ as.length K hj,List.length_map] using hmoment K hK j hj
    · simp only [coordinateProfile_clip_above φ as.length K hj,Pi.zero_apply,abs_zero,List.length_map,
        zero_pow (by omega : 4*Ds.length ≠ 0),disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have H := T.disorderProfileJets_errorFirst_wholeLaw_moment_L2 hw φ F hF ho v q x hq hq0
    (clipDirection as.length A) (Ds.map (clipDirection as.length))
    (by simpa only [List.length_map] using hk) hB hbounds hC hrho hT P hP hD hs hm
  simpa only [List.map_cons,List.length_map] using H

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_twoErrorFirst_wholeLaw_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι→ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::A::Ds, ∀ j i, |D j i| ≤ B)
    {C M rho p : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hrho : 0 < rho) (hp : 2 < p)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))))
    (hA : ∀ j σ τ, |ReplicaTree.coordinateProfile φ A j σ τ| ≤ M)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j (pairSpin as j σ).1
        (pairSpin as j σ).2|^((2*(p/(p-2)))*(Ds.length:ℝ))) x ≤ rho^((2*(p/(p-2)))*(Ds.length:ℝ))) :
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
  have H := disorderOffDiagonalJets_markedTest_twoError_wholeLaw_L2 hw φ ho v q x Ks 0 Ds.length
    (by simp only [Ks,List.length_map,zero_add]) hC hM hp T hT P hP
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) Fin.elim0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)
    (by intro K hK; obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK; exact hrho)
    (ReplicaTree.coordinateProfile φ A) hA hD hsecond
    (by intro K hK j; obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK; exact hmoment L hL j)
  simpa only [hKs,hprod,Ks,List.length_map,Fin.prod_univ_zero,mul_one] using H

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderProfileJets_twoErrorFirst_finite_wholeLaw_moment_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : ι → ℝ)
    (hF : ∀ σ i, (φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι→ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A : ℕ → ι → ℝ) (Ds : List (ℕ → ι → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ A::A::Ds, ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    {C M rho p : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hrho : 0 < rho) (hp : 2 < p)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))))
    (hA : ∀ j, j ≤ as.length → ∀ σ τ, |ReplicaTree.coordinateProfile φ A j σ τ| ≤ M)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => (ReplicaTree.coordinateProfile φ A j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ L ∈ Ds, ∀ j, j ≤ as.length → (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ L j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^((2*(p/(p-2)))*(Ds.length:ℝ))) x ≤ rho^((2*(p/(p-2)))*(Ds.length:ℝ))) :
    |disorderProfileJets w φ v q x
      ((A::A::Ds).map (ReplicaTree.coordinateProfile φ)) T P| ≤
      pairForkVariation r*pairForkVariation (r+2)*absJetVariation (r+4) Ds.length*C*M^((p-2)/p)*M^((p-2)/p)*rho^Ds.length*
        (T.forkCost (fun j => D j^(4/p)) + (∫ u, edgeDensity 0 as (fun j => D j^(4/p)) u)) := by
  rw [disorderProfileJets_eq_clipDirections w φ v q x (A::A::Ds) T P]
  simp only [List.map_cons]
  have hbounds := clipDirection_bounded as.length (A::A::Ds) hB hDs
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
        (pairSpin as j σ).1 (pairSpin as j σ).2|^((2*(p/(p-2)))*((Ds.map (clipDirection as.length)).length:ℝ))) x
        ≤ rho^((2*(p/(p-2)))*((Ds.map (clipDirection as.length)).length:ℝ)) := by
    intro L hL j
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hL
    by_cases hj : j ≤ as.length
    · simpa only [coordinateProfile_clip_below φ as.length K hj,List.length_map] using hmoment K hK j hj
    · by_cases hlen : Ds.length=0
      · simp only [coordinateProfile_clip_above φ as.length K hj,Pi.zero_apply,abs_zero,
          List.length_map,hlen,Nat.cast_zero,mul_zero,Real.rpow_zero,(pairClock as j).disorderExpect_one hw φ ho]
        norm_num
      · have he : 0 < (2*(p/(p-2)))*(Ds.length:ℝ) := by
          have hp0 : 0 < p := by linarith
          have hpm : 0 < p-2 := by linarith
          have hl : 0 < (Ds.length:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hlen)
          positivity
        simp only [coordinateProfile_clip_above φ as.length K hj,Pi.zero_apply,abs_zero,List.length_map,
          Real.zero_rpow he.ne',disorderExpect,mul_zero,Finset.sum_const_zero]
        exact Real.rpow_nonneg hrho.le _
  have hAc : ∀ j σ τ, |ReplicaTree.coordinateProfile φ (clipDirection as.length A) j σ τ| ≤ M := by
    intro j σ τ
    by_cases hj : j ≤ as.length
    · simp only [coordinateProfile_clip_below φ as.length A hj]
      exact hA j hj σ τ
    · simp only [coordinateProfile_clip_above φ as.length A hj,Pi.zero_apply,abs_zero]
      exact hM
  have H := T.disorderProfileJets_twoErrorFirst_wholeLaw_moment_L2 hw φ F hF ho v q x hq hq0
    (clipDirection as.length A) (Ds.map (clipDirection as.length))
    hB hbounds hC hM hrho hp hT P hP hAc hD hs hm
  simpa only [List.map_cons,List.length_map] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
