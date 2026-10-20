module

public import CavityMarginalProfileJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem profilePairTest_const_mul {as : List PositiveMass} {T : ClockTree S as}
    (c : ℝ) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    profilePairTest (fun σ => c*P σ) K p r = fun σ => c*profilePairTest P K p r σ := by
  funext σ
  simp only [profilePairTest,mul_assoc]

 theorem disorderProfileJets_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P : T.Assignment → ℝ) (c : ℝ) :
    disorderProfileJets w φ v q x Ks T (fun σ => c*P σ) =
      c*disorderProfileJets w φ v q x Ks T P := by
  induction Ks generalizing T with
  | nil =>
    simp only [disorderProfileJets,disorderExpect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  | cons K Ks ih =>
    simp only [disorderProfileJets,profilePairTest_const_mul,ih]
    simp only [mul_left_comm _ c,List.sum_map_mul_left]
    ring

 theorem actual_profileJets_zero_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (Ds : List (ℕ → ι → ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) r.tree
          (fun σ => P (p.restrict (r.restrict σ)))).sum).sum = 0 := by
  have hi (p : MarkedPlacement T) :
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) r.tree
          (fun σ => P (p.restrict (r.restrict σ)))).sum =
      disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
        (fun σ => P (p.restrict σ)) := by
    have he : ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) r.tree
          (fun σ => P (p.restrict (r.restrict σ)))).sum =
        ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
          (fun σ => P (p.restrict σ))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro r hr
      rw [p.tree.markedAttach_profileJets_preserves_actual hw φ ho r hr v q hq hq0 Ds hB hDs
        (fun σ => P (p.restrict σ)) x]
    rw [he,List.sum_map_mul_right,p.tree.markedAttach_hit,one_mul]
  simp_rw [hi]
  have he : ((T.markedAttach 0).map fun p => p.coeff*
      disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
        (fun σ => P (p.restrict σ))).sum =
      ((T.markedAttach 0).map fun p => p.coeff*
        disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_profileJets_preserves_actual hw φ ho p hp v q hq hq0 Ds hB hDs P x]
  rw [he,List.sum_map_mul_right,T.markedAttach_mass,zero_mul]

 theorem actual_profile_diagonal_remainingJets (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} {T : ClockTree S as} (p : MarkedPlacement T)
    (r : MarkedPlacement p.tree) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (P : T.Assignment → ℝ)
    {E : ℕ → S → S → ℝ} {d : ℝ} (hE : ∀ σ, E as.length σ σ=d) (x : ι → ℝ) :
    r.hit p.mark*disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r) =
      d*r.hit p.mark*disorderProfileJets w φ v q x Ks r.tree
        (fun σ => P (p.restrict (r.restrict σ))) := by
  classical
  by_cases h : r.mark = r.embed p.mark
  · have hs (σ : r.tree.Assignment) : p.spin (r.restrict σ)=r.spin σ := by
      rw [p.spin_at,r.restrict_at,←h,←r.spin_at]
    have hj : r.tree.splitIndex (r.embed p.mark) r.mark = as.length := by
      rw [←h,r.tree.splitIndex_self]
    have he : profilePairTest P E p r = fun σ => d*P (p.restrict (r.restrict σ)) := by
      funext σ
      simp only [profilePairTest,hj,hs,hE,mul_comm]
    simp only [MarkedPlacement.hit,ite_eq_left h,one_mul,mul_one]
    rw [he,disorderProfileJets_const_mul]
  · simp only [MarkedPlacement.hit,ite_eq_right h,zero_mul,mul_zero]

 def disorderOffDiagonalProfileJets (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (E : ℕ → S → S → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (x : ι → ℝ) : ℝ :=
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*(1-r.hit p.mark)*
        disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r)).sum).sum/2

 theorem disorderProfileJets_errorFirst_eq_offDiagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (Ds : List (ℕ → ι → ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B) (P : T.Assignment → ℝ)
    {E : ℕ → S → S → ℝ} {d : ℝ} (hE : ∀ σ, E as.length σ σ=d) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (E::Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      T.disorderOffDiagonalProfileJets w φ v q P E (Ds.map (ReplicaTree.coordinateProfile φ)) x := by
  let Ks := Ds.map (ReplicaTree.coordinateProfile φ)
  have ht (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      r.coeff*disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r) =
      r.coeff*(1-r.hit p.mark)*disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r)+
        d*(r.coeff*r.hit p.mark*disorderProfileJets w φ v q x Ks r.tree
          (fun σ => P (p.restrict (r.restrict σ)))) := by
    calc
      _ = r.coeff*(1-r.hit p.mark)*disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r)+
        r.coeff*(r.hit p.mark*disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r)) := by ring
      _ = _ := by rw [actual_profile_diagonal_remainingJets w φ p r v q Ks P hE x]; ring
  change ((T.markedAttach 0).map fun p => p.coeff*
    ((p.tree.markedAttach 0).map fun r => r.coeff*
      disorderProfileJets w φ v q x Ks r.tree (profilePairTest P E p r)).sum).sum/2 = _
  simp_rw [ht,List.sum_map_add,List.sum_map_mul_left,mul_add]
  rw [List.sum_map_add]
  have he : ((T.markedAttach 0).map fun p => p.coeff*(d*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x Ks r.tree
          (fun σ => P (p.restrict (r.restrict σ)))).sum)).sum =
      d*((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        disorderProfileJets w φ v q x Ks r.tree
          (fun σ => P (p.restrict (r.restrict σ)))).sum).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    ring
  rw [he]
  dsimp only [Ks]
  rw [T.actual_profileJets_zero_diagonal hw φ ho v q hq hq0 Ds hB hDs P x,
    mul_zero,add_zero]
  rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
