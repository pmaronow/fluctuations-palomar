module

public import ComparisonSignedCavityActualGhostProfileRow
public import ComparisonSignedCavityActualHighPairingMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 10000000
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem exists_single_direction_finite_bound (d : ℕ) (D : ℕ→ι→ℝ) :
    ∃B : ℝ,0 ≤ B ∧ ∀A∈[D],∀j,j ≤ d→∀i,|A j i| ≤ B := by
  classical
  let B : ℝ:=∑j : Fin (d+1),∑i : ι,|D j.val i|
  refine ⟨B,Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>abs_nonneg _)),?_⟩
  intro A hA j hj i
  simp only [List.mem_singleton] at hA
  subst A
  let r : Fin (d+1):=⟨j,by omega⟩
  have H₁ : |D j i| ≤ ∑z : ι,|D j z| :=
    Finset.single_le_sum (s:=Finset.univ) (f:=fun z : ι=>|D j z|)
      (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
  have H₂ : (∑z : ι,|D j z|) ≤ B := by
    simpa only [B,r] using (Finset.single_le_sum (s:=Finset.univ)
      (f:=fun t : Fin (d+1)=>∑z : ι,|D t.val z|)
      (fun _ _=>Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (Finset.mem_univ r))
  exact H₁.trans H₂

theorem native_profile_single_marked_marginal
    {w : S→ℝ} (hw : ∀s,0 < w s) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (P : T.Assignment→ℝ) (x : ι→ℝ) :
    disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D]
      p.tree (fun σ=>P (p.restrict σ))=
    disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] T P := by
  obtain ⟨B,hB,hD⟩:=exists_single_direction_finite_bound as.length D
  change disorderProfileJets w φ v q x ([D].map (ReplicaTree.coordinateProfile φ)) _ _=
    disorderProfileJets w φ v q x ([D].map (ReplicaTree.coordinateProfile φ)) _ _
  rw [disorderProfileJets_eq_clipDirections w φ v q x [D] p.tree _,
    disorderProfileJets_eq_clipDirections w φ v q x [D] T P]
  exact T.markedAttach_profileJets_preserves_actual hw φ ho p hp v q hq hq0
    ([D].map (clipDirection as.length)) hB (clipDirection_bounded as.length [D] hB hD) P x

theorem nativeMarkedProfileRow_clip_directions
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (Ds : List (ℕ→ι→ℝ))
    (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) :
    nativeMarkedProfileRow w φ T v q (Ds.map (ReplicaTree.coordinateProfile φ)) P B x=
      nativeMarkedProfileRow w φ T v q
        ((Ds.map (clipDirection as.length)).map (ReplicaTree.coordinateProfile φ)) P B x := by
  unfold nativeMarkedProfileRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [disorderProfileJets_eq_clipDirections]

theorem native_profile_row_single_marked_marginal
    {w : S→ℝ} (hw : ∀s,0 < w s) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (P : T.Assignment→ℝ)
    (u x : ι→ℝ) :
    nativeMarkedProfileRow w φ p.tree v q [ReplicaTree.coordinateProfile φ D]
      (fun σ=>P (p.restrict σ)) (fun s=>φ s u) x=
    nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D]
      P (fun s=>φ s u) x := by
  obtain ⟨B,hB,hD⟩:=exists_single_direction_finite_bound as.length D
  change nativeMarkedProfileRow w φ p.tree v q ([D].map (ReplicaTree.coordinateProfile φ)) _ _ _=
    nativeMarkedProfileRow w φ T v q ([D].map (ReplicaTree.coordinateProfile φ)) _ _ _
  rw [nativeMarkedProfileRow_clip_directions w φ p.tree v q [D],
    nativeMarkedProfileRow_clip_directions w φ T v q [D]]
  exact native_marked_profile_row_marginal hw φ T ho p hp v q hq hq0
    ([D].map (clipDirection as.length)) hB (clipDirection_bounded as.length [D] hB hD) P u x

end OAI.SKFluctuations.Hierarchy.ClockTree
