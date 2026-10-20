module

public import ComparisonSignedCavityActualMixedProfile
public import ComparisonSignedCavityGeneratedResourcesForks
public import CavityFiniteProfilePermutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

private theorem transient_sum_map_div {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map (fun a => f a/c)).sum=(L.map f).sum/c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih,add_div]

theorem native_profilePairTest_add_kernel {as : List PositiveMass} {T : ClockTree S as}
    (P : T.Assignment → ℝ) (A B : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    profilePairTest P (fun j σ τ => A j σ τ+B j σ τ) p r =
      fun σ => profilePairTest P A p r σ+profilePairTest P B p r σ := by
  funext σ
  simp only [profilePairTest,mul_add]

theorem native_profilePairTest_mul_kernel {as : List PositiveMass} {T : ClockTree S as}
    (P : T.Assignment → ℝ) (A : ℕ → S → S → ℝ) (c : ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    profilePairTest P (fun j σ τ => c*A j σ τ) p r =
      fun σ => c*profilePairTest P A p r σ := by
  funext σ
  simp only [profilePairTest]
  ring

theorem native_profileJets_add_kernel (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (pre post : List (ℕ → S → S → ℝ)) (A B : ℕ → S → S → ℝ)
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x (pre ++ (fun j σ τ => A j σ τ+B j σ τ)::post) T P =
      disorderProfileJets w φ v q x (pre ++ A::post) T P +
        disorderProfileJets w φ v q x (pre ++ B::post) T P := by
  induction pre generalizing T P with
  | nil =>
    simp only [List.nil_append,disorderProfileJets,native_profilePairTest_add_kernel,
      disorderProfileJets_add,mul_add,List.sum_map_add,add_div]
  | cons K pre ih =>
    simp only [List.cons_append,disorderProfileJets,ih,mul_add,List.sum_map_add,add_div]

theorem native_profileJets_mul_kernel (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (pre post : List (ℕ → S → S → ℝ)) (A : ℕ → S → S → ℝ) (c : ℝ)
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x (pre ++ (fun j σ τ => c*A j σ τ)::post) T P =
      c*disorderProfileJets w φ v q x (pre ++ A::post) T P := by
  induction pre generalizing T P with
  | nil =>
    simp only [List.nil_append,disorderProfileJets,native_profilePairTest_mul_kernel,
      disorderProfileJets_const_mul,mul_left_comm _ c,List.sum_map_mul_left]
    ring
  | cons K pre ih =>
    simp only [List.cons_append,disorderProfileJets,ih,mul_left_comm _ c,
      List.sum_map_mul_left]
    ring

theorem native_finite_directions_bounded (N : ℕ) (Ds : List (ℕ → ι → ℝ)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ D∈Ds,∀ j,j ≤ N → ∀ i,|D j i| ≤ B := by
  let f : Fin Ds.length × Fin (N+1) × ι → ℝ :=
    fun p => |Ds.get p.1 p.2.1.val p.2.2|
  obtain ⟨B,hB⟩ := (Set.finite_range f).bddAbove
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro D hD j hj i
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hD
  have H := hB (Set.mem_range.mpr ⟨(k,⟨j,by omega⟩,i),rfl⟩)
  simpa only [f,hk] using H.trans (le_max_left B 0)

theorem native_profileJets_perm_without_budget {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (hq : ∀ i,Monotone (fun j => q j i))
    (hq0 : ∀ i,v i ≤ q 0 i) (Ds Es : List (ℕ → ι → ℝ)) (hperm : Ds.Perm Es)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderProfileJets w φ v q x (Es.map (ReplicaTree.coordinateProfile φ)) T P := by
  obtain ⟨B,hB,hDs⟩ := native_finite_directions_bounded as.length Ds
  exact T.actual_profileJets_perm_finite hw φ ho v q hq hq0 hB hperm hDs P x

def nativeTripleJointTest {as : List PositiveMass} {T : ClockTree S as}
    (P : T.Assignment → ℝ) (A B E : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (u : MarkedPlacement t.tree) (v : MarkedPlacement u.tree) : v.tree.Assignment → ℝ :=
  profilePairTest (profilePairTest (profilePairTest P A p r) B s t) E u v

theorem nativeTripleJointTest_product {as : List PositiveMass} {T : ClockTree S as}
    (P : T.Assignment → ℝ) (A B E : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (u : MarkedPlacement t.tree) (v : MarkedPlacement u.tree) (σ : v.tree.Assignment) :
    nativeTripleJointTest P A B E p r s t u v σ =
      P (p.restrict (r.restrict (s.restrict (t.restrict (u.restrict (v.restrict σ)))))) *
      A (r.tree.splitIndex (r.embed p.mark) r.mark)
        (p.spin (r.restrict (s.restrict (t.restrict (u.restrict (v.restrict σ))))))
        (r.spin (s.restrict (t.restrict (u.restrict (v.restrict σ))))) *
      B (t.tree.splitIndex (t.embed s.mark) t.mark)
        (s.spin (t.restrict (u.restrict (v.restrict σ)))) (t.spin (u.restrict (v.restrict σ))) *
      E (v.tree.splitIndex (v.embed u.mark) v.mark) (u.spin (v.restrict σ)) (v.spin σ) := by
  unfold nativeTripleJointTest profilePairTest
  ring

theorem native_three_profile_eq_six_mark_sum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v₀ : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (A B E : ℕ → S → S → ℝ) (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v₀ q x [A,B,E] T P =
      ((T.markedAttach 0).map (fun p => p.coeff *
        ((p.tree.markedAttach 0).map (fun r => r.coeff *
          ((r.tree.markedAttach 0).map (fun s => s.coeff *
            ((s.tree.markedAttach 0).map (fun t => t.coeff *
              ((t.tree.markedAttach 0).map (fun u => u.coeff *
                ((u.tree.markedAttach 0).map (fun v => v.coeff *
                  v.tree.disorderExpect w φ v₀ q (nativeTripleJointTest P A B E p r s t u v) x)).sum)).sum)).sum)).sum)).sum)).sum/8 := by
  simp only [disorderProfileJets,nativeTripleJointTest]
  simp only [← mul_div_assoc,transient_sum_map_div,div_div]
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_cutTSlope_low_error_split (n U : ℕ) (b h K : ℕ → ℝ) (l : ℝ) :
    cutTSlope n U l b h K = fun j i =>
      cutTSlope n U 0 b h K j i+l*cutLowError n U b h K j i := by
  funext j i
  rcases i with (i|i)|(i|i) <;>
    simp only [cutTSlope,cutLowError,rowInterpolationSlope,relocatedClock] <;>
      split_ifs <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] <;> ring

theorem native_coordinateProfile_add_scale {S ι : Type*} [Fintype ι]
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (A D : ℕ → ι → ℝ) (c : ℝ) :
    ReplicaTree.coordinateProfile φ (fun j i => A j i+c*D j i) =
      fun j σ τ => ReplicaTree.coordinateProfile φ A j σ τ+
        c*ReplicaTree.coordinateProfile φ D j σ τ := by
  classical
  funext j σ τ
  unfold ReplicaTree.coordinateProfile
  simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def nativeTransientHighJet (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x
    ((List.replicate k (cutLSlope n U t b h K) ++ [cutTSlope n U 0 b h K]).map
      (ReplicaTree.coordinateProfile (fullFeature n))) T P

def nativeTransientLowErrorJet (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x
    ((List.replicate k (cutLSlope n U t b h K) ++ [cutLowError n U b h K]).map
      (ReplicaTree.coordinateProfile (fullFeature n))) T P

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
  (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
  (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
include ho hq0 hq hb hh hK hbm hhm hKm

theorem native_cutMixedJet_transient_split (P : T.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (k : ℕ) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    cutMixedJet n q U b h K T P x k l t =
      nativeTransientHighJet n q U b h K T P x k l t +
      l*nativeTransientLowErrorJet n q U b h K T P x k l t +
      (k:ℝ)*nativeTransientLowErrorJet n q U b h K T P x (k-1) l t := by
  have Hsplit (m : ℕ) : ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) x
      ((List.replicate m (cutLSlope n U t b h K) ++ [cutTSlope n U l b h K]).map
        (ReplicaTree.coordinateProfile (fullFeature n))) T P =
      nativeTransientHighJet n q U b h K T P x m l t +
        l*nativeTransientLowErrorJet n q U b h K T P x m l t := by
    rw [native_cutTSlope_low_error_split]
    simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil]
    rw [native_coordinateProfile_add_scale]
    rw [ClockTree.native_profileJets_add_kernel,ClockTree.native_profileJets_mul_kernel]
    simp only [nativeTransientHighJet,nativeTransientLowErrorJet,List.map_append,
      List.map_replicate,List.map_cons,List.map_nil]
  cases k with
  | zero =>
    rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho P x hq0 hq hb hh hK
      hbm hhm hKm hl ht]
    have H := Hsplit 0
    simpa only [List.replicate_zero,List.nil_append,List.map_cons,List.map_nil,
      Nat.cast_zero,zero_mul,add_zero] using H
  | succ k =>
    rw [native_cutMixedJet_eq_profiles n q U b h K T ho P x hq0 hq hb hh hK
      hbm hhm hKm k hl ht,Hsplit]
    rfl

theorem native_centered_third_transient_ledger
    (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
    (x : ActiveCoordinate n → ℝ) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    let g := fun i : Fin 4 => cutLowJet n q U b h K T
      (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x) i l 0
    let H := fun J k => nativeTransientHighJet n q U b h K T J (cavityEmbed x) k l t
    let D := fun J k => nativeTransientLowErrorJet n q U b h K T J (cavityEmbed x) k l t
    let J := fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2
    let A := fun σ => P (T.cavityAssignment σ).1
    cutCenteredMixedJet n q U b h K T P Q x 3 l t =
      (H J 3-productJet3 g (fun i => H A i) 3) +
      l*(D J 3-productJet3 g (fun i => D A i) 3) +
      3*(D J 2-productJet3 g (fun i => D A i) 2) := by
  dsimp only
  simp only [cutCenteredMixedJet,productJet3]
  simp_rw [native_cutMixedJet_transient_split n q U b h K T ho hq0 hq hb hh hK
    hbm hhm hKm _ _ _ hl ht]
  simp only [Fin.val_zero,Fin.val_one,show (2:Fin 4).val=2 from rfl,
    show (3:Fin 4).val=3 from rfl,Nat.cast_zero,zero_mul]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  ring

end
end OAI.SKFluctuations.Cavity
