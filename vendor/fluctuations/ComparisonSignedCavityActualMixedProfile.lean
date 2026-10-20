module

public import ComparisonSignedCavityProfileTestCalculus
public import CavityFiniteProfilePermutation
public import CavityActualFrozenInsertion

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

def nativeMovingLowCorrection (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (L D : ℕ → S → S → ℝ) : ℕ → (T : ClockTree S as) → (T.Assignment → ℝ) → ℝ
  | 0, _, _ => 0
  | k+1, T, P =>
      disorderProfileJets w φ v q x (D :: List.replicate k L) T P +
      ((T.markedAttach 0).map (fun p => p.coeff *
        ((p.tree.markedAttach 0).map (fun r => r.coeff *
          nativeMovingLowCorrection w φ v q x L D k r.tree
            (profilePairTest P L p r))).sum)).sum / 2

theorem native_moving_low_profile_hasDerivAt {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q K : ℕ → ι → ℝ) {a b : ℝ}
    (hp : ∀ s ∈ Ioo a b, ∀ i, Monotone (fun j => q j i+s*K j i))
    (hr : ∀ s ∈ Ioo a b, ∀ i, v i ≤ q 0 i+s*K 0 i)
    (L : ℝ → ℕ → S → S → ℝ) (D : ℕ → S → S → ℝ)
    (k : ℕ) (T : ClockTree S as) (P : ℝ → T.Assignment → ℝ)
    (P' : T.Assignment → ℝ) (x : ι → ℝ) {t : ℝ} (ht : t ∈ Ioo a b)
    (hP : ∀ σ, HasDerivAt (fun s => P s σ) (P' σ) t)
    (hL : ∀ j σ τ, HasDerivAt (fun s => L s j σ τ) (D j σ τ) t) :
    HasDerivAt (fun s => disorderProfileJets w φ v (fun j i => q j i+s*K j i) x
      (List.replicate k (L s)) T (P s))
      (disorderProfileJets w φ v (fun j i => q j i+t*K j i) x
          (List.replicate k (L t) ++ [ReplicaTree.coordinateProfile φ K]) T (P t) +
        disorderProfileJets w φ v (fun j i => q j i+t*K j i) x
          (List.replicate k (L t)) T P' +
        nativeMovingLowCorrection w φ v (fun j i => q j i+t*K j i) x (L t) D k T (P t)) t := by
  induction k generalizing T P P' with
  | zero =>
    have H := native_profileJets_hasDerivAt_testFamily hw φ ho v q K hp hr [] T P P' x ht hP
    simpa only [List.replicate_zero,List.nil_append,nativeMovingLowCorrection,
      add_zero,zero_add,add_comm] using H
  | succ k ih =>
    have Hd (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :=
      ih r.tree (fun s => profilePairTest (P s) (L s) p r)
        (fun σ => profilePairTest P' (L t) p r σ + profilePairTest (P t) D p r σ)
        (fun σ => by
          have H := (hP (p.restrict (r.restrict σ))).mul
            (hL (r.tree.splitIndex (r.embed p.mark) r.mark)
              (p.spin (r.restrict σ)) (r.spin σ))
          convert H using 1 <;> rfl)
    have H := (hasDerivAt_listSum (T.markedAttach 0) _ _ (fun p _ =>
      (hasDerivAt_listSum (p.tree.markedAttach 0) _ _ (fun r _ =>
        (Hd p r).const_mul r.coeff)).const_mul p.coeff)).div_const 2
    convert H using 1
    · funext s
      simp only [List.replicate_succ,disorderProfileJets]
    · simp only [List.replicate_succ,List.cons_append,disorderProfileJets,
        nativeMovingLowCorrection,disorderProfileJets_add]
      simp only [mul_add,List.sum_map_add]
      ring

theorem native_moving_low_profile_continuous {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℝ → ℕ → ι → ℝ)
    (hq : ∀ j, Continuous (fun s => q s j))
    (L : ℝ → ℕ → S → S → ℝ) (hL : ∀ j σ τ, Continuous (fun s => L s j σ τ))
    (k : ℕ) (Ks : List (ℕ → S → S → ℝ))
    (T : ClockTree S as) (P : ℝ → T.Assignment → ℝ)
    (hP : ∀ σ, Continuous (fun s => P s σ)) (x : ℝ → ι → ℝ) (hx : Continuous x) :
    Continuous (fun s => disorderProfileJets w φ v (q s) (x s)
      (List.replicate k (L s) ++ Ks) T (P s)) := by
  induction k generalizing T P with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      native_profileJets_continuous_testFamily hw φ ho v q hq Ks T P x hx hP
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,disorderProfileJets]
    apply Continuous.div_const
    apply joint_continuous_listSum
    intro p hp
    apply Continuous.const_mul
    apply joint_continuous_listSum
    intro r hr
    apply Continuous.const_mul
    apply ih r.tree (fun s => profilePairTest (P s) (L s) p r)
    intro σ
    exact (hP (p.restrict (r.restrict σ))).mul
      (hL (r.tree.splitIndex (r.embed p.mark) r.mark)
        (p.spin (r.restrict σ)) (r.spin σ))

theorem nativeMovingLowCorrection_succ_eq {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (A D : ℕ → ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ j, j ≤ as.length → ∀ i, |A j i| ≤ B)
    (hD : ∀ j, j ≤ as.length → ∀ i, |D j i| ≤ B)
    (k : ℕ) (T : ClockTree S as) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    nativeMovingLowCorrection w φ v q x (ReplicaTree.coordinateProfile φ A)
      (ReplicaTree.coordinateProfile φ D) (k+1) T P =
      ((k+1:ℕ):ℝ) * disorderProfileJets w φ v q x
        ((List.replicate k A ++ [D]).map (ReplicaTree.coordinateProfile φ)) T P := by
  induction k generalizing T P with
  | zero =>
    simp only [nativeMovingLowCorrection,List.replicate_zero,List.nil_append,
      List.map_cons,List.map_nil,mul_zero,List.map_const',List.sum_replicate,
      nsmul_zero,zero_div,add_zero,Nat.zero_add,Nat.cast_one,one_mul]
  | succ k ih =>
    have Hperm := T.actual_profileJets_perm_finite hw φ ho v q hq hq0 hB
      (show ([D] ++ List.replicate (k+1) A).Perm
        (List.replicate (k+1) A ++ [D]) from List.perm_append_comm)
      (by
        intro E hE j hj i
        simp only [List.singleton_append,List.mem_cons,List.mem_replicate] at hE
        rcases hE with rfl | ⟨_,rfl⟩
        · exact hD j hj i
        · exact hA j hj i) P x
    simp only [List.singleton_append,List.map_cons,List.map_append,List.map_replicate,
      List.map_nil] at Hperm
    rw [nativeMovingLowCorrection]
    rw [Hperm]
    simp_rw [ih]
    simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil]
    have Hsum :
        ((T.markedAttach 0).map (fun p => p.coeff *
          ((p.tree.markedAttach 0).map (fun r => r.coeff *
            (((k+1:ℕ):ℝ) * disorderProfileJets w φ v q x
              (List.replicate k (ReplicaTree.coordinateProfile φ A) ++
                [ReplicaTree.coordinateProfile φ D]) r.tree
              (profilePairTest P (ReplicaTree.coordinateProfile φ A) p r)))).sum)).sum / 2 =
        ((k+1:ℕ):ℝ) * disorderProfileJets w φ v q x
          (List.replicate (k+1) (ReplicaTree.coordinateProfile φ A) ++
            [ReplicaTree.coordinateProfile φ D]) T P := by
      simp only [List.replicate_succ,List.cons_append,disorderProfileJets]
      simp only [mul_left_comm _ ((k+1:ℕ):ℝ),List.sum_map_mul_left]
      ring
    rw [Hsum]
    push_cast
    ring

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_cutLSlope_affine (n U : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    cutLSlope n U t b h K = fun j i =>
      cutLSlope n U 0 b h K j i + t * cutLowError n U b h K j i := by
  funext j i
  rcases i with (i|i)|(i|i) <;>
    simp only [cutLSlope,cutLowError,fullVariance,rowInterpolationSlope] <;>
      split_ifs <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] <;> ring

theorem native_cutLSlope_profile_affine (n U : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) =
      fun j σ τ =>
        ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) j σ τ +
        t * ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ := by
  classical
  rw [native_cutLSlope_affine]
  funext j σ τ
  unfold ReplicaTree.coordinateProfile
  simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem native_finite_direction_bound {ι : Type*} [Fintype ι]
    (N : ℕ) (A D : ℕ → ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ j, j ≤ N → ∀ i, |A j i| ≤ B) ∧
      (∀ j, j ≤ N → ∀ i, |D j i| ≤ B) := by
  let f : Fin (N+1) × ι → ℝ := fun p => max |A p.1.val p.2| |D p.1.val p.2|
  obtain ⟨B,hB⟩ := (Set.finite_range f).bddAbove
  refine ⟨max B 0,le_max_right _ _,?_,?_⟩
  · intro j hj i
    exact (le_max_left _ _).trans
      ((hB (Set.mem_range.mpr ⟨(⟨j,by omega⟩,i),rfl⟩)).trans (le_max_left _ _))
  · intro j hj i
    exact (le_max_right _ _).trans
      ((hB (Set.mem_range.mpr ⟨(⟨j,by omega⟩,i),rfl⟩)).trans (le_max_left _ _))

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
  (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
  (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
  (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
include ho hq0 hq hb hh hK hbm hhm hKm

theorem native_cutMixedJet_eq_profiles_interior (k : ℕ) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1) :
    cutMixedJet n q U b h K T P x (k+1) l t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((List.replicate (k+1) (cutLSlope n U t b h K) ++
          [cutTSlope n U l b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P +
      ((k+1:ℕ):ℝ) * ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((List.replicate k (cutLSlope n U t b h K) ++
          [cutLowError n U b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P := by
  let L := fun s => ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K)
  let D := ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)
  have hp := cutT_affine_monotone n q U hl hq hb hh hK hbm hhm hKm
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i,
      (0 : FullCoordinate n → ℝ) i ≤ cutTBase n q U l b h K 0 i + s*cutTSlope n U l b h K 0 i := by
    intro s hs i
    simpa only [cutFullVariance_t_affine,Pi.zero_apply] using
      cutFullVariance_nonneg n q U hl ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
  have hL j σ τ : HasDerivAt (fun s => L s j σ τ) (D j σ τ) t := by
    have H := ((hasDerivAt_id t).mul_const (D j σ τ)).const_add
      (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) j σ τ)
    simp only [one_mul] at H
    convert H using 1
    funext s
    exact congrFun (congrFun (congrFun (native_cutLSlope_profile_affine n U b h K s) j) σ) τ
  have HD := ClockTree.native_moving_low_profile_hasDerivAt (fullWeight_pos n) (fullFeature n)
    ho 0 (cutTBase n q U l b h K) (cutTSlope n U l b h K) hp hr L D (k+1)
    T (fun _ => P) (fun _ => 0) x ht (fun σ => hasDerivAt_const t (P σ)) hL
  simp only [←cutFullVariance_t_affine,ClockTree.disorderProfileJets_zero,add_zero] at HD
  have HE : (fun s => cutLowJet n q U b h K T P x (k+1) l s) =ᶠ[𝓝 t]
      (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l s b h K) x (List.replicate (k+1) (L s)) T P) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact cutLowJet_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK
      hbm hhm hKm (k+1) hl ⟨hs.1.le,hs.2.le⟩
  have H := (cutLowJet_hasDerivAt_t n q U hl ht b h K hq0 hq hb hh hK
    hbm hhm hKm T ho P x (k+1)).unique (HD.congr_of_eventuallyEq HE)
  obtain ⟨B,hB,hA,hD⟩ := native_finite_direction_bound as.length
    (cutLSlope n U t b h K) (cutLowError n U b h K)
  have HC := ClockTree.nativeMovingLowCorrection_succ_eq (fullWeight_pos n) (fullFeature n)
    ho 0 (cutFullVariance n q U l t b h K)
    (cutFullVariance_monotone n q U hl ⟨ht.1.le,ht.2.le⟩ hq hb hh hK hbm hhm hKm)
    (fun i => cutFullVariance_nonneg n q U hl ⟨ht.1.le,ht.2.le⟩ hq0 hb hh hK 0 i)
    (cutLSlope n U t b h K) (cutLowError n U b h K) hB hA hD k T P x
  rw [HC] at H
  simpa only [L,D,List.map_append,List.map_replicate,List.map_cons,List.map_nil] using H

theorem native_cutMixedJet_eq_profiles (k : ℕ) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    cutMixedJet n q U b h K T P x (k+1) l t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((List.replicate (k+1) (cutLSlope n U t b h K) ++
          [cutTSlope n U l b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P +
      ((k+1:ℕ):ℝ) * ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        ((List.replicate k (cutLSlope n U t b h K) ++
          [cutLowError n U b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P := by
  have he : EqOn (cutMixedJet n q U b h K T P x (k+1) l)
      (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l s b h K) x
          ((List.replicate (k+1) (cutLSlope n U s b h K) ++
            [cutTSlope n U l b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P +
        ((k+1:ℕ):ℝ) * ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l s b h K) x
          ((List.replicate k (cutLSlope n U s b h K) ++
            [cutLowError n U b h K]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P)
      (Ioo (0:ℝ) 1) := fun s hs => native_cutMixedJet_eq_profiles_interior n q U b h K T ho
        P x hq0 hq hb hh hK hbm hhm hKm k hl hs
  have hLc j σ τ : Continuous (fun s =>
      ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j σ τ) := by
    have H : Continuous (fun s : ℝ =>
        ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) j σ τ +
        s * ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ) := by
      fun_prop
    convert H using 1
    funext s
    exact congrFun (congrFun (congrFun (native_cutLSlope_profile_affine n U b h K s) j) σ) τ
  have hc (r : ℕ) (D : ℕ → FullCoordinate n → ℝ) := ClockTree.native_moving_low_profile_continuous
    (fullWeight_pos n) (fullFeature n) ho 0 (fun s => cutFullVariance n q U l s b h K)
    (cutFullVariance_continuous_t n q U b h K l)
    (fun s => ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K)) hLc r
    [ReplicaTree.coordinateProfile (fullFeature n) D] T (fun _ => P)
    (fun _ => continuous_const) (fun _ => x) continuous_const
  have hR := (hc (k+1) (cutTSlope n U l b h K)).add
    ((hc k (cutLowError n U b h K)).const_mul ((k+1:ℕ):ℝ))
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil] at he ⊢
  have H := he.closure (cutMixedJet_continuous_t n q U b h K T P x (k+1) l) hR
  apply H
  simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using ht

theorem native_cutMixedJet_zero_eq_profile {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    cutMixedJet n q U b h K T P x 0 l t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        [ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U l b h K)] T P := by
  have hp := cutT_affine_monotone n q U hl hq hb hh hK hbm hhm hKm
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i,
      (0 : FullCoordinate n → ℝ) i ≤ cutTBase n q U l b h K 0 i + s*cutTSlope n U l b h K 0 i := by
    intro s hs i
    simpa only [cutFullVariance_t_affine,Pi.zero_apply] using
      cutFullVariance_nonneg n q U hl ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
  have he : EqOn (cutMixedJet n q U b h K T P x 0 l)
      (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l s b h K) x
        [ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U l b h K)] T P)
      (Ioo (0:ℝ) 1) := by
    intro s hs
    have HD := ClockTree.hasDerivAt_finiteProfileJets (fullWeight_pos n) (fullFeature n)
      ho 0 (cutTBase n q U l b h K) (cutTSlope n U l b h K) hp hr [] T P x hs
    simp only [←cutFullVariance_t_affine,List.nil_append] at HD
    have HE : (fun s => cutLowJet n q U b h K T P x 0 l s) =ᶠ[𝓝 s]
        (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l s b h K) x [] T P) := by
      exact Eventually.of_forall (fun s => cutLowJet_zero n q U b h K T ho P x l s)
    exact (cutLowJet_hasDerivAt_t n q U hl hs b h K hq0 hq hb hh hK hbm hhm hKm
      T ho P x 0).unique (HD.congr_of_eventuallyEq HE)
  have hc := ClockTree.disorderProfileJets_continuous (fullWeight_pos n) (fullFeature n)
    ho 0 (fun s => cutFullVariance n q U l s b h K)
    (cutFullVariance_continuous_t n q U b h K l) (fun _ => x) continuous_const
    [ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U l b h K)] T P
  have H := he.closure (cutMixedJet_continuous_t n q U b h K T P x 0 l) hc
  apply H
  simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using ht

end
end OAI.SKFluctuations.Cavity
