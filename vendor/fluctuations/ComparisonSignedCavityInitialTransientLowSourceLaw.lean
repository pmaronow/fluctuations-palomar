module

public import ComparisonSignedCavityInitialAtomicPairJetLaw
public import ComparisonSignedCavityTransientLowPartProfileBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 26000000

 def nativeInitialLowJetClone (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  nativeInitialAtomicPairJetClone (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x i
    (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K))
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))) T P

 def nativeInitialLowJetRetained (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  nativeInitialAtomicPairJetRetained (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x i
    (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K))
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))) T P

 theorem native_initial_transient_LOW_jet_eq_clone_add_retained
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq0 : ∀j x,0≤q j x) (hq : ∀x,Monotone (fun j=>q j x))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (x : FullCoordinate n→ℝ)
    (k : ℕ) (hi : i<as.length) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientLowErrorPartJet n q i star U b h K T P x .initial k l t=
      nativeInitialLowJetClone n q i U b h K T P x k l t+
        nativeInitialLowJetRetained n q i U b h K T P x k l t := by
  let law:=cutFullVariance n q U l t b h K
  let A:=nativeTransientLowErrorPartDirection n U i star b h K .initial
  let Ds:=List.replicate k (cutLSlope n U t b h K)
  have Hlaw x : Monotone (fun j=>law j x):=cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm x
  have Hzero x : (0:ℝ)≤law 0 x:=cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 x
  have Hperm:=native_profileJets_perm_without_budget (fullWeight_pos n) (fullFeature n) T ho 0 law
    Hlaw Hzero (Ds++[A]) (A::Ds) (by
      simpa only [List.append_nil] using (List.perm_middle (a:=A) (l₁:=Ds) (l₂:=[]))) P x
  unfold nativeTransientLowErrorPartJet
  rw [←native_transient_low_part_direction_profile]
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil,Ds] at Hperm
  rw [Hperm]
  have Hoff:=native_profileJets_allOffDiagonal_without_budget (fullWeight_pos n) (fullFeature n)
    (fun z=>(fullAmplitude n z)^2) (by
      intro σ z
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ z)
    T ho 0 law Hlaw Hzero (A::Ds) P x
  simp only [List.map_cons,List.map_replicate,Ds] at Hoff
  rw [Hoff]
  simp only [A,native_transient_low_part_direction_profile]
  exact native_initial_atomic_pair_jet_eq_clone_add_retained (fullWeight n) (fullFeature n)
    0 law x i hi (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K))
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))) T P

 def nativeInitialCenteredLowClone (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (Q : T.cavityRight.Assignment→ℝ) (x : ActiveCoordinate n→ℝ) (l t : ℝ) : ℝ :=
  let g:=fun j : Fin 4=>cutLowJet n q U b h K T
    (fun σ=>Q (T.cavityAssignment σ).2) (cavityEmbed x) j l 0
  let D:=fun J k=>nativeInitialLowJetClone n q i U b h K T J (cavityEmbed x) k l t
  let J:=fun σ=>P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2
  let A:=fun σ=>P (T.cavityAssignment σ).1
  l*(D J 3-productJet3 g (fun j=>D A j) 3)+
    3*(D J 2-productJet3 g (fun j=>D A j) 2)

 def nativeInitialCenteredLowRetained (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (Q : T.cavityRight.Assignment→ℝ) (x : ActiveCoordinate n→ℝ) (l t : ℝ) : ℝ :=
  let g:=fun j : Fin 4=>cutLowJet n q U b h K T
    (fun σ=>Q (T.cavityAssignment σ).2) (cavityEmbed x) j l 0
  let D:=fun J k=>nativeInitialLowJetRetained n q i U b h K T J (cavityEmbed x) k l t
  let J:=fun σ=>P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2
  let A:=fun σ=>P (T.cavityAssignment σ).1
  l*(D J 3-productJet3 g (fun j=>D A j) 3)+
    3*(D J 2-productJet3 g (fun j=>D A j) 2)

 theorem native_initial_centered_LOW_eq_clone_add_retained
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq0 : ∀j x,0≤q j x) (hq : ∀x,Monotone (fun j=>q j x))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (P : T.cavityLeft.Assignment→ℝ) (Q : T.cavityRight.Assignment→ℝ) (x : ActiveCoordinate n→ℝ)
    (hi : i<as.length) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientCenteredLowErrorPart n q i star U b h K T P Q x .initial l t=
      nativeInitialCenteredLowClone n q i U b h K T P Q x l t+
        nativeInitialCenteredLowRetained n q i U b h K T P Q x l t := by
  unfold nativeTransientCenteredLowErrorPart nativeInitialCenteredLowClone nativeInitialCenteredLowRetained
  dsimp only
  simp_rw [native_initial_transient_LOW_jet_eq_clone_add_retained n q i star U b h K T ho
    hq0 hq hb hh hK hbm hhm hKm _ _ _ hi hl ht,native_transient_productJet3_add]
  ring

end OAI.SKFluctuations.Cavity
