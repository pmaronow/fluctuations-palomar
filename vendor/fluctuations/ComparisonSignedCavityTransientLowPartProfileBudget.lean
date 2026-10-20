module

public import ComparisonSignedCavityTransientLowErrorParts
public import ComparisonSignedCavityOriginalTransientHighBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

def nativeTransientLowErrorPartDirection (n U i star : ℕ) (b h K : ℕ→ℝ) :
    NativeTransientLowErrorPart→ℕ→FullCoordinate n→ℝ
  | .initial,j,x=>if j=i then cutLowError n U b h K j x else 0
  | .star,j,x=>if j≠i ∧ j=star then cutLowError n U b h K j x else 0
  | .moving,j,x=>if j≠i ∧ j≠star then cutLowError n U b h K j x else 0

theorem native_transient_low_part_direction_profile (n U i star : ℕ) (b h K : ℕ→ℝ)
    (part : NativeTransientLowErrorPart) :
    ReplicaTree.coordinateProfile (fullFeature n) (nativeTransientLowErrorPartDirection n U i star b h K part)=
      nativeTransientLowErrorPartKernel i star
        (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)) part := by
  funext j σ τ
  cases part <;> by_cases hi : j=i <;> by_cases hs : j=star <;>
    simp_all [nativeTransientLowErrorPartDirection,nativeTransientLowErrorPartKernel,
      ReplicaTree.coordinateProfile]

theorem native_transient_low_part_radius (n U i star : ℕ) (b h K : ℕ→ℝ)
    (as : List PositiveMass) (law : ℕ→FullCoordinate n→ℝ) (part : NativeTransientLowErrorPart) (j : ℕ) :
    nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K part) j=
      match part with
      | .initial=>if j=i then nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j else 0
      | .star=>if j≠i ∧ j=star then nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j else 0
      | .moving=>if j≠i ∧ j≠star then nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j else 0 := by
  cases part <;> by_cases hi : j=i <;> by_cases hs : j=star <;>
    simp_all [nativeWholeLawErrorRadius,nativeWholeLawErrorSecond,
      nativeTransientLowErrorPartDirection,ReplicaTree.coordinateProfile,ClockTree.disorderExpect]

theorem native_transient_low_part_wholeLaw_first_bound (n U i star k : ℕ) (hk : 0<k)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.Assignment→ℝ)
    (part : NativeTransientLowErrorPart)
    {l t C rho : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hrho : 0<rho)
    (hq0 : ∀j x,0≤q j x) (hq : ∀x,Monotone (fun j=>q j x))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ=>|P σ|^4) 0≤C^4)
    (hLow : ∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k)) :
    |nativeTransientLowErrorPartJet n q i star U b h K T P 0 part k l t|≤
      let law:=cutFullVariance n q U l t b h K
      let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K part)
      ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*C*rho^k*
        (T.forkCost R+ClockTree.edgeBudget 0 as R) := by
  let law:=cutFullVariance n q U l t b h K
  let A:=nativeTransientLowErrorPartDirection n U i star b h K part
  let Ds:=List.replicate k (cutLSlope n U t b h K)
  let B:=wholeLawFiniteDirectionBound as.length (Ds++[A])
  have hlaw x : Monotone (fun j=>law j x):=cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm x
  have hzero x : (0:ℝ)≤law 0 x:=cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 x
  have hperm : (Ds++[A]).Perm (A::Ds) := by
    simpa only [List.append_nil] using (List.perm_middle (a:=A) (l₁:=Ds) (l₂:=[]))
  have Hperm:=T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho 0 law
    hlaw hzero (wholeLawFiniteDirectionBound_nonneg _ _) hperm
    (wholeLawFiniteDirectionBound_bounds _ _) P 0
  unfold nativeTransientLowErrorPartJet
  rw [←native_transient_low_part_direction_profile]
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil,Ds] at Hperm
  rw [Hperm]
  have H:=T.disorderProfileJets_errorFirst_finite_wholeLaw_moment_L2
    (fullWeight_pos n) (fullFeature n) (fun x=>(fullAmplitude n x)^2) (by
      intro σ x
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ x) ho 0 law 0 hlaw hzero A Ds
    (by simpa only [Ds,List.length_replicate] using hk)
    (wholeLawFiniteDirectionBound_nonneg as.length (A::Ds))
    (wholeLawFiniteDirectionBound_bounds as.length (A::Ds)) hC hrho hT P hP
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro D hD j hj
      rw [(List.mem_replicate.mp hD).2]
      simpa only [Ds,List.length_replicate] using hLow j hj)
  simpa only [List.map_cons,List.map_replicate,Ds,List.length_replicate,Real.rpow_one,ClockTree.edgeDensity_integral ho,
    law,A] using H

end OAI.SKFluctuations.Cavity
