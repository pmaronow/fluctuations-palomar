module

public import ComparisonSignedCavityWholeLawTransientPhysical
public import ComparisonSignedCavityTransientMixedAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_transient_high_wholeLaw_first_bound (n U k : ℕ) (hk : 0<k)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.Assignment→ℝ)
    {l t C rho : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hrho : 0<rho)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ=>|P σ|^4) 0≤C^4)
    (hLow : ∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k)) :
    |nativeTransientHighJet n q U b h K T P 0 k l t|≤
      ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*C*rho^k*
        nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
          (cutTSlope n U 0 b h K) T 1 := by
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Ds:=List.replicate k (cutLSlope n U t b h K)
  let B:=wholeLawFiniteDirectionBound as.length (Ds++[A])
  have hlaw i : Monotone (fun j=>law j i):=cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm i
  have hzero i : (0:ℝ)≤law 0 i:=cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 i
  have hperm : (Ds++[A]).Perm (A::Ds) := by
    simpa only [List.append_nil] using (List.perm_middle (a:=A) (l₁:=Ds) (l₂:=[]))
  have Hperm:=T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho 0 law
    hlaw hzero (wholeLawFiniteDirectionBound_nonneg _ _) hperm
    (wholeLawFiniteDirectionBound_bounds _ _) P 0
  unfold nativeTransientHighJet
  change |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
    ((Ds++[A]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P|≤_
  rw [Hperm]
  have H:=T.disorderProfileJets_errorFirst_finite_wholeLaw_moment_L2
    (fullWeight_pos n) (fullFeature n) (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i) ho 0 law 0 hlaw hzero A Ds
    (by simpa only [Ds,List.length_replicate] using hk)
    (wholeLawFiniteDirectionBound_nonneg as.length (A::Ds))
    (wholeLawFiniteDirectionBound_bounds as.length (A::Ds)) hC hrho hT P hP
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro D hD j hj
      rw [(List.mem_replicate.mp hD).2]
      simpa only [Ds,List.length_replicate] using hLow j hj)
  simpa only [List.map_cons,Ds,List.length_replicate,nativeWholeLawProfileCost,
    Real.rpow_one,law,A] using H

end OAI.SKFluctuations.Cavity
