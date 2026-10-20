module

public import ComparisonSignedCavityOriginalFixedLowHighBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem native_fixed_low_two_high_wholeLaw_bound (n U k : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.Assignment→ℝ)
    {l t s C rho Mcap p : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hrho : 0<rho) (hMcap : 0≤Mcap) (hp : 2<p)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ=>|P σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))))
    (hHigh : ∀j,j≤as.length→∀σ τ,|ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ|≤Mcap)
    (hLow : ∀j,j≤as.length→(pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0≤rho^((2*(p/(p-2)))*(k:ℝ))) :
    |nativeFixedLowHighProfile n q U b h K T P k 2 s l t|≤
      pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) k*C*
        Mcap^((p-2)/p)*Mcap^((p-2)/p)*rho^k*
        nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T (4/p) := by
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Ds:=List.replicate k (cutLSlope n U s b h K)
  let B:=wholeLawFiniteDirectionBound as.length (Ds++[A,A])
  have hlaw i : Monotone (fun j=>law j i):=cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm i
  have hzero i : (0:ℝ)≤law 0 i:=cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 i
  have hperm : (Ds++[A,A]).Perm (A::A::Ds):=by
    simpa only [List.cons_append,List.nil_append] using (List.perm_append_comm : (Ds++[A,A]).Perm ([A,A]++Ds))
  have Hperm:=T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho 0 law
    hlaw hzero (wholeLawFiniteDirectionBound_nonneg _ _) hperm
    (wholeLawFiniteDirectionBound_bounds _ _) P 0
  unfold nativeFixedLowHighProfile
  change |disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
    ((Ds++[A,A]).map (ReplicaTree.coordinateProfile (fullFeature n))) T P|≤_
  rw [Hperm]
  have H:=T.disorderProfileJets_twoErrorFirst_finite_wholeLaw_moment_L2
    (fullWeight_pos n) (fullFeature n) (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i) ho 0 law 0 hlaw hzero A Ds
    (wholeLawFiniteDirectionBound_nonneg as.length (A::A::Ds))
    (wholeLawFiniteDirectionBound_bounds as.length (A::A::Ds)) hC hMcap hrho hp hT P hP hHigh
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro D hD j hj
      rw [(List.mem_replicate.mp hD).2]
      simpa only [Ds,List.length_replicate] using hLow j hj)
  simpa only [List.map_cons,Ds,List.length_replicate,nativeWholeLawProfileCost,law,A] using H

end OAI.SKFluctuations.Cavity
