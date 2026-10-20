module

public import ComparisonSignedCavityFixedErrorRawJets
public import ComparisonSignedCavityWholeLawTaylorMoments
public import ComparisonSignedCavityMixedErrorRetainedBudget
public import ComparisonSignedCavityBareContinuumLowProfile
public import ComparisonSignedCavityLowGammaFullRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_fixed_low_second_restoration_wholeLaw_bound (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {r : ℕ} (hT : T.leaves≤r) (P : T.Assignment→ℝ)
    (u z : T.Slot) (huz : u≠z) (hcut : T.splitIndex u z<U)
    {l C rho B : ℝ} (hl : l∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hrho : 0<rho) (hB : 0≤B)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤h j+b j*S j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone (fun j=>h j+b j*S j))
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|P σ|^4) 0≤C^4)
    (hclock : ∀j,j≤as.length→|b j|≤B∧|h j|≤B∧|h j+b j*S j|≤B)
    (hmoment : ∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U 1 b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0≤rho^8) :
    |cutLowJet n q U b h (fun j=>h j+b j*S j) T
      (fun σ=>P σ*restCenteredFixedForkKernel n b S (T.splitIndex u z) 0
        (T.atSlot σ u).1 (T.atSlot σ z).1) 0 2 l 1|≤
      ClockTree.absJetVariation r 2*C*
        nativeWholeLawErrorRadius n as
          (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
          (cutLowError n U b h (fun j=>h j+b j*S j)) (T.splitIndex u z)*rho^2 := by
  let K:=fun j=>h j+b j*S j
  let law:=cutFullVariance n q U l 1 b h K
  let A:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S (T.splitIndex u z) 0 σ.1 τ.1
  let d:=nativeWholeLawErrorRadius n as law (cutLowError n U b h K) (T.splitIndex u z)
  have Hsecond : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(A (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) 0≤d^2 := by
    have HE : (fun σ=>(A (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2)=
        fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)
          (T.splitIndex u z) (ClockTree.pairSpin as (T.splitIndex u z) σ).1
          (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2 := by
      funext σ
      exact native_fixed_low_rest_kernel_square_eq_low_error n U b h S hcut _ _
    rw [HE]
    exact le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law (cutLowError n U b h K) _)
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0 hq0 hq hb hh hK hbm hhm hKm
    2 hl (by norm_num)]
  have H:=T.disorderProfileJets_fixedError_finite_wholeLaw_raw_bound
    (fullWeight_pos n) (fullFeature n) (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i) ho 0 law 0
    (fun i=>cutFullVariance_monotone n q U hl (by norm_num) hq hb hh hK hbm hhm hKm i)
    (fun i=>cutFullVariance_nonneg n q U hl (by norm_num) hq0 hb hh hK 0 i)
    (List.replicate 2 (cutLSlope n U 1 b h K)) (by simp) hB hC hrho
    (nativeWholeLawErrorRadius_nonneg n as law (cutLowError n U b h K) _)
    (by
      intro D hD j hj i
      rw [(List.mem_replicate.mp hD).2]
      exact cutLSlope_one_coordinate_abs_le n U as.length b h K hB hclock j hj i)
    hT P hP A u z huz Hsecond (by
      intro D hD j hj
      rw [(List.mem_replicate.mp hD).2]
      simpa only [List.length_replicate] using hmoment j hj)
  simpa only [List.map_replicate,List.length_replicate,A,d,law,K] using H

end OAI.SKFluctuations.Cavity
