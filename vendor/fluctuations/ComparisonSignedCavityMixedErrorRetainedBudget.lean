module

public import ComparisonSignedCavityMixedErrorFixedProfile
public import ComparisonSignedCavityActualLowSplitSupport
public import ComparisonSignedCavityWholeLawErrorProfiles

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

def nativeFixedLowRestPayload (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (b S : ℕ→ℝ) (j₀ : ℕ) (u z : T.Slot) (τ : T.cavityLeft.Assignment) : ℝ :=
  P τ*restCenteredFixedForkKernel n b S j₀ 0
    (T.cavityLeft.atSlot τ (T.cavityLeftSlot u)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))

theorem native_fixed_low_rest_kernel_square_eq_low_error (n U : ℕ) (b h S : ℕ→ℝ)
    {j : ℕ} (hj : j<U) (σ τ : Spin n×Bool) :
    (restCenteredFixedForkKernel n b S j 0 σ.1 τ.1)^2=
      (ReplicaTree.coordinateProfile (fullFeature n)
        (cutLowError n U b h (fun j=>h j+b j*S j)) j σ τ)^2 := by
  rw [cutLowError_centered_square n U b h S j σ τ,ite_eq_left hj]
  unfold restCenteredFixedForkKernel
  simp only [deletedOverlap,joinSpin_old]
  ring

theorem native_retained_high_fixed_low_error_wholeLaw_bound (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.cavityLeft.Assignment→ℝ)
    (u z : T.Slot) (huz : u≠z) (hcut : T.splitIndex u z<U)
    {C p Mlow Mhigh : ℝ} (hC : 0 ≤ C) (hp : 2 < p) (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h (fun j=>h j+b j*S j))
      (fun σ=>|P (T.cavityAssignment σ).1|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))))
    (hLow : ∀σ τ : Spin n,
      |restCenteredFixedForkKernel n b S (T.splitIndex u z) 0 σ τ| ≤ Mlow)
    (hHigh : ∀(j : ℕ) (σ τ : Spin n×Bool),
      |ReplicaTree.coordinateProfile (fullFeature n)
        (cutTSlope n U 0 b h (fun j=>h j+b j*S j)) j σ τ| ≤ Mhigh) :
    let K:=fun j=>h j+b j*S j
    let law:=cutFullVariance n q U 0 0 b h K
    let low:=cutLowError n U b h K
    let high:=cutTSlope n U 0 b h K
    |retainedSignedJets n q U b h K [restHighKernel n U b h K] T
      (nativeFixedLowRestPayload n T P b S (T.splitIndex u z) u z) []| ≤
      ClockTree.pairForkVariation r*C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*
        (nativeWholeLawErrorRadius n as law low (T.splitIndex u z))^(2/p)*
        (T.forkCost (fun j=>(nativeWholeLawErrorRadius n as law high j)^(2/p))+
          (∫s,ClockTree.edgeDensity 0 as (fun j=>(nativeWholeLawErrorRadius n as law high j)^(2/p)) s)) := by
  dsimp only
  let K:=fun j=>h j+b j*S j
  let law:=cutFullVariance n q U 0 0 b h K
  let low:=cutLowError n U b h K
  let high:=cutTSlope n U 0 b h K
  let A:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S (T.splitIndex u z) 0 σ.1 τ.1
  let B:=ReplicaTree.coordinateProfile (fullFeature n) high
  let dlow:=nativeWholeLawErrorRadius n as law low (T.splitIndex u z)
  let Dhigh:=nativeWholeLawErrorRadius n as law high
  have Hlow : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(A (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) 0 ≤ dlow^2 := by
    have heq : (fun σ=>(A (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2)=
      fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) low (T.splitIndex u z)
        (ClockTree.pairSpin as (T.splitIndex u z) σ).1 (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2 := by
      funext σ
      exact native_fixed_low_rest_kernel_square_eq_low_error n U b h S hcut _ _
    rw [heq]
    exact le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law low (T.splitIndex u z))
  have H:=T.disorderProfileJets_fixedLow_highError_wholeLaw_product_bound
    (fullWeight_pos n) (fullFeature n) ho 0 law 0 hT
    (fun σ=>P (T.cavityAssignment σ).1) hC hp hMlow hMhigh
    (nativeWholeLawErrorRadius_nonneg n as law low (T.splitIndex u z)) hP
    A u z huz (fun σ τ=>hLow σ.1 τ.1) Hlow B
    (fun σ=>fullFeature_coordinateProfile_self n high as.length σ) hHigh Dhigh
    (nativeWholeLawErrorRadius_nonneg n as law high)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law high j))
  have heqPayload : (fun σ=>P (T.cavityAssignment σ).1*A (T.atSlot σ u) (T.atSlot σ z))=
      fun σ=>nativeFixedLowRestPayload n T P b S (T.splitIndex u z) u z (T.cavityAssignment σ).1*
        siteMonomial T σ [] := by
    funext σ
    simp only [nativeFixedLowRestPayload,A,T.atSlot_cavityLeft,siteMonomial,mul_one]
  rw [heqPayload] at H
  dsimp only [B,high,law,K] at H
  rw [←siteRestKernel_eq_cut_high] at H
  have HE:=actual_site_rest_jets_eq_retained n q U b h (fun j=>h j+b j*S j)
    [restHighKernel n U b h (fun j=>h j+b j*S j)] T ho
    (nativeFixedLowRestPayload n T P b S (T.splitIndex u z) u z) []
  simp only [List.map_cons,List.map_nil] at HE
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
