module

public import ComparisonSignedCavityWholeLawErrorProfiles
public import ComparisonSignedCavityWholeLawLowProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def wholeLawFiniteDirectionBound {ι : Type*} [Fintype ι] (N : ℕ)
    (Ds : List (ℕ→ι→ℝ)) : ℝ :=
  ∑d : Fin Ds.length,∑j : Fin (N+1),∑i : ι,|Ds.get d j i|

theorem wholeLawFiniteDirectionBound_nonneg {ι : Type*} [Fintype ι] (N : ℕ)
    (Ds : List (ℕ→ι→ℝ)) : 0 ≤ wholeLawFiniteDirectionBound N Ds := by
  exact Finset.sum_nonneg fun d _=>Finset.sum_nonneg fun j _=>Finset.sum_nonneg fun i _=>abs_nonneg _

theorem wholeLawFiniteDirectionBound_bounds {ι : Type*} [Fintype ι] (N : ℕ)
    (Ds : List (ℕ→ι→ℝ)) (D : ℕ→ι→ℝ) (hD : D∈Ds) (j : ℕ) (hj : j ≤ N) (i : ι) :
    |D j i| ≤ wholeLawFiniteDirectionBound N Ds := by
  classical
  obtain ⟨d,hd⟩:=List.mem_iff_get.mp hD
  let r : Fin (N+1):=⟨j,by omega⟩
  have H1 : |Ds.get d j i| ≤ ∑z : ι,|Ds.get d j z|:=
    Finset.single_le_sum (s:=Finset.univ) (f:=fun z : ι=>|Ds.get d j z|)
      (fun z _=>abs_nonneg _) (Finset.mem_univ i)
  have H2 : (∑z : ι,|Ds.get d j z|) ≤ ∑u : Fin (N+1),∑z : ι,|Ds.get d u z| := by
    simpa only [r] using Finset.single_le_sum
      (s:=Finset.univ) (f:=fun u : Fin (N+1)=>∑z : ι,|Ds.get d u z|)
      (fun u _=>Finset.sum_nonneg fun z _=>abs_nonneg _) (Finset.mem_univ r)
  have H3 : (∑u : Fin (N+1),∑z : ι,|Ds.get d u z|) ≤ wholeLawFiniteDirectionBound N Ds :=
    Finset.single_le_sum (s:=Finset.univ)
      (f:=fun e : Fin Ds.length=>∑u : Fin (N+1),∑z : ι,|Ds.get e u z|)
      (fun e _=>Finset.sum_nonneg fun u _=>Finset.sum_nonneg fun z _=>abs_nonneg _)
      (Finset.mem_univ d)
  rw [←hd]
  exact H1.trans (H2.trans H3)

theorem finitePhysicalCavitySquareVariance_monotone (n U : ℕ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (i : FullCoordinate n) :
    Monotone (fun j=>finitePhysicalCavitySquareVariance n U as b h l t j i) := by
  apply cavityPath_monotone n U hl ht
    (q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
    (fun i=>by cases i <;> first | exact hb | exact hh) hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0)
    hb0 hh0 (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0)

theorem finitePhysicalCavitySquareVariance_nonneg (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (j : ℕ) (i : FullCoordinate n) :
    0 ≤ finitePhysicalCavitySquareVariance n U as b h l t j i := by
  exact cutFullVariance_nonneg n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U hl ht
    (fun j i=>by cases i <;> first | exact hb0 j | exact hh0 j) hb0 hh0
    (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) j i

theorem nativeWholeLaw_first_profile_error_bound (n U k : ℕ) (hk : 0 < k)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ→ℝ)
    (hb : Monotone b) (hh : Monotone h) (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    {l t s : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (T : ClockTree (Spin n×Bool) as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment→ℝ) {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|P σ|^4) 0 ≤ C^4)
    (hLow : ∀j,j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0 ≤ rho^(4*k))
    (A : ℕ→FullCoordinate n→ℝ) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) 0
      ((A::List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))).map
        (ReplicaTree.coordinateProfile (fullFeature n))) T P| ≤
      ClockTree.pairForkVariation r*ClockTree.absJetVariation (r+2) k*C*rho^k*
        nativeWholeLawProfileCost n (finitePhysicalCavitySquareVariance n U as b h l t) A T 1 := by
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  let Ds:=List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))
  let B:=wholeLawFiniteDirectionBound as.length (A::Ds)
  have H:=T.disorderProfileJets_errorFirst_finite_wholeLaw_moment_L2
    (fullWeight_pos n) (fullFeature n) (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i)
    ho 0 q 0 (finitePhysicalCavitySquareVariance_monotone n U ho b h hb hh hb0 hh0 hl ht)
    (finitePhysicalCavitySquareVariance_nonneg n U as b h hb0 hh0 hl ht 0)
    A Ds (by simpa only [Ds,List.length_replicate] using hk)
    (wholeLawFiniteDirectionBound_nonneg _ _) (wholeLawFiniteDirectionBound_bounds _ _)
    hC hrho hT P hP (nativeWholeLawErrorRadius_nonneg n as q A)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho q A j))
    (by
      intro L hL j hj
      have HE:=List.mem_replicate.mp hL
      rw [HE.2]
      simpa only [Ds,List.length_replicate,finitePhysicalSquareLowKernel] using hLow j hj)
  simpa only [q,Ds,List.length_replicate,nativeWholeLawProfileCost,Real.rpow_one] using H

theorem nativeWholeLaw_two_profile_error_bound (n U k : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ→ℝ)
    (hb : Monotone b) (hh : Monotone h) (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    {l t s : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (T : ClockTree (Spin n×Bool) as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment→ℝ) {C rho M p : ℝ}
    (hC : 0 ≤ C) (hrho : 0 < rho) (hM : 0 ≤ M) (hp : 2 < p)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|P σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))))
    (hLow : ∀j,j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0 ≤ rho^((2*(p/(p-2)))*(k:ℝ)))
    (A : ℕ→FullCoordinate n→ℝ)
    (hA : ∀j,j ≤ as.length → ∀σ τ,|ReplicaTree.coordinateProfile (fullFeature n) A j σ τ| ≤ M) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) 0
      ((A::A::List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))).map
        (ReplicaTree.coordinateProfile (fullFeature n))) T P| ≤
      ClockTree.pairForkVariation r*ClockTree.pairForkVariation (r+2)*ClockTree.absJetVariation (r+4) k*
        C*M^((p-2)/p)*M^((p-2)/p)*rho^k*
        nativeWholeLawProfileCost n (finitePhysicalCavitySquareVariance n U as b h l t) A T (4/p) := by
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  let Ds:=List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))
  have H:=T.disorderProfileJets_twoErrorFirst_finite_wholeLaw_moment_L2
    (fullWeight_pos n) (fullFeature n) (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i)
    ho 0 q 0 (finitePhysicalCavitySquareVariance_monotone n U ho b h hb hh hb0 hh0 hl ht)
    (finitePhysicalCavitySquareVariance_nonneg n U as b h hb0 hh0 hl ht 0)
    A Ds (wholeLawFiniteDirectionBound_nonneg as.length (A::A::Ds))
    (wholeLawFiniteDirectionBound_bounds as.length (A::A::Ds)) hC hM hrho hp hT P hP hA
    (nativeWholeLawErrorRadius_nonneg n as q A)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho q A j))
    (by
      intro L hL j hj
      have HE:=List.mem_replicate.mp hL
      rw [HE.2]
      simpa only [Ds,List.length_replicate,finitePhysicalSquareLowKernel] using hLow j hj)
  simpa only [q,Ds,List.length_replicate,nativeWholeLawProfileCost] using H

end OAI.SKFluctuations.Cavity
