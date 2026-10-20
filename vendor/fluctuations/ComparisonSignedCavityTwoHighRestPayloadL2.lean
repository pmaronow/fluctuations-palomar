module

public import ComparisonSignedCavityTwoHighWholeLawL2
public import ComparisonSignedCavityWholeLawScalarClock
public import ComparisonSignedCavityLowAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_rest_payload_current_full_L2_le
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r : ℕ} (hT : T.leaves ≤ r) {C Bclock : ℝ} (hC : 0 ≤ C)
    (hclock : K as.length+b as.length+h as.length ≤ Bclock)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>P σ^2) 0 ≤ C^2) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ=>P (T.cavityAssignment σ).1^2) 0 ≤
      (Real.exp (wholeLawRowComparisonConstant r*Bclock)*C)^2 := by
  let J:=fun σ : T.Assignment=>P (T.cavityAssignment σ).1^2
  have H:=cavityPath_expect_close n U T ho hl ht
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)∈Icc 0 1)
    hq hbm hhm hKm hq0 hb hh hK J (fun _=>sq_nonneg _) 0
  change ExpClose
    (wholeLawRowComparisonConstant T.leaves*(K as.length+b as.length+h as.length))
    (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K) J 0)
    (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K) J 0) at H
  have hclock0 : 0 ≤ K as.length+b as.length+h as.length :=
    add_nonneg (add_nonneg (hK _) (hb _)) (hh _)
  have HB : wholeLawRowComparisonConstant T.leaves*(K as.length+b as.length+h as.length) ≤
      wholeLawRowComparisonConstant r*Bclock :=
    mul_le_mul (wholeLawRowComparisonConstant_mono hT) hclock hclock0
      (wholeLawRowComparisonConstant_nonneg _)
  have Hdec : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) J 0 ≤ C^2 := by
    rw [show J=(fun σ=>(fun τ=>P τ^2) (T.cavityAssignment σ).1) from rfl,
      native_decoupled_rest_expect n q U b h K T ho (fun τ=>P τ^2)]
    exact hP
  have Hbound := (H.mono HB).le_mul.trans
    (mul_le_mul_of_nonneg_left Hdec (Real.exp_pos _).le)
  have HE : 1 ≤ Real.exp (wholeLawRowComparisonConstant r*Bclock) :=
    Real.one_le_exp (mul_nonneg (wholeLawRowComparisonConstant_nonneg _)
      (hclock0.trans hclock))
  apply Hbound.trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (le_self_pow₀ HE (by norm_num : (2:ℕ)≠0))
    (pow_nonneg hC _)

theorem cutFrozenLowHighJet_two_high_rest_L2_bound
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r : ℕ} (hT : T.leaves ≤ r) {C M Bclock : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hclock : K as.length+b as.length+h as.length ≤ Bclock)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>P σ^2) 0 ≤ C^2)
    (hcap : ∀j,j ≤ as.length→∀σ τ,
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| ≤ M)
    {D : ℕ→ℝ} (hD : ∀j,0 ≤ D j)
    (hsecond : ∀j,(pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 t b h K)
      (fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) 0 ≤ (D j)^2) :
    |cutFrozenLowHighJet n q U b h K T (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t| ≤
      pairForkVariation r*pairForkVariation (r+2)*M*
        (Real.exp (wholeLawRowComparisonConstant r*Bclock)*C)*
        (T.forkCost D+edgeBudget 0 as D) := by
  have HP:=native_rest_payload_current_full_L2_le n q U b h K T ho P
    (by norm_num : (0:ℝ)∈Icc 0 1) ht hq0 hq hb hh hK hbm hhm hKm hT hC hclock hP
  exact cutFrozenLowHighJet_two_high_wholeLaw_L2_bound n q U b h K T ho
    (fun σ=>P (T.cavityAssignment σ).1) 0 ht hq0 hq hb hh hK hbm hhm hKm hT
    (mul_nonneg (Real.exp_pos _).le hC) hM HP hcap hD hsecond

theorem native_rest_payload_high_second_restoration_L2_bound
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r : ℕ} (hT : T.leaves ≤ r) {C M Bclock : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hclock : K as.length+b as.length+h as.length ≤ Bclock)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>P σ^2) 0 ≤ C^2)
    (hcap : ∀j,j ≤ as.length→∀σ τ,
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| ≤ M)
    {D : ℕ→ℝ} (hD : ∀j,0 ≤ D j)
    (hsecond : ∀t∈Icc (0:ℝ) 1,∀j,
      (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 t b h K)
      (fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) 0 ≤ (D j)^2) :
    |∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K T
      (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t| ≤
      pairForkVariation r*pairForkVariation (r+2)*M*
        (Real.exp (wholeLawRowComparisonConstant r*Bclock)*C)*
        (T.forkCost D+edgeBudget 0 as D) := by
  have Hnonneg : 0 ≤ pairForkVariation r*pairForkVariation (r+2)*M*
      (Real.exp (wholeLawRowComparisonConstant r*Bclock)*C)*
      (T.forkCost D+edgeBudget 0 as D) :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) hM)
      (mul_nonneg (Real.exp_pos _).le hC))
      (add_nonneg (T.forkCost_nonneg hD) (edgeBudget_nonneg ho hD))
  have H:=weighted_unit_integral_abs_le Hnonneg (fun t ht=>
    cutFrozenLowHighJet_two_high_rest_L2_bound n q U b h K T ho P ht hq0 hq hb hh hK
      hbm hhm hKm hT hC hM hclock hP hcap hD (hsecond t ht)) 1
  simpa only [pow_one] using H

end OAI.SKFluctuations.Cavity
