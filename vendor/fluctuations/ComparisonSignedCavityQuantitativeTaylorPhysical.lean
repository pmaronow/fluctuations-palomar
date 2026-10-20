module

public import CavityActualFrozenRawBudget
public import CavityOffDiagonalErrorBudget
public import ComparisonSignedCavityFrozenAssembly
public import CavityQuantitativeClosure

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativePhysicalTaylorSplitCost (n U : ℕ) {as : List PositiveMass}
    (b h : ℕ → ℝ) (T : ClockTree (Spin n × Bool) as) (t e : ℝ) : ℝ :=
  T.forkCost (fun j => (finitePhysicalHighRadius n U as b h t j)^e) +
    ClockTree.edgeBudget 0 as (fun j => (finitePhysicalHighRadius n U as b h t j)^e)

def nativePhysicalTaylorTwoErrorBudget (n U r k : ℕ) {as : List PositiveMass}
    (b h : ℕ → ℝ) (T : ClockTree (Spin n × Bool) as)
    (C B rho p t : ℝ) : ℝ :=
  ClockTree.pairForkVariation r * ClockTree.pairForkVariation (r+2) *
    ClockTree.absJetVariation (r+4) k * C *
    (4*B)^((p-2)/p) * (4*B)^((p-2)/p) * rho^k *
    nativePhysicalTaylorSplitCost n U b h T t (4/p)

def nativePhysicalTaylorOneErrorBudget (n U r k : ℕ) {as : List PositiveMass}
    (b h : ℕ → ℝ) (T : ClockTree (Spin n × Bool) as) (C rho t : ℝ) : ℝ :=
  ClockTree.pairForkVariation r * ClockTree.absJetVariation (r+2) k * C * rho^k *
    nativePhysicalTaylorSplitCost n U b h T t 1

theorem nativePhysicalTaylorSplitCost_nonneg (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (T : ClockTree (Spin n × Bool) as) (t e : ℝ) :
    0 ≤ nativePhysicalTaylorSplitCost n U b h T t e := by
  exact add_nonneg (T.forkCost_nonneg (fun j =>
    Real.rpow_nonneg (finitePhysicalHighRadius_nonneg n U as b h t j) e))
    (ClockTree.edgeBudget_nonneg ho (fun j =>
      Real.rpow_nonneg (finitePhysicalHighRadius_nonneg n U as b h t j) e))

theorem nativePhysicalTaylorSplitCost_eq_density (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (T : ClockTree (Spin n × Bool) as) (t e : ℝ) :
    nativePhysicalTaylorSplitCost n U b h T t e =
      T.forkCost (fun j => (finitePhysicalHighRadius n U as b h t j)^e) +
        (∫ u, ClockTree.edgeDensity 0 as
          (fun j => (finitePhysicalHighRadius n U as b h t j)^e) u) := by
  rw [ClockTree.edgeDensity_integral ho]
  rfl

theorem nativePhysicalTaylor_two_error_raw (n U l : ℕ) (hl : 0 < l)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j)
    (T : ClockTree (Spin n × Bool) as) {r k : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C B rho p : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hrho : 0 < rho) (hp : 2 < p)
    (hP : ∀ σ, |P σ| ≤ C)
    (hcap : ∀ j, j ≤ as.length → b j ≤ B ∧ h j ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (horder : (p/(p-2))*(k:ℝ) ≤ (2*l:ℕ))
    (hraw : ∀ j, j ≤ as.length →
      finitePhysicalLowRawBudget n l as b h j ≤ rho^(2*l)) :
    |cutFrozenLowHighJet n (fun j => Sum.elim (fun _ => b j) (fun _ => h j))
      U b h (finitePhysicalMixedClock (n+1) as b h) T P 0 k 2 t| ≤
      nativePhysicalTaylorTwoErrorBudget n U r k b h T C B rho p t := by
  rw [nativePhysicalTaylorTwoErrorBudget,
    nativePhysicalTaylorSplitCost_eq_density n U ho]
  exact cutFrozenLowHighJet_actualPhysical_twoError_raw_budget n U l hl ho b h
    hb hh hb0 hh0 T hT P hC hB hrho hp hP hcap ht horder hraw

theorem nativePhysicalTaylor_one_error_zero_low (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j)
    (T : ClockTree (Spin n × Bool) as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C rho : ℝ} (hC : 0 ≤ C)
    (hP : ∀ σ, |P σ| ≤ C) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |cutFrozenLowHighJet n (fun j => Sum.elim (fun _ => b j) (fun _ => h j))
      U b h (finitePhysicalMixedClock (n+1) as b h) T P 0 0 1 t| ≤
      nativePhysicalTaylorOneErrorBudget n U r 0 b h T C rho t := by
  let K := finitePhysicalMixedClock (n+1) as b h
  have hq0 : ∀ j (i : RestCoordinate n),
      0 ≤ Sum.elim (fun _ => b j) (fun _ => h j) i := by
    intro j i
    cases i <;> first | exact hb0 j | exact hh0 j
  have hqm : ∀ i : RestCoordinate n,
      Monotone (fun j => Sum.elim (fun _ => b j) (fun _ => h j) i) := by
    intro i
    cases i <;> first | exact hb | exact hh
  rw [cutFrozenLowHighJet_eq_profileJets n _ U b h K T ho P 0 hq0 hqm hb0 hh0
    (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0) 0 1 ht]
  simp only [List.replicate_zero,List.nil_append,List.replicate_one]
  have H := T.disorderProfileJets_oneError_offDiagonal_L2
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavityVariance n U as b h t) 0 hT P hC hP
    (finitePhysicalHighKernel n U as b h)
    (fun σ => fullFeature_coordinateProfile_self n
      (cutTSlope n U 0 b h K) as.length σ)
    (finitePhysicalHighRadius_nonneg n U as b h t)
    (fun j => le_of_eq (finitePhysicalHighSecond_eq_radius_sq n U ho b h t j))
  simpa only [nativePhysicalTaylorOneErrorBudget,ClockTree.absJetVariation,
    nativePhysicalTaylorSplitCost,Real.rpow_one,pow_zero,mul_one,
    ClockTree.edgeDensity_integral ho,finitePhysicalCavityVariance,
    finitePhysicalHighKernel,K] using H

theorem nativePhysicalTaylor_one_error_raw (n U l : ℕ) (hl : 0 < l)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j)
    (T : ClockTree (Spin n × Bool) as) {r k : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C B rho : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hrho : 0 < rho)
    (hP : ∀ σ, |P σ| ≤ C)
    (hcap : ∀ j, j ≤ as.length → b j ≤ B ∧ h j ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (horder : 2*k ≤ 2*l)
    (hraw : ∀ j, j ≤ as.length →
      finitePhysicalLowRawBudget n l as b h j ≤ rho^(2*l)) :
    |cutFrozenLowHighJet n (fun j => Sum.elim (fun _ => b j) (fun _ => h j))
      U b h (finitePhysicalMixedClock (n+1) as b h) T P 0 k 1 t| ≤
      nativePhysicalTaylorOneErrorBudget n U r k b h T C rho t := by
  by_cases hk : k = 0
  · subst k
    exact nativePhysicalTaylor_one_error_zero_low n U ho b h hb hh hb0 hh0
      T hT P hC hP ht
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let K := finitePhysicalMixedClock (n+1) as b h
  have hK0 : ∀ j, 0 ≤ K j := finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0
  have hKm : Monotone K := finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0
  have hq0 : ∀ j (i : RestCoordinate n),
      0 ≤ Sum.elim (fun _ => b j) (fun _ => h j) i := by
    intro j i
    cases i <;> first | exact hb0 j | exact hh0 j
  have hqm : ∀ i : RestCoordinate n,
      Monotone (fun j => Sum.elim (fun _ => b j) (fun _ => h j) i) := by
    intro i
    cases i <;> first | exact hb | exact hh
  have hc : ∀ j, j ≤ as.length →
      |b j| ≤ 2*B ∧ |h j| ≤ 2*B ∧ |K j| ≤ 2*B := by
    intro j hj
    have Hj := hcap j hj
    have HK := finitePhysicalMixedClock_le_add (n+1) ho b h hb0 j
    rw [abs_of_nonneg (hb0 j),abs_of_nonneg (hh0 j),abs_of_nonneg (hK0 j)]
    dsimp only [K] at HK ⊢
    constructor
    · linarith
    constructor <;> linarith
  have H := cutFrozenLowHighJet_oneError_moment_budget n _ U b h K T ho P 0
    hq0 hqm hb0 hh0 hK0 hb hh hKm hT hkpos hC hrho.le (by positivity : 0 ≤ 2*B)
    hP hc ht (finitePhysicalHighRadius_nonneg n U as b h t)
    (fun j _ => le_of_eq (finitePhysicalHighSecond_eq_radius_sq n U ho b h t j))
    (fun j hj => by
      have hpraw : (0:ℝ) < (2*k:ℕ) := Nat.cast_pos.mpr (by omega)
      have hpr : ((2*k:ℕ):ℝ) ≤ (2*l:ℕ) := Nat.cast_le.mpr horder
      have HR := finitePhysicalLow_real_moment_le_raw n l U hl ho ht b h hb hh
        hb0 hh0 j hj hpraw hpr hrho.le (hraw j hj)
      simpa only [finitePhysicalLowKernel,finitePhysicalCavityVariance,K,
        Real.rpow_natCast] using HR)
  simpa only [nativePhysicalTaylorOneErrorBudget,nativePhysicalTaylorSplitCost,
    Real.rpow_one,ClockTree.edgeDensity_integral ho] using H

end OAI.SKFluctuations.Cavity
