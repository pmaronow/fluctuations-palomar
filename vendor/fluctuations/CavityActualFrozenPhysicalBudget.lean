module

public import CavityPhysicalErrorRadius
public import CavityFrozenTwoErrorBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem cutFrozenLowHighJet_actualPhysical_twoError_budget (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j)
    (T : ClockTree (Spin n × Bool) as) {r k : ℕ} (hT : T.leaves≤r)
    (P : T.Assignment → ℝ) {C B rho p : ℝ}
    (hC : 0≤C) (hB : 0≤B) (hrho : 0<rho) (hp : 2<p)
    (hP : ∀ σ, |P σ|≤C)
    (hcap : ∀ j, j≤as.length → b j≤B ∧ h j≤B)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hmoment : ∀ j, j≤as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavityVariance n U as b h t)
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U 1 b h (finitePhysicalMixedClock (n+1) as b h)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((p/(p-2))*(k:ℝ))) 0
        ≤rho^((p/(p-2))*(k:ℝ))) :
    |cutFrozenLowHighJet n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h
      (finitePhysicalMixedClock (n+1) as b h) T P 0 k 2 t| ≤
      ClockTree.pairForkVariation r*ClockTree.pairForkVariation (r+2)*ClockTree.absJetVariation (r+4) k*C*
        (4*B)^((p-2)/p)*(4*B)^((p-2)/p)*rho^k*
        (T.forkCost (fun j=>(finitePhysicalHighRadius n U as b h t j)^(4/p))+
          (∫ u, ClockTree.edgeDensity 0 as (fun j=>(finitePhysicalHighRadius n U as b h t j)^(4/p)) u)) := by
  let K := finitePhysicalMixedClock (n+1) as b h
  have hK0 : ∀ j, 0≤K j := finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0
  have hKm : Monotone K := finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0
  have hqc : ∀ j (i : RestCoordinate n), 0≤(Sum.elim (fun _=>b j) (fun _=>h j)) i := by
    intro j i
    cases i <;> first | exact hb0 j | exact hh0 j
  have hqm : ∀ i : RestCoordinate n, Monotone (fun j=>(Sum.elim (fun _=>b j) (fun _=>h j)) i) := by
    intro i
    cases i <;> first | exact hb | exact hh
  have hc : ∀ j, j≤as.length → |b j|≤2*B ∧ |h j|≤2*B ∧ |K j|≤2*B := by
    intro j hj
    have H := hcap j hj
    have HK := finitePhysicalMixedClock_le_add (n+1) ho b h hb0 j
    rw [abs_of_nonneg (hb0 j),abs_of_nonneg (hh0 j),abs_of_nonneg (hK0 j)]
    dsimp only [K] at HK ⊢
    constructor
    · linarith
    constructor <;> linarith
  have hkernel : ∀ j, j≤as.length → ∀ σ τ,
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ|≤4*B := by
    apply cutTSlope_zero_covariance_abs_le n U as.length b h K (by positivity)
    intro j hj
    have H := hcap j hj
    have HK := finitePhysicalMixedClock_le_add (n+1) ho b h hb0 j
    rw [abs_of_nonneg (hh0 j),abs_of_nonneg (hb0 j),abs_of_nonneg (hK0 j)]
    dsimp only [K] at HK ⊢
    linarith
  have hs : ∀ j, j≤as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n
        (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U 0 t b h K)
      (fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) 0
      ≤(finitePhysicalHighRadius n U as b h t j)^2 := by
    intro j _
    exact le_of_eq (finitePhysicalHighSecond_eq_radius_sq n U ho b h t j)
  exact cutFrozenLowHighJet_twoError_moment_budget n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
    U b h K T ho P 0 hqc hqm hb0 hh0 hK0 hb hh hKm hT hC hrho (by positivity)
    (by positivity) hp hP hc ht (finitePhysicalHighRadius_nonneg n U as b h t) hkernel hs hmoment

end OAI.SKFluctuations.Cavity
