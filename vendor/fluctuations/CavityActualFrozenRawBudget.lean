module

public import CavityActualFrozenPhysicalBudget
public import CavityActualLowRawMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem cutFrozenLowHighJet_actualPhysical_twoError_raw_budget (n U l : ℕ) (hl : 0<l)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j)
    (T : ClockTree (Spin n × Bool) as) {r k : ℕ} (hT : T.leaves≤r)
    (P : T.Assignment → ℝ) {C B rho p : ℝ}
    (hC : 0≤C) (hB : 0≤B) (hrho : 0<rho) (hp : 2<p)
    (hP : ∀ σ, |P σ|≤C)
    (hcap : ∀ j, j≤as.length → b j≤B ∧ h j≤B)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (horder : (p/(p-2))*(k:ℝ) ≤ (2*l:ℕ))
    (hraw : ∀ j, j≤as.length → finitePhysicalLowRawBudget n l as b h j≤rho^(2*l)) :
    |cutFrozenLowHighJet n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h
      (finitePhysicalMixedClock (n+1) as b h) T P 0 k 2 t| ≤
      ClockTree.pairForkVariation r*ClockTree.pairForkVariation (r+2)*ClockTree.absJetVariation (r+4) k*C*
        (4*B)^((p-2)/p)*(4*B)^((p-2)/p)*rho^k*
        (T.forkCost (fun j=>(finitePhysicalHighRadius n U as b h t j)^(4/p))+
          (∫ u, ClockTree.edgeDensity 0 as (fun j=>(finitePhysicalHighRadius n U as b h t j)^(4/p)) u)) := by
  apply cutFrozenLowHighJet_actualPhysical_twoError_budget n U ho b h hb hh hb0 hh0 T hT
    P hC hB hrho hp hP hcap ht
  intro j hj
  by_cases hk : k=0
  · simp only [hk,Nat.cast_zero,mul_zero,Real.rpow_zero]
    simpa only [ClockTree.disorderExpect,mul_one] using
      ((ClockTree.pairClock (S := Spin n × Bool) as j).disorderWeight_probability
        (fullWeight_pos n) (fullFeature n) ho 0 (finitePhysicalCavityVariance n U as b h t) 0).2.le
  · have hkpos : 0<(k:ℝ) := Nat.cast_pos.mpr (by omega)
    have hpraw : 0<(p/(p-2))*(k:ℝ) := mul_pos (div_pos (by linarith) (by linarith)) hkpos
    exact finitePhysicalLow_real_moment_le_raw n l U hl ho ht b h hb hh hb0 hh0 j hj
      hpraw horder hrho.le (hraw j hj)

end OAI.SKFluctuations.Cavity
