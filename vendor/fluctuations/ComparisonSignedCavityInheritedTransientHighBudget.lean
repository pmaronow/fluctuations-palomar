module

public import ComparisonSignedCavityInheritedFixedLowOneHigh
public import ComparisonSignedCavityOriginalTransientHighBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_transient_high_budget
    (aDegree k rBound : ℕ) (ha : 0<aDegree) (hk : 0<k)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀es : List T.Slot,
          |nativeTransientHighJet n q U b h K T
            (fun σ=>(G.canonicalMinimumSource M forms).product σ*siteMonomial T σ es) 0 k l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*(Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp,Cq,hCp,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_one_high_budget
    (D:=D) aDegree k rBound ha hk Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass es
  exact hj U T l t t hU hl ht ht hT G forms initial x W hxsx hxW hcut hmass es

end OAI.SKFluctuations.Cavity
