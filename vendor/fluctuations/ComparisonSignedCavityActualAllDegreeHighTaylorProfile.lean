module

public import ComparisonSignedCavityActualCanonicalHighTaylorProfile
public import ComparisonSignedCavityActualConstantHighTaylorProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_minimum_inherited_all_degree_HIGH_parts_profile
    (aDegree rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W → W ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
          |nativeActualHigherHighPart part n q U b h K T (G.canonicalMinimumSource M forms).product a z l t| ≤
            C*W*sourceMonomialScale x W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  by_cases ha0 : aDegree=0
  · subst aDegree
    obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile
      (D:=D) rBound dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hsource hxs L us hus hret hmesh
    filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hx hxW hW1 hcut hmass a z l t hl ht part
    have HP : (G.canonicalMinimumSource M forms).product=(fun _=>1):=by
      funext σ
      unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
      apply Finset.prod_eq_one
      intro e he
      exact Fin.elim0 e
    have HI : initial=∅:=by
      ext e
      exact Fin.elim0 e
    rw [HP,HI]
    simpa only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] using
      hj U T hU hT W (hx.trans hxW) hW1 hcut a z l t hl ht part
  · exact eventually_actual_minimum_inherited_canonical_HIGH_parts_profile
      (D:=D) aDegree rBound dOrder (Nat.pos_of_ne_zero ha0) hd p hp hOrder
      Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt

end OAI.SKFluctuations.Cavity
