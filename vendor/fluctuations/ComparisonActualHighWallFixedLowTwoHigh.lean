module

public import ComparisonSignedCavityOriginalFixedTwoHighBudget
public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallHighAllDegreeContinuumMoments
public import ComparisonSignedCavityCanonicalTransientHighBudget
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_canonical_fixed_low_two_high_budget
    (aDegree k rBound dOld ellLow : ℕ) (hdOld : 0 < dOld) (hellLow : 0 < ellLow)
    (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤(dOld:ℝ))
    (hLowOrder : (2*(p/(p-2)))*(k:ℝ)≤((2*ellLow:ℕ):ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃Cp Cq : ℝ,0< Cp ∧ 0< Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤ as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es) k 2 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*ClockTree.absJetVariation (rBound+4) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                M.data.d^aDegree)*(2*max Bclock 0)^((p-2)/p)*(2*max Bclock 0)^((p-2)/p)*(Cq*M.data.d)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (D:=D) aDegree dOld rBound hdOld Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_continuum_low_profile_moment
    (D:=D) ellLow hellLow Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    hnQ M hwork L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t s _hU hl ht hs hT G forms hcut hmass es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=2*max Bclock 0
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    M.data.d^aDegree
  let rho:=Cq*M.data.d
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hd := M.data.hd
  have HC : 0 ≤ C:=by dsimp only [C];positivity
  have Hrho : 0 < rho:=by dsimp only [rho];positivity
  let P:=fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es
  have HrawOld:=hgrid U T l t hl ht hT G forms hmass
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 P
      (by have Hq : 0< p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOld:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [P,abs_mul,native_site_monomial_abs_one,mul_one,Real.rpow_natCast,C,law,q,b,h,S,K,Mclock,as] using HrawOld
  have Hb j : b j ≤ max Bclock 0 := by
    have HT := M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have HH := (M.hf (partitionPoint 0 as j)).coe_nonneg
    change (M.bf (partitionPoint 0 as j):ℝ) ≤ max Bclock 0
    exact (by linarith : (M.bf (partitionPoint 0 as j):ℝ) ≤ M.data.T).trans
      (M.hT.trans (le_max_left _ _))
  have Hhigh:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have HQmoment j (hj : j≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0≤ rho^((2*(p/(p-2)))*(k:ℝ)) := by
    by_cases hk0 : k=0
    · simp only [hk0,Nat.cast_zero,mul_zero,Real.rpow_zero]
      exact le_of_eq ((ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0)
    · have hek : 0<(2*(p/(p-2)))*(k:ℝ):=by
        have Hq : 0< p/(p-2):=div_pos (by linarith) (by linarith)
        have Hk : 0<(k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hk0
        positivity
      apply (ClockTree.pairClock as j).disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0
        (fun σ=>ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) hek hLowOrder Hrho.le
      simp only [Real.rpow_natCast]
      exact hgridQ U l t s hl ht hs hcut j hj
  exact native_fixed_low_two_high_wholeLaw_bound n U k q b h K T ho hT P hl ht HC Hrho
    (show 0 ≤ 2*max Bclock 0 by positivity) hp
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment
    (fun j _=>Hhigh j) HQmoment

end OAI.SKFluctuations.Cavity
