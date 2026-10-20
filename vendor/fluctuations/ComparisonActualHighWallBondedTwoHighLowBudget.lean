module

public import ComparisonActualHighWallBondedLowFactorMoments
public import ComparisonSignedCavityMixedErrorCanonicalLedger
public import ComparisonSignedCavityWholeLawTaylorMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_high_wall_canonical_two_high_low_factor
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*M.data.d →
          |cutFrozenLowHighJet n q U b h K T
            (fun σ=>(G.canonicalHighWallSource M f).product σ*
              (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))) 0 0 2 t| ≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                (M.data.d*M.data.d^aDegree))*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_low_factor_even_moment
    (D:=D) aDegree dOrder rBound hd Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T t ht hT G f hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=2*max Bclock 0
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (M.data.d*M.data.d^aDegree)
  let J:=fun σ=>(G.canonicalHighWallSource M f).product σ*
    (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
      (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hTemp:=(M.data.hepsilon.1.trans M.data.hepsilon.2).le
  have Hb j : b j ≤ M.data.T:=by
    have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have HH:=(M.hf (partitionPoint 0 as j)).coe_nonneg
    dsimp only [b]
    linarith
  have hD:=M.data.hd.le
  have HC : 0 ≤ C:=by dsimp only [C];positivity
  have Hraw:=hgridP U T 0 t (by norm_num) ht hT G f hmass c d hcd hmassNew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,Mclock,law,q,b,h,S,K,as] using Hraw
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have Hclock j (_hj : j≤as.length) : |b j| ≤ Mclock ∧ |h j| ≤ Mclock ∧ |K j| ≤ Mclock:=by
    have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have Hhn:=(M.hf (partitionPoint 0 as j)).coe_nonneg
    have Hbn:=(M.bf (partitionPoint 0 as j)).coe_nonneg
    have HK : K j ≤ M.data.T:=by
      have HR:=mul_le_mul_of_nonneg_left (HS j).2 Hbn
      dsimp only [K,b,h]
      linarith
    have Hbound:=M.hT.trans (le_max_left Bclock 0)
    rw [abs_of_nonneg Hbn,abs_of_nonneg Hhn,abs_of_nonneg (hK0 j)]
    dsimp only [Mclock,b,h]
    exact ⟨by linarith,by linarith,by linarith⟩
  have H:=cutFrozenLowHighJet_twoError_wholeLaw_moment_budget n q U b h K T ho J 0 ht
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT
    (k:=0) (rho:=1) HC (by norm_num) HM (show 0 ≤ 2*M.data.T by positivity) hp Hmoment Hclock
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro j _
      have HE:=(ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0
      simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero] using HE.le)
  simpa only [C,J,Mclock,law,q,A,K,b,h,S,as,ClockTree.absJetVariation,pow_zero,mul_one,
    nativeWholeLawProfileCost] using H

end OAI.SKFluctuations.Cavity
