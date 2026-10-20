module

public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallAllDegreeContinuumMoments
public import ComparisonSignedCavityInheritedAllDegreeLowRestorationLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_canonical_low_restoration_ledger
    (aDegree rBound : ℕ)
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalHighWallSource M forms).restProduct a z| ≤
            4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                M.data.d^aDegree)*
              (actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
                (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ)))*
              (Cq*M.data.d)^2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_continuum_all_degree_even_moment
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_continuum_low_profile_moment
    (D:=D) 4 (by norm_num) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    hnQ M hwork L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T hU hT G forms hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*max Bclock 0
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    M.data.d^aDegree
  let rho:=Cq*M.data.d
  let d:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ))
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
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have HC : 0 ≤ C:=by
    dsimp only [C]
    exact mul_nonneg (by positivity) (pow_nonneg M.data.hd.le _)
  have Hrho : 0 < rho:=by dsimp only [rho];exact mul_pos hCq M.data.hd
  have hTemp : 0 ≤ M.data.T:=M.data.hepsilon.1.le.trans M.data.hepsilon.2.le
  have Hd : 0 ≤ d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg (2*M.data.T) hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock j (_hj : j ≤ as.length) : |b j| ≤ Mclock ∧ |h j| ≤ Mclock ∧ |K j| ≤ Mclock:=by
    have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have Hscale : M.data.T ≤ max Bclock 0:=M.hT.trans (le_max_left _ _)
    have HSj:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock,K,b,h,S] at *
    have Hbj:=NNReal.coe_nonneg (M.bf (partitionPoint 0 as j))
    have Hhj:=NNReal.coe_nonneg (M.hf (partitionPoint 0 as j))
    have HB : 0 ≤ max Bclock 0:=le_max_right _ _
    exact ⟨by linarith,by linarith,by linarith⟩
  have HQmoment l (hl : l∈Icc (0:ℝ) 1) j (hj : j ≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0 ≤ rho^8 := by
    exact hgridQ U l 1 1 hl (by norm_num) (by norm_num) hcut j hj
  apply native_centered_low_gamma_low_restoration_wholeLaw_bound n U q b h S T ho hT
    (G.canonicalHighWallSource M forms).restProduct a z hU haz HC Hrho HM Hd
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    _ Hclock _ HQmoment
  · intro l hl
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct] using
      hgrid U T l 1 hl (by norm_num) hT G forms hmass
  · intro l hl
    have H:=M.data.current_low_error_radius_le_original M.alpha as ho U hl
      (show (1:ℝ)∈Icc 0 1 by norm_num) _ (T.splitIndex_le_clockLength a z)
    dsimp only at H
    simpa only [haz,ite_true] using H

end OAI.SKFluctuations.Cavity
