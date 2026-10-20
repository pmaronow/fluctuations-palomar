module

public import ComparisonSignedCavityInheritedAllDegreeLowRestorationLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_joint_LOW_restoration_price
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalMinimumSource M forms).restProduct a z|  ≤
            C*sourceMonomialScale M.xs W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ)))*W^2 := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_inherited_all_degree_canonical_low_restoration_ledger
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let base:=4*(rBound:ℝ)*(rBound+1)*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^aDegree)*(Cq*(1+Ccut))^2
  have hbase : 0 ≤ base:=by
    have HV:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [base]
    positivity
  refine ⟨base+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z haz
  have Hraw:=hj U T hU hT G forms initial W hxW hcut hmass a z haz
  let Z:=sourceMonomialScale M.xs W initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us jGrid) (T.splitIndex a z)+1/(n+1:ℕ))
  have hZ : 0 ≤ Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hd : 0 ≤ d:=by
    dsimp only [d,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
    (show 0 ≤ Z*d*W^2 by positivity)
  apply Hraw.trans
  convert Hmajor using 1 <;> dsimp only [base,Z,d] <;> ring

end OAI.SKFluctuations.Cavity
