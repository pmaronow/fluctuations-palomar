module

public import ComparisonActualHighWallLowRestorationLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_high_wall_canonical_joint_LOW_restoration_price
    (aDegree rBound : ℕ)
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalHighWallSource M forms).restProduct a z|  ≤
            C*M.data.d^aDegree*
              (actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
                (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ)))*M.data.d^2 := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_high_wall_canonical_low_restoration_ledger
    (D:=D) aDegree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let base:=4*(rBound:ℝ)*(rBound+1)*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^aDegree)*Cq^2
  have hbase : 0 ≤ base:=by
    have HV:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [base]
    positivity
  refine ⟨base+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms hcut hmass a z haz
  have Hraw:=hj U T hU hT G forms hcut hmass a z haz
  let Z:=M.data.d^aDegree
  let d:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us jGrid) (T.splitIndex a z)+1/(n+1:ℕ))
  have hZ : 0 ≤ Z:=pow_nonneg M.data.hd.le _
  have hTemp : 0 ≤ M.data.T:=M.data.hepsilon.1.le.trans M.data.hepsilon.2.le
  have hd : 0 ≤ d:=by
    dsimp only [d,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
    (show 0 ≤ Z*d*M.data.d^2 by positivity)
  apply Hraw.trans
  convert Hmajor using 1 <;> dsimp only [base,Z,d] <;> ring

end OAI.SKFluctuations.Cavity
