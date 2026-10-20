module

public import ComparisonActualHighWallBondedTwoHighLowBudget
public import ComparisonActualGeneralCMarkedCanonicalSource
public import ComparisonSignedCavitySignedLowRestorationBudget
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_C_two_high_profile_budget
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (pexp : ℝ) (hpExp : 2 < pexp) (hOrder : pexp/(pexp-2) ≤ (dOrder:ℝ))
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm), partitionPoint 0 as U ≤ Cmass*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d)→
        ∀a z : T.Slot,T.splitIndex a z < U→
          let R:=M.data.highErrorEnvelope M.alpha as U
          let f:=fun j=>(R j)^(4/pexp)
          |nativeCenteredLowGammaHighSecondRemainder n q U b h K S T
            (G.canonicalHighWallSource M forms).restProduct a z| ≤
            pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
              (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
                (M.data.d*M.data.d^aDegree))*(2*M.data.T)^((pexp-2)/pexp)*(2*M.data.T)^((pexp-2)/pexp)*
              pairForkVariation rBound*(T.forkCost f+edgeBudget 0 as f) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_high_wall_canonical_two_high_low_factor
    (D:=D) aDegree dOrder (rBound+2) hd pexp hpExp hOrder Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*max Bclock 0
  let R:=M.data.highErrorEnvelope M.alpha as U
  let f:=fun j=>(R j)^(4/pexp)
  let Phi:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
      (M.data.d*M.data.d^aDegree))*(2*M.data.T)^((pexp-2)/pexp)*(2*M.data.T)^((pexp-2)/pexp)
  let P:=(G.canonicalHighWallSource M forms).restProduct
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark*
      (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K r.tree
        (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW:=M.data.hd.le
  have hscale : 0 ≤ M.data.d^aDegree:=pow_nonneg M.data.hd.le _
  have hTemp:=M.data.hTpos.le
  have hPhi : 0 ≤ Phi := by
    dsimp only [Phi]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hR j : 0 ≤ R j := by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (2*M.data.T) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have HF (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      |F p r| ≤ 2*Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
    let Pi:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
    have hProfile : 0 ≤ r.tree.forkCost f+edgeBudget 0 as f:=
      add_nonneg (r.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
    by_cases hPi : Pi=0
    · change |Pi*_| ≤ _
      rw [hPi,zero_mul,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hPhi) hProfile
    · have hold : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
      have hsplit : r.tree.splitIndex (r.embed p.mark) r.mark=T.splitIndex a z := by
        have H:=native_low_scalar_pairing_split_weight r.tree ho U K
          (fun j=>if j=T.splitIndex a z then (1:ℝ) else 0)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [hold])
        rw [hold,ite_eq_left rfl,one_mul] at H
        by_contra hne
        rw [ite_eq_right hne,zero_mul] at H
        exact hPi H.symm
      have hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U:=by rwa [hsplit]
      have hcd : r.embed p.mark≠r.mark := by
        intro H
        rw [H,r.tree.splitIndex_self] at hlow
        omega
      have hleaf : r.tree.leaves ≤ rBound+2 := by
        have H1:=T.markedAttach_leaves 0 p hp
        have H2:=p.tree.markedAttach_leaves 0 r hr
        omega
      let Gr:=(G.nativeCMarkedLift p hp).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e ≤ Cmass*M.data.d := by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hnew : partitionPoint 0 as (r.tree.splitIndex (r.embed p.mark) r.mark) ≤ Cmass*M.data.d :=
        (partitionPoint_mono as ho hlow.le).trans hcut
      have Htest:=G.physicalC_inserted_canonical_low_test M.bf M.hf forms U b S p hp r hr hlow
      have Hjet t (ht : t∈Icc (0:ℝ) 1) :
          |cutFrozenLowHighJet n q U b h K r.tree
            (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t|≤
          Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
        have Hraw:=hgrid U r.tree t ht hleaf Gr forms hGr (r.embed p.mark) r.mark hcd hnew
        have Hprof:=M.data.current_high_profile_le_original M.alpha r.tree ho U (l:=0) (t:=t) (by norm_num) ht (exponent:=4/pexp)
            (div_nonneg (by norm_num) (by linarith))
        have HH:=mul_le_mul_of_nonneg_left Hprof hPhi
        rw [Htest]
        exact Hraw.trans HH
      have HI:=weighted_unit_integral_abs_le (mul_nonneg hPhi hProfile) Hjet 1
      have HPi:=native_low_scalar_pairing_abs_le_two r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
      change |Pi*_|≤_
      rw [abs_mul]
      have HH:=mul_le_mul HPi (by simpa only [pow_one] using HI) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      nlinarith only [HH]
  have HT:=T.signedPair_abs_le_pairAbsSum F
  have HM:=(HT.trans (T.pairAbsSum_mono HF))
  rw [T.pairAbsSum_const_mul (2*Phi)] at HM
  have HB:=T.pairAbsSum_forkBudget_le ho hT hf (d:=0) (by norm_num)
  simp only [add_zero] at HB
  have HX:=HM.trans (mul_le_mul_of_nonneg_left HB (mul_nonneg (by norm_num : (0:ℝ)≤2) hPhi))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  dsimp only [nativeCenteredLowGammaHighSecondRemainder,F,P,Phi,R,f,q,b,h,K,S,Mclock] at HX ⊢
  nlinarith only [HX]

end OAI.SKFluctuations.Cavity
