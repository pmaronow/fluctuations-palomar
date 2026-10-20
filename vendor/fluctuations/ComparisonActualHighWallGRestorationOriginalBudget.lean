module

public import ComparisonActualHighWallGWordRestorationCanonical
public import ComparisonActualGeneralGRestorationDiagonal

public import ComparisonSignedCavityGRestorationOriginalBudget
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_G_word_restoration_original_budget
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
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
        let Mclock:=2*M.data.T
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),
          |nativeActualLawRestorationRemainder n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a)| ≤
            nativeOriginalGWordRestorationCost g U (rBound+3) M.bf M.hf K a Mclock M.data.T p
              (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Ch^aDegree*
                M.data.d^aDegree)
              (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Cl^aDegree*
                M.data.d^aDegree) (Cq*M.data.d) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_high_wall_canonical_G_word_high_restoration
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,hCl,Cq,hCq,HL⟩:=eventually_actual_high_wall_canonical_G_word_low_restoration
    (D:=D) aDegree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hwork L us hus hret hmesh
  filter_upwards [hnH M hwork L us hus hret hmesh,
    hnL M hwork L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms hcut hmass g a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*M.data.T
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock M.data.T
  let j:=g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark|
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Ch^aDegree*
    M.data.d^aDegree
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Cl^aDegree*
    M.data.d^aDegree
  let BH:=κ*(ClockTree.pairForkVariation (rBound+3)*CH*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
    (R j)^(2/p)*(g.tree.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation (rBound+3) 1*CL*R j*(Cq*M.data.d))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hdiag : g.z.embed g.r.mark=g.z.mark
  · rw [nativeOriginalGWordRestorationCost,ite_eq_left hdiag,
      actual_general_G_word_diagonal_restoration_zero M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) T ho g U _ a hdiag,abs_zero]
  · have hscale : 0 ≤ M.data.d^aDegree:=pow_nonneg M.data.hd.le _
    have hCH : 0 ≤ CH:=by dsimp [CH];positivity
    have hCL : 0 ≤ CL:=by dsimp [CL];positivity
    have hκ : 0 ≤ κ:=abs_nonneg _
    have hW : 0 ≤ M.data.d := M.data.hd.le
    have hTemp := M.data.hTpos.le
    have hPV := ClockTree.pairForkVariation_nonneg (rBound+3)
    have hAV := ClockTree.absJetVariation_nonneg (rBound+3) 1
    have hR (j : ℕ) : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock M.data.hTpos.le)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        |cutMixedJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a) 0 0 0 t| ≤ BH:=by
      have H:=hgridH U T t hU ht hT G forms hmass g a hdiag
      apply H.trans
      have HR:=M.data.current_high_error_radius_le_original (l:=0) (t:=t) M.alpha ho U
        (by norm_num) ht j (g.tree.splitIndex_le_clockLength _ _)
      change nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 t b h K)
        (cutTSlope n U 0 b h K) j ≤ R j at HR
      have HC:=M.data.current_high_profile_le_original (l:=0) (t:=t) M.alpha g.tree ho U
        (by norm_num) ht (show 0 ≤ 2/p by positivity)
      have hProf := native_whole_law_profile_cost_nonneg n ho
        (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)
      have hRj := hR j
      change nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K)
        (cutTSlope n U 0 b h K) g.tree (2/p) ≤
        g.tree.forkCost (fun j=>(R j)^(2/p))+edgeBudget 0 as (fun j=>(R j)^(2/p)) at HC
      dsimp only [BH,CH,κ]
      (gcongr; first | exact HR | exact HC | positivity | exact nativeWholeLawErrorRadius_nonneg _ _ _ _ _)
    have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
        |cutLowJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a) 0 1 l 1| ≤ BL:=by
      have H:=hgridL U T l hU hl hT G forms hcut hmass g a hdiag
      apply H.trans
      have HR:=M.data.current_high_error_radius_le_original (l:=l) (t:=1) M.alpha ho U
        hl (by norm_num) j (g.tree.splitIndex_le_clockLength _ _)
      change nativeWholeLawErrorRadius n as (cutFullVariance n q U l 1 b h K)
        (cutTSlope n U 0 b h K) j ≤ R j at HR
      dsimp only [BL,CL,κ]
      gcongr
    have H:=native_actual_law_restoration_abs_le n q U b h K g.tree
      (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a) BH BL hH hL
    rw [nativeOriginalGWordRestorationCost,ite_eq_right hdiag]
    convert H using 1
    dsimp only [BH,BL,κ,CH,CL,R,j,Mclock,K,b,h,S,as]
    ring_nf

end OAI.SKFluctuations.Cavity
