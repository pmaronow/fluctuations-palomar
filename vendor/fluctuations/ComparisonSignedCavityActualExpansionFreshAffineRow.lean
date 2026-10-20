module

public import ComparisonSignedCavityActualFreshAffineRowRate
public import ComparisonSignedCavityActualExpansionSourceLaws

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_expansion_signed_fresh_affine_high_row_saved_cubic
    (a : ℕ) (Bclock Temp Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(U : ℕ) (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
          (hlen : U≤(pre++(mid++tail)).length) (seedWeight : ℝ)
          (Γrow : (st : NativeHighSwitchState (Spin n×Bool) (pre++(mid++tail))) → MarkedPlacement st.tree → ℝ)
          (ops : List NativeActualExpansionOp)
          (Q : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
          Q∈nativeActualResourceExpansion Γrow hU (by omega) ops
            (nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) seedWeight (by omega)) →
        ∀(b fslot : Q.tree.Slot) (useNew : Bool),
          (Q.term.live.test.target,b)∈Q.term.live.test.edges →
          (Q.term.live.test.target,fslot)∈Q.term.live.test.edges →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a Q.tree) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)),
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
          |nativeCanonicalObservedFreshAffineHighRow n a M Q.tree (pre.length+mid.length) U Q.term.live.test.target b fslot useNew
            G forms q (retainedStarMixedClock n M.bf M.hf as)|≤
            (2*(Q.tree.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale M.xs W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_signed_fresh_affine_high_row_saved_cubic
    a Bclock Temp Cmass Ccal hTemp hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,C,hCp,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass U hmid hU hlen seedWeight Γrow ops Q hQ b fslot useNew hbEdge hfEdge
    hWU hstar hz G forms initial hmassG
  have hP:=nativeActualInitialExpansion_valid _ _ _ U (by omega) hU hlen seedWeight Γrow ops Q hQ
  have hT:=hP.persistentLowForks (by omega)
  have hcb:=Q.term.live.ancestry.edges_low _ hbEdge
  have hcf : Q.tree.splitIndex Q.term.live.test.target fslot≤pre.length+mid.length := by
    have H:=Q.term.live.ancestry.edges_low _ hfEdge
    simp only [Prod.fst,Prod.snd] at H
    omega
  exact hk pre mid tail hcut hmass Q.tree Q.term.live.test.target b fslot useNew U hmid hU hT hcb hcf
    hWU hstar hz G forms initial hmassG

end OAI.SKFluctuations.Cavity
