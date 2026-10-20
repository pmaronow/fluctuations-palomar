module

public import ComparisonSignedCavityActualSquareWeightedGEnvelope
public import ComparisonSignedCavityActualMixedTerminalDepth

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualSquareInitialWeightedGFrontierDecay
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Cbeta : ℝ) (branches : NativeActualWeightedBranches) (depth : ℕ) (saving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→((Lnet+1:ℕ):ℝ)⁻¹≤(M n).xs→
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U i : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U≤as.length),
    ∀x : ℝ,(M n).xs≤x→x≤W n→partitionPoint 0 as i≤Cmass*x→
    ∀(Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ),
      (∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)→
    ∀beta : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ,
      (∀st b,b∈branches→|beta st b.1|≤Cbeta)→
    ∀a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
      |nativeActualInitialSquareWeightedGFrontier (M n) as (W n) i star U hi hs hU
        Γ branches beta depth a t|≤((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2

theorem actual_square_weighted_g_frontier_decay_of_pair_producers
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin gamma : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hTemp : 0 < Temp) (hgamma : 0 < gamma) (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n))
    (Hpair : ∀degree : ℕ,0 < degree→∃A : ℝ,1≤A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNet degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀Cbeta : ℝ,0≤Cbeta→∀branches : NativeActualWeightedBranches,
      ∀L : ℕ,(∀b∈branches,b.2.length≤L)→
      ∀increment : ℕ,0 < increment→
        (∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)→
      ∀depth : ℕ,threshold≤depth→
        ActualSquareInitialWeightedGFrontierDecay Cbeta branches depth saving Cmass M W w := by
  obtain ⟨threshold,hth,saving,hs,Hrate⟩:=exists_actual_mixed_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  refine ⟨threshold,hth,saving,hs,?_⟩
  intro Cbeta hCbeta branches L hL increment hinc hmark depth hdepth
  obtain ⟨A,hA,HA⟩:=Hpair (1+depth*increment) (by omega)
  obtain ⟨Cenv,hCenv,Henv⟩:=actual_square_weighted_g_envelope_of_pair_budget
    hcl hcu hAz hTemp Cbeta hCbeta branches L hL increment hmark depth hA Cmass
    M W hxs hWlim hb hh Cs w Hw HA
  let ops:=List.replicate (depth*increment) NativeActualExpansionOp.highRow
  have hcount : nativeActualExpansionMarkedCount ops=depth*increment := by
    simp [ops,nativeActualExpansionMarkedCount,NativeActualExpansionOp.markedIncrement]
  have hthcount : threshold≤nativeActualExpansionMarkedCount ops := by
    rw [hcount]
    exact hdepth.trans (Nat.le_mul_of_pos_right depth hinc)
  filter_upwards [Henv,Hrate Cenv hCenv] with n hn hnrate
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh] with j hj
  dsimp only at hj ⊢
  intro U i hi hstarU hU x hxsx hxW hmass Γ hΓ beta hbeta a t ha ht
  have HG:=hj U i hi hstarU hU x hxsx hxW hmass Γ hΓ beta hbeta a t ha ht
  have HR:=hnrate (M n) ops hthcount
  rw [hcount] at HR
  exact HG.trans HR

theorem exists_actual_bare_sharp_square_weighted_g_frontier_decay
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hTemp : 0 < Temp) (hL : 0 < Lwin) (hCcal : 1≤Ccal)
    (Cmass : ℝ) (hCm : 0≤Cmass)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n)) ∧
      ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
        ∀Cbeta : ℝ,0≤Cbeta→∀branches : NativeActualWeightedBranches,
        ∀L : ℕ,(∀b∈branches,b.2.length≤L)→
        ∀increment : ℕ,0 < increment→
          (∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)→
        ∀depth : ℕ,threshold≤depth→
          ActualSquareInitialWeightedGFrontierDecay Cbeta branches depth saving Cmass M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,_,Hp⟩:=exists_actual_bare_sharp_square_resource_pair_budget_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal Cmass hCm
    M W hcanonical hWlim hcompare hb hh
  refine ⟨Cs,hCs,w,hw,?_⟩
  exact actual_square_weighted_g_frontier_decay_of_pair_producers
    hm hcl hcu hAz hC0 hTemp hs Cmass M W
    (fun n=>by rw [hcanonical];exact le_max_left _ _) hWlim hb hh Cs w
    (hw.mono (fun _ hn=>hn.1)) Hp

end OAI.SKFluctuations.LaplaceWindowFormalization
