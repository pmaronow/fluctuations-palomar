module

public import ComparisonSignedCavityActualWeightedGTerminal
public import ComparisonSignedCavityActualParentRecursionWeight
public import ComparisonSignedCavityActualSharpSquarePairProducer

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def nativeActualInitialSquareWeightedGFrontier
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ)
    (branches : NativeActualWeightedBranches)
    (beta : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    (depth : ℕ) (a t : ℝ) : ℝ :=
  let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h a t
  let weight:=fun st tag=>nativeActualParentRecursionWeight M W U st (beta st tag)
  ((nativeActualWeightedFrontier Γ hs (by omega) branches weight depth
    (nativeActualInitialState as i star 0 (by omega))).map
      (nativeActualGResourceResponse M U 0 q 0 W)).sum

theorem actual_square_weighted_g_envelope_of_pair_budget
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin saving A : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hTemp : 0 < Temp)
    (Cbeta : ℝ) (hCbeta : 0≤Cbeta)
    (branches : NativeActualWeightedBranches) (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (depth : ℕ) (hA : 1≤A) (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n))
    (Hpair : ActualSquareResourcePairBudgetOnEveryFinalNet (1+depth*increment) A saving Cmass M W w) :
    ∃Cenv : ℝ,0≤Cenv ∧ ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
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
          Γ branches beta depth a t|≤Cenv*(((n+1:ℕ):ℝ)^(-saving))^(depth*increment) := by
  obtain ⟨Cweight,hCweight,Hweight⟩:=eventually_actual_parent_recursion_weight_bound
    hcl hcu hAz hTemp Cbeta hCbeta M W hxs hWlim hb hh Cs w Hw
  let Cenv:=nativeActualWeightedFrontierCost branches Cweight L 2 depth*A^(1+depth*increment)*
    (2*Temp)*nativeActualGInsertionCost (2+2*depth*L)
  have HA : 0<A:=zero_lt_one.trans_le hA
  have HV:=nativeActualWeightedFrontierCost_nonneg branches hCweight L 2 depth
  have HG:=nativeActualGInsertionCost_nonneg (2+2*depth*L)
  have hCenv : 0≤Cenv:=by dsimp only [Cenv];positivity
  refine ⟨Cenv,hCenv,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hpair,Hweight,HW] with n hn hnweight hnW
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh,hnweight us hus hstar] with j hj hjweight
  dsimp only at hj hjweight ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  have hlen : as.length=(finiteCutMasses us j).length:=rfl
  intro U i hi hs hU x hxsx hxW hmass Γ hΓ beta hbeta a t ha ht
  change i ≤ star at hi
  change star<U at hs
  change U≤as.length at hU
  have hx : 0<x:=(M n).hxs.trans_le hxsx
  have hW : 0<W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0<((n+1:ℕ):ℝ)^(-saving):=by positivity
  let weight:=fun st tag=>nativeActualParentRecursionWeight (M n) (W n) U st (beta st tag)
  have hw st b (hb : b∈branches) : |weight st b.1|≤Cweight :=
    hjweight i U hs hU st _ (hbeta st b hb)
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (by omega : i≤as.length)
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term :=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i≤as.length;omega))
  have HP Q (hQ : Q∈nativeActualWeightedFrontier Γ hs (by omega) branches weight depth st) :=
    hj U i Q.generation Q.tree Q.term
      (nativeActualWeightedFrontier_valid Γ hs (by omega) branches weight depth st hst Q hQ)
      (by
        have H:=nativeActualWeightedFrontier_generation Γ hs (by omega) branches weight increment hinc depth st Q hQ
        change Q.generation=0+depth*increment at H
        omega)
      (by omega) x hxsx hxW hmass a t ha ht
  have HH:=nativeActualWeightedFrontier_g_insertion_abs_le (M n) hcl hAz hTemp.le (hb n) (hh n)
    ho Γ hΓ hi hs hU branches weight hCweight hw L hL increment hinc depth st rfl hst
    2 (nativeActualInitialState_leaves_le as i star 0 (by omega))
    0 (finitePhysicalCavitySquareVariance n U as b h a t) 0
    A x (W n) (((n+1:ℕ):ℝ)^(-saving)) HA hx hW heps HP
  dsimp only at HH
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    List.length_singleton,nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,NativeResourceMark.savedScale,mul_one] at HH
  change |nativeActualInitialSquareWeightedGFrontier (M n) as (W n) i star U hi hs hU
    Γ branches beta depth a t|≤_ at HH
  apply HH.trans
  have Hx : x≤1:=hxW.trans hnW
  have Hmul:=mul_le_mul_of_nonneg_left Hx
    (show 0≤Cenv*(((n+1:ℕ):ℝ)^(-saving))^(depth*increment) by positivity)
  dsimp only [Cenv] at Hmul ⊢
  nlinarith only [Hmul]

end OAI.SKFluctuations.LaplaceWindowFormalization
