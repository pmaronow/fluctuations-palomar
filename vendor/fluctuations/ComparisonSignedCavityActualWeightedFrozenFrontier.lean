module

public import ComparisonSignedCavityActualFrozenMeanResourceCorrection
public import ComparisonSignedCavityActualSquareWeightedGEnvelope

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def nativeActualInitialOriginalFrozenFrontier
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ)
    (branches : NativeActualWeightedBranches)
    (beta : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ) (depth : ℕ) : ℝ :=
  let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let weight:=fun st tag=>nativeActualParentRecursionWeight M W U st (beta st tag)
  ((nativeActualWeightedFrontier Γ hs (by omega) branches weight depth
    (nativeActualInitialState as i star 0 (by omega))).map
      (fun Q=>nativeActualResourceGInsertion M Q.term.freeze U Q.generation 0 q 0 W)).sum

def ActualOriginalWeightedFrozenFrontierSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Cbeta : ℝ) (branches : NativeActualWeightedBranches) (depth : ℕ) (Cmass : ℝ)
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
      |nativeActualInitialOriginalFrozenFrontier (M n) as (W n) i star U hi hs hU Γ branches beta depth|≤
        ((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2

theorem actual_original_weighted_frozen_frontier_saving_of_pair_budget
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin gamma A : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hTemp : 0 < Temp) (hgamma : 0 < gamma)
    (Cbeta : ℝ) (hCbeta : 0≤Cbeta)
    (branches : NativeActualWeightedBranches) (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (depth : ℕ) (hA : 1≤A) (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n))
    (Hpair : ActualSquareResourcePairBudgetOnEveryFinalNet (1+depth*increment) A gamma Cmass M W w) :
    ActualOriginalWeightedFrozenFrontierSaving Cbeta branches depth Cmass M W w := by
  obtain ⟨Cweight,hCweight,Hweight⟩:=eventually_actual_parent_recursion_weight_bound
    hcl hcu hAz hTemp Cbeta hCbeta M W hxs hWlim hb hh Cs w Hw
  let V:=nativeActualWeightedFrontierCost branches Cweight L 2 depth
  let Cenv:=V*A^(1+depth*increment)
  have HA : 0<A:=zero_lt_one.trans_le hA
  have HV : 0≤V:=nativeActualWeightedFrontierCost_nonneg branches hCweight L 2 depth
  have hCenv : 0≤Cenv:=by dsimp only [Cenv];positivity
  have Hrate:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=(1:ℝ)/3) (s:=(1:ℝ)/6) (by norm_num) 0 Cenv)
  have Hmean:=eventually_actual_frozen_resource_correction (delta:=delta) (cu:=cu) (Ct:=Ct) (D:=D)
    (2+2*depth*L) Bclock Temp hTemp.le
    hm hcl hAz hC0
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hpair,Hweight,Hmean,HW,Hrate] with n hn hnweight hnmean hnW hnrate
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh,hnweight us hus hstar,hnmean (M n) (hb n) (hh n) us hus]
    with j hj hjweight hjmean
  dsimp only at hj hjweight hjmean ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  have hlen : as.length=(finiteCutMasses us j).length:=rfl
  intro U i hi hs hU x hxsx hxW hmass Γ hΓ beta hbeta
  change i ≤ star at hi
  change star<U at hs
  change U≤as.length at hU
  have hx : 0<x:=(M n).hxs.trans_le hxsx
  have hW : 0<W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0<((n+1:ℕ):ℝ)^(-gamma):=by positivity
  have hN : (1:ℝ)≤((n+1:ℕ):ℝ):=by exact_mod_cast (show 1≤n+1 by omega)
  have heps1 : ((n+1:ℕ):ℝ)^(-gamma)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  let weight:=fun st tag=>nativeActualParentRecursionWeight (M n) (W n) U st (beta st tag)
  have hw st z (hz : z∈branches) : |weight st z.1|≤Cweight:=hjweight i U hs hU st _ (hbeta st z hz)
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (by omega : i≤as.length)
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term :=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i≤as.length;omega))
  have HB : 0≤A^(1+depth*increment)*x*(((n+1:ℕ):ℝ)^(-gamma))^(depth*increment)*
      (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2) := by positivity
  have HH:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs (by omega) branches weight
    hCweight hw L hL depth st (nativeActualInitialState_leaves_le as i star 0 (by omega))
    (fun Q=>nativeActualResourceGInsertion (M n) Q.term.freeze U Q.generation 0
      (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 (W n)) HB (by
      intro Q hQ
      have HG:=nativeActualWeightedFrontier_valid Γ hs (by omega) branches weight depth st hst Q hQ
      have HD:=nativeActualWeightedFrontier_generation Γ hs (by omega) branches weight increment hinc depth st Q hQ
      change Q.generation=0+depth*increment at HD
      simp only [zero_add] at HD
      have HL:=nativeActualWeightedFrontier_leaves_le Γ hs (by omega) branches weight L hL depth st Q
        (nativeActualInitialState_leaves_le as i star 0 (by omega)) hQ
      have HP:=hj U i Q.generation Q.tree Q.term HG (by omega) (by omega) x hxsx hxW hmass
        1 1 (by constructor <;> norm_num) (by constructor <;> norm_num)
      have H:=hjmean i star U Q.generation [.initial] Q.tree Q.term HG HL A x (W n)
        (((n+1:ℕ):ℝ)^(-gamma)) HA hx hW heps hi (by omega) HP
      rw [HD] at H
      simpa only [List.length_singleton,nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,
        List.prod_nil,NativeResourceMark.savedScale,mul_one,mul_assoc,HD,b,h,as] using H)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul] at HH
  change |nativeActualInitialOriginalFrozenFrontier (M n) as (W n) i star U hi hs hU Γ branches beta depth|≤_ at HH
  apply HH.trans
  have hpow : (((n+1:ℕ):ℝ)^(-gamma))^(depth*increment)≤1:=pow_le_one₀ heps.le heps1
  have hxe : x*(((n+1:ℕ):ℝ)^(-gamma))^(depth*increment)≤1 :=
    (mul_le_mul (hxW.trans hnW) hpow (pow_nonneg heps.le _) (by norm_num)).trans_eq (by ring)
  have Habsorb : Cenv*((n+1:ℕ):ℝ)^(-(1:ℝ)/3)≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6) := by
    simpa only [pow_zero,mul_one,neg_div] using hnrate
  calc
    _=(Cenv*(((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2))*
      (x*(((n+1:ℕ):ℝ)^(-gamma))^(depth*increment)) := by dsimp only [Cenv,V];ring
    _≤Cenv*(((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2) :=
      (mul_le_mul_of_nonneg_left hxe (by positivity)).trans_eq (by ring)
    _≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2 := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right Habsorb (sq_nonneg (M n).xs)

end OAI.SKFluctuations.LaplaceWindowFormalization
