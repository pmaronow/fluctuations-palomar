module

public import ComparisonActualGeneralSecondLowFreshCubicLedger
public import ComparisonActualHighWallSecondLowOccupiedCReplacementBudgetAlong
public import ComparisonActualHighWallSecondLowUnobservedPrice
public import ComparisonActualHighWallSecondLowWholeObservedAlong
public import ComparisonActualHighWallSecondLowOccupiedOldCBaselineCubicAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
theorem eventually_actual_high_wall_second_low_fresh_raw_cubic_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.data.wallRadius M.alpha (partitionPoint 0 as pre.length) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshFullB0Source (dim n) q U b h K T s
          (pre.length+mid.length) (G.canonicalHighWallSource M forms).restProduct| ≤
          C*M.data.d^3*sourceMonomialScale x W initial := by
  obtain ⟨Cu,hCu,HU⟩:=eventually_actual_high_wall_second_low_unobserved_class_cubic_price
    (D:=D) degree (rBound+1) Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Co,hCo,HO⟩:=eventually_actual_high_wall_second_low_whole_observed_saved_rate_along
    (D:=D) degree rBound Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_second_low_occupied_c_replacement_budget_along
    (D:=D) degree rBound Bclock Cmass Rmacro F Cx hCx heta hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cb,hCb,HB⟩:=eventually_actual_high_wall_second_low_occupied_old_c_baseline_cubic_price_along
    (D:=D) degree rBound Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let C:=8*Cu+Co+Cb+Cr+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [hdim.eventually HU,HO,HR,HB,hdim.eventually (eventually_ge_atTop (1:ℕ))]
    with n hnU hnO hnR hnB hn1
  intro M hwork L us hus hret hmesh
  filter_upwards [hnU M hwork L us hus hret hmesh,hnO M hwork L us hus hret hmesh,
    hnR M hwork L us hus hret hmesh,hnB M hwork L us hus hret hmesh] with k hkU hkO hkR hkB
  dsimp only at hkU hkO hkR hkB ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hpersistent hLeaves hcut hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighWallSource M forms).restProduct
  let g:=nativeFreshAtSlot T 0 s star
  let Pg:=fun old=>P (g.restRestrict old)
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let rate:=M.data.d^3*M.data.d^degree
  have hd:=M.data.hd
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have hxEq : x=M.data.d:=le_antisymm hxW (hwork ▸ hxsx)
  have Hscale : sourceMonomialScale x M.data.d initial=M.data.d^degree:=by
    rw [hxEq,sourceMonomialScale_self]
  have Hmass : ∀e,G.sourceLowMass e≤Cmass*M.data.d:=by
    intro e
    simpa only [hxEq,sourceFactorScale,ite_self] using hmass e
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    exact hparts ▸ finiteCutMasses_ordered us hus k
  have hPower : (dim n:ℝ)^(-eta)≤1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn1) (neg_nonpos.mpr heta.le)
  have HfullU : U≤(finiteCutMasses us k).length:=by simpa only [hparts] using hU
  rw [hparts] at hkU hkB
  let Gfresh:=G.retainOnMarked 0 g (nativeFreshAtSlot_mem T 0 s star)
  have HPfresh : (Gfresh.canonicalHighWallSource M forms).restProduct=Pg:=by
    funext old
    simpa only [ActualNaturalBoundaryShape.canonicalHighWallSource] using
      G.retained_canonical_physical_restProduct M.bf M.hf forms 0 g (nativeFreshAtSlot_mem T 0 s star) old
  have HmassFresh : ∀e,Gfresh.sourceLowMass e≤Cmass*M.data.d:=by
    intro e
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact Hmass e
  have HgLeaves : g.tree.leaves≤rBound+1:=
    (T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s star)).trans (by omega)
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hstar.le.trans hU)]
  have Huno : ∀j : Fin 8,|nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg
      (g.embed s) g.mark j false/2|≤Cu*rate:=by
    intro j
    have HH:=hkU U g.tree hU (by simpa only [hparts] using hcut) HgLeaves Gfresh forms HmassFresh
      (g.embed s) g.mark (Hsplit ▸ hstar) j
    rw [HPfresh] at HH
    simpa only [rate,q,b,h,K,as,mul_assoc] using HH
  have HradiusPos : 0<M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) U):=
    lt_of_lt_of_le (by positivity : 0<4*M.data.d) Hhigh
  have HWU : M.data.d≤M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) U):=by linarith
  have HstarHalf : M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) star)≤
      M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) U)/2:=by
    have HH:=Hrs.trans (min_le_left _ _)
    exact HH.trans (by linarith)
  have HzHalf : M.z≤M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) U)/2:=by
    have HH:=Hz.trans (min_le_left _ _)
    exact HH.trans (by linarith)
  have Hobs0:=hkO pre mid tail hparts.symm Hms T s U hU hmid hstar hLeaves hpersistent HWU HstarHalf HzHalf
    G forms initial x hxsx hxW hmass
  have HK : nativeContinuumMixedClock (dim n) M.bf M.hf (finiteCutMasses us k)=K:=by
    rw [hparts]
    rfl
  rw [HK] at Hobs0
  have Hobs : |(∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg
      (g.embed s) g.mark j true/2)-χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P|≤Co*rate:=by
    have HH : |(∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg
        (g.embed s) g.mark j true/2)-χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P|
        ≤Co*(dim n:ℝ)^(-eta)*rate:=by
      simpa only [hparts,nativeContinuumMixedClock,hwork,Hscale,rate,as,b,h,K,q,g,P,Pg,χ,star,mul_assoc,←pow_succ',Nat.reduceAdd] using Hobs0
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPower hCo.le) hrate using 1; ring
  have Hrep0:=hkR pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hpersistent hLeaves hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  have Hrep : |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|≤Cr*rate:=by
    have HH : |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|
        ≤Cr*(dim n:ℝ)^(-eta)*rate:=by
      simpa only [hparts,hwork,Hscale,rate,as,b,h,K,q,P,star,mul_assoc,←pow_succ'] using Hrep0
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPower hCr.le) hrate using 1; ring
  have Hbase : |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|≤Cb*rate:=by
    simpa only [q,b,h,K,as,P,rate,mul_assoc] using hkB pre.length star U T hU (by dsimp only [star];omega)
      hstar hLeaves hpersistent (by simpa only [hparts] using hcut) G forms Hmass s
  have Htotal:=actual_general_fresh_full_B0_abs_le_of_literal_budgets (dim n) T ho q U b h K s star hstar hU P
    Huno Hobs Hbase Hrep
  have HC:=mul_le_mul_of_nonneg_right (show 8*Cu+Co+Cb+Cr≤C by dsimp only [C];linarith) hrate
  have HCnum : 8*(Cu*rate)+Co*rate+Cb*rate+Cr*rate≤C*rate:=by
    simpa only [add_mul,mul_assoc] using HC
  simpa only [hparts,Hscale,rate,as,b,h,K,q,P,star,mul_assoc] using Htotal.trans HCnum

end OAI.SKFluctuations.Cavity
