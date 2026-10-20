module

public import ComparisonActualGeneralSecondLowFreshCubicLedger
public import ComparisonActualHighWallSecondLowOccupiedCReplacementBudgetAlong
public import ComparisonActualHighWallSecondLowUnobservedInitialPrice
public import ComparisonActualHighWallSecondLowWholeObservedAlong
public import ComparisonActualHighWallSecondLowOldCInitialBaselineAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
theorem eventually_actual_high_wall_second_low_fresh_raw_initial_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB : ℝ,0 < C ∧ 0 < CiU ∧ 0 < CiB ∧ ∀ᶠn : ℕ in atTop,
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
          (G : ActualNaturalBoundaryShape (dim n) (degree+1) T)
          (forms : Fin (degree+1)→NativeSourceFactorForm) (initial : Finset (Fin (degree+1)))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          ∀(e0 : Fin (degree+1)) (initialCut : ℕ),forms e0=.centered →
            T.splitIndex (G.i e0) (G.j e0)=initialCut →
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
          C*M.data.d^3*sourceMonomialScale x W initial*(
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (CiU*M.data.d) 8+
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (CiB*M.data.d) 8+
            (dim n:ℝ)^(-eta)) := by
  obtain ⟨Cu,CiU,hCu,hCiU,HU⟩:=eventually_actual_high_wall_second_low_unobserved_class_initial_modulus_price
    (D:=D) degree (rBound+1) Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Co,hCo,HO⟩:=eventually_actual_high_wall_second_low_whole_observed_saved_rate_along
    (D:=D) (degree+1) rBound Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_second_low_occupied_c_replacement_budget_along
    (D:=D) (degree+1) rBound Bclock Cmass Rmacro F Cx hCx heta hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cb,CiB,hCb,hCiB,HB⟩:=eventually_actual_high_wall_second_low_occupied_old_c_baseline_initial_modulus_price_along
    (D:=D) degree rBound Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let C:=8*Cu*CiU+Co+Cb*CiB+Cr+1
  refine ⟨C,CiU,CiB,by dsimp only [C];positivity,hCiU,hCiB,?_⟩
  filter_upwards [hdim.eventually HU,HO,HR,HB]
    with n hnU hnO hnR hnB
  intro M hwork L us hus hret hmesh
  filter_upwards [hnU M hwork L us hus hret hmesh,hnO M hwork L us hus hret hmesh,
    hnR M hwork L us hus hret hmesh,hnB M hwork L us hus hret hmesh] with k hkU hkO hkR hkB
  dsimp only at hkU hkO hkR hkB ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hpersistent hLeaves hcut hxsx hxW hmacroW hLOW hmass e0 initialCut hform hinit Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
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
  let rate:=M.data.d^3*M.data.d^(degree+1)
  let etaU:=originalInitialLowMomentModulus
    (originalHighWallInitialPairErrorScale M as initialCut) (CiU*M.data.d) 8
  let etaB:=originalInitialLowMomentModulus
    (originalHighWallInitialPairErrorScale M as initialCut) (CiB*M.data.d) 8
  have he:=original_high_wall_initial_pair_error_scale_nonneg M as initialCut
  have hEtaU : 0 ≤ etaU:=original_initial_low_moment_modulus_nonneg he
    (mul_nonneg hCiU.le M.data.hd.le) 8
  have hEtaB : 0 ≤ etaB:=original_initial_low_moment_modulus_nonneg he
    (mul_nonneg hCiB.le M.data.hd.le) 8
  have hRateN : 0 ≤ (dim n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd:=M.data.hd
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have hxEq : x=M.data.d:=le_antisymm hxW (hwork ▸ hxsx)
  have Hscale : sourceMonomialScale x M.data.d initial=M.data.d^(degree+1):=by
    rw [hxEq,sourceMonomialScale_self]
  have Hmass : ∀e,G.sourceLowMass e≤Cmass*M.data.d:=by
    intro e
    simpa only [hxEq,sourceFactorScale,ite_self] using hmass e
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    exact hparts ▸ finiteCutMasses_ordered us hus k
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
      (g.embed s) g.mark j false/2|≤Cu*rate*CiU*etaU:=by
    intro j
    have HinitFresh : g.tree.splitIndex (Gfresh.i e0) (Gfresh.j e0)=initialCut:=by
      dsimp only [Gfresh,ActualNaturalBoundaryShape.retainOnMarked]
      rw [(T.markedAttach_embed_preserves 0 g (nativeFreshAtSlot_mem T 0 s star)).2]
      exact hinit
    have HH:=hkU U g.tree hU (by simpa only [hparts] using hcut) HgLeaves Gfresh forms HmassFresh
      e0 initialCut hform HinitFresh (g.embed s) g.mark (Hsplit ▸ hstar) j
    rw [HPfresh] at HH
    convert HH using 1 <;> dsimp only [rate,etaU,q,b,h,K,as] <;> ring
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
      (g.embed s) g.mark j true/2)-χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P|≤Co*(dim n:ℝ)^(-eta)*rate:=by
    simpa only [hparts,nativeContinuumMixedClock,hwork,Hscale,rate,as,b,h,K,q,g,P,Pg,χ,star,mul_assoc,←pow_succ',Nat.reduceAdd] using Hobs0
  have Hrep0:=hkR pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hpersistent hLeaves hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  have Hrep : |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|≤Cr*(dim n:ℝ)^(-eta)*rate:=by
    simpa only [hparts,hwork,Hscale,rate,as,b,h,K,q,P,star,mul_assoc,←pow_succ'] using Hrep0
  have Hbase : |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|≤Cb*rate*CiB*etaB:=by
    convert (hkB pre.length star U T hU (by dsimp only [star];omega)
      hstar hLeaves hpersistent (by simpa only [hparts] using hcut) G forms Hmass
      e0 initialCut hform hinit s) using 1 <;> dsimp only [q,b,h,K,as,P,rate,etaB] <;> ring
  have Htotal:=actual_general_fresh_full_B0_abs_le_of_literal_budgets (dim n) T ho q U b h K s star hstar hU P
    Huno Hobs Hbase Hrep
  have hC1 : 8*Cu*CiU≤C:=by dsimp only [C];nlinarith [mul_pos hCb hCiB, mul_pos hCo hCiU, mul_pos hCr hCiB]
  have hC2 : Cb*CiB≤C:=by dsimp only [C];nlinarith [mul_pos hCu hCiU]
  have hC3 : Co+Cr≤C:=by dsimp only [C];nlinarith [mul_pos hCu hCiU,mul_pos hCb hCiB]
  have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hrate) hEtaU
  have H2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hrate) hEtaB
  have H3:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hrate) hRateN
  have HtotalBound : 8*(Cu*rate*CiU*etaU)+Co*(dim n:ℝ)^(-eta)*rate+
      Cb*rate*CiB*etaB+Cr*(dim n:ℝ)^(-eta)*rate≤C*rate*(etaU+etaB+(dim n:ℝ)^(-eta)):=by
    linarith only [H1,H2,H3]
  simpa only [hparts,Hscale,rate,etaU,etaB,mul_assoc] using Htotal.trans HtotalBound

end OAI.SKFluctuations.Cavity
