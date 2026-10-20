module

public import ComparisonSignedCavitySecondLowInheritedOccupiedCReplacementBudgetAlong
public import SKProof.Port.ComparisonActualOriginalQClassifiedFarCanonicalTransport
public import SKProof.Port.ComparisonActualOriginalQLowUnpairedResamplingSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedOriginalCReplacementSavingAlong
public import ComparisonSignedCavitySecondLowActualClassifiedOldCanonicalAnchors
public import ComparisonSignedCavitySecondLowOccupiedOldCBaselineSource
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem replacement_outer_weight_abs_le_original_q {α : Type} (L : List α) (w F : α→ℝ)
    {B : ℝ} (H : ∀x∈L,|F x|≤B) :
    |(L.map (fun x=>w x*F x)).sum|≤(L.map (fun x=>|w x|)).sum*B := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (H x List.mem_cons_self) (abs_nonneg _))
      (ih (fun y hy=>H y (List.mem_cons_of_mem _ hy))))

private theorem replacement_outer_filtered_nonneg_sum_le_original_q {α : Type} (L : List α) (P : α→Bool)
    (F : α→ℝ) (H : ∀x∈L,0≤F x) :
    ((L.filter P).map F).sum≤(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    have HH:=ih (fun y hy=>H y (List.mem_cons_of_mem x hy))
    cases HP : P x with
    | true=>simpa only [List.filter_cons,HP,ite_true,List.map_cons,List.sum_cons]
        using add_le_add (le_refl (F x)) HH
    | false=>
      simp only [List.filter_cons,HP,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons]
      exact HH.trans (le_add_of_nonneg_left (H x List.mem_cons_self))

private theorem replacement_outer_HIGH_variation_original_q {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (a : T.Slot) (U rBound : ℕ) (hT : T.leaves≤rBound) :
    ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>|p.coeff|)).sum≤2*(rBound:ℝ) := by
  rw [nativeHighMarkedRows_eq_filter]
  apply (replacement_outer_filtered_nonneg_sum_le_original_q (T.markedAttach 0)
    (fun p=>decide (U-1<p.tree.splitIndex (p.embed a) p.mark)) _ (fun p _=>abs_nonneg p.coeff)).trans
  rw [T.markedAttach_variation ho,sub_zero]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)

theorem eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along_original_q
    (a rBound : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.sweepBf M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (s : T.Slot) (U : ℕ) (hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.sweepRadius (partitionPoint 0 as U) →
          M.z ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.sweepRadius (G.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.sweepRadius (partitionPoint 0 as pre.length) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
          (pre.length+mid.length) hU (G.canonicalOriginalQSource M forms).restProduct| ≤
          C*(dim n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  classical
  obtain ⟨Cpoint,hCpoint,H⟩:=eventually_actual_minimum_inherited_second_low_original_c_replacement_saving_along_original_q
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  let Poly:ℝ:=2*(rBound+1)^2*(rBound+2)^2
  let C:=1+Poly*Cpoint
  have hPoly:0 ≤ Poly:=by dsimp [Poly];positivity
  have hC:0 < C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hT hLeaves hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.sweepBf M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let g:=nativeFreshAtSlot T 0 s star
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  let p0:=sourceMonomialScale x W initial
  let rate:=(dim n:ℝ)^(-eta)*W*M.xs^2*p0
  let B:=Cpoint*(rBound+2:ℕ)^2*rate
  have ho:MassOrdered 0 as:=by
    dsimp only [as]
    exact hparts ▸ finiteCutMasses_ordered us hus k
  have hW:0 < W:=M.hxs.trans_le (hxsx.trans hxW)
  have hp0:0 ≤ p0:=by
    have hx:0 < x:=M.hxs.trans_le hxsx
    dsimp [p0]
    unfold sourceMonomialScale
    positivity
  have hrate:0 ≤ rate:=by dsimp [rate];positivity
  have hB:0 ≤ B:=by dsimp [B];positivity
  have hgMem:g∈T.markedAttach 0:=nativeFreshAtSlot_mem T 0 s star
  have hgLeaves:g.tree.leaves ≤ rBound+1:=
    (T.markedAttach_leaves 0 g hgMem).trans (by omega)
  have Hpoint (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU)
      (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
      |nativeSecondLowUnweightedCReplacementRow (dim n) q U b h K p.tree p.mark
        (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
        (fun old=>Pg (p.restRestrict old))| ≤ B := by
    rw [native_second_low_fresh_occupied_old_slot_exact]
    let c:=p.embed (g.embed (nativeSecondLowFreshOccupiedOldSlot T s star U hU block))
    obtain ⟨hp0,hpH⟩:=(mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp
    obtain ⟨E⟩:=native_second_low_actual_fresh_occupied_post_f_classified_high_whole_c_source
      (dim n) pre mid tail T s U hmid hstar hU ho hT block p hp 0 q 0
    let GP:=nativeFreshObservedShape G s star p hp0
    let GO:=GP.orientAway c U
    have HpH:U ≤ p.tree.splitIndex p.mark (p.embed (g.embed s)):=by
      rw [p.tree.splitIndex_symm]
      omega
    have Hp:NativePersistentLowForks pre.length star U p.tree:=
      (hT.freshStar 0 s).observedHigh (by omega) hstar 0 p hp0 (g.embed s) HpH
    have HL:∀e,p.tree.splitIndex (GP.i e) (GP.j e) < U:=
      native_second_low_fresh_observed_canonical_factors_LOW G s star U p hp0 hLOW
    have Hanchors:∀(d:E.source.core.D.Slot) e,
        p.tree.splitIndex (E.toRetainedCSource.originalSlot d) (GO.i e) < U:=by
      intro d e
      exact (E.oriented_old_anchor_at_every_D GP hstar hU Hp HL le_rfl d e).2.1
    have Hsource:∀σ,(GO.canonicalOriginalQSource M forms).restProduct σ=Pg (p.restRestrict σ):=by
      intro σ
      exact native_second_low_fresh_observed_oriented_complete_rest_source_original_q G s star U p hp0 c M forms σ
    have Hmass:∀e,GO.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e:=by
      intro e
      rw [native_second_low_fresh_observed_oriented_source_mass G s star U p hp0 c e]
      exact hmass e
    have Hlow:∀(d:E.source.core.D.Slot) e,
        U ≤ p.tree.splitIndex (E.toRetainedCSource.originalSlot d) (GO.j e) →
        M.sweepRadius (GO.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) U)/8) (Rmacro/4):=by
      intro d e _
      rw [native_second_low_fresh_observed_oriented_source_mass G s star U p hp0 c e]
      exact Hrlow e
    have Hcuts:=native_second_low_fresh_occupied_old_c_equal_LOW_cuts T s pre.length star U hU
      (by omega) hstar hT block p hp
    dsimp only at Hcuts
    rw [native_second_low_fresh_occupied_old_slot_exact] at Hcuts
    change (p.tree.splitIndex p.mark c=pre.length ∧ p.tree.splitIndex c (p.embed g.mark)=pre.length) ∨
      (p.tree.splitIndex p.mark c=star ∧ p.tree.splitIndex c (p.embed g.mark)=star) at Hcuts
    have Hfc:p.tree.splitIndex p.mark c < U:=by rcases Hcuts with H|H <;> omega
    have Hcz:p.tree.splitIndex c (p.embed g.mark) < U:=by rcases Hcuts with H|H <;> omega
    have Hmf:partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex p.mark c) ≤ Cmass*W:=by
      rcases Hcuts with H|H
      · rw [H.1];exact Hmi
      · rw [H.1];exact Hms
    have Hmz:partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex (p.embed g.mark) c) ≤ Cmass*W:=by
      rw [p.tree.splitIndex_symm]
      rcases Hcuts with H|H
      · rw [H.2];exact Hmi
      · rw [H.2];exact Hms
    have Hrf:M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex p.mark c)) ≤
        min (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) U)/8) (Rmacro/4):=by
      rcases Hcuts with H|H
      · rw [H.1];exact Hri
      · rw [H.1];exact Hrs
    have Hrz:M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex (p.embed g.mark) c)) ≤
        min (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) U)/8) (Rmacro/4):=by
      rw [p.tree.splitIndex_symm]
      rcases Hcuts with H|H
      · rw [H.2];exact Hri
      · rw [H.2];exact Hrs
    have hk' := hk pre mid tail hparts
    have HH:=hk' p.tree GO forms initial p.mark c (p.embed g.mark) U x sourceMass
      hsourceMass E hstar hU Hp Hfc Hcz hxsx hxW hWmacro Hanchors Hmass Hhigh Hz Hlow Hmf Hmz Hrf Hrz HCx Hdyadic
    have HPfun:(GO.canonicalOriginalQSource M forms).restProduct=(fun old=>Pg (p.restRestrict old)):=funext Hsource
    rw [HPfun] at HH
    have hpLeaves:p.tree.leaves ≤ rBound+2:=
      (g.tree.markedAttach_leaves 0 p hp0).trans (by omega)
    have Hd:E.source.core.D.leaves ≤ rBound+2:=
      E.toRetainedCSource.occupied_leaves_le.trans hpLeaves
    have Hd2:(E.source.core.D.leaves:ℝ)^2 ≤ (rBound+2:ℕ)^2:=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr Hd) 2
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hd2 hCpoint.le) hrate using 1
    dsimp only [B,rate,p0,q,b,h,K,as,W]
    ring
  have Hblock (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
      |nativeSecondLowCanonicalCReplacementSource (dim n) q U b h K g.tree Pg
        (g.embed s) (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val) g.mark| ≤
        2*(rBound+1)*B := by
    unfold nativeSecondLowCanonicalCReplacementSource
    have Hnorm (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
        |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
          nativeSecondLowUnweightedCReplacementRow (dim n) q U b h K p.tree p.mark
            (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
            (fun old=>Pg (p.restRestrict old))| ≤ B := by
      rw [abs_mul]
      have HG:=native_full_scalar_cut_moment_abs_le_one p.tree ho U K [p.embed (g.embed s),p.mark]
      change |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark| ≤ 1 at HG
      exact (mul_le_mul HG (Hpoint block p hp) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have HH:=replacement_outer_weight_abs_le_original_q (nativeHighMarkedRows g.tree (g.embed s) (U-1) 0)
      (fun p=>p.coeff) _ Hnorm
    simp_rw [mul_assoc] at HH ⊢
    apply HH.trans
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using mul_le_mul_of_nonneg_right
      (replacement_outer_HIGH_variation_original_q g.tree ho (g.embed s) U (rBound+1) hgLeaves) hB
  unfold nativeSecondLowFreshOccupiedCReplacementSource
  dsimp only
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun block _=>Hblock block)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have Hcount:=native_second_low_fresh_occupied_middle_block_count T s star U hU
  have HcountR:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ) ≤ rBound:=
    Nat.cast_le.mpr (Hcount.trans hLeaves)
  have Hpoly:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)*
      (2*(rBound+1)) ≤ 2*(rBound+1)^2:=by
    have Hr:0 ≤ (rBound:ℝ):=Nat.cast_nonneg _
    nlinarith only [HcountR,Hr]
  have HH:=mul_le_mul_of_nonneg_right Hpoly hB
  rw [←mul_assoc]
  apply HH.trans
  convert mul_le_mul_of_nonneg_right (show Poly*Cpoint ≤ C by dsimp [C];linarith) hrate using 1 <;>
    dsimp only [Poly,B,C,rate,p0,q,b,h,K,as,W] <;> push_cast <;> ring

end OAI.SKFluctuations.Cavity
