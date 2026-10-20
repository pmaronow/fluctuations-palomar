module

public import ComparisonSignedCavitySecondLowStarOnlyFreshB0ModuloUnweightedAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0StarUnobservedCompatibleSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0WholeObservedPhysicalSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
def ActualSecondLowStarOnlyFreshB0ModuloUnweightedOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Couter Cerr Cmoving Csaved : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1)→(w n).star∈us→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
  ∀ᶠk in atTop,
    let as:=finiteCutMasses us k
    let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    ∀(mid tail : List PositiveMass),as=mid++tail→mid.length=retainedMassPrefixIndex (w n).star.val as→
    ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) (mid++tail)) (hU : U≤(mid++tail).length),
      0< mid.length→mid.length<U→NativePersistentLowForks mid.length mid.length U T→T.leaves≤rBound→
      partitionPoint 0 as U≤Couter*W n→W n≤(M n).sweepRadius (partitionPoint 0 as U)→
      (M n).sweepRadius (partitionPoint 0 as mid.length)≤(M n).sweepRadius (partitionPoint 0 as U)/2→
      (M n).z≤(M n).sweepRadius (partitionPoint 0 as U)/2→
    ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
      (initial_original_q : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
      (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial_original_q e)→∀s:T.Slot,
      let g:=nativeFreshAtSlot T 0 s mid.length
      let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
      let Pg:=fun old=>P (g.restRestrict old)
      let χ:=(scalarTerminal.schedule (scalarBoundaryClocks (mid++tail) (relocatedClock U 0 K))).H 0 0
      let p0:=sourceMonomialScale x (W n) initial_original_q
      let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
      |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
        χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P|≤
        16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
        Cmoving*W n*Cerr*rho*p0+
        Csaved*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0

theorem actual_second_low_star_only_fresh_B0_modulo_unweighted_budget_along_original_q
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (_heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cmoving Csaved : ℝ,0<Cmoving ∧ 0<Csaved ∧
      ActualSecondLowStarOnlyFreshB0ModuloUnweightedOnEveryFinalNetAlong_original_q degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cmoving Csaved dim M W w := by
  obtain ⟨Cm,hCmRate,HU⟩:=actual_second_low_star_only_unobserved_budget_along_original_q degree (rBound+1) Cmass Couter
    hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  let Ccommon:=Cmass+Couter+1
  have hCommon:0≤Ccommon:=by dsimp [Ccommon];linarith
  obtain ⟨Co,hCo,HO⟩:=eventually_actual_minimum_inherited_second_low_whole_observed_saved_rate_original_q
    (D:=D) degree rBound Bclock Temp Cf Ccommon Ccal hTemp hCf hCommon hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cm,Co,hCmRate,hCo,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HU,hdim.eventually HO,Hsource,Hcompare,HW1,Hcutoff] with n hnU hnO hs hc hw1 hnCutoff
  have hxW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have hxs:(M n).xs≤1:=hxW.trans hw1
  have hWdef:W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)):=by
    rw [hcanonical];rfl
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnU L us hus hStarNode hret hmesh,hnO (M n) hnCutoff.1 hnCutoff.2 hs hxs hc L us hus hret hmesh] with k hkU hkO
  dsimp only at hkU hkO ⊢
  rw [←hWdef] at hkO
  intro mid tail hparts hindex U T hU hmid hstar hpersistent hLeaves houter hWU hRstar hz
    G forms initial_original_q x hxsx hxW hmass s
  rw [hparts] at hkU hkO hindex houter hWU hRstar hz ⊢
  rw [←hindex] at hkU
  let as:=mid++tail
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot T 0 s mid.length
  let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  have ho:MassOrdered 0 as:=by change MassOrdered 0 (mid++tail);rw [←hparts];exact finiteCutMasses_ordered us hus k
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  let Gfresh:=G.retainOnMarked 0 g (nativeFreshAtSlot_mem T 0 s mid.length)
  have HP:(Gfresh.canonicalOriginalQSource (M n) forms).restProduct=Pg:=by
    funext τ;exact G.retained_canonical_restProduct_original_q (M n) forms 0 g (nativeFreshAtSlot_mem T 0 s mid.length) τ
  have Hpf:NativePersistentLowForks mid.length mid.length U g.tree:=hpersistent.freshStar 0 s
  have Hleaves:g.tree.leaves≤rBound+1:=
    (T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s mid.length)).trans (Nat.add_le_add_right hLeaves 1)
  have HmassFresh:∀e,Gfresh.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial_original_q e:=by
    intro e;rw [ActualNaturalBoundaryShape.retained_source_mass];exact hmass e
  have Hsplit:g.tree.splitIndex (g.embed s) g.mark=mid.length:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (by omega)]
  have BU:=hkU U g.tree hU hstar Hpf Hleaves houter Gfresh forms initial_original_q x hxsx hxW HmassFresh
    (g.embed s) g.mark Hsplit
  rw [HP] at BU
  have Hweak:NativePersistentLowForks 0 mid.length U T:=by
    intro a z
    rcases hpersistent a z with H|H|H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr H)
  have HmassStar:partitionPoint 0 as mid.length≤Ccommon*W n:=by
    have HM:=(partitionPoint_mono as ho hstar.le).trans houter
    exact HM.trans (mul_le_mul_of_nonneg_right (by dsimp [Ccommon];linarith : Couter≤Ccommon) hW.le)
  have HmassOld:∀e,G.sourceLowMass e≤Ccommon*sourceFactorScale x (W n) initial_original_q e:=by
    intro e
    exact (hmass e).trans (mul_le_mul_of_nonneg_right (by dsimp [Ccommon];linarith : Cmass≤Ccommon)
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial_original_q e).le)
  have HOlocal:=hkO [] mid tail
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at HOlocal
  have BO:=HOlocal trivial HmassStar T s U hU hmid hstar hLeaves Hweak hWU hRstar hz
    G forms initial_original_q x hxsx hxW HmassOld
  have HKliteral:nativeSecondLowInheritedSavedMixedClock (dim n) (M n).sweepBf (M n).sweepHf (mid++tail)=K:=rfl
  have HGliteral:nativeFreshAtSlot T 0 s (0+mid.length)=g:=by rw [Nat.zero_add]
  rw [HKliteral,HGliteral] at BO
  have Hsaved:|(∑j:Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P|≤
      Co*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*sourceMonomialScale x (W n) initial_original_q:=by
    simpa only [P,Pg,q,b,h,K,g,as,mul_assoc] using BO
  have Hjoint:=native_second_low_joint_ledger_half_eq_observed_unobserved (dim n) q U b h K g.tree ho hU Pg
    (g.embed s) g.mark (Hsplit ▸ hstar)
  have HE:nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P=
      ((∑j:Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
        ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
          nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P)+
      (∑j:Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j false/2):=by
    rw [Hjoint];ring
  change |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
    ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
      nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P|≤_
  rw [HE]
  apply (abs_add_le _ _).trans
  apply (add_le_add Hsaved BU).trans_eq
  ring

end OAI.SKFluctuations.Cavity
