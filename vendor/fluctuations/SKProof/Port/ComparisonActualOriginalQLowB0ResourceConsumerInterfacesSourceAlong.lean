module

public import ComparisonSignedCavitySecondLowActualHistoryFullResourceB0ModulusAlong
public import ComparisonSignedCavitySecondLowActualHistoryFullHalfRetargetB0ModulusAlong
public import ComparisonSignedCavitySecondLowActualFreshReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowActualCenteredFreshReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowOriginalConstantB0Vanishing
public import ComparisonSignedCavitySecondLowFullCenteredB0ModulusAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0ConstantResourceInterfacesSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowDensitySourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
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
def ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail) →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(V U k : ℕ) (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (_hU : U ≤ (pre++(mid++tail)).length)
      (seed : List NativeResourceMark) (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P → P.resources.length ≤ degree →
      0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → pre.length+mid.length < U → T.leaves ≤ rBound →
      partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*W n →
    ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      4*W n ≤ (M n).sweepRadius (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).sweepRadius (partitionPoint 0 as pre.length) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    |((W n)⁻¹)^k*nativeActualOriginalCenteredResourceB0_original_q (M n) U P| ≤
      |P.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

def ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail) →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(V U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
      (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term → st.term.resources.length ≤ degree →
      0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → pre.length+mid.length < U → st.tree.leaves ≤ rBound →
      partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*W n →
    ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      4*W n ≤ (M n).sweepRadius (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).sweepRadius (partitionPoint 0 as pre.length) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    |((W n)⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q (M n) U st .secondLow| ≤
      |st.term.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

theorem actual_second_low_full_half_retarget_from_actual_resource_rows_along_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hrows : ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong_original_q degree (rBound+1)
      Cmass Ccut Couter Rmacro Cx Cerr Ci eps dim M W w) :
    ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong_original_q degree rBound
      Cmass Ccut Couter Rmacro Cx Cerr ((3/2:ℝ)*Ci) (fun n=>(3/2:ℝ)*eps n) dim M W w := by
  filter_upwards [Hrows] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hg
  dsimp only at hg ⊢
  intro pre mid tail hparts hindex V U hU seed st hP hdegree hmid hV hiV hVstar hs hT hcut houter
    x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let price:=Ci*partitionPoint 0 (finiteCutMasses us jGrid) U*(M n).xs*Cerr*
      (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf (finiteCutMasses us jGrid) pre.length+1/(dim n+1:ℕ))+
    eps n*W n*(M n).xs^2
  let B:=|st.term.coefficient| *nativeResourceScale x (W n) 1 seed*price
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have hgLeaf : g.tree.leaves ≤ rBound+1:=by
    have HH:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have H0:=hg pre mid tail hparts hindex V U st.generation st.tree hU seed st.term hP hdegree
    hmid hV hiV hVstar hs (hT.trans (by omega)) hcut houter x sourceMass hsourceMass hx hxW hmi hms
    Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have H1:=hg pre mid tail hparts hindex V U st.generation g.tree hU seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hmid hV hiV hVstar hs hgLeaf
    hcut houter x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have HO:=native_actual_original_full_four_second_low_abs_le_original_q (M n) U hU ho hs st (W n) B
    (by exact H0) (by simpa only [NativeResourceTerm.retarget] using H1)
  exact HO.trans_eq (by dsimp only [B,price];ring)

def ActualSecondLowFreshB0ReplacementBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Ccut Couter Cerr Cinitial Cmoving Csaved Cstar : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V≤Ccut*(M n).xs → T.leaves≤rBound →
          partitionPoint 0 as U≤Couter*W n → W n≤(M n).sweepRadius (partitionPoint 0 as U) →
          (M n).sweepRadius (partitionPoint 0 as star)≤(M n).sweepRadius (partitionPoint 0 as U)/2 →
          (M n).z≤(M n).sweepRadius (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x → x≤W n →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e) →
        ∀s : T.Slot,
          let g:=nativeFreshAtSlot T 0 s star
          let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
            χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            Cstar*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0+
            Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0

def ActualSecondLowCenteredFreshReplacementBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Ccut Couter Cerr Cinitial Cmoving Csaved Cstar : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V≤Ccut*(M n).xs → T.leaves≤rBound →
          partitionPoint 0 as U≤Couter*W n → W n≤(M n).sweepRadius (partitionPoint 0 as U) →
          (M n).sweepRadius (partitionPoint 0 as star)≤(M n).sweepRadius (partitionPoint 0 as U)/2 →
          (M n).z≤(M n).sweepRadius (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x → x≤W n →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e) →
        ∀s : T.Slot,
          let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowFreshB0MinusCReplacementSource (dim n) q U b h K T s star hU
            (nativeOriginalCenteredRestTest (dim n) q U b h K T P)|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            Cstar*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0+
            Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0

def actualSecondLowOriginalConstantB0Amplitude_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Temp Cf Couter C : ℝ) : ℝ :=
  16*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))+
    C*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (M.actualOriginalLowErrorDensitySaving (Couter+1)+(1/(n+1:ℕ):ℝ)/M.xs^2)

def ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNet_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (Couter : ℝ) (eps : ℕ → ℝ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
        ∀(U : ℕ),U ≤ as.length → star < U → partitionPoint 0 as U ≤ Couter*W n →
          |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2| ≤
            eps n*W n*(M n).xs^2

def ActualSecondLowFullCenteredB0ModulusOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (V : ℕ) (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
          0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*(W n) →
          (M n).xs ≤ x → x ≤ (W n) →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*(W n) →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*(W n) →
          4*(W n) ≤ (M n).sweepRadius (partitionPoint 0 as U) →
          (M n).z ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,(M n).sweepRadius (G.sourceLowMass e) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          (M n).sweepRadius (partitionPoint 0 as pre.length) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (M n).sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*(M n).xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
        let Pc:=nativeOriginalCenteredRestTest (dim n) q U b h K T P
        let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree
          (fun σ=>Pc (g.restRestrict σ)) [g.embed s,g.mark]/2| ≤
          Ci*partitionPoint 0 as U*(M n).xs*Cerr*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))*
            sourceMonomialScale x (W n) initial+
          (eps n)*(W n)*(M n).xs^2*sourceMonomialScale x (W n) initial

end OAI.SKFluctuations.Cavity
