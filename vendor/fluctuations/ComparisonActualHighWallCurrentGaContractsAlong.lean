module

public import ComparisonActualGeneralTriplePairedValue
public import ComparisonActualGeneralTripleGValue
public import ComparisonActualGeneralGTripleRowAlgebra
public import ComparisonActualGeneralGProjectedRowLaw
public import ComparisonSignedCavityActualCurrentGProjectedCubic
public import ComparisonSignedCavityActualIncomingSourceErrorProductRate
public import ComparisonSignedCavityActualPairedIncomingSourceErrorRate
public import ComparisonSignedCavityActualPairedStarIncomingSourceErrorRate
public import ComparisonSignedCavityActualPowerSourceErrorProductRate
public import ComparisonSignedCavityActualSpineGIncomingCubic
public import ComparisonSignedCavityActualSpineGIncomingNormalized
public import ComparisonSignedCavityActualSpineGIncomingRate
public import ComparisonSignedCavityActualSpineGPowerCubic
public import ComparisonSignedCavityActualSpineGPowerNormalized
public import ComparisonSignedCavityActualSpineGPowerRate
public import ComparisonSignedCavityActualSpineGStarIncomingCubic
public import ComparisonSignedCavityActualSpineGStarIncomingNormalized
public import ComparisonSignedCavityActualSpineGStarIncomingRate
public import ComparisonSignedCavityActualStarIncomingSourceErrorProductRate
public import ComparisonSignedCavityActualTripleIncomingRate
public import ComparisonSignedCavityActualTriplePowerRate
public import ComparisonSignedCavityActualTripleStarIncomingRate
public import ComparisonActualHighWallCurrentGaProductContractsAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualHighWallGeneratedTripleIncomingErrorOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualHighWallGeneratedTripleStarIncomingErrorOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualHighWallGeneratedTriplePowerErrorOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta saving Cmass : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualHighWallGeneratedSpineGIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta saving Cmass Temp Cg Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))

def ActualHighWallGeneratedSpineGStarIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta saving Cmass Temp Cg Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))

def ActualHighWallGeneratedSpineGPowerOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta saving Cmass Temp Cg : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*
      (∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))

def ActualHighWallNormalizedSpineGIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass Temp Cg Ai Ap : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) ((M n).xs+partitionPoint 0 as pre.length) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualHighWallNormalizedSpineGStarIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass Temp Cg Ai Ap : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) (W n) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualHighWallNormalizedSpineGPowerOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta Cmass Temp Cg Ap : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    ∀(V : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualHighWallSpineGIncomingCubicOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length)  ≤  Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    T.leaves ≤ rBound →
    ∀(Tcur : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest Tcur)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀V : ℝ,W n  ≤  V → V  ≤  1 →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |actualGeneralTripleSpineGRow spine (M n).bf (M n).hf ((M n).data.wallRadius (M n).alpha) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualHighWallSpineGStarIncomingCubicOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length)  ≤  Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    T.leaves ≤ rBound →
    ∀(Tcur : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest Tcur)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀V : ℝ,W n  ≤  V → V  ≤  1 →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |actualGeneralTripleSpineGRow spine (M n).bf (M n).hf ((M n).data.wallRadius (M n).alpha) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualHighWallSpineGPowerCubicOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length)  ≤  Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    T.leaves ≤ rBound →
    ∀(Tcur : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest Tcur)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀V : ℝ,W n  ≤  V → V  ≤  1 →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |actualGeneralTripleSpineGRow spine (M n).bf (M n).hf ((M n).data.wallRadius (M n).alpha) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualHighWallCurrentGProjectedCubicOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → U≤(pre++(mid++tail)).length → P.live.test.teeth.length=d →
      P.live.test.exterior.length=a → P.live.test.edges.length=b+d →
    T.leaves≤rBound →
    ∀V : ℝ,W n ≤ V → V ≤ 1 → V≤(M n).data.wallRadius (M n).alpha (partitionPoint 0 as U) →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |actualGeneralDecoupledGProjectedResampling T P.live.test (pre.length+mid.length) U (M n).bf (M n).hf q| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length))

end OAI.SKFluctuations.LaplaceWindowFormalization
