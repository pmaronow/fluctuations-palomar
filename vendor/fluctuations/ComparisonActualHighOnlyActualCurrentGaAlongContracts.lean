module

public import ComparisonActualHighOnlyActualGProjectedRowLaw
public import ComparisonActualHighOnlyActualTripleGValue
public import ComparisonActualHighOnlyGTripleRowAlgebra
public import ComparisonActualHighOnlyTriplePairedValue
public import ComparisonSignedCavityActualCurrentGaAlongContracts
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualCanonicalIncomingSourceErrorProductOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape (dim n) a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighOnlySource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelIncomingErrorProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center error
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)*
            ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualCanonicalStarIncomingSourceErrorProductOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape (dim n) a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighOnlySource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelStarIncomingErrorProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center error
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)*
            ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualCanonicalPowerSourceErrorProductOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape (dim n) a T) (forms : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(b : ℕ) (GH : ActualNaturalBoundaryShape (dim n) b T) (s : T.cavityLeft.Slot)
        (E : NativeCanonicalExteriorSource (dim n) b pre mid tail T s GH 0 q 0)
        (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelPowerErrorProduct (dim n) j k E.Ei E.Es E.D
          (fun η ζ δ=>(G.canonicalHighOnlySource (M n) forms).restProduct (E.read η ζ δ))
          E.target t qi qs center error (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)*
            ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualCanonicalPairedIncomingSourceErrorOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape (dim n) a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(G₀ : ActualNaturalBoundaryShape (dim n) b T) (forms₀ : Fin b→NativeSourceFactorForm)
        (initial₀ : Finset (Fin b)),
        (∀e,G₀.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial₀ e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighOnlySource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ=
          (G.canonicalHighOnlySource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
      ∀F : T.cavityLeft.Assignment→ℝ,(∀η ζ δ,F (E.read η ζ δ)=error δ) →
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              ((B σ*F σ)*Y (T.cavityLeft.atSlot σ c)^d-
                ((G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ*F σ)*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          (Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
          ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape (dim n) a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(G₀ : ActualNaturalBoundaryShape (dim n) b T) (forms₀ : Fin b→NativeSourceFactorForm)
        (initial₀ : Finset (Fin b)),
        (∀e,G₀.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial₀ e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighOnlySource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ=
          (G.canonicalHighOnlySource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
      ∀F : T.cavityLeft.Assignment→ℝ,(∀η ζ δ,F (E.read η ζ δ)=error δ) →
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              ((B σ*F σ)*Y (T.cavityLeft.atSlot σ c)^d-
                ((G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ*F σ)*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          (Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
          ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualGeneratedTripleIncomingErrorOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeTripleResetPairedErrorValue_high_only (dim n) T P.live.test (M n) p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualGeneratedTripleStarIncomingErrorOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeTripleResetPairedErrorValue_high_only (dim n) T P.live.test (M n) p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualGeneratedTriplePowerErrorOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta saving Cmass : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeTripleResetPairedErrorValue_high_only (dim n) T P.live.test (M n) p rr zz q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

def ActualGeneratedSpineGIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta saving Cmass Temp Cg Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))

def ActualGeneratedSpineGStarIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta saving Cmass Temp Cg Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*
      (nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))

def ActualGeneratedSpineGPowerOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta saving Cmass Temp Cg : ℝ)
    (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*
      (∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))

def ActualNormalizedSpineGIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass Temp Cg Ai Ap : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) ((M n).xs+partitionPoint 0 as pre.length) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualNormalizedSpineGStarIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass Temp Cg Ai Ap : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) (W n) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualNormalizedSpineGPowerOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta Cmass Temp Cg Ap : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue_high_only spine (M n) U p rr zz q| ≤
      Temp*Cg*v*(
      (((dim n):ℝ)^(-eta))^2*Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

def ActualSpineGIncomingCubicOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |nativeActualTripleSpineGRow_high_only spine (M n) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualSpineGStarIncomingCubicOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |nativeActualTripleSpineGRow_high_only spine (M n) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualSpineGPowerCubicOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      (M n).R (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |nativeActualTripleSpineGRow_high_only spine (M n) U V q|  ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

def ActualCurrentGProjectedCubicOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
    ∀V : ℝ,W n ≤ V → V ≤ 1 → V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeActualDecoupledGProjectedResampling_high_only T P.live.test (pre.length+mid.length) U (M n) q| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length))

end OAI.SKFluctuations.LaplaceWindowFormalization
