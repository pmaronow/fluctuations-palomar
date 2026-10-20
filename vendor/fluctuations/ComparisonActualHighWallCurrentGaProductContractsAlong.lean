module

public import ComparisonActualHighWallSourceMoments
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
public import ComparisonActualHighWallStarProjectionPowersAlong

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

def ActualHighWallCanonicalIncomingSourceErrorProductOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighWallSource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
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

def ActualHighWallCanonicalStarIncomingSourceErrorProductOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighWallSource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
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

def ActualHighWallCanonicalPowerSourceErrorProductOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelPowerErrorProduct (dim n) j k E.Ei E.Es E.D
          (fun η ζ δ=>(G.canonicalHighWallSource (M n) forms).restProduct (E.read η ζ δ))
          E.target t qi qs center error (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)*
            ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualHighWallCanonicalPairedIncomingSourceErrorOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighWallSource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalHighWallSource (M n) forms₀).restProduct σ=
          (G.canonicalHighWallSource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
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
                ((G₀.canonicalHighWallSource (M n) forms₀).restProduct σ*F σ)*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          (Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
          ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

def ActualHighWallCanonicalPairedStarIncomingSourceErrorOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalHighWallSource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalHighWallSource (M n) forms₀).restProduct σ=
          (G.canonicalHighWallSource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
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
                ((G₀.canonicalHighWallSource (M n) forms₀).restProduct σ*F σ)*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          (Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
          ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

end OAI.SKFluctuations.LaplaceWindowFormalization
