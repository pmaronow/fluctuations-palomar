module

public import ComparisonSignedCavityActualAllSourceErrorProducts
public import ComparisonSignedCavityPairedErrorAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(G₀ : ActualNaturalBoundaryShape n b T) (forms₀ : Fin b→NativeSourceFactorForm)
        (initial₀ : Finset (Fin b)),
        (∀e,G₀.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial₀ e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s (G.canonicalMinimumSource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalMinimumSource (M n) forms₀).restProduct σ=
          (G.canonicalMinimumSource (M n) f).restProduct σ*
            (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
      ∀(e₁ e₂ : T.cavityLeft.Slot),e₁ ≠ e₂ →
        let errorCenter:=orderedPathS (n+1) (M n).bf (M n).hf
          (partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))
      ∀error : E.D.Assignment→ℝ,
        (∀η ζ δ,deletedOverlap n (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₁,false))
          (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e₂,false))-errorCenter=error δ) →
      ∀F : T.cavityLeft.Assignment→ℝ,(∀η ζ δ,F (E.read η ζ δ)=error δ) →
        let qs:=nativeStarSuffixClock n pre mid q
        |nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection n tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              ((B σ*F σ)*Y (T.cavityLeft.atSlot σ c)^d-
                ((G₀.canonicalMinimumSource (M n) forms₀).restProduct σ*F σ)*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          (Cp*((n:ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            (((n+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
          ((M n).xs+partitionPoint 0 as (T.cavityLeft.splitIndex e₁ e₂))

theorem actual_canonical_paired_star_incoming_source_error_from_products
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalStarIncomingSourceErrorProductOnEveryFinalNet a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerSourceErrorProductOnEveryFinalNet b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  have HPfin:=Filter.eventually_all.mpr (fun j : Fin d=>HP j.val)
  filter_upwards [HI,HPfin] with n hnI hnP
  intro L us hus hret hmesh hstar
  have HPgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hnP j L us hus hret hmesh hstar)
  filter_upwards [hnI L us hus hret hmesh hstar,HPgrid] with r hrI hrP
  dsimp only at hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG G₀ forms₀ initial₀ hG₀
    s E e t hst c e₀ hc he B hdiff v hWv hvr hlow hz e₁ e₂ hef error herror F hF
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have H:=E.paired_incoming_star_error_allocation ho c e₀ t e hc he
    (G₀.canonicalMinimumSource (M n) forms₀).restProduct B F error hF hdiff d
    (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)
  rw [add_mul,Finset.sum_mul]
  apply (congrArg abs H).le.trans
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have HIn:=hrI pre mid tail hcut hindex hmass T G forms initial x
      hxsx hxW hG s E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    simp only [Nat.zero_add] at HIn
    convert HIn using 1
    congr 3
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hJ : j<d:=Finset.mem_range.mp hj
    have HJ:=hrP ⟨j,hJ⟩ pre mid tail hcut hindex hmass T G₀ forms₀ initial₀ x hxsx hxW hG₀
      a (G.canonicalMinimumSource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

end OAI.SKFluctuations.LaplaceWindowFormalization
