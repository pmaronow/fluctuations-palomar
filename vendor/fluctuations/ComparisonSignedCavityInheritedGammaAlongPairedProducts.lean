module

public import ComparisonSignedCavityInheritedGammaAlongProducts
public import ComparisonSignedCavityActualPairedIncomingRate
public import ComparisonSignedCavityActualPairedStarIncomingRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
variable {dim : ℕ → ℕ}

def ActualCanonicalPairedIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalMinimumSource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalMinimumSource (M n) forms₀).restProduct σ=
          (G.canonicalMinimumSource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              (B σ*Y (T.cavityLeft.atSlot σ c)^d-
                (G₀.canonicalMinimumSource (M n) forms₀).restProduct σ*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_canonical_paired_incoming_from_products_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalIncomingProductOnEveryFinalNetAlong a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  have HPfin:=Filter.eventually_all.mpr (fun j : Fin d=>HP j.val)
  filter_upwards [HI,HPfin] with n hnI hnP
  intro L us hus hret hmesh hstar
  have HPgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hnP j L us hus hret hmesh hstar)
  filter_upwards [hnI L us hus hret hmesh hstar,HPgrid] with r hrI hrP
  dsimp only at hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG G₀ forms₀ initial₀ hG₀
    s E e t hst c e₀ hc he B hdiff v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have H:=E.paired_incoming_i_allocation ho c e₀ t e hc he
    (G₀.canonicalMinimumSource (M n) forms₀).restProduct B hdiff d
    (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)
  apply (congrArg abs H).le.trans
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have HIn:=hrI pre mid tail hcut hindex hmass T G forms initial x
      hxsx hxW hG s E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz
    simp only [Nat.zero_add] at HIn
    convert HIn using 1
    congr 3
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hJ : j<d:=Finset.mem_range.mp hj
    have HJ:=hrP ⟨j,hJ⟩ pre mid tail hcut hindex hmass T G₀ forms₀ initial₀ x hxsx hxW hG₀
      a (G.canonicalMinimumSource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

def ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ) (Cpower Cbase : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
        (E : NativeDynamicCanonicalExteriorSource (dim n) a pre mid tail T s (G.canonicalMinimumSource (M n) f) 0 q 0)
        (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e) →
      ∀B : T.cavityLeft.Assignment→ℝ,
        (∀σ,B σ-(G₀.canonicalMinimumSource (M n) forms₀).restProduct σ=
          (G.canonicalMinimumSource (M n) f).restProduct σ*
            (deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ c,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
              deletedOverlap (dim n) (joinSpin (T.cavityLeft.atSlot σ s,false))
                (joinSpin (T.cavityLeft.atSlot σ e₀,false)))) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              (B σ*Y (T.cavityLeft.atSlot σ c)^d-
                (G₀.canonicalMinimumSource (M n) forms₀).restProduct σ*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_canonical_paired_star_incoming_from_products_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalStarIncomingProductOnEveryFinalNetAlong a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  have HPfin:=Filter.eventually_all.mpr (fun j : Fin d=>HP j.val)
  filter_upwards [HI,HPfin] with n hnI hnP
  intro L us hus hret hmesh hstar
  have HPgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hnP j L us hus hret hmesh hstar)
  filter_upwards [hnI L us hus hret hmesh hstar,HPgrid] with r hrI hrP
  dsimp only at hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG G₀ forms₀ initial₀ hG₀
    s E e t hst c e₀ hc he B hdiff v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have H:=E.paired_incoming_star_allocation ho c e₀ t e hc he
    (G₀.canonicalMinimumSource (M n) forms₀).restProduct B hdiff d
    (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)
  apply (congrArg abs H).le.trans
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have HIn:=hrI pre mid tail hcut hindex hmass T G forms initial x
      hxsx hxW hG s E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz
    simp only [Nat.zero_add] at HIn
    convert HIn using 1
    congr 3
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hJ : j<d:=Finset.mem_range.mp hj
    have HJ:=hrP ⟨j,hJ⟩ pre mid tail hcut hindex hmass T G₀ forms₀ initial₀ x hxsx hxW hG₀
      a (G.canonicalMinimumSource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

theorem eventually_inherited_canonical_paired_products_from_same_star_along
    (hdim : Tendsto dim atTop atTop)
    (a b d : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ∃Cstar : ℝ,0 < Cstar ∧ ∃Chstar : ℝ,0 < Chstar ∧
      ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
      ActualCanonicalPairedIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w ∧
      ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cstar Chstar Cpower Cbase M W w := by
  obtain ⟨Cp,hCp,Ch,hCh,HI⟩ := eventually_inherited_canonical_incoming_product_from_same_star_along
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource w (Hmixed 0 d)
  obtain ⟨Cstar,hCstar,Chstar,hChstar,HS⟩ := eventually_inherited_canonical_star_incoming_product_from_same_star_along
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource w (Hmixed 0 d)
  have HP := fun j=>eventually_inherited_canonical_power_product_from_same_star_along
    hdim b j (d-1-j) Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource w (Hmixed (2*j) (2*(d-1-j)))
  choose Cpower hCpower Cbase hCbase Hpower using HP
  exact ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,
    fun j=>⟨hCpower j,hCbase j⟩,
    actual_canonical_paired_incoming_from_products_along HI Hpower,
    actual_canonical_paired_star_incoming_from_products_along HS Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
