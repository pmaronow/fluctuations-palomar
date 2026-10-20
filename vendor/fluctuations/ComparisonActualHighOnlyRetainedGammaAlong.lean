module

public import ComparisonSignedCavityInheritedGammaAlongProducts
public import ComparisonSignedCavityInheritedGammaAlongPairedProducts
public import ComparisonSignedCavityActualResetPairedRateAlong
public import ComparisonSignedCavityActualResetStarPairedRateAlong
public import ComparisonSignedCavityActualResetPowerRateAlong
public import ComparisonSignedCavityActualResetNormalizedRateAlong
public import ComparisonSignedCavityActualResetStarNormalizedRateAlong
public import ComparisonSignedCavityActualResetPowerNormalizedRateAlong
public import ComparisonSignedCavityInheritedResetNormalizedAlong
public import ComparisonSignedCavityInheritedContinuumGammaRadius
public import ComparisonSignedCavityInheritedGammaRowInterval
public import ComparisonSignedCavityInheritedSavedIncomingRow
public import ComparisonSignedCavityInheritedSavedPowerRow
public import ComparisonSignedCavityInheritedSavedRowPolynomialDecay
public import ComparisonSignedCavityActualResetIncomingCubicRowAlong
public import ComparisonSignedCavityActualResetStarCubicRowAlong
public import ComparisonSignedCavityActualResetPowerCubicRowAlong
public import ComparisonSignedCavityActualCurrentCubicRowAlong
public import ComparisonSignedCavityInheritedCurrentGammaCubicAlong
public import ComparisonSignedCavityActualRetainedGammaProjectedReadout
public import ComparisonSignedCavityActualFourRetainedGammaReadout
public import ComparisonSignedCavityActualResourceRetainedGammaNorm
public import ComparisonSignedCavityInheritedResourceRetainedGammaAlong
public import ComparisonSignedCavityActualFourRetainedGammaNorm
public import ComparisonSignedCavityInheritedFourRetainedGammaAlong
public import ComparisonSignedCavityActualConstantSourceRetainedGammaAlong
public import ComparisonSignedCavityActualRetainedGammaCategorySum
public import ComparisonActualHighOnlyRetainedGammaPhysicalSources
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyNearPairedGammaRows
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
noncomputable section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ → ℕ}

def ActualCanonicalIncomingProductOnEveryFinalNetAlong_high_only
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelIncomingProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_inherited_canonical_incoming_product_from_same_star_along_high_only
    (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalIncomingProductOnEveryFinalNetAlong_high_only a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth_high_only
    (D:=D) Bclock Temp Cf Cmass Ccal hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_minimum_inherited_canonical_two_level_projection_fourth_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal hCf hTemp hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb,mul_pos hCa hCb,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,Hmixed,hW1,hsource,hcompare,Hcutoff] with n hnA hnB hnY hnW hnSource hnCompare hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) hs0 hsxs hnSource hxs1 hnCompare L us hus hret hmesh,
    hnB (M n) hs0 hsxs hnSource hxs1 hnCompare L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrY
  dsimp only at hrA hrB hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us r
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 as l):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
  let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
  let qs:=nativeStarSuffixClock (dim n) pre mid q
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos (dim n)) (restFeature (dim n))
    pre mid tail ho 0 q 0
  have HA4:=(hrA pre mid tail hcut hmass E.D E.target t hst v hWv hvr hlow hz).2
  have HB4:=hrB pre mid tail hcut T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  have HY2:=hrY pre mid tail hcut hindex E.D E.target t
  have hratio : (((dim n):ℝ)/((dim n)+1:ℕ))^4 ≤ 1:=pow_le_one₀ (by positivity)
    ((div_le_one (by positivity : (0:ℝ)<((dim n)+1:ℕ))).mpr (by exact_mod_cast Nat.le_succ (dim n)))
  have HA4':=HA4.trans (mul_le_of_le_one_left (by positivity) hratio)
  have hA:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>((inner ℝ (WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ E.target))))
      (nativeWeightedExteriorAnchor (dim n) (ClockTree.single tail) (fun _=>1) (ClockTree.singleSlot tail) qs (exteriorForestStarRoot z)))^4)
    (fun _ _=>by positivity)
  have hB:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ E.target))))
      (nativeTwoLevelWeightedAnchor (dim n) E.Ei E.Es E.H e qi qs (exteriorForestIRoot z) (exteriorForestStarRoot z))^4)
    (fun _ _=>by positivity)
  have hY:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
      nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^2)
    (fun _ _=>sq_nonneg _)
  have hmass0 : 0 ≤ partitionPoint 0 as pre.length:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) _).1
  have hxspos := (M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*((dim n):ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleB : 0 ≤ Cb*((dim n):ℝ)^(-eta)*savedWeightedExteriorScale (M n).xs (W n) v
      ((M n).xs+partitionPoint 0 as pre.length)*(Ch^a*sourceMonomialScale x (W n) initial) := by
    unfold savedWeightedExteriorScale sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have HC:=two_level_incoming_moment_scales hA hB hY hscaleA hscaleB hscaleY HA4' HB4
    (by
      convert HY2 using 1
      · rfl
      · rw [←pow_mul]
        congr 1
        omega)
  have HI:=native_two_level_incoming_product_abs_le_moments (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as]
  ring

def ActualCanonicalStarIncomingProductOnEveryFinalNetAlong_high_only
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelStarIncomingProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_inherited_canonical_star_incoming_product_from_same_star_along_high_only
    (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalStarIncomingProductOnEveryFinalNetAlong_high_only a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth_high_only
    (D:=D) Bclock Temp Cf Cmass Ccal hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_minimum_inherited_canonical_star_two_level_projection_fourth_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal hCf hTemp hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb,mul_pos hCa hCb,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,Hmixed,hW1,hsource,hcompare,Hcutoff] with n hnA hnB hnY hnW hnSource hnCompare hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) hs0 hsxs hnSource hxs1 hnCompare L us hus hret hmesh,
    hnB (M n) hs0 hsxs hnSource hxs1 hnCompare L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrY
  dsimp only at hrA hrB hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us r
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 as l):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
  let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
  let qs:=nativeStarSuffixClock (dim n) pre mid q
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos (dim n)) (restFeature (dim n))
    pre mid tail ho 0 q 0
  have HA4:=(hrA pre mid tail hcut hmass E.D E.target t hst v hWv hvr hlow hz).2
  have HB4:=hrB pre mid tail hcut T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  have HY2:=hrY pre mid tail hcut hindex E.D E.target t
  have hratio : (((dim n):ℝ)/((dim n)+1:ℕ))^4 ≤ 1:=pow_le_one₀ (by positivity)
    ((div_le_one (by positivity : (0:ℝ)<((dim n)+1:ℕ))).mpr (by exact_mod_cast Nat.le_succ (dim n)))
  have HA4':=HA4.trans (mul_le_of_le_one_left (by positivity) hratio)
  have hA:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>((inner ℝ (WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ E.target))))
      (nativeWeightedExteriorAnchor (dim n) (ClockTree.single tail) (fun _=>1) (ClockTree.singleSlot tail) qs (exteriorForestStarRoot z)))^4)
    (fun _ _=>by positivity)
  have hB:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin (dim n) (E.D.atSlot σ E.target))))
      (nativeTwoLevelWeightedAnchor (dim n) E.Es E.Ei (fun ζ η=>E.H η ζ) e qs qi (exteriorForestStarRoot z) (exteriorForestIRoot z))^4)
    (fun _ _=>by positivity)
  have hY:=native_root_test_expect_nonneg (dim n) E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
      nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^2)
    (fun _ _=>sq_nonneg _)
  have hmass0 : 0 ≤ partitionPoint 0 as (pre.length+mid.length):=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) _).1
  have hxspos := (M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*((dim n):ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleB : 0 ≤ Cb*((dim n):ℝ)^(-eta)*savedWeightedExteriorScale (M n).xs (W n) v
      ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*(Ch^a*sourceMonomialScale x (W n) initial) := by
    unfold savedWeightedExteriorScale sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have HC:=two_level_star_incoming_moment_scales hA hB hY hscaleA hscaleB hscaleY HA4' HB4
    (by
      convert HY2 using 1
      · rfl
      · rw [←pow_mul]
        congr 1
        omega)
  have HI:=native_two_level_star_incoming_product_abs_le_moments (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as]
  ring

def ActualCanonicalPowerProductOnEveryFinalNetAlong_high_only
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelPowerProduct (dim n) j k E.Ei E.Es E.D
          (fun η ζ δ=>(G.canonicalHighOnlySource (M n) forms).restProduct (E.read η ζ δ))
          E.target t qi qs center (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_inherited_canonical_power_product_from_same_star_along_high_only
    (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalPowerProductOnEveryFinalNetAlong_high_only a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth_high_only
    (D:=D) Bclock Temp Cf Cmass Ccal hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HZ⟩:=eventually_actual_minimum_inherited_canonical_source_base_fourth_high_only
    (D:=D) a Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca^2,sq_pos_of_pos hCa,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdim.eventually HA,hdim.eventually HZ,Hmixed,hW1,hsource,hcompare,Hcutoff] with n hnA hnZ hnY hnW hnSource hnCompare hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) hs0 hsxs hnSource hxs1 hnCompare L us hus hret hmesh,
    hnZ (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrZ hrY
  dsimp only at hrA hrZ hrY ⊢
  rw [←hcan] at hrA
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG b GH s E t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us r
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 as l):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
  let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
  let qs:=nativeStarSuffixClock (dim n) pre mid q
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos (dim n)) (restFeature (dim n))
    pre mid tail ho 0 q 0
  have HA4:=(hrA pre mid tail hcut hmass E.D E.target t hst v hWv hvr hlow hz).2
  have HZ4:=hrZ pre mid tail hcut T G forms initial x (W n) hxsx hxW hG b GH s E
  have HY4:=hrY pre mid tail hcut hindex E.D E.target t
  have hratio : (((dim n):ℝ)/((dim n)+1:ℕ))^4 ≤ 1:=pow_le_one₀ (by positivity)
    ((div_le_one (by positivity : (0:ℝ) < ((dim n)+1:ℕ))).mpr (by exact_mod_cast Nat.le_succ (dim n)))
  have HA4':=HA4.trans (mul_le_of_le_one_left (by positivity) hratio)
  have hxspos:=(M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*((dim n):ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleZ : 0 ≤ Ch^a*sourceMonomialScale x (W n) initial := by
    unfold sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have Hbound:=native_two_level_power_product_bound (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end
    (fun η ζ δ=>(G.canonicalHighOnlySource (M n) forms).restProduct (E.read η ζ δ))
    E.target t qi qs center μ exteriorForestIRoot exteriorForestStarRoot
    departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
    hscaleA hscaleZ hscaleY HZ4 (by
      simpa only [nativeRootTestExpect,native_star_centered_projection_difference,
        nativeSubtreeExteriorProjectionFourth] using HA4') (by
      convert HY4 using 1
      · rfl
      · rw [←pow_mul]
        congr 1
        omega)
  convert Hbound using 1
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ → ℕ}

def ActualCanonicalPairedIncomingOnEveryFinalNetAlong_high_only
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
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              (B σ*Y (T.cavityLeft.atSlot σ c)^d-
                (G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_canonical_paired_incoming_from_products_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalIncomingProductOnEveryFinalNetAlong_high_only a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerProductOnEveryFinalNetAlong_high_only b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
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
    (G₀.canonicalHighOnlySource (M n) forms₀).restProduct B hdiff d
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
      a (G.canonicalHighOnlySource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

def ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong_high_only
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
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |nativeStarFieldDisorderMean (restWeight (dim n)) (restFeature (dim n)) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection (dim n) tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              (B σ*Y (T.cavityLeft.atSlot σ c)^d-
                (G₀.canonicalHighOnlySource (M n) forms₀).restProduct σ*
                  Y (T.cavityLeft.atSlot σ s)^d)) 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^d+
          ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            ((Cbase j)^b*sourceMonomialScale x (W n) initial₀)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_canonical_paired_star_incoming_from_products_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalStarIncomingProductOnEveryFinalNetAlong_high_only a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerProductOnEveryFinalNetAlong_high_only b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
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
    (G₀.canonicalHighOnlySource (M n) forms₀).restProduct B hdiff d
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
      a (G.canonicalHighOnlySource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

theorem eventually_inherited_canonical_paired_products_from_same_star_along_high_only
    (hdim : Tendsto dim atTop atTop)
    (a b d : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ∃Cstar : ℝ,0 < Cstar ∧ ∃Chstar : ℝ,0 < Chstar ∧
      ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
      ActualCanonicalPairedIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w ∧
      ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cstar Chstar Cpower Cbase M W w := by
  obtain ⟨Cp,hCp,Ch,hCh,HI⟩ := eventually_inherited_canonical_incoming_product_from_same_star_along_high_only
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed 0 d)
  obtain ⟨Cstar,hCstar,Chstar,hChstar,HS⟩ := eventually_inherited_canonical_star_incoming_product_from_same_star_along_high_only
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed 0 d)
  have HP := fun j=>eventually_inherited_canonical_power_product_from_same_star_along_high_only
    hdim b j (d-1-j) Bclock Temp Cf Cmass Ccal hTemp hCf hCm hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed (2*j) (2*(d-1-j)))
  choose Cpower hCpower Cbase hCbase Hpower using HP
  exact ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,
    fun j=>⟨hCpower j,hCbase j⟩,
    actual_canonical_paired_incoming_from_products_along_high_only HI Hpower,
    actual_canonical_paired_star_incoming_from_products_along_high_only HS Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualGeneratedResetPairedIncomingOnEveryFinalNetAlong_high_only
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_generated_reset_paired_incoming_from_canonical_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedResetPairedIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    r₀ p hp hh v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(nativeGeneratedExteriorShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let G₀:=(nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,htRead,heRead,hsplit,Hlaw⟩:=native_actual_reset_incoming_i_paired_source_high_only
    (dim n) pre mid tail hP hmid hU ht e₀ hIn hi r₀ p hp hh ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j :=
    native_actual_observed_exterior_source_mass (dim n) P (by omega) hlen r₀ p hp Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_incoming_product_self,native_two_level_power_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d center=0 := by
      simp only [native_generated_marked_canonical_rest_product_high_only] at Hlaw
      unfold nativeResetPairedProjectionValue_high_only
      convert Hlaw using 1
      congr 1
    rw [hzero,abs_zero]
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length := by
      apply add_nonneg (M n).hxs.le
      exact (partitionPoint_mem (finiteCutMasses us r) (finiteCutMasses_ordered us hus r) pre.length).1
    apply native_reset_paired_budget_nonneg (dim n) _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have hc : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ) (p.tree.cavityLeftSlot p.mark)=E.D.atSlot δ t:=htRead
    have he : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ)
        (p.tree.cavityLeftSlot (p.embed e₀))=E.Ei.atSlot η e:=by
      simpa only [p.restRestrict_at] using heRead
    have Hbound:=hr pre mid tail hcut hindex hmass p.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) E e t hst
      (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed e₀)) hc he _
      (fun σ=>native_generated_marked_reset_change_high_only (dim n) P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) r₀ p hp σ) v hWv (by simpa only [hsplit] using hvr) hlow hz
    dsimp only [G₀] at Hbound
    simpa only [nativeResetPairedProjectionValue_high_only,nativeResetPairedBudget,
      native_generated_marked_canonical_rest_product_high_only,p.restRestrict_at,MarkedPlacement.restSpin] using Hbound

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualGeneratedResetPairedStarIncomingOnEveryFinalNetAlong_high_only
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_generated_reset_paired_star_incoming_from_canonical_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedStarIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedResetPairedStarIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    r₀ p hp hh v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(nativeGeneratedExteriorShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let G₀:=(nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,htRead,heRead,hsplit,Hlaw⟩:=native_actual_reset_incoming_star_paired_source_high_only
    (dim n) pre mid tail hP hmid hU ht e₀ hIn hi r₀ p hp hh ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j :=
    native_actual_observed_exterior_source_mass (dim n) P (by omega) hlen r₀ p hp Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_star_incoming_product_self,native_two_level_power_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d center=0 := by
      simp only [native_generated_marked_canonical_rest_product_high_only] at Hlaw
      unfold nativeResetPairedProjectionValue_high_only
      convert Hlaw using 1
      congr 1
    rw [hzero,abs_zero]
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length) := by
      apply add_nonneg (M n).hxs.le
      exact (partitionPoint_mem (finiteCutMasses us r) (finiteCutMasses_ordered us hus r) (pre.length+mid.length)).1
    apply native_reset_paired_budget_nonneg (dim n) _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have hc : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ) (p.tree.cavityLeftSlot p.mark)=E.D.atSlot δ t:=htRead
    have he : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ)
        (p.tree.cavityLeftSlot (p.embed e₀))=E.Es.atSlot ζ e:=by
      simpa only [p.restRestrict_at] using heRead
    have Hbound:=hr pre mid tail hcut hindex hmass p.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) E e t hst
      (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed e₀)) hc he _
      (fun σ=>native_generated_marked_reset_change_high_only (dim n) P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) r₀ p hp σ) v hWv (by simpa only [hsplit] using hvr) hlow hz
    dsimp only [G₀] at Hbound
    simpa only [nativeResetPairedProjectionValue_high_only,nativeResetPairedBudget,
      native_generated_marked_canonical_rest_product_high_only,p.restRestrict_at,MarkedPlacement.restSpin] using Hbound

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualGeneratedResetPowerOnEveryFinalNetAlong_high_only
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_generated_reset_power_from_canonical_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ∀j,ActualCanonicalPowerProductOnEveryFinalNetAlong_high_only b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualGeneratedResetPowerOnEveryFinalNetAlong_high_only b d eta saving Cmass Cpower Cbase M W w := by
  have Hfin:=Filter.eventually_all.mpr (fun j : Fin d=>H j.val)
  filter_upwards [Hfin] with n hn
  intro L us hus hret hmesh hstar
  have Hgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hn j L us hus hret hmesh hstar)
  filter_upwards [Hgrid] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn x hxsx hxW hmi
    r₀ p hp hh v hWv hvr hlow hz
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length < (pre++(mid++tail)).length:=
    hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
  let G₀:=(nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,htRead,hsplit,Hlaw⟩:=native_actual_reset_power_paired_source_high_only
    (dim n) pre mid tail hP hmid hU ht hIn r₀ p hp hh ho (M n) 0 q 0 d center
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have HE : nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d center=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct (dim n) j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>(G₀.canonicalHighOnlySource (M n) (fun _=>NativeSourceFactorForm.centered)).restProduct
          (E.read η ζ δ)) E.target t
        (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+l))
        (nativeStarSuffixClock (dim n) pre mid q) center (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0 := by
    simp only [native_generated_marked_canonical_rest_product_high_only] at Hlaw
    dsimp only [G₀]
    simp only [native_generated_marked_canonical_rest_product_high_only]
    unfold nativeResetPairedProjectionValue_high_only
    convert Hlaw using 1 <;> congr 3
  rw [HE]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hst : E.target=t
  · rw [←hst]
    simp only [native_two_level_power_product_self,integral_zero,abs_zero]
    have h1:0 ≤ Cpower j:=(hC j).1
    have h2:0 ≤ Cbase j:=(hC j).2
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    unfold sourceMonomialScale
    positivity
  · have HJ:=hr ⟨j,Finset.mem_range.mp hj⟩ pre mid tail hcut hindex hmass p.tree G₀
      (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length)
      x hxsx hxW hG₀ _ _ (p.tree.cavityLeftSlot (p.embed P.live.test.target))
      E.toNativeCanonicalExteriorSource t hst v hWv (by simpa only [hsplit] using hvr) hlow hz
    have hpow:j+(d-1-j)=d-1:=by have:=Finset.mem_range.mp hj;omega
    rw [hpow] at HJ
    convert HJ using 1

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualNormalizedResetIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass Ai Ap : ℝ)
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) ((M n).xs+partitionPoint 0 as pre.length) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_normalized_reset_incoming_from_actual_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedResetPairedIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualNormalizedResetIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass (Cp*Ch^a)
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    r₀ p hp hh v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx r₀ p hp hh v hWv hvr hlow hz
  have hscale:=native_generated_reset_incoming_i_source_scale P.live.test P.live.ancestry
    (by omega) ht e₀ hIn hi s (W n)
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  have Hnorm:=native_reset_paired_budget_normalize (dim n) a b d eta hsaving hCp hCh zero_le_one hC
    (M n).hxs.le hW hv hs
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (by rw [←hscale];exact sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (show savedWeightedExteriorScale (M n).xs (W n) v s ≤ 1*savedWeightedExteriorScale (M n).xs (W n) v s by simp)
  have Hfinal:=Hraw.trans Hnorm
  simpa only [mul_one,←hscale] using Hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualNormalizedResetStarIncomingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass Ai Ap : ℝ)
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) (W n) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_normalized_reset_star_incoming_from_actual_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedResetPairedStarIncomingOnEveryFinalNetAlong_high_only a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualNormalizedResetStarIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass (Cp*Ch^a*Real.sqrt (1+Cmass))
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    r₀ p hp hh v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx r₀ p hp hh v hWv hvr hlow hz
  have hscale:=native_generated_reset_incoming_star_source_scale P.live.test P.live.ancestry
    (by omega) ht e₀ hIn hi s (W n)
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  have Hnorm:=native_reset_paired_budget_normalize (dim n) a b d eta hsaving hCp hCh (Real.sqrt_nonneg (1+Cmass)) hC
    (M n).hxs.le hW hv hW
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (by rw [←hscale];exact sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (savedWeightedExteriorScale_star_band (M n).hxs.le hW hv (by linarith : 0 ≤ Cmass) (hxsW n) hmass)
  have Hfinal:=Hraw.trans Hnorm
  simpa only [←hscale] using Hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualNormalizedResetPowerOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta Cmass Ap : ℝ)
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue_high_only (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (((dim n):ℝ)^(-eta))^2*Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_normalized_reset_power_from_actual_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedResetPowerOnEveryFinalNetAlong_high_only b d eta saving Cmass Cpower Cbase M W w) :
    ActualNormalizedResetPowerOnEveryFinalNetAlong_high_only b d eta Cmass
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    r₀ p hp hh v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    (min s (W n)) hx hxW hmassx r₀ p hp hh v hWv hvr hlow hz
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  exact Hraw.trans (native_reset_power_budget_normalize (dim n) b d eta hsaving hC hW hv
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le))

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000
variable {dim : ℕ→ℕ}

theorem inherited_same_star_normalized_reset_bounds_along_high_only
    {m delta eta saving cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (a b d : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hsaving : 0 ≤ saving)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃Ai : ℝ,0 < Ai ∧∃As : ℝ,0 < As ∧∃Ap : ℝ,0 ≤ Ap ∧
      ActualNormalizedResetIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass Ai Ap M W w ∧
      ActualNormalizedResetStarIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass As Ap M W w ∧
      ActualNormalizedResetPowerOnEveryFinalNetAlong_high_only b d eta Cmass Ap M W w := by
  obtain ⟨Cp,hCp,Ch,hCh,HI⟩:=eventually_inherited_canonical_incoming_product_from_same_star_along_high_only
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf (by linarith) hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed 0 d)
  obtain ⟨Cstar,hCstar,Chstar,hChstar,HS⟩:=eventually_inherited_canonical_star_incoming_product_from_same_star_along_high_only
    hdim a 0 d Bclock Temp Cf Cmass Ccal hTemp hCf (by linarith) hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed 0 d)
  have HP j:=eventually_inherited_canonical_power_product_from_same_star_along_high_only
    hdim b j (d-1-j) Bclock Temp Cf Cmass Ccal hTemp hCf (by linarith) hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hsource Hcutoff w (Hmixed (2*j) (2*(d-1-j)))
  choose Cpower hCpower Cbase hCbase Hpower using HP
  have hC j : 0 ≤ Cpower j ∧ 0 ≤ Cbase j:=⟨(hCpower j).le,(hCbase j).le⟩
  have HX n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have Hin:=actual_generated_reset_paired_incoming_from_canonical_along_high_only hCp.le hCh.le hC
    (actual_canonical_paired_incoming_from_products_along_high_only HI Hpower)
  have Hstar:=actual_generated_reset_paired_star_incoming_from_canonical_along_high_only hCstar.le hChstar.le hC
    (actual_canonical_paired_star_incoming_from_products_along_high_only HS Hpower)
  have Hpow:=actual_generated_reset_power_from_canonical_along_high_only hC Hpower
  refine ⟨Cp*Ch^a,by positivity,Cstar*Chstar^a*Real.sqrt (1+Cmass),by positivity,
    ∑j∈Finset.range d,Cpower j*(Cbase j)^b,?_,
    actual_normalized_reset_incoming_from_actual_along_high_only hsaving hCm hCp.le hCh.le hC HX Hin,
    actual_normalized_reset_star_incoming_from_actual_along_high_only hsaving hCm hCstar.le hChstar.le hC HX Hstar,
    actual_normalized_reset_power_from_actual_along_high_only hsaving hCm hC HX Hpow⟩
  exact Finset.sum_nonneg fun j _=>mul_nonneg (hC j).1 (pow_nonneg (hC j).2 _)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 4000000

theorem eventually_actual_minimum_inherited_continuum_scalar_gamma_radius_bound_high_only
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀(tree : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U →
      ∀a c : tree.Slot,a≠c →
        let v:=M.R (partitionPoint 0 as (tree.splitIndex a c))
        M.xs ≤ v → M.z ≤ v →
        |fullScalarCutGamma tree U (nativeContinuumMixedClock n M.bf M.hf as) a c| ≤ Cg*v := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound_high_only
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg*(1+cu),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hs0 hsxs hsource as ho tree U hU a c hac
  dsimp only
  intro hxv hzv
  have H:=hn M hs0 hsxs hsource as ho tree U hU a c hac
  let u:=partitionPoint 0 as (tree.splitIndex a c)
  let v:=M.R u
  have hu:=partitionPoint_mem as ho (tree.splitIndex a c)
  have hv:=M.shiftedNativeModel.R_bounds u
  have hmass : u ≤ cu*v:=by
    have Hreg:=(M.regular v ⟨hzv,hv.2⟩).2
    have HS : M.alpha.val.val v=u :=
      M.shiftedNativeModel.R_spec ⟨(M.radius_high_mass (M.hxs.trans_le hxv)).le,hu.2⟩
    change M.alpha.val.val v≤cu*v at Hreg
    rw [HS] at Hreg
    exact Hreg
  apply H.trans
  have Hsum : M.xs+u ≤ (1+cu)*v:=by linarith only [hxv,hmass]
  exact (mul_le_mul_of_nonneg_left Hsum hCg.le).trans_eq (by ring)

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_gamma_radius_row_bound_high_only
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀v : ℝ,M.xs ≤ v → M.z ≤ v → M.R (partitionPoint 0 as star) ≤ v/2 →
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target (nativeRadiusRowBand M.R as v) p)).sum ≤
            Cg*v^2 := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_radius_bound_high_only
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*Cg*(2*cu+1),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hs0 hsxs hsource _hxs L us hus _hret _hmesh
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (gt_mem_nhds M.hxs)
  filter_upwards [Hmesh] with k hkmesh
  dsimp only
  intro i star U T seed depth P hP hi hU v hxv hzv hstar
  let as:=finiteCutMasses us k
  let f:=nativeRadiusRowBand M.R as v
  let s:=P.live.test.target
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hzero : ∀c:T.Slot,c≠s → f (T.splitIndex s c)=0 := by
    intro c hc
    have hsplit : T.splitIndex s c ≤ star:=
      le_of_not_gt (fun H=>hc ((hP.targetStarSingleton hi) c H))
    have HR:=(show Monotone M.R from M.shiftedNativeModel.R_monotone) (partitionPoint_mono as ho hsplit)
    unfold f nativeRadiusRowBand
    split_ifs with hband
    · linarith [hband.1]
    · rfl
  have Hrow:=native_target_weighted_profile_le T s ho f
    (nativeRadiusRowBand_nonneg _ _ _) hzero
    (fun p=>fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark)
    (C:=2*Cg*v) (by
      intro p hp hne hf
      have hband : v ≤ M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ∧
          M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ≤ 2*v := by
        unfold f nativeRadiusRowBand at hf
        split_ifs at hf with hband
        · exact hband
        · exact (hf rfl).elim
      have H:=hn M hs0 hsxs hsource as ho p.tree U hU (p.embed s) p.mark hne (hxv.trans hband.1) (hzv.trans hband.1)
      exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left hband.2 hCg.le]))
  have Hbudget:=actual_minimum_radius_band_edgeBudget_le_high_only M hcu.le hv.le hzv as ho
    (finiteCutMasses_end us hus k) (finiteCutMasses_mesh us hus k) (by positivity)
  have Hb : edgeBudget 0 as f ≤ (2*cu+1)*v := by
    exact Hbudget.trans (by linarith [hkmesh,hxv])
  exact Hrow.trans (by nlinarith [mul_le_mul_of_nonneg_left Hb (show 0 ≤ 2*Cg*v by positivity)])

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_saved_incoming_row_bound_high_only
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 →
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W (M.xs+partitionPoint 0 as i)
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            Cg*Real.log ((n+1:ℕ):ℝ)*(W*M.xs^2) := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_gamma_radius_row_bound_high_only
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HC:=eventually_actual_minimum_radius_dyadic_cover_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  refine ⟨Cg*(2/Real.log 2+2),by positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)],?_⟩
  filter_upwards [HG,HC] with n hn hc
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar
  let as:=finiteCutMasses us k
  let s:=P.live.test.target
  let radius:=fun p : MarkedPlacement T=>M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark))
  let weight:=fun p : MarkedPlacement T=>if p.embed s=p.mark then 0 else
    |p.coeff| * |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark|
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hmass : 0 ≤ partitionPoint 0 as i:=(partitionPoint_mem as ho i).1
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hV : 0 < V:=M.hxs.trans_le hxV
  have hincoming : 0 < M.xs+partitionPoint 0 as i:=add_pos_of_pos_of_nonneg M.hxs hmass
  have H:=native_finite_saved_incoming_row_le (T.markedAttach 0) weight radius
    (x:=M.xs) (W:=W) (s:=M.xs+partitionPoint 0 as i) (V:=V) (C:=Cg)
    (by intro p hp;dsimp only [weight];split_ifs <;> positivity)
    (by intro p hp;exact (M.shiftedNativeModel.R_bounds _).2)
    M.hxs.le hW hincoming hV hxW (by linarith) (by
      intro j hj
      have hvj : V ≤ V*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j)]
      have HB:=hk i star U T seed depth P hP hi hU (V*(2:ℝ)^j)
        (hxV.trans hvj) (hzV.trans hvj) (by linarith)
      convert HB using 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      dsimp only [weight,radius,nativeTargetOffDiagonalProfile,nativeRadiusRowBand,s,as]
      split_ifs <;> ring)
  have Heq : (T.markedAttach 0).map (fun p=>weight p*(if V ≤ radius p then
      nativeSavedIncomingScale M.xs W (M.xs+partitionPoint 0 as i) (radius p) else 0))=
      (T.markedAttach 0).map (fun p=>|p.coeff| *
        |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark| *
        nativeTargetOffDiagonalProfile T s (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
          nativeSavedIncomingScale M.xs W (M.xs+partitionPoint 0 as i) (M.R (partitionPoint 0 as j)) else 0) p) := by
    apply List.map_congr_left
    intro p hp
    dsimp only [weight,radius,nativeTargetOffDiagonalProfile]
    split_ifs <;> ring
  rw [Heq] at H
  exact H.trans (by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc M V hxV hV1).1 hCg.le) (show 0 ≤ W*M.xs^2 by positivity)
    convert HH using 1
    ring)

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_saved_power_row_bound_high_only
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 →
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W W
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            Cg*Real.log ((n+1:ℕ):ℝ)*(W*M.xs^2) := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_gamma_radius_row_bound_high_only
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HC:=eventually_actual_minimum_radius_dyadic_cover_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  refine ⟨Cg*(2/Real.log 2+2),by positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)],?_⟩
  filter_upwards [HG,HC] with n hn hc
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar
  let as:=finiteCutMasses us k
  let s:=P.live.test.target
  let radius:=fun p : MarkedPlacement T=>M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark))
  let weight:=fun p : MarkedPlacement T=>if p.embed s=p.mark then 0 else
    |p.coeff| * |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark|
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hV : 0 < V:=M.hxs.trans_le hxV
  have H:=native_finite_saved_incoming_row_le (T.markedAttach 0) weight radius
    (x:=M.xs) (W:=W) (s:=W) (V:=V) (C:=Cg)
    (by intro p hp;dsimp only [weight];split_ifs <;> positivity)
    (by intro p hp;exact (M.shiftedNativeModel.R_bounds _).2)
    M.hxs.le hW hW hV hxW hxW (by
      intro j hj
      have hvj : V ≤ V*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j)]
      have HB:=hk i star U T seed depth P hP hi hU (V*(2:ℝ)^j)
        (hxV.trans hvj) (hzV.trans hvj) (by linarith)
      convert HB using 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      dsimp only [weight,radius,nativeTargetOffDiagonalProfile,nativeRadiusRowBand,s,as]
      split_ifs <;> ring)
  have Heq : (T.markedAttach 0).map (fun p=>weight p*(if V ≤ radius p then
      nativeSavedIncomingScale M.xs W W (radius p) else 0))=
      (T.markedAttach 0).map (fun p=>|p.coeff| *
        |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark| *
        nativeTargetOffDiagonalProfile T s (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
          nativeSavedIncomingScale M.xs W W (M.R (partitionPoint 0 as j)) else 0) p) := by
    apply List.map_congr_left
    intro p hp
    dsimp only [weight,radius,nativeTargetOffDiagonalProfile]
    split_ifs <;> ring
  rw [Heq] at H
  exact H.trans (by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc M V hxV hV1).1 hCg.le) (show 0 ≤ W*M.xs^2 by positivity)
    convert HH using 1
    ring)

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only
    {eta : ℝ} (heta : 0 < eta) (A : ℝ) (hA : 0 ≤ A)
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 →
        ∀s : ℝ,s=M.xs+partitionPoint 0 as i ∨ s=W →
          A*((n:ℝ)^(-eta))^2*
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W s
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            (n:ℝ)^(-eta)*(W*M.xs^2) := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_saved_incoming_row_bound_high_only
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_saved_power_row_bound_high_only
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HRi:=eventually_native_saved_row_polynomial_decay heta (A*Ci) (mul_nonneg hA hCi.le)
  have HRp:=eventually_native_saved_row_polynomial_decay heta (A*Cp) (mul_nonneg hA hCp.le)
  filter_upwards [HI,HP,HRi,HRp] with n hnI hnP hnRi hnRp
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnI M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with k hkI hkP
  dsimp only at hkI hkP ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar s hs
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hscale : 0 ≤ W*M.xs^2:=by positivity
  rcases hs with hs|hs
  · subst s
    have H:=mul_le_mul_of_nonneg_left
      (hkI i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar)
      (show 0 ≤ A*((n:ℝ)^(-eta))^2 by positivity)
    apply H.trans
    convert mul_le_mul_of_nonneg_right hnRi hscale using 1
    ring
  · subst s
    have H:=mul_le_mul_of_nonneg_left
      (hkP i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar)
      (show 0 ≤ A*((n:ℝ)^(-eta))^2 by positivity)
    apply H.trans
    convert mul_le_mul_of_nonneg_right hnRp hscale using 1
    ring

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualResetIncomingCubicRowOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass : ℝ)
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
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V q
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_reset_incoming_cubic_row_from_normalized_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ai Ap Temp Cf : ℝ} {a b d : ℕ}
    (heta : 0 < eta) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedResetIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass Ai Ap M W w) :
    ActualResetIncomingCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w := by
  have HrowI:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta Ai hAi
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HrowP:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta Ap hAp
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP,HW,Hsource,Hcutoff] with n hn hnI hnP hnW hnSource hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxs1: (M n).xs ≤ 1:=(hxsW n).trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,
    hnI (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh,
    hnP (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r)
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).R (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).shiftedNativeModel.R_bounds _).1
  have hxs0:0 ≤ (M n).xs:=(M n).hxs.le
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0:0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_reset_projected_gamma_row_abs_le_high_only (dim n) T P.live.test (M n) U V q K d center ho
    ((((dim n):ℝ)^(-eta))^2) Ai Ap p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) s (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) hAi hAp hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp hhigh hVR
      have hhigh':U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target):=by
        rwa [p.tree.splitIndex_symm]
      have hVR':V ≤ (M n).R (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi
        0 p hp hhigh' _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      simpa only [q,K,center,p0,s,R,hcut] using Hpt)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    s (Or.inl (by simp only [s,hcut]))
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [K,R,p0,s] <;> (try simp only [hcut]) <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualResetStarIncomingCubicRowOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass : ℝ)
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
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V q
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_reset_star_incoming_cubic_row_from_normalized_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ai Ap Temp Cf : ℝ} {a b d : ℕ}
    (heta : 0 < eta) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedResetStarIncomingOnEveryFinalNetAlong_high_only a b d eta Cmass Ai Ap M W w) :
    ActualResetStarIncomingCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w := by
  have HrowI:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta Ai hAi
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HrowP:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta Ap hAp
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP,HW,Hsource,Hcutoff] with n hn hnI hnP hnW hnSource hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxs1: (M n).xs ≤ 1:=(hxsW n).trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,
    hnI (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh,
    hnP (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r)
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).R (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).shiftedNativeModel.R_bounds _).1
  have hxs0:0 ≤ (M n).xs:=(M n).hxs.le
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0:0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_reset_projected_gamma_row_abs_le_high_only (dim n) T P.live.test (M n) U V q K d center ho
    ((((dim n):ℝ)^(-eta))^2) Ai Ap p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) hAi hAp hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp hhigh hVR
      have hhigh':U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target):=by
        rwa [p.tree.splitIndex_symm]
      have hVR':V ≤ (M n).R (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi
        0 p hp hhigh' _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      simpa only [q,K,center,p0,s,R,hcut] using Hpt)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [K,R,p0,s] <;> (try simp only [hcut]) <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualResetPowerCubicRowOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta Cmass : ℝ)
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
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V q
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_reset_power_cubic_row_from_normalized_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ap Temp Cf : ℝ} {b d : ℕ}
    (heta : 0 < eta) (hAp : 0 ≤ Ap)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedResetPowerOnEveryFinalNetAlong_high_only b d eta Cmass Ap M W w) :
    ActualResetPowerCubicRowOnEveryFinalNetAlong_high_only b d eta Cmass M W w := by
  have HrowI:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta (0:ℝ) le_rfl
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HrowP:=eventually_actual_minimum_inherited_saved_polarized_row_decay_high_only heta Ap hAp
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP,HW,Hsource,Hcutoff] with n hn hnI hnP hnW hnSource hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxs1: (M n).xs ≤ 1:=(hxsW n).trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,
    hnI (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh,
    hnP (M n) hs0 hsxs hnSource hxs1 L us hus hret hmesh] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hdeg hIn V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r)
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).R (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).shiftedNativeModel.R_bounds _).1
  have hxs0:0 ≤ (M n).xs:=(M n).hxs.le
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0:0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_reset_projected_gamma_row_abs_le_high_only (dim n) T P.live.test (M n) U V q K d center ho
    ((((dim n):ℝ)^(-eta))^2) 0 Ap p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) le_rfl hAp hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp hhigh hVR
      have hhigh':U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target):=by
        rwa [p.tree.splitIndex_symm]
      have hVR':V ≤ (M n).R (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hdeg hIn
        0 p hp hhigh' _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      simpa only [q,K,center,p0,s,R,hcut,zero_mul,zero_add,mul_assoc] using Hpt)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [K,R,p0,s] <;> (try simp only [hcut]) <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualCurrentProjectedCubicRowOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass : ℝ)
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
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth.length=d →
      P.live.test.exterior.length=a → P.live.test.edges.length=b+d →
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V q
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) 0
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_current_projected_cubic_row_from_reset_along_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass : ℝ} {a b d : ℕ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualResetIncomingCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w)
    (HS : ActualResetStarIncomingCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w)
    (HP : ActualResetPowerCubicRowOnEveryFinalNetAlong_high_only b d eta Cmass M W w) :
    ActualCurrentProjectedCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w := by
  filter_upwards [HI,HS,HP] with n hnI hnS hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hnI L us hus hret hmesh hstar,hnS L us hus hret hmesh hstar,
    hnP L us hus hret hmesh hstar] with r hrI hrS hrP
  dsimp only at hrI hrS hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hi:pre.length < pre.length+mid.length:=by omega
  obtain ⟨A,base,seed₀,k₀,hBase,hBaseTeeth,⟨spine⟩⟩:=hP.projectionDecomposition
  have hd:spine.toothCount=d:=by have H:=spine.teeth_length;simp only [hBaseTeeth,List.length_nil,Nat.zero_add,ht] at H;exact H.symm
  have haBase:base.live.test.exterior.length=a:=spine.exterior_length.symm.trans ha
  have hbBase:base.live.test.edges.length=b:=by have H:=spine.edges_length;rw [hb,hd] at H;omega
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r)
  have hNode:partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)=(w n).star.val:=by
    rw [hcut,hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have hCenter:pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
      (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
      (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))=
      orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val:=by
    rw [hNode]
    exact (orderedPathPair_eq_completed ((dim n)+1) (by omega) (M n).bf (M n).hf
      ((M n).bf_monotone) ((M n).hf_monotone) (orderedOverlap ((dim n)+1))
      ⟨(w n).star.property,by rw [←hNode];exact (partitionPoint_mem _ ho _).2⟩).symm
  have Hrow:=native_projected_gamma_row_spine_high_only (dim n) spine (hBase.targetStarSingleton hi.le)
    (hP.targetStarSingleton hi.le) (M n) U V q K ho hU
  dsimp only at Hrow
  rw [hCenter,hd] at Hrow
  change |nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V q K 0 _| ≤ _
  rw [Hrow,native_projection_spine_source_scale spine hi,hd]
  have hInDegree:=base.live.ancestry.incoming_degree
  cases hIn:base.live.test.incoming with
  | nil=>exact hrP pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth hbBase hIn V hWV hV1 hlow hz
  | cons e es=>
    cases es with
    | nil=>
      rcases base.live.ancestry.incoming_cuts e (by simp [hIn]) with he|he
      · exact hrI pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth haBase hbBase e hIn he V hWV hV1 hlow hz
      · exact hrS pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth haBase hbBase e hIn he V hWV hV1 hlow hz
    | cons e' es=>simp [hIn] at hInDegree

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {dim : ℕ→ℕ}

theorem inherited_same_star_current_Gamma_cubic_rows_along_high_only
    {m delta eta saving cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta) (hsaving : 0 ≤ saving)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∀a b d : ℕ,ActualCurrentProjectedCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w := by
  intro a b d
  obtain ⟨Ai,hAi,As,hAs,Ap,hAp,HI,HS,HP⟩:=inherited_same_star_normalized_reset_bounds_along_high_only
    a b d Cmass hCm hsaving hm hdelta hroom hgap hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W hcanonical hWlim hcompare hsource Hcutoff w Hmixed
  have hxW n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  exact actual_current_projected_cubic_row_from_reset_along_high_only
    (actual_reset_incoming_cubic_row_from_normalized_along_high_only heta hAi.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource Hcutoff HI)
    (actual_reset_star_incoming_cubic_row_from_normalized_along_high_only heta hAs.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource Hcutoff HS)
    (actual_reset_power_cubic_row_from_normalized_along_high_only heta hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource Hcutoff HP)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

private theorem retained_gamma_pair_factor_smul_high_only (n : ℕ) (as : List PositiveMass)
    (star : ℕ) (q : ℕ→RestCoordinate n→ℝ≥0) (A : Spin n→Spin n→ℝ)
    (beta : ℝ) (y : RestCoordinate n→ℝ) (u : Spin n) :
    nativeStarPairFactor (restWeight n) (restFeature n) as star q (fun v z=>beta*A v z) y u=
      beta*nativeStarPairFactor (restWeight n) (restFeature n) as star q A y u := by
  simp only [nativeStarPairFactor,ClockTree.expect,Finset.mul_sum,mul_left_comm]

theorem native_reset_projected_gamma_row_eq_full_of_radius_le_high_only
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : U≤(pre++(mid++tail)).length)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    nativeResetProjectedGammaRow_high_only n T P M U V q K d center=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
        nativeResetPairedProjectionValue_high_only n T P M p q d center)).sum := by
  unfold nativeResetProjectedGammaRow_high_only
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed P.target) p.mark
  · have Hrad:=(show Monotone M.R from M.shiftedNativeModel.R_monotone) (partitionPoint_mono _ ho hhigh)
    simp only [hhigh,hV.trans Hrad,and_self,ite_true]
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (lt_of_not_ge hhigh)]
    simp only [mul_zero,zero_mul]

theorem native_actual_generated_retained_gamma_affine_eq_reset_row_high_only
    {n : ℕ} {pre mid tail : List PositiveMass}
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i U k : ℕ} {seed : List NativeResourceMark}
    {P₀ : NativeResourceTerm i (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed k T P₀)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (alpha offset beta center : ℝ) :
    let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) j)
    nativeRetainedGammaProjectedDisplacement T P₀.live.test.target (pre.length+mid.length) U q K
      (fun u v=>beta*(R u v-center))
      (fun σ=>alpha*nativeRestGeneratedTestValue T P₀.live.test R C σ-offset)=
      (-beta*alpha/2)*nativeResetProjectedGammaRow_high_only n T P₀.live.test M U V q K 0 center := by
  dsimp only
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let P:=nativeRestGeneratedTestValue T P₀.live.test R C
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) center
  have HF (y : RestCoordinate n→ℝ) (u : Spin n) :
      nativeStarPairFactor (restWeight n) (restFeature n) as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y u=
        beta*Y y u := by
    rw [retained_gamma_pair_factor_smul_high_only]
    exact congrArg (beta*·) (nativeStarPairFactor_two_level_centered_projection n pre mid tail _ center y u)
  rw [native_actual_generated_retained_gamma_eq_paired_source hP hi hs ho,
    native_retained_gamma_paired_row_fresh_fold T P₀.live.test.target star U hs hP.highCut_le_length ho,
    native_reset_projected_gamma_row_eq_full_of_radius_le_high_only n T P₀.live.test M U V q K 0 center ho hP.highCut_le_length hV]
  have Hsum : ((T.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) r.tree.cavityLeft
        (r.tree.cavityLeftSlot (r.embed P₀.live.test.target)) star 0 q
        (fun y σ=>((alpha*P (r.restRestrict σ)-offset)-
          (alpha*P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
            (r.restRestrict σ) (r.restSpin σ))-offset))*
          (nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y (r.restSpin σ)-
          nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y
            (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target)))) 0)).sum=
      (-beta*alpha)*((T.markedAttach 0).map (fun r=>r.coeff*
        fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
        nativeResetPairedProjectionValue_high_only n T P₀.live.test M r q 0 center)).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    simp only [HF]
    have Htest : (fun y σ=>((alpha*P (r.restRestrict σ)-offset)-
        (alpha*P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
          (r.restRestrict σ) (r.restSpin σ))-offset))*
        (beta*Y y (r.restSpin σ)-beta*Y y
          (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target))))=
      (fun y σ=>(-beta*alpha)*((Y y (r.restSpin σ)-Y y
        (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target)))*
        (P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
          (r.restRestrict σ) (r.restSpin σ))-P (r.restRestrict σ)))) := by
      funext y σ
      ring
    rw [Htest,native_star_field_disorder_mean_const_mul]
    dsimp only [nativeResetPairedProjectionValue_high_only]
    simp only [pow_zero,mul_one]
    ring
  calc
    _=(1/2:ℝ)*((-beta*alpha)*((T.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
      nativeResetPairedProjectionValue_high_only n T P₀.live.test M r q 0 center)).sum) := congrArg ((1/2:ℝ)*·) Hsum
    _=_:=by ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def nativeActualResourceRetainedGammaRow_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i : ℕ} (U : ℕ) (V : ℝ) (P : NativeResourceTerm i (pre.length+mid.length) T) : ℝ :=
  nativeActualResourceOriginalScalar_high_only M U P*
    nativeResetProjectedGammaRow_high_only n T P.live.test M U V
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)))
      (nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))) 0
      (nativePhysicalResourceCenter n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length))

theorem actual_minimum_resource_centered_retained_gamma_eq_projected_row_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed k T P)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let as:=pre++(mid++tail)
    let star:=pre.length+mid.length
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeRetainedGammaProjectedDisplacement T P.live.test.target star U q K
      (restCenteredFixedForkKernel n b C star 0) Pc=
      (-b star/2)*nativeActualResourceRetainedGammaRow_high_only M U V P := by
  dsimp only
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have H:=native_actual_generated_retained_gamma_affine_eq_reset_row_high_only (pre:=pre) (mid:=mid) (tail:=tail) hP hi hs M ho V hV q K
    (nativeActualResourceOriginalScalar_high_only M U P)
    (nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
    (b star) (C star)
  dsimp only at H
  have HR : (fun u v : Spin n=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))=
      fun u v=>(∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ) := by
    funext u v
    simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  rw [HR] at H
  have HRpoint (u v : Spin n):=congrFun (congrFun HR u) v
  simp only [HRpoint] at H
  have Hscalar : nativeActualResourceOriginalScalar_high_only M U P=
      P.scalar (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 := rfl
  rw [Hscalar] at H
  have Hkernel : (fun u v=>b star*((∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ)-C star))=
      restCenteredFixedForkKernel n b C star 0 := rfl
  change nativeRetainedGammaProjectedDisplacement T P.live.test.target star U q K
      (fun u v=>b star*((∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ)-C star))
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))=
      (-b star*(nativeActualResourceOriginalScalar_high_only M U P)/2)*
        nativeResetProjectedGammaRow_high_only n T P.live.test M U V q K 0 (C star) at H
  rw [Hkernel] at H
  exact H.trans (by
    change (-b star*nativeActualResourceOriginalScalar_high_only M U P/2)*
      nativeResetProjectedGammaRow_high_only n T P.live.test M U V q K 0 (C star)=
      (-b star/2)*(nativeActualResourceOriginalScalar_high_only M U P*
        nativeResetProjectedGammaRow_high_only n T P.live.test M U V q K 0 (C star))
    ring)

theorem actual_minimum_four_retained_gamma_category_eq_projected_rows_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let as:=pre++(mid++tail)
    let star:=pre.length+mid.length
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast_high_only M U st .gammaRetained=
      (-chi*(M.bf (partitionPoint 0 as star):ℝ)/2)*
        (nativeActualResourceRetainedGammaRow_high_only M U V st.term-
          (1/2:ℝ)*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0)) := by
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_resource_centered_retained_gamma_eq_projected_row_high_only (pre:=pre) (mid:=mid) (tail:=tail) M hP hi hs ho V hV
  have H1:=actual_minimum_resource_centered_retained_gamma_eq_projected_row_high_only (pre:=pre) (mid:=mid) (tail:=tail) M hP.retarget hi hs ho V hV
  dsimp only at H0 H1 ⊢
  change nativeRetainedGammaProjectedDisplacement g.tree g.mark star U q K
      (restCenteredFixedForkKernel n b C star 0)
      (nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C))=
    (-b star/2)*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold nativeActualOriginalFourOtherCategoryContrast_high_only nativeActualOriginalOtherSourceCategory
  dsimp only
  rw [H0,H1]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

theorem actual_resource_original_scalar_live_normalized_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < as.length) (hdegree : P.resources.length ≤ degree)
    {A x W Cmass price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W)
    (hCm : 0 ≤ Cmass) (hmi : partitionPoint 0 as i ≤ Cmass*x) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W 1)
    (live : ℝ)
    (Hlive : |live| ≤
      price*sourceMonomialScale (M.xs+partitionPoint 0 as i) W
        (nativeGeneratedCompleteInitial P.live.test i)) :
    |(W⁻¹)^k*(nativeActualResourceOriginalScalar_high_only M U P*live)| ≤
      |P.coefficient| *((1+Cmass)^degree*A^degree)*price*nativeResourceScale x W 1 seed := by
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  have hlive : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have Hscale:=sourceMonomialScale_initial_scale_le (nativeGeneratedCompleteInitial P.live.test i)
    (M.hxs.le.trans (le_add_of_nonneg_right (partitionPoint_mem as ho i).1)) hx0.le hW.le
    (show 1 ≤ 1+Cmass by linarith) (show M.xs+partitionPoint 0 as i ≤ (1+Cmass)*x by nlinarith) hlive
  have HS:=P.scalar_mul_canonical_live_scale_le (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0 hA hx0 hxW hi hs Hpair
  let scalar:=nativeActualResourceOriginalScalar_high_only M U P
  have Hp : 0 ≤ price*(1+Cmass)^degree:=mul_nonneg hprice (pow_nonneg (by linarith) _)
  have HL : |live| ≤ (price*(1+Cmass)^degree)*sourceMonomialScale x W
      (nativeGeneratedCompleteInitial P.live.test i):=by
    exact Hlive.trans ((mul_le_mul_of_nonneg_left Hscale hprice).trans_eq (by ring))
  have Hprod : |scalar*live| ≤
      |P.coefficient| *nativeResourceEnvelope A x W 1 P.resources*(price*(1+Cmass)^degree):=by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left HL (abs_nonneg scalar)).trans
    convert mul_le_mul_of_nonneg_right HS Hp using 1
    dsimp only [scalar,nativeActualResourceOriginalScalar_high_only]
    ring
  have Hnorm:=mul_le_mul_of_nonneg_left Hprod (show 0 ≤ (W⁻¹)^k by positivity)
  have HE : (W⁻¹)^k*(|P.coefficient| *nativeResourceEnvelope A x W 1 P.resources*(price*(1+Cmass)^degree))=
      |P.coefficient| *A^P.resources.length*nativeResourceScale x W 1 seed*(price*(1+Cmass)^degree) := by
    rw [nativeResourceEnvelope_scale]
    calc
      _=|P.coefficient| *A^P.resources.length*((W⁻¹)^k*nativeResourceScale x W 1 P.resources)*
          (price*(1+Cmass)^degree):=by ring
      _=_:=by rw [hP.normalized_saved_scale x W 1 hW.ne',one_pow,mul_one]
  rw [HE] at Hnorm
  have hseed : 0 ≤ nativeResourceScale x W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos hx0 hW zero_lt_one).le
  have Hfinal:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hdegree) (abs_nonneg P.coefficient)) hseed) Hp
  rw [←abs_of_nonneg (show 0 ≤ (W⁻¹)^k by positivity),←abs_mul] at Hnorm
  change |(W⁻¹)^k*(nativeActualResourceOriginalScalar_high_only M U P*live)| ≤ _ at Hnorm
  apply (Hnorm.trans Hfinal).trans_eq
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualResourceRetainedGammaOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree rBound : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U k : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P →
      P.resources.length ≤ degree → 0 < mid.length → pre.length+mid.length < U →
      U≤(pre++(mid++tail)).length → T.leaves≤rBound →
    ∀x V : ℝ,(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → W n ≤ V → V ≤ 1 →
      V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      |((W n)⁻¹)^k*nativeActualResourceRetainedGammaRow_high_only (M n) U V P| ≤
        |P.coefficient| *C*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed

theorem actual_resource_retained_Gamma_from_cubic_rows_along_high_only (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock Temp Cf eta Cmass : ℝ}
    (degree rBound : ℕ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1)
    (Hrows : ∀a b d : ℕ,ActualCurrentProjectedCubicRowOnEveryFinalNetAlong_high_only a b d eta Cmass M W w) :
    ∃C : ℝ,0<C ∧ ActualResourceRetainedGammaOnEveryFinalNetAlong_high_only degree rBound eta Cmass C M W w := by
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_high_only
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*((1+Cmass)^degree*A^degree)
  have hC : 0<C:=by dsimp only [C];have hA0:=zero_lt_one.trans_le hA;positivity
  refine ⟨C,hC,?_⟩
  let F:=Fin (degree+1)×Fin (degree+1)×Fin (degree+1)
  have HF (p : F):=Hrows p.1 p.2.1 p.2.2
  filter_upwards [Filter.eventually_all.mpr HF,hdim.eventually HA,hsource,hxs,Hcutoff] with n hnR hnA hnsource hnxs hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  intro L us hus hret hmesh hstar
  filter_upwards [Filter.eventually_all.mpr (fun p : F=>hnR p L us hus hret hmesh hstar),
    hnA (M n) hs0 hsxs hnsource hnxs L us hus hret hmesh] with j hjR hjA
  dsimp only at hjR hjA ⊢
  intro pre mid tail hcut hindex hmass T U k seed P hP hdegree hmid hs hU _hT
    x V hx hxW hmi hWV hV1 hVU hlow hz
  have he : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have hlen : P.live.test.edges.length=P.live.test.exterior.length+
      P.live.test.teeth.length+P.live.test.incoming.length:=by
    simp only [NativeGeneratedTest.edges,List.length_append,List.length_map]
  let p : F:=⟨⟨P.live.test.exterior.length,by omega⟩,
    ⟨P.live.test.edges.length-P.live.test.teeth.length,by omega⟩,
    ⟨P.live.test.teeth.length,by omega⟩⟩
  have HL:=hjR p pre mid tail hcut hindex hmass T U k seed P hP hmid hs
    rfl rfl (by dsimp only [p];omega) V hWV hV1 hlow hz
  have HP:=hjA U pre.length (pre.length+mid.length)
  rw [←hcut] at HP
  have HP':=HP T P (by omega) (by omega) (by omega) x (W n) hx hxW
    (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass)
    1 1 (by norm_num) (by norm_num)
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus j
  have hNode : partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)=(w n).star.val:=by
    rw [hcut,hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus j) (w n).star
      (finiteCutMasses_nodes us j hstar)
  have hCenter : nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf
      (pre++(mid++tail)) (pre.length+mid.length)=
      orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val:=by
    unfold nativePhysicalResourceCenter
    rw [hNode]
    exact (orderedPathPair_eq_completed (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).bf_monotone (M n).hf_monotone (orderedOverlap (dim n+1))
      ⟨(w n).star.property,by rw [←hNode];exact (partitionPoint_mem _ ho _).2⟩).symm
  have H:=actual_resource_original_scalar_live_normalized_bound_high_only (M n) hP ho (by omega) (by omega)
    hdegree hA hx hxW hCm (by simpa only [hcut] using hmi)
    (price:=2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2))
    (by have hW:0<W n:=(M n).hxs.trans_le (hx.trans hxW);positivity) HP'
    (nativeResetProjectedGammaRow_high_only (dim n) T P.live.test (M n) U V
      (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)))
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail))) 0
      (nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf (pre++(mid++tail)) (pre.length+mid.length)))
    (by rw [hCenter];simpa only [hcut] using HL)
  change |((W n)⁻¹)^k*nativeActualResourceRetainedGammaRow_high_only (M n) U V P| ≤ _ at H
  apply H.trans_eq
  dsimp only [C]
  ring

theorem eventually_inherited_same_star_resource_retained_Gamma_along_high_only (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (degree rBound : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualResourceRetainedGammaOnEveryFinalNetAlong_high_only degree rBound eta Cmass C M W w := by
  have HX : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),Hcutoff] with n hn hgate
    have hs0 := hgate.1
    have hsxs := hgate.2
    exact ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hn.le
  exact actual_resource_retained_Gamma_from_cubic_rows_along_high_only hdim degree rBound hTemp hCf
    (zero_le_one.trans hCm) hm hdelta hroom hcl hcu hAz hC0 hCt M W w hsource Hcutoff HX
    (inherited_same_star_current_Gamma_cubic_rows_along_high_only Cmass hCm heta hsaving hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal hdim M W hcanonical hWlim hcompare hsource Hcutoff w Hmixed)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

def nativeActualOriginalFourRetainedGammaError_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0;
  -((W⁻¹)^st.generation/(chi*K star))*nativeActualOriginalFourOtherCategoryContrast_high_only M U st .gammaRetained

theorem actual_minimum_four_retained_gamma_error_eq_rows_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i ≤ (pre.length+mid.length)) (hs : (pre.length+mid.length) < U) (ho : MassOrdered 0 (pre++(mid++tail))) (W V : ℝ) (hV : V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))
    nativeActualOriginalFourRetainedGammaError_high_only M U W st=
      ((M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K (pre.length+mid.length)))*
        ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0))) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail)) (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.bf_monotone M.hf_monotone (pre++(mid++tail)) ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.bf_monotone M.hf_monotone (pre++(mid++tail)) ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K (pre++(mid++tail)).length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hc : chi≠0:=ne_of_gt ((Real.exp_pos _).trans_le Hchi.1)
  unfold nativeActualOriginalFourRetainedGammaError_high_only
  rw [actual_minimum_four_retained_gamma_category_eq_projected_rows_high_only M st hP hi hs ho V hV]
  dsimp only
  let b : ℝ:=(M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)
  change -((W⁻¹)^st.generation/(chi*K (pre.length+mid.length)))*
    ((-chi*b/2)*(nativeActualResourceRetainedGammaRow_high_only M U V st.term-
        (1/2:ℝ)*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0))) =
    (b/(2*K (pre.length+mid.length)))*
      ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0)))
  by_cases hk : K (pre.length+mid.length)=0
  · simp only [hk,mul_zero,div_zero,neg_zero,zero_mul]
  · field_simp [hc,hk]

theorem actual_minimum_four_retained_gamma_error_abs_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i ≤ pre.length+mid.length) (hs : pre.length+mid.length < U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) U))
    {W cK B Temp : ℝ} (hW : 0<W) (hcK : 0<cK) (hB : 0≤B) (hTemp : 0≤Temp)
    (hb : (M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ) ≤ Temp)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length))
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourRetainedGammaError_high_only M U W st| ≤
      |st.term.coefficient| *(Temp/cK)*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length)
  have hK0 : 0<K:=(mul_pos hcK hW).trans_le hK
  have hterm : 0≤|st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V st.term)
    0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow_high_only M U V (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
    linarith
  rw [actual_minimum_four_retained_gamma_error_eq_rows_high_only M st hP hi hs ho W V hV]
  rw [abs_mul,abs_of_nonneg (show 0≤(M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K) by positivity)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (by positivity)).trans
  have Hfrac : (M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K) ≤ Temp/(2*(cK*W)):=
    div_le_div₀ hTemp hb (mul_pos (by norm_num) (mul_pos hcK hW))
      (mul_le_mul_of_nonneg_left hK (by norm_num))
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (seedBound k₀ r₀ depth : ℕ) (eta Cmass cK C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(U : ℕ) (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves≤r₀ →
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term →
      0 < mid.length → ∀(hs : pre.length+mid.length < U) (hU : U≤(pre++(mid++tail)).length),
    ∀x V : ℝ,(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → W n ≤ V → V ≤ 1 →
      V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as (pre.length+mid.length) →
      ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st]).map
        (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum ≤
        |st.term.coefficient| *C*((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed

theorem actual_four_retained_Gamma_forest_from_resource_rows_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf eta Cmass cK C₀ : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hcK : 0<cK) (hC₀ : 0<C₀)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1)
    (Hrows : ActualResourceRetainedGammaOnEveryFinalNetAlong_high_only (seedBound+k₀+depth) (r₀+6*depth+1)
      eta Cmass C₀ M W w) :
    ∃C : ℝ,0<C ∧ ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only seedBound k₀ r₀ depth eta Cmass cK C M W w := by
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0≤Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0≤Vcost:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let C:=2*Vcost*(Temp/cK)*C₀+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hrows,hsource,hxs,Hcutoff] with n hn hnsource hnxs hgate
  have hs0 := hgate.1
  have hsxs := hgate.2
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro pre mid tail hcut hindex hmass U seed st hseedlength hgen hleaf hP hmid hs hU
    x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=(dim n)) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as pre.length star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st]
  have ho : MassOrdered 0 as:=by simpa only [as,hcut] using finiteCutMasses_ordered us hus j
  have hx0:0<x:=(M n).hxs.trans_le hx
  have hW:0<W n:=hx0.trans_le hxW
  have hseed : 0≤nativeResourceScale x (W n) 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos hx0 hW zero_lt_one).le
  let B:=C₀*((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed
  have hB : 0≤B:=by dsimp only [B];positivity
  have HK : cK*W n ≤ K star:=by simpa only [as,K,star,hcut] using hstarK
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(Temp/cK)*B:=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) Q hQ
    have Hdegree : Q.term.resources.length ≤ seedBound+k₀+depth:=by
      rw [Hvalid.total_factor_depth]
      omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [g] at HH ⊢
      omega
    have H0:=hj pre mid tail hcut hindex hmass Q.tree U Q.generation seed Q.term Hvalid
      Hdegree hmid hs hU (by omega) x V hx hxW hmi hWV hV1 hVU hlow hz
    have H1:=hj pre mid tail hcut hindex hmass g.tree U Q.generation seed (Q.term.retarget 0)
      Hvalid.retarget (by simpa only [NativeResourceTerm.retarget_resources] using Hdegree)
      hmid hs hU hg x V hx hxW hmi hWV hV1 hVU hlow hz
    apply actual_minimum_four_retained_gamma_error_abs_le_high_only (M n) Q Hvalid (by omega) hs ho V (by simpa only [hcut] using hVU) hW hcK hB hTemp
      (hnsource _ (partitionPoint_mem as ho star)).1 HK
    · convert H0 using 1
      dsimp only [B]
      ring
    · convert H1 using 1
      dsimp only [B,NativeResourceTerm.retarget]
      ring
  have Hsum:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hCw (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks_high_only
      (M n) hCf hnsource hnxs hW hcK as ho hs hU HK Q tag) depth st hleaf
    (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)
    (B:=(Temp/cK)*B) (by positivity) (by
      intro Q hQ
      rw [abs_abs]
      exact (Hrow Q hQ).trans_eq (by ring))
  have Hnonneg : 0≤(rows.map (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum:=
    List.sum_nonneg (by intro z hz;obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hz;exact abs_nonneg _)
  change |(rows.map (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum| ≤ _ at Hsum
  rw [abs_of_nonneg Hnonneg] at Hsum
  apply Hsum.trans
  have HC : 2*Vcost*(Temp/cK)*C₀ ≤ C:=by dsimp only [C];linarith
  have HH:=mul_le_mul_of_nonneg_left HC
    (show 0≤|st.term.coefficient| *((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed by positivity)
  convert HH using 1 <;> (try dsimp only [Vcost,B]) <;> ring

theorem eventually_inherited_same_star_four_retained_Gamma_forest_along_high_only (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0<cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only seedBound k₀ r₀ depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,HC⟩:=eventually_inherited_same_star_resource_retained_Gamma_along_high_only hdim
    (seedBound+k₀+depth) (r₀+6*depth+1) Cmass hCm heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource Hcutoff saving hsaving w Hmixed
  have HX : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),Hcutoff] with n hn hgate
    have hs0 := hgate.1
    have hsxs := hgate.2
    exact ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hn.le
  exact actual_four_retained_Gamma_forest_from_resource_rows_along_high_only seedBound k₀ r₀ depth hTemp hCf hcK hC
    M W w hsource Hcutoff HX HC

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem nativeActualConstantSourceChildren_coefficient_variation_unconditional_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length) :
    ((nativeActualConstantSourceChildren_high_only M as star U hs hU).map
      (fun Q=>|Q.term.coefficient|)).sum≤6 := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.bf_monotone M.hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.bf_monotone M.hf_monotone as ho
  have Hbounds:=native_full_gamma_row_uniform_bounds n (single (S:=Spin n×Bool) as) ho 0 ho U
    (by omega) hU K hKm hK (B:=K as.length) le_rfl (singleSlot as)
  rw [native_full_gamma_row_hessian n _ ho 0 ho U (by omega) K] at Hbounds
  have Hchi : 0 ≤ chi ∧ chi ≤ 1:=⟨(Real.exp_pos _).le.trans Hbounds.1,Hbounds.2⟩
  have Hrow:=nativeActualResourceStep_coefficient_variation_le ho (nativeOriginalHighRowGamma U K)
    (fun st p _=>nativeOriginalHighRowGamma_abs_le_one ho U K st p)
    hs (hs.le.trans hU) .highRow base
    (show base.tree.leaves≤1 by simp only [base,nativeActualConstantState,single_leaves_exact,le_refl])
  have Hcoef : base.term.coefficient=1:=rfl
  rw [Hcoef] at Hrow
  norm_num only [abs_one,NativeActualExpansionOp.coefficientCost,Nat.cast_one,mul_one,one_mul] at Hrow
  unfold nativeActualConstantSourceChildren_high_only
  simp only [List.map_cons,List.sum_cons,NativeActualResourceState.reweight,
    NativeResourceTerm.reweight,NativeActualResourceState.projection,NativeResourceTerm.projection,
    nativeActualConstantState,NativeResourceTerm.ofLive,mul_one]
  change |chi|+_≤6
  rw [abs_of_nonneg Hchi.1]
  have Hchi1 : chi≤1:=Hchi.2
  change chi+((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    .highRow base).map (fun Q=>|Q.term.coefficient|)).sum≤6
  linarith

theorem actual_constant_source_children_forest_abs_sum_le_unconditional_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (F : NativeActualResourceState (Spin n×Bool) as 0 star→ℝ) (hB : 0 ≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren_high_only M as star U hs hU,
      ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [Q]).map (fun R=>|F R|)).sum ≤ |Q.term.coefficient| *B) :
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
      (nativeActualConstantSourceChildren_high_only M as star U hs hU)).map (fun R=>|F R|)).sum ≤ 6*B := by
  unfold nativeActualMinimumFourCenteredForest_high_only at H ⊢
  rw [nativeActualFourCenteredForest_eq_flatMap_singletons,List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation_unconditional_high_only M ho hs hU) hB

def ActualConstantSourceRetainedGammaOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U : ℕ) (hs : star < U) (hU : U ≤ as.length) (V : ℝ),
      partitionPoint 0 as star ≤ Cmass*W n→W n ≤ V→V ≤ 1→V ≤ (M n).R (partitionPoint 0 as U)→
      (M n).R (partitionPoint 0 as star) ≤ V/2→(M n).z ≤ V/2→
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star→
    ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum ≤ C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only.constant_source_children_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only 0 1 3 depth eta Cmass cK C M W w)
    (hC : 0 ≤ C) (hCm : 0 ≤ Cmass) (hxs : ∀n,(M n).xs ≤ W n)
    :
    ActualConstantSourceRetainedGammaOnEveryFinalNetAlong_high_only depth eta Cmass cK (6*C) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let mid:=retainedMassBefore (w n).star.val as
  let tail:=retainedMassAfter (w n).star.val as
  have Hcut : mid++tail=as:=retainedMass_append (w n).star.val as
  have Hmid : 0 < mid.length:=by
    have HP:=nativeRetainedCut_partitionPoint as (finiteCutMasses_ordered us hus j)
      (w n).star (finiteCutMasses_nodes us j hstar)
    by_contra Hm
    have Hz : star=0:=by change mid.length=0;omega
    change partitionPoint 0 as star=(w n).star.val at HP
    rw [Hz] at HP
    simp only [partitionPoint,partitionValues_zero,id_eq] at HP
    linarith [(w n).star.property]
  intro U hs hU V hmass hWV hV1 hVU hlow hz hstarK
  let B:=C*(dim n:ℝ)^(-eta)*(M n).xs^2
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  let P : ℕ→List PositiveMass→Prop:=fun ss bs=>
    ∀(hs' : ss < U) (hU' : U ≤ bs.length) (st : NativeActualResourceState (Spin (dim n)×Bool) bs 0 ss),
      NativeActualResourceGenerated 0 ss U [] st.generation st.tree st.term→
      st.generation=1→st.tree.leaves ≤ 3→
      ((nativeActualMinimumFourCenteredForest_high_only (M n) hs' hU' (W n) depth [st]).map
        (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum ≤ |st.term.coefficient| *B
  have HP : P (0+mid.length) (mid++tail):=by
    intro hs' hU' st hgen hdepth hleaf
    have Hj:=hj [] mid tail
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at Hj
    have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm (M n).hxs.le
    have HH:=Hj Hcut rfl hmass U [] st (by simp) hdepth hleaf hgen Hmid (by simpa only [Nat.zero_add] using hs') hU'
      (M n).xs V le_rfl (hxs n) Hmi hWV hV1 hVU hlow hz hstarK
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,B,mul_assoc] using HH
  have HP0 : P mid.length (mid++tail):=(Nat.zero_add mid.length) ▸ HP
  have HP' : P star as:=Hcut ▸ HP0
  have HB:=actual_constant_source_children_forest_abs_sum_le_unconditional_high_only (M n)
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth
    (nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n)) hB (by
      intro Q hQ
      exact HP' hs hU Q (nativeActualConstantSourceChildren_valid_high_only (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_generation_high_only (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_leaves_high_only (M n) hs hU Q hQ))
  exact HB.trans_eq (by dsimp only [B];ring)

theorem eventually_inherited_same_star_constant_source_retained_Gamma_along_high_only
    {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0 < cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceRetainedGammaOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,H⟩:=eventually_inherited_same_star_four_retained_Gamma_forest_along_high_only hdim
    0 1 3 depth Cmass cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCf hCcal M W hcanonical hWlim hcompare hsource Hcutoff saving hsaving w Hmixed
  exact ⟨6*C,by positivity,H.constant_source_children_high_only hC.le (zero_le_one.trans hCm)
    (fun n=>(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm)⟩

def ActualFourRetainedGammaInitialOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n → 0 < mid.length →
    ∀(U : ℕ) (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length) (a x V : ℝ),
      (M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
      W n ≤ V → V ≤ 1 → V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as (pre.length+mid.length) →
      ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only (M n) U (W n) Q|)).sum ≤
        C*((dim n):ℝ)^(-eta)*(M n).xs^2*x

theorem ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only.initial_high_only
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourRetainedGammaForestOnEveryFinalNetAlong_high_only 1 0 2 depth eta Cmass cK C M W w) :
    ActualFourRetainedGammaInitialOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro pre mid tail hcut hindex hmass hmid U hs hU a x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  let as:=pre++(mid++tail)
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as pre.length (pre.length+mid.length) a (by dsimp only [as];simp)
  have Hleaf:=nativeActualInitialState_leaves_le (S:=Spin (dim n)×Bool) as pre.length
    (pre.length+mid.length) a (by dsimp only [as];simp)
  have Hvalid : NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial]
      st.generation st.tree st.term:=
    .physical (.seed as hU a .initial (Or.inl rfl) (by change pre.length ≤ as.length;dsimp only [as];simp))
  have HH:=hj pre mid tail hcut hindex hmass U [.initial] st (by simp) rfl Hleaf Hvalid hmid hs hU
    x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] using HH

theorem eventually_inherited_same_star_four_retained_Gamma_initial_along_high_only {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0<cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualFourRetainedGammaInitialOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,HC⟩:=eventually_inherited_same_star_four_retained_Gamma_forest_along_high_only hdim
    1 0 2 depth Cmass cK hCm hcK heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource Hcutoff saving hsaving w Hmixed
  exact ⟨C,hC,HC.initial_high_only⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000

theorem actual_retained_gamma_category_signed_sum_abs_le_error_sum_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum_high_only M U W xs .gammaRetained|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourRetainedGammaError_high_only M U W Q|)).sum := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only
    M hCf HS hxs hW hcK ho hs hU hstarK
  have Hsum : (xs.map (fun Q=>nativeActualOriginalFourRetainedGammaError_high_only M U W Q)).sum=
      -(nativeActualFourOtherCategorySum_high_only M U W xs .gammaRetained)/den := by
    calc
      _ = ((xs.map (fun Q=>(W⁻¹)^Q.generation*
          nativeActualOriginalFourOtherCategoryContrast_high_only M U Q .gammaRetained)).sum)*(-den⁻¹) := by
        rw [←List.sum_map_mul_right]
        apply congrArg List.sum
        apply List.map_congr_left
        intro Q _
        dsimp only [nativeActualOriginalFourRetainedGammaError_high_only,den,chi,K]
        ring
      _ = _ := by unfold nativeActualFourOtherCategorySum_high_only;ring
  dsimp only
  have H:=native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourRetainedGammaError_high_only M U W Q)
  rw [Hsum,abs_div,abs_neg,abs_of_pos hden] at H
  exact H

end OAI.SKFluctuations.Cavity
