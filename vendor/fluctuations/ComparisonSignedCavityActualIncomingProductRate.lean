module

public import ComparisonSignedCavityTwoLevelIncomingProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

def ActualCanonicalIncomingProductOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
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
      ∀(s : T.cavityLeft.Slot)
        (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalMinimumSource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock n pre mid q
        |∫z,nativeTwoLevelIncomingProduct n j k E.Ei E.Es E.D E.H e E.target t qi qs center
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0| ≤
          Cp*((n:ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem actual_canonical_incoming_product_from_same_star
    (a j k : ℕ) (Bclock Temp Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalIncomingProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_star_subtree_projection_fourth
    (D:=D) Bclock Temp Cmass Ccal hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_minimum_canonical_two_level_projection_fourth
    (D:=D) a Bclock Temp Cmass Ccal hTemp hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb,mul_pos hCa hCb,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HA,HB,Hmixed,hW1] with n hnA hnB hnY hnW
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hb n) (hh n) hxs1 (hcompare n) L us hus hret hmesh,
    hnB (M n) (hb n) (hh n) hxs1 (hcompare n) L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrY
  dsimp only at hrA hrB hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us r
  let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 as l):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
  let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
  let qs:=nativeStarSuffixClock n pre mid q
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho 0 q 0
  have HA4:=(hrA pre mid tail hcut hmass E.D E.target t hst v hWv hvr hlow hz).2
  have HB4:=hrB pre mid tail hcut T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz
  have HY2:=hrY pre mid tail hcut hindex E.D E.target t
  have hratio : ((n:ℝ)/(n+1:ℕ))^4 ≤ 1:=pow_le_one₀ (by positivity)
    ((div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (by exact_mod_cast Nat.le_succ n))
  have HA4':=HA4.trans (mul_le_of_le_one_left (by positivity) hratio)
  have hA:=native_root_test_expect_nonneg n E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>((inner ℝ (WithLp.toLp 2 (normalizedSpin n (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (E.D.atSlot σ E.target))))
      (nativeWeightedExteriorAnchor n (ClockTree.single tail) (fun _=>1) (ClockTree.singleSlot tail) qs (exteriorForestStarRoot z)))^4)
    (fun _ _=>by positivity)
  have hB:=native_root_test_expect_nonneg n E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n (E.D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (E.D.atSlot σ E.target))))
      (nativeTwoLevelWeightedAnchor n E.Ei E.Es E.H e qi qs (exteriorForestIRoot z) (exteriorForestStarRoot z))^4)
    (fun _ _=>by positivity)
  have hY:=native_root_test_expect_nonneg n E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
      nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^2)
    (fun _ _=>sq_nonneg _)
  have hmass0 : 0 ≤ partitionPoint 0 as pre.length:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) _).1
  have hxspos := (M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*(n:ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleB : 0 ≤ Cb*(n:ℝ)^(-eta)*savedWeightedExteriorScale (M n).xs (W n) v
      ((M n).xs+partitionPoint 0 as pre.length)*(Ch^a*sourceMonomialScale x (W n) initial) := by
    unfold savedWeightedExteriorScale sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have HC:=two_level_incoming_moment_scales hA hB hY hscaleA hscaleB hscaleY HA4' HB4
    (by
      convert HY2 using 1
      · rfl
      · rw [←pow_mul]
        congr 1
        omega)
  have HI:=native_two_level_incoming_product_abs_le_moments n j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as]
  ring

theorem exists_actual_bare_sharp_canonical_incoming_products
    {m delta eta cl cu Az C0 Ct D Bclock Temp L Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 < Temp) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp L Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNet p saving M W w) ∧
      (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) ∧
      ∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualCanonicalIncomingProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed⟩:=exists_actual_bare_sharp_star_all_mixed_projection_powers
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_⟩
  intro a j k
  exact actual_canonical_incoming_product_from_same_star a j k Bclock Temp Cmass Ccal hTemp.le
    hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hb hh w (Hmixed j k)

end OAI.SKFluctuations.LaplaceWindowFormalization
