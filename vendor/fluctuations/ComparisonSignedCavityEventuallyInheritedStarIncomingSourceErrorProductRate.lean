module

public import ComparisonSignedCavityInheritedStarIncomingSourceErrorProductRate
public import ComparisonSignedCavityActualStarIncomingSourceErrorProductRate
public import ComparisonSignedCavityInheritedCalibratedStarSubtreeProjection
public import ComparisonSignedCavityInheritedCanonicalTwoLevelProjection
public import ComparisonSignedCavityInheritedCanonicalStarTwoLevelProjection
public import ComparisonSignedCavityInheritedSourceErrorMoment
public import ComparisonSignedCavityInheritedSourceBaseEighth

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

theorem eventually_inherited_canonical_star_incoming_source_error_product_from_same_star
    (a j k : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNet (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalStarIncomingSourceErrorProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth
    (D:=D) Bclock Temp Cf Cmass Ccal hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_minimum_inherited_canonical_star_two_level_projection_fourth
    (D:=D) a Bclock Temp Cf Cmass Ccal hCf hTemp hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_minimum_inherited_canonical_source_error_even_bound
    (D:=D) 2 (by decide) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb*Ce,mul_pos (mul_pos hCa hCb) hCe,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HA,HB,HE,Hmixed,hW1,hsource] with n hnA hnB hnE hnY hnW hnSource
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) hnSource hxs1 (hcompare n) L us hus hret hmesh,
    hnB (M n) hnSource hxs1 (hcompare n) L us hus hret hmesh,
    hnE (M n) hnSource hxs1 L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrE hrY
  dsimp only at hrA hrB hrE hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz e₁ e₂ he₁₂ error herror
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
  let je:=T.cavityLeft.splitIndex e₁ e₂
  let errorCenter:=orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as je)
  have HE4:=hrE pre mid tail hcut T a (G.canonicalMinimumSource (M n) f) s e₁ e₂ he₁₂ E error herror
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
      (nativeTwoLevelWeightedAnchor n E.Es E.Ei (fun ζ η=>E.H η ζ) e qs qi (exteriorForestStarRoot z) (exteriorForestIRoot z))^4)
    (fun _ _=>by positivity)
  have hY:=native_root_test_expect_nonneg n E.D ho.suffix_end.suffix_end qs μ exteriorForestStarRoot
    (fun z σ=>(nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
      nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4)
    (fun _ _=>by positivity)
  have hmass0 : 0 ≤ partitionPoint 0 as (pre.length+mid.length):=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) _).1
  have hxspos := (M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*(n:ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleB : 0 ≤ Cb*(n:ℝ)^(-eta)*savedWeightedExteriorScale (M n).xs (W n) v
      ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*(Ch^a*sourceMonomialScale x (W n) initial) := by
    unfold savedWeightedExteriorScale sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have hmassE:0 ≤ partitionPoint 0 as je:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) je).1
  have hscaleE:0 ≤ Ce*((M n).xs+partitionPoint 0 as je):=by positivity
  have HY4 : nativeRootTestExpect n E.D qs μ exteriorForestStarRoot
      (fun z σ=>(nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
        nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4) ≤
      ((((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k))^4 := by
    have hp (u v : ℝ) : (u^(2*j)*v^(2*k))^2=(u^j*v^k)^4 := by
      simp only [mul_pow,←pow_mul]
      congr 1 <;> congr 1 <;> omega
    simp_rw [hp] at HY2
    convert HY2 using 1
    · rfl
    · rw [←pow_mul]
      congr 1
      omega
  have HC:=native_four_saved_moment_scales hA hB hY hscaleA hscaleB hscaleE hscaleY
    HA4' HB4 HE4 HY4
  have HI:=native_two_level_star_incoming_error_product_abs_le_moments n j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center error μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as,je]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
