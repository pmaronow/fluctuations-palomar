module

public import ComparisonSignedCavityActualPowerSourceErrorProductRate
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

theorem inherited_canonical_power_source_error_product_from_same_star
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
    (hsource : ∀n,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualMixedStarProjectionPowersOnEveryFinalNet (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualCanonicalPowerSourceErrorProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth
    (D:=D) Bclock Temp Cf Cmass Ccal hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HZ⟩:=eventually_actual_minimum_inherited_canonical_source_base_eighth
    (D:=D) a Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_minimum_inherited_canonical_source_error_even_bound
    (D:=D) 4 (by decide) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca^2*Ce,mul_pos (sq_pos_of_pos hCa) hCe,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [HA,HZ,HE,Hmixed,hW1] with n hnA hnZ hnE hnY hnW
  have hcan : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan];exact le_max_left _ _
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hsource n) hxs1 (hcompare n) L us hus hret hmesh,
    hnZ (M n) (hsource n) hxs1 L us hus hret hmesh,
    hnE (M n) (hsource n) hxs1 L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrZ hrE hrY
  dsimp only at hrA hrZ hrE hrY ⊢
  rw [←hcan] at hrA
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG b GH s E t hst v hWv hvr hlow hz e₁ e₂ he₁₂ error herror
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
  have HZ8:=hrZ pre mid tail hcut T G forms initial x (W n) hxsx hxW hG b GH s E
  let je:=T.cavityLeft.splitIndex e₁ e₂
  let errorCenter:=orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as je)
  have HE8:=hrE pre mid tail hcut T b GH s e₁ e₂ he₁₂ E error herror
  have HY4:=hrY pre mid tail hcut hindex E.D E.target t
  have hratio : ((n:ℝ)/(n+1:ℕ))^4 ≤ 1:=pow_le_one₀ (by positivity)
    ((div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr (by exact_mod_cast Nat.le_succ n))
  have HA4':=HA4.trans (mul_le_of_le_one_left (by positivity) hratio)
  have hxspos:=(M n).hxs
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have hv : 0 < v:=hW.trans_le hWv
  have hscaleA : 0 ≤ Ca*(n:ℝ)^(-eta)*savedProjectedScale (M n).xs (W n) v := by
    unfold savedProjectedScale
    positivity
  have hscaleZ : 0 ≤ Ch^a*sourceMonomialScale x (W n) initial := by
    unfold sourceMonomialScale
    positivity
  have hscaleY : 0 ≤ (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k) := by positivity
  have hmassE:0 ≤ partitionPoint 0 as je:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) je).1
  have hscaleE:0 ≤ Ce*((M n).xs+partitionPoint 0 as je):=by positivity
  have Hbound:=native_two_level_power_error_product_bound n j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end
    (fun η ζ δ=>(G.canonicalMinimumSource (M n) forms).restProduct (E.read η ζ δ))
    E.target t qi qs center error μ exteriorForestIRoot exteriorForestStarRoot
    departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
    hscaleA hscaleZ hscaleE hscaleY HZ8 HE8 (by
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
