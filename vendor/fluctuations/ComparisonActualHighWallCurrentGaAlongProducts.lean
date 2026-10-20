module

public import ComparisonActualHighWallCanonicalTwoLevelProjection
public import ComparisonActualHighWallCanonicalStarTwoLevelProjection
public import ComparisonActualHighWallCalibratedStarSubtreeProjection
public import ComparisonActualHighWallCanonicalSourceBaseEighth
public import ComparisonActualHighWallSourceErrorMoment
public import ComparisonActualHighWallGammaProductsAlong
public import ComparisonSignedCavityEventuallyInheritedIncomingSourceErrorProductRate
public import ComparisonSignedCavityEventuallyInheritedPowerSourceErrorProductRate
public import ComparisonSignedCavityEventuallyInheritedStarIncomingSourceErrorProductRate
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

theorem eventually_actual_high_wall_canonical_incoming_source_error_product_from_same_star_along (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualHighWallCanonicalIncomingSourceErrorProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_high_wall_canonical_two_level_projection_fourth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_high_wall_canonical_source_error_even_bound
    (D:=D) 2 (by decide) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb*Ce,mul_pos (mul_pos hCa hCb) hCe,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,hdim.eventually HE,Hmixed,hW1] with n hnA hnB hnE hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnB (M n) (hfixed n) L us hus hret hmesh,
    hnE (M n) L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrE hrY
  dsimp only at hrA hrB hrE hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz e₁ e₂ he₁₂ error herror
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
  let je:=T.cavityLeft.splitIndex e₁ e₂
  let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as je)
  have HE4:=hrE pre mid tail hcut T a (G.canonicalHighWallSource (M n) f) s e₁ e₂ he₁₂ E error herror
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
      nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4)
    (fun _ _=>by positivity)
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
  have hmassE:0 ≤ partitionPoint 0 as je:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) je).1
  have hscaleE:0 ≤ Ce*((M n).xs+partitionPoint 0 as je):=by positivity
  have HY4 : nativeRootTestExpect (dim n) E.D qs μ exteriorForestStarRoot
      (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
        nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4) ≤
      (((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k))^4 := by
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
  have HI:=native_two_level_incoming_error_product_abs_le_moments (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center error μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as,je]
  ring

theorem eventually_actual_high_wall_canonical_star_incoming_source_error_product_from_same_star_along (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualHighWallCanonicalStarIncomingSourceErrorProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_high_wall_canonical_star_two_level_projection_fourth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_high_wall_canonical_source_error_even_bound
    (D:=D) 2 (by decide) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb*Ce,mul_pos (mul_pos hCa hCb) hCe,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,hdim.eventually HE,Hmixed,hW1] with n hnA hnB hnE hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnB (M n) (hfixed n) L us hus hret hmesh,
    hnE (M n) L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrB hrE hrY
  dsimp only at hrA hrB hrE hrY ⊢
  rw [←hcan] at hrA hrB
  intro pre mid tail hcut hindex hmass T G f initial x hxsx hxW hG s E e t hst v hWv hvr hlow hz e₁ e₂ he₁₂ error herror
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
  let je:=T.cavityLeft.splitIndex e₁ e₂
  let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as je)
  have HE4:=hrE pre mid tail hcut T a (G.canonicalHighWallSource (M n) f) s e₁ e₂ he₁₂ E error herror
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
      nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4)
    (fun _ _=>by positivity)
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
  have hmassE:0 ≤ partitionPoint 0 as je:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) je).1
  have hscaleE:0 ≤ Ce*((M n).xs+partitionPoint 0 as je):=by positivity
  have HY4 : nativeRootTestExpect (dim n) E.D qs μ exteriorForestStarRoot
      (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ E.target)^j*
        nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (E.D.atSlot σ t)^k)^4) ≤
      (((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k))^4 := by
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
  have HI:=native_two_level_star_incoming_error_product_abs_le_moments (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end E.H e E.target t qi qs center error μ
    exteriorForestIRoot exteriorForestStarRoot departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
  have HF:=HI.trans HC
  convert HF using 1
  dsimp only [as,je]
  ring

theorem eventually_actual_high_wall_canonical_power_source_error_product_from_same_star_along (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong (2*j) (2*k) saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualHighWallCanonicalPowerSourceErrorProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HZ⟩:=eventually_actual_high_wall_canonical_source_base_eighth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_high_wall_canonical_source_error_even_bound
    (D:=D) 4 (by decide) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca^2*Ce,mul_pos (sq_pos_of_pos hCa) hCe,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdim.eventually HA,hdim.eventually HZ,hdim.eventually HE,Hmixed,hW1] with n hnA hnZ hnE hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnZ (M n) (hfixed n) L us hus hret hmesh,
    hnE (M n) L us hus hret hmesh,
    hnY us hus hstar] with r hrA hrZ hrE hrY
  dsimp only at hrA hrZ hrE hrY ⊢
  rw [←hcan] at hrA hrZ
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG b GH s E t hst v hWv hvr hlow hz e₁ e₂ he₁₂ error herror
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
  have hxEq : x=W n:=le_antisymm hxW (by simpa only [hcan,hfixed n] using hxsx)
  have hmassG e : G.sourceLowMass e ≤ Cmass*W n:=by
    simpa only [hxEq,sourceFactorScale,ite_self] using hG e
  have HZ8raw:=hrZ pre mid tail hcut T G forms hmassG b GH s E
  have HZ8 : (∫z,nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight (dim n)) (restFeature (dim n)) qi qs
      (fun η ζ δ=>(G.canonicalHighWallSource (M n) forms).restProduct (E.read η ζ δ)^8)
      (exteriorForestIRoot z) (exteriorForestStarRoot z) ∂μ) ≤
      (Ch^a*sourceMonomialScale x (W n) initial)^8:=by
    rw [hxEq,sourceMonomialScale_self]
    convert HZ8raw using 1; rfl
  let je:=T.cavityLeft.splitIndex e₁ e₂
  let errorCenter:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as je)
  have HE8:=hrE pre mid tail hcut T b GH s e₁ e₂ he₁₂ E error herror
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
  have hmassE:0 ≤ partitionPoint 0 as je:=(partitionPoint_mem as (finiteCutMasses_ordered us hus r) je).1
  have hscaleE:0 ≤ Ce*((M n).xs+partitionPoint 0 as je):=by positivity
  have Hbound:=native_two_level_power_error_product_bound (dim n) j k E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end
    (fun η ζ δ=>(G.canonicalHighWallSource (M n) forms).restProduct (E.read η ζ δ))
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
