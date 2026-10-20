module

public import ComparisonActualHighWallCanonicalTwoLevelProjection
public import ComparisonActualHighWallCanonicalStarTwoLevelProjection
public import ComparisonActualHighWallCalibratedStarSubtreeProjection
public import ComparisonActualHighWallStarProjectionPowersAlong
public import ComparisonActualHighWallCanonicalExteriorMoments
public import ComparisonSignedCavityInheritedGammaAlongProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
variable {dim : ℕ → ℕ}

def ActualHighWallCanonicalIncomingProductOnEveryFinalNetAlong
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelIncomingProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_actual_high_wall_canonical_incoming_product_from_same_star_along
    (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualHighWallCanonicalIncomingProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_high_wall_canonical_two_level_projection_fourth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb,mul_pos hCa hCb,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,Hmixed,hW1]
    with n hnA hnB hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnB (M n) (hfixed n) L us hus hret hmesh,
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

def ActualHighWallCanonicalStarIncomingProductOnEveryFinalNetAlong
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelStarIncomingProduct (dim n) j k E.Ei E.Es E.D E.H e E.target t qi qs center
          (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as (pre.length+mid.length))*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_actual_high_wall_canonical_star_incoming_product_from_same_star_along
    (hdim : Tendsto dim atTop atTop)
    (a j k : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta saving cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
      ActualHighWallCanonicalStarIncomingProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cb,hCb,Ch,hCh,HB⟩:=eventually_actual_high_wall_canonical_star_two_level_projection_fourth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Ca*Cb,mul_pos hCa hCb,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HA,hdim.eventually HB,Hmixed,hW1]
    with n hnA hnB hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnB (M n) (hfixed n) L us hus hret hmesh,
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

def ActualHighWallCanonicalPowerProductOnEveryFinalNetAlong
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
        let qi:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+l)
        let qs:=nativeStarSuffixClock (dim n) pre mid q
        |∫z,nativeTwoLevelPowerProduct (dim n) j k E.Ei E.Es E.D
          (fun η ζ δ=>(G.canonicalHighWallSource (M n) forms).restProduct (E.read η ζ δ))
          E.target t qi qs center (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0| ≤
          Cp*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem eventually_actual_high_wall_canonical_power_product_from_same_star_along
    (hdim : Tendsto dim atTop atTop)
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
      ActualHighWallCanonicalPowerProductOnEveryFinalNetAlong a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (D:=D) Bclock Cmass hCm hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HZ⟩:=eventually_actual_high_wall_canonical_source_base_fourth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ca^2,sq_pos_of_pos hCa,Ch,hCh,?_⟩
  have hW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdim.eventually HA,hdim.eventually HZ,Hmixed,hW1]
    with n hnA hnZ hnY hnW
  have hcan : W n=(M n).data.d:=hcanonical n
  have hxsW : (M n).xs ≤ W n:=by rw [hcan,hfixed n]
  have hxs1 : (M n).xs ≤ 1:=hxsW.trans hnW
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hret hmesh hstar
  filter_upwards [hnA (M n) (hfixed n) L us hus hret hmesh,
    hnZ (M n) (hfixed n) L us hus hret hmesh,
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
  have hxEq : x=(M n).data.d:=by
    rw [hfixed n] at hxsx
    rw [hcanonical n] at hxW
    exact le_antisymm hxW hxsx
  have hmassD e : G.sourceLowMass e≤Cmass*(M n).data.d:=by
    simpa only [hxEq,hcanonical n,sourceFactorScale,ite_self] using hG e
  have HZ4:=hrZ pre mid tail hcut T G forms hmassD b GH s E
  have Hscale : sourceMonomialScale x (W n) initial=(M n).data.d^a:=by
    rw [hxEq,hcanonical n,sourceMonomialScale_self]
  rw [←Hscale] at HZ4
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
    (fun η ζ δ=>(G.canonicalHighWallSource (M n) forms).restProduct (E.read η ζ δ))
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
