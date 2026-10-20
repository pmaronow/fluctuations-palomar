module

public import ComparisonActualHighOnlySecondLowInheritedClassifiedIndexedLayerRate
public import ComparisonSignedCavitySecondLowInheritedClassifiedCovarianceRate
public import ComparisonActualHighOnlyClassifiedFarCanonicalTransport
public import ComparisonActualHighOnlyLowUnpairedResamplingSourceAlong
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonSignedCavitySecondLowClassifiedIndexedCloneLedgerLaw
public import ComparisonActualHighOnlySecondLowInheritedCloneProductRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

 theorem native_second_low_full_two_LOW_payload_eq_canonical_minus_KK_high_only
    (n U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f c z : T.Slot) (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (K : ℕ→ℝ) (σ : T.cavityLeft.Assignment) :
    nativeSecondLowUnweightedCOldPayload n U
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
      K T f c z (fun _=>1) σ=
      ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M f c σ*
        ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M z c σ-
        K (T.splitIndex f c)*K (T.splitIndex c z) := by
  rw [native_unweighted_c_canonical_row_eq_LOW_high_only n U T M f c Hfc,
    native_unweighted_c_canonical_row_eq_LOW_high_only n U T M z c (by rwa [T.splitIndex_symm])]
  unfold nativeSecondLowUnweightedCOldPayload
  simp only [Hfc,Hcz,ite_true,one_mul,T.splitIndex_symm z c]
  have Hsymm (s t : Spin n) (j : ℕ) :
      restLowKernel n U (fun k=>(M.bf (partitionPoint 0 as k):ℝ))
        (fun k=>(M.hf (partitionPoint 0 as k):ℝ)) j s t=
      restLowKernel n U (fun k=>(M.bf (partitionPoint 0 as k):ℝ))
        (fun k=>(M.hf (partitionPoint 0 as k):ℝ)) j t s:=by
    simp only [restLowKernel,mul_comm]
  rw [Hsymm (T.cavityLeft.atSlot σ (T.cavityLeftSlot z))
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)) (T.splitIndex c z)]

 theorem native_second_low_classified_covariance_eq_original_clone_product_high_only
    {n : ℕ} {pre mid tail : List PositiveMass}
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
    {v₀ : RestCoordinate n→ℝ} {q₀ : ℕ→RestCoordinate n→ℝ} {x₀ : RestCoordinate n→ℝ}
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v₀ q₀ x₀)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U cut : ℕ) (hc : pre.length+mid.length < cut)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U) :
    nativeSecondLowClassifiedRetainedCovariance E U cut q
      (fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
      (fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)) K P=
      let p:=nativeCloneBlockAtSlot T c cut
      let F0:=fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M f c σ*
        ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M z c σ
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>(P (p.restOldRestrict σ)-P (p.restNewRestrict σ))*
          (F0 (p.restOldRestrict σ)-F0 (p.restNewRestrict σ))) 0 := by
  unfold nativeSecondLowClassifiedRetainedCovariance
  have HE:=E.source.retained_clone_whole_law (restWeight_pos n) ho E.source.target cut hc 0 q
    (fun σ τ=>(P σ-P τ)*(nativeSecondLowUnweightedCOldPayload n U
      (fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
      (fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)) K T f c z (fun _=>1) σ-
      nativeSecondLowUnweightedCOldPayload n U
      (fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
      (fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)) K T f c z (fun _=>1) τ)) 0
  rw [E.source.embed_target] at HE
  refine (HE.symm.trans (nativeRetainedCloneCut_rest_disorderLaw (restWeight_pos n)
    (restFeature n) T ho c cut 0 q _ 0)).trans ?_
  apply congrArg (fun Q=>(nativeCloneBlockAtSlot T c cut).tree.cavityLeft.disorderExpect
    (restWeight n) (restFeature n) 0 q Q 0)
  funext σ
  rw [native_second_low_full_two_LOW_payload_eq_canonical_minus_KK_high_only n U T M f c z Hfc Hcz K,
    native_second_low_full_two_LOW_payload_eq_canonical_minus_KK_high_only n U T M f c z Hfc Hcz K]
  ring

theorem eventually_actual_minimum_inherited_second_low_classified_covariance_rate_high_only
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U cut : ℕ) (x v : ℝ)
          (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ cut →
          T.splitIndex f c < U → T.splitIndex c z < U →
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀e,T.splitIndex c (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          4*W ≤ M.R (partitionPoint 0 as cut) →
          M.z  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀e,cut ≤ T.splitIndex c (G.j e) →
            M.R (G.sourceLowMass e)  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          M.R (partitionPoint 0 as (T.splitIndex f c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          v ≤ partitionPoint 0 as cut →
        |v*nativeSecondLowClassifiedRetainedCovariance E U cut q
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))
          (G.canonicalHighOnlySource M forms).restProduct| ≤
          C*((n:ℝ)^(-eta))^2*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_clone_product_rate_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U cut x v E
    hstar hUcut Hfc Hcz hxsx hxW hv hWmacro hcut hout hmass Hmf Hmz hhigh hz hlow Hrf Hrz hvmass
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  rw [hparts] at hk
  simp only [hparts] at hcut Hmf Hmz hhigh hz hlow Hrf Hrz hvmass ⊢
  rw [native_second_low_classified_covariance_eq_original_clone_product_high_only E ho M U cut
    (hstar.trans_le hUcut) _ _ _ Hfc Hcz]
  exact hk T G forms initial f c z cut x v hxsx hxW hv hWmacro hcut
    (by rw [T.splitIndex_symm];exact Hfc.trans_le hUcut) (Hcz.trans_le hUcut)
    hout hmass Hmf Hmz hhigh hz hlow Hrf Hrz hvmass

end OAI.SKFluctuations.Cavity
