module

public import ComparisonActualHighOnlySecondLowClassifiedIndexedCloneLedgerLaw
public import ComparisonSignedCavitySecondLowInheritedClassifiedIndexedLayerRate
public import ComparisonActualHighOnlyClassifiedFarCanonicalTransport
public import ComparisonActualHighOnlyLowUnpairedResamplingSourceAlong
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonSignedCavitySecondLowClassifiedIndexedCloneLedgerLaw
public import ComparisonActualHighOnlySecondLowInheritedClassifiedCloneSumBudget
public import ComparisonActualHighOnlySecondLowInheritedCloneProductRate
public import ComparisonSignedCavityWholeLawHolder

@[expose] public section

noncomputable section
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
attribute [local instance] nativeSecondLowSlotFintype

private theorem indexed_original_clone_square_nonneg_high_only (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (cut : ℕ) (q : ℕ→RestCoordinate n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    0 ≤ nativeSecondLowRestCloneSquare n T s cut q P := by
  unfold nativeSecondLowRestCloneSquare
  exact ClockTree.wholeLaw_disorderExpect_nonneg (restWeight_pos n) (restFeature n) _ ho 0 q
    _ (fun _=>sq_nonneg _) 0

theorem eventually_actual_minimum_inherited_second_low_classified_indexed_layer_rate_high_only
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
      ∀(L : ℕ) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U cut : ℕ) (x v zLayer : ℝ)
          (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U → U ≤ cut →
          v ≤ zLayer → zLayer ≤ 2*v → M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀(d : E.source.D.Slot) e,T.splitIndex (E.originalSlot d) (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.R (partitionPoint 0 as cut) →
          M.z ≤ min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,cut ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.R (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          v ≤ partitionPoint 0 as cut →
        let ho : MassOrdered 0 (pre++(mid++tail)):=_hparts ▸ finiteCutMasses_ordered us hus k
        |nativeSecondLowClassifiedIndexedLayer E ho U cut v zLayer q
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))
          (G.canonicalHighOnlySource M forms).restProduct| ≤
          C*(E.source.D.leaves:ℝ)^2*((n:ℝ)^(-eta))^2*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨Cp,Cq,hCp,hCq,H⟩:=eventually_actual_minimum_inherited_second_low_classified_clone_sum_budget_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  let C:=1+24*(a:ℝ)*(1+Temp)^2*Cp^a*Cq^2*(2*C0)^6
  have hC:0 < C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U cut x v zLayer E
    hstar hU hT Hfc Hcz hUcut hvz hzLayer hxsx hxW hv hWmacro hcut
    hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hvmass
  have HM:=hk pre mid tail hparts T G forms initial f c z U cut x v E
    hstar hU hT Hfc Hcz hUcut hxsx hxW hv hWmacro hcut hout hmass hhigh hz hlow
    Hmf Hmz Hrf Hrz hvmass
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  simp only [hparts] at HM ⊢
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let q' : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
  let b:=fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 (pre++(mid++tail)) j)
  let qi:=fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+j)
  let qs:=fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+(mid.length+j))
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q' 0
  let P0:=(G.canonicalHighOnlySource M forms).restProduct
  let F0:=fun d σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M f (E.originalSlot d) σ*
    ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M z (E.originalSlot d) σ
  let p0:=sourceMonomialScale x W initial
  let save:=(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  let sp:=(a:ℝ)*(1+Temp)*(2*save)/x*(Cp^a*p0)
  let sf:=4*(1+Temp)*Cq^2*W*save
  let ell:=(E.source.D.leaves:ℝ)
  let IP:=∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q'
    (fun σ τ=>(P0 σ-P0 τ)^2) r ∂μ
  let IF:=∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q'
    (fun σ τ=>(F0 d σ-F0 d τ)^2) r ∂μ
  let layer:=nativeSecondLowClassifiedIndexedLayer E ho U cut v zLayer q' b h K P0
  have hx:0 < x:=M.hxs.trans_le hxsx
  have hW:0 < W:=hx.trans_le hxW
  have hp0:0 ≤ p0:=by dsimp [p0];unfold sourceMonomialScale;positivity
  have hsave:0 ≤ save:=mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (savedExteriorScale_pos (mul_pos (by positivity) M.hxs) hW hv).le
  have hsp:0 ≤ sp:=by dsimp [sp];positivity
  have hsf:0 ≤ sf:=by dsimp [sf];positivity
  have hell:0 ≤ ell:=Nat.cast_nonneg _
  have HP:IP ≤ ell*sp^2:=by
    convert HM.1 using 1
    dsimp only [sp,save,p0,W,ell]
    ring
  have HF:IF ≤ ell*sf^2:=HM.2
  have HC:pre.length+mid.length < cut:=hstar.trans_le hUcut
  have hIFn:0 ≤ IF:=by
    dsimp only [IF,μ]
    rw [native_second_low_classified_integrated_square_sum_eq_original E ho cut HC]
    exact Finset.sum_nonneg fun d _=>indexed_original_clone_square_nonneg_high_only n T ho
      (E.originalSlot d) cut q' (F0 d)
  let :=nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho 0 q' 0
  have hoTail0:MassOrdered 0 tail:=ho.suffix_end.suffix_end.lower (by norm_num)
    (clockSteps_ordered ho.suffix_end.suffix_end qs).nonneg
  have htailcut:cut-(pre.length+mid.length) ≤ tail.length:=by
    have HH:cut ≤ (pre++(mid++tail)).length:=by simpa only [←hparts] using hcut
    simp only [List.length_append] at HH
    omega
  have HGram:=native_exterior_indexed_virtual_incoming_layer_clone_gram_sq_le_map
    E.source.Ei E.source.Es E.source.D (restWeight_pos n) (restFeature n)
    (cut-(pre.length+mid.length)) ho.suffix_end hoTail0 hv.le htailcut qi qs hvz hzLayer
    (fun η ζ δ=>P0 (E.source.read η ζ δ)) ((E.toWholeCSource ho).twoLow U b h K) μ
    (fun r=>(exteriorForestIRoot r,exteriorForestStarRoot r))
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  dsimp only [qi,qs,b,h] at HGram
  simp_rw [native_second_low_classified_indexed_OLD_ledger_eq_sum E cut q' P0,
    native_second_low_classified_indexed_NEW_ledger_eq_sum_high_only E ho M U cut q' K hstar hU hT Hfc Hcz] at HGram
  change layer^2 ≤ (3*ell*v)^2*IP*IF at HGram
  have Hsquare:layer^2 ≤ (3*ell^2*v*(sp*sf))^2:=by
    calc
      _ ≤ _:=HGram
      _ ≤ (3*ell*v)^2*(ell*sp^2)*IF:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left HP (sq_nonneg _)) hIFn
      _ ≤ (3*ell*v)^2*(ell*sp^2)*(ell*sf^2):=mul_le_mul_of_nonneg_left HF (by positivity)
      _=_:=by ring
  have Habs:|layer| ≤ 3*ell^2*v*(sp*sf):=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using Hsquare)
  apply Habs.trans
  have Hscale:=saved_boundary_layer_flexible_scale_le M.hxs hW hv hxsx hxW hp0
    (by positivity : 0 ≤ 2*C0)
  have Hcoef:0 ≤ 24*(a:ℝ)*(1+Temp)^2*Cp^a*Cq^2*ell^2*((n:ℝ)^(-eta))^2:=by positivity
  calc
    3*ell^2*v*(sp*sf)=
      (24*(a:ℝ)*(1+Temp)^2*Cp^a*Cq^2*ell^2*((n:ℝ)^(-eta))^2)*
        (v*(W*savedExteriorScale ((2*C0)*M.xs) W v)*
          (p0*savedExteriorScale ((2*C0)*M.xs) W v/x)):=by dsimp [sp,sf,save];ring
    _ ≤ (24*(a:ℝ)*(1+Temp)^2*Cp^a*Cq^2*ell^2*((n:ℝ)^(-eta))^2)*
      ((2*C0)^6*(p0*W*M.xs^2)):=mul_le_mul_of_nonneg_left Hscale Hcoef
    _=(C-1)*(ell^2*((n:ℝ)^(-eta))^2*W*M.xs^2*p0):=by dsimp [C];ring
    _ ≤ C*(ell^2*((n:ℝ)^(-eta))^2*W*M.xs^2*p0):=mul_le_mul_of_nonneg_right
      (by linarith : C-1 ≤ C) (by positivity)
    _=_:=by ring

end OAI.SKFluctuations.Cavity
