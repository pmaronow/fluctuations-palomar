module

public import ComparisonSignedCavityInheritedPairedGammaHighSecondWorkingUniformRow
public import ComparisonSignedCavityInheritedGammaHighSecondBoundedDegree

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_generated_paired_gamma_high_second_row_working_scale
    (a rBound : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(x : ℝ),M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (P : NativeGeneratedTest T)
          (i star U : ℕ),NativeGeneratedTestAncestry i star P → P.edges.length=a →
          i ≤ star → star < U → U ≤ as.length →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        ∀(p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree),
          p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0 → p.tree.leaves ≤ rBound →
          U ≤ p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark →
          p.mark≠p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target) →
        let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
        let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |fullScalarCutGamma p.tree U K (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark*
          nativeRestPayloadHighSecondIntegral n q U b h K p.tree
            (nativeRestProjectedPairedTest T P.target star A (nativeRestGeneratedTestValue T P A center) p)| ≤
          C*sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)*W^2*
            (p.tree.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_paired_gamma_high_second_uniform_row_working_scale
    (D:=D) a rBound ha Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hsource hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro x hxsx hxW T P i star U hP hdegree hi hs hlen hmacroW hsmall hmi hms p hp hleaves hhigh hne
  subst a
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot T 0 P.target star
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  let GP:=nativeFreshObservedShape G P.target star p hp
  let js:=nativeFreshObservedReplacementSlots G P.target star p
  let Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
  have Hspl:=native_fresh_observed_endpoint_splits T P.target hs hlen p hp hhigh
  have Hmass l : GP.sourceLowMass l ≤ Cmass*sourceFactorScale x
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs)))
      (nativeGeneratedCompleteInitial P i) l := by
    dsimp only [GP,nativeFreshObservedShape]
    rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass n P hP hi (hs.trans_le hlen) _ _ _ hmi hms l
  have HH:=hk U (by omega) x hxsx hxW p.tree GP (fun _=>NativeSourceFactorForm.centered)
    (nativeGeneratedCompleteInitial P i) hleaves hmacroW hsmall Hmass js Hgeom.2.1 Hgeom.2.2.1
    (p.embed g.mark) p.mark (p.embed (g.embed P.target)) hne
    (Hspl.1.trans Hspl.2.symm)
    (by rw [Hspl.1,p.tree.splitIndex_symm];exact hs.trans_le hhigh)
    (by rw [Hspl.1];exact hms)
    (by
      intro l hl
      rw [Hgeom.2.2.2 l hl]
      exact p.tree.splitIndex_symm _ _)
  have HE:=funext (native_generated_paired_source_eq_endpoint_retarget P hP hi hs hlen p hp hhigh M)
  rw [HE,fullScalarCutGamma_symm p.tree _ _ (p.embed (g.embed P.target)) p.mark]
  exact HH

theorem eventually_actual_minimum_inherited_generated_Gamma_high_second_profile_working_scale
    (a rBound : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.canonicalDirectTestBandScale
        ∀(x : ℝ),M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length=a →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
        let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A
          (nativeRestGeneratedTestValue T P₀.live.test A center)| ≤
          C*sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_generated_paired_gamma_high_second_row_working_scale
    (D:=D) a (rBound+2) ha Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  let Cfinal:=(C/2)*(4*((rBound:ℝ)+1)+1)+1
  have hCfinal : 0 < Cfinal:=by dsimp only [Cfinal];positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hsource hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro x hxsx hxW T i star U kGen seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
    (4*Cf+2*Temp) Temp
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let P:=nativeRestGeneratedTestValue T P₀.live.test A center
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  let E:=fun p : MarkedPlacement g.tree=>fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
    nativeRestPayloadHighSecondIntegral n q U b h K p.tree
      (nativeRestProjectedPairedTest T P₀.live.test.target star A P p)
  let B:=C*sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs.trans_le hxsx
  have hW:=M.canonical_direct_test_band_pos
  have hB : 0 ≤ B:=by
    dsimp only [B,sourceMonomialScale]
    positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hlo j (hj : j<U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HE p (hp : p∈g.tree.markedAttach 0) : |E p| ≤ B*(p.tree.forkCost R+edgeBudget 0 as R) := by
    have hcost:=mul_nonneg hB (add_nonneg (p.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR))
    by_cases hhigh : U ≤ p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark
    · by_cases hne : p.mark≠p.embed (g.embed P₀.live.test.target)
      · have HG:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P₀.live.test.target star)
        have HP:=g.tree.markedAttach_leaves 0 p hp
        exact hk x hxsx hxW T P₀.live.test i star U P₀.live.ancestry hdegree hi hs hlen
          hmacroW hsmall hmi hms p hp (by omega) hhigh hne
      · have hself:=not_ne_iff.mp hne
        dsimp only [E]
        rw [native_rest_projected_paired_self_zero T _ star A P p hself,
          actual_minimum_rest_payload_high_second_integral_zero M p.tree ho U,mul_zero,abs_zero]
        exact hcost
    · dsimp only [E]
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hlen (lt_of_not_ge hhigh),zero_mul,abs_zero]
      exact hcost
  have Hsum:=native_paired_current_rows_high_profile_le T ho P₀.live.test.target hs hT R hR hlo E hB HE
  rw [actual_minimum_generated_Gamma_high_second_eq_paired_source M hP hi hs ho A P]
  have Hrow : |(1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*E p)).sum| ≤
      (C/2*(4*((rBound:ℝ)+1)+1))*
        sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2*
          (T.forkCost R+edgeBudget 0 as R) := by
    convert Hsum using 1
    dsimp only [B]
    ring
  have hscale : 0 ≤ sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i) := by
    unfold sourceMonomialScale
    positivity
  have Hprice : C/2*(4*((rBound:ℝ)+1)+1) ≤ Cfinal := by dsimp only [Cfinal];linarith
  have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Hprice hscale) (sq_nonneg W))
    (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR))
  have Hfinal:=Hrow.trans HC
  simpa only [E,g,K,q,b,h,W,R,as,mul_assoc] using Hfinal

theorem eventually_actual_minimum_inherited_generated_high_second_bounded_degree_working_scale
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let W:=M.canonicalDirectTestBandScale
        ∀(x : ℝ),M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |nativeActualGeneratedHighSecond M T star U P₀.live.test| ≤
          C*sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  classical
  have Hchoose (j : Fin degree):=eventually_actual_minimum_inherited_generated_Gamma_high_second_profile_working_scale
    (D:=D) (j.val+1) rBound (by omega) Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  choose Cs hCs H using Hchoose
  let C:=1+∑j : Fin degree,Cs j
  have hsum : 0 ≤ ∑j : Fin degree,Cs j:=Finset.sum_nonneg (fun j _=>(hCs j).le)
  have hC : 0 < C:=by dsimp only [C];linarith
  have hCj j : Cs j ≤ C := by
    have Hj:=Finset.single_le_sum (s:=Finset.univ) (f:=Cs) (fun k _=>(hCs k).le) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr H] with n hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun j : Fin degree=>hn j M hsource hxs hcompare L us hus hret hmesh)] with k hk
  dsimp only at hk ⊢
  intro x hxsx hxW T i star U kGen seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf (finiteCutMasses us k)
    (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs.trans_le hxsx
  have hW:=M.canonical_direct_test_band_pos
  have hscale : 0 ≤ sourceMonomialScale x W (nativeGeneratedCompleteInitial P₀.live.test i) := by
    unfold sourceMonomialScale
    positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  by_cases hzero : P₀.live.test.edges.length=0
  · rw [actual_minimum_generated_high_second_empty_live M hP hi hs ho (List.length_eq_zero_iff.mp hzero),abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hscale) (sq_nonneg W)) hcost
  · let j : Fin degree:=⟨P₀.live.test.edges.length-1,by omega⟩
    have Hrow:=hk j x hxsx hxW T i star U kGen seed P₀ hP (by dsimp only [j];omega)
      hi hs hlen hT hmacroW hsmall hmi hms
    have HC:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCj j) hscale) (sq_nonneg W)) hcost
    apply le_trans _ HC
    convert Hrow using 1
    dsimp only [nativeActualGeneratedHighSecond,nativePhysicalResourceCenter,W,R]
    rfl

end OAI.SKFluctuations.Cavity
