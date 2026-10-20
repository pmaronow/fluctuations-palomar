module

public import ComparisonSignedCavitySecondLowInheritedObservedAffineSavedRate
public import SKProof.Port.ComparisonActualOriginalQLowB0ObservedAffineCompleteReadoutSourceAlong
public import SKProof.Port.ComparisonActualOriginalQRetainedGammaPhysicalSources
public import SKProof.Port.ComparisonActualOriginalQNearPairedGammaRows
public import SKProof.Port.ComparisonActualOriginalQPairedFarSchedule

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
private theorem low_b0_second_low_inherited_original_fresh_residual
    (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot) (U : ℕ),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → U≤T.splitIndex s e →
          (T.splitIndex s b=pre.length ∨ T.splitIndex s b=pre.length+mid.length) →
        ∀v : ℝ,W≤v → M.sweepRadius (partitionPoint 0 as (T.splitIndex s e))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length))≤v/2 → M.z≤v/2 →
        ∀(Z : T.cavityLeft.Assignment→ℝ) (p : ℝ),0≤p →
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>Z σ^2) 0≤p^2 →
          |nativeOriginalFreshResidual n T s e b 0 (pre.length+mid.length) 0 q 0 Z|≤
            p*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v) := by
  obtain ⟨C,hC,H⟩:=eventually_calibrated_minimum_inherited_star_subtree_projection_fourth_original_q
    Bclock Temp Cf Cmass Ccal hCf hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz Z p hp hZ
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let r:=C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hv : 0 < v:=hW.trans_le hWv
  have hr : 0≤r:=by
    change 0≤C*(n:ℝ)^(-eta)*(M.xs^3/(W*v))
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (div_nonneg (pow_nonneg M.hxs.le _) (mul_nonneg hW.le hv.le))
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hfrac : ((n:ℝ)/(n+1:ℕ))≤1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.le_succ n
  have hfrac4 : ((n:ℝ)/(n+1:ℕ))^4≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)/(n+1:ℕ)) hfrac 4
  have hdrop : ((n:ℝ)/(n+1:ℕ))^4*r^4≤r^4 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac4 (pow_nonneg hr 4)
  have hJ (Dtree : ClockTree (Spin n) tail) (td de : Dtree.Slot) (hne : td≠de)
      (hsplit : pre.length+mid.length+Dtree.splitIndex td de=T.splitIndex s e) :=
    hk pre mid tail hcut hmass Dtree td de hne v hWv (by simpa only [hsplit] using hvr) hlow hz
  rcases hsb with hsb|hsb
  · apply native_original_fresh_moment_bound n pre mid tail T s e b ho 0 q 0
      (native_actual_full_fresh_anchor_with_old_moments n pre mid tail T s e b
        hmid hU hT hsb hse ho 0 q 0) Z hp hr hZ
    intro Dtree td de hne hsplit
    exact (hJ Dtree td de hne hsplit).1.trans hdrop
  · apply native_original_same_fresh_moment_bound n pre mid tail T s e b ho 0 q 0
      (native_actual_full_same_fresh_anchor_with_old_moments n pre mid tail T s e b
        hmid hU hT hsb hse ho 0 q 0) Z hp hr hZ
    intro Dtree td de hne hsplit
    exact (hJ Dtree td de hne hsplit).2.trans hdrop

private theorem low_b0_second_low_inherited_old_low_second_moment
    (a : ℕ) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
        ∀(i j : T.Slot),i≠j→partitionPoint 0 as (T.splitIndex i j)≤Cmass*W→
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (fun σ=>(ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M i j σ*
              (G.canonicalOriginalQSource M f).restProduct σ)^2) 0≤
            (C*W*(C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_original_q
    (a+1) 1 (by omega) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W hxsx hxW hmass i j hij hlow
  have hmass' : ∀e,(G.consLowShape i j hij).sourceLowMass e≤
      Cmass*sourceFactorScale x W (sourceConsInitial initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [G.cons_low_source_mass_zero,source_cons_factor_zero] using hlow
    · simpa only [G.cons_low_source_mass_succ,source_cons_factor_succ] using hmass e
  have Hmoment:=hk T (G.consLowShape i j hij) (Fin.cases .row f)
    (sourceConsInitial initial) x W hxsx hxW hmass'
  simp_rw [ActualNaturalBoundaryShape.canonical_cons_restProduct_original_q] at Hmoment
  norm_num only [Nat.mul_one,sq_abs] at Hmoment
  rw [source_cons_monomial] at Hmoment
  convert Hmoment using 1
  ring

private theorem low_b0_second_low_inherited_canonical_saved_cubic
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot) (U : ℕ),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → U≤T.splitIndex s e →
          (T.splitIndex s b=pre.length ∨ T.splitIndex s b=pre.length+mid.length) →
        ∀v : ℝ,W≤v → M.sweepRadius (partitionPoint 0 as (T.splitIndex s e))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length))≤v/2 → M.z≤v/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(i j : T.Slot),i≠j → partitionPoint 0 (pre++(mid++tail)) (T.splitIndex i j)≤Cmass*W →
        ∀Γ Cg : ℝ,0≤Cg → |Γ|≤Cg*v →
          |Γ*nativeOriginalFreshResidual n T s e b 0 (pre.length+mid.length) 0 q 0
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M i j σ*
              (G.canonicalOriginalQSource M f).restProduct σ)|≤
            Cg*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cr,hCr,HR⟩:=low_b0_second_low_inherited_original_fresh_residual
    Bclock Temp Cf Cmass Ccal hCf hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=low_b0_second_low_inherited_old_low_second_moment
    a Bclock Temp Cf Cmass hTemp hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr*Cp,hCp,mul_pos hCr hCp,?_⟩
  filter_upwards [HR,HP] with n hnR hnP
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnR M hs0 hsxs HS hxs hcompare L us hus hret hmesh,
    hnP M hs0 hsxs HS hxs L us hus hret hmesh] with k hkR hkP
  dsimp only at hkR hkP ⊢
  intro pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz
    G f initial x hxsx hxW hmassG i j hij hmassLow Γ Cg hCg hΓ
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let Z:=fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M i j σ*
    (G.canonicalOriginalQSource M f).restProduct σ
  let p0:=Cp^a*sourceMonomialScale x W initial
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hp0 : 0≤p0:=
    mul_nonneg (pow_nonneg hCp.le _) (mul_nonneg (pow_nonneg (M.hxs.trans_le hxsx).le _) (pow_nonneg hW.le _))
  have hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>Z σ^2) 0≤(Cp*W*p0)^2 := by
    have HK:=hcut.symm ▸ hkP
    have H:=HK T G f initial x W hxsx hxW hmassG i j hij hmassLow
    simpa only [Z,p0,q,hcut] using H
  have Hres:=hkR pre mid tail hcut hmass T s e b U hmid hU hT hse hsb
    v hWv hvr hlow hz Z (Cp*W*p0) (by positivity) hP
  have H:=observed_whole_law_gamma_saved_cubic hCg hCr.le hCp.le
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hp0 M.hxs.le hW (hW.trans_le hWv)
    (le_max_left _ _) hΓ Hres
  simpa only [mul_assoc] using H

private theorem low_b0_second_low_inherited_scalar_gamma_bound
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta<3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(T : ClockTree (Spin n×Bool) as) (U : ℕ),0<U →
        ∀s e : T.Slot,s≠e →
        let v:=M.sweepRadius (partitionPoint 0 as (T.splitIndex s e))
        M.xs≤v → M.z≤v →
        |fullScalarCutGamma T U (nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf as) s e|≤Cg*v := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound_original_q
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg*(1+cu),by positivity,?_⟩
  filter_upwards [HG,eventually_rmin_lt_xs_original_q hm hC0] with n hn hnorigin
  intro M hs0 hsxs HS _hxs L us hus _hret _hmesh
  apply Eventually.of_forall
  intro k
  dsimp only
  intro T U hU s e hse hxv hzv
  let as:=finiteCutMasses us k
  let v:=M.sweepRadius (partitionPoint 0 as (T.splitIndex s e))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have Hgamma:=hn M hs0 hsxs HS as ho T U hU s e hse
  have hv1: v≤1:=(M.R_bounds _).2
  have Hmass:partitionPoint 0 as (T.splitIndex s e)≤cu*v:=by
    have H:=(M.regular v ⟨hzv,hv1⟩).2
    rw [M.R_spec_high (partitionPoint_mem as ho (T.splitIndex s e))
      ((hnorigin M).trans_le hxv)] at H
    exact H
  have Hscale:M.xs+partitionPoint 0 as (T.splitIndex s e)≤(1+cu)*v:=by linarith
  apply Hgamma.trans
  convert mul_le_mul_of_nonneg_left Hscale hCg.le using 1
  ring

private theorem low_b0_second_low_inherited_gamma_canonical_saved_cubic
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot) (U : ℕ),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → U≤T.splitIndex s e →
          (T.splitIndex s b=pre.length ∨ T.splitIndex s b=pre.length+mid.length) →
        ∀v : ℝ,W≤v → M.sweepRadius (partitionPoint 0 as (T.splitIndex s e))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length))≤v/2 → M.z≤v/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(i j : T.Slot),i≠j → partitionPoint 0 (pre++(mid++tail)) (T.splitIndex i j)≤Cmass*W →
          |fullScalarCutGamma T U (nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf as) s e*
            nativeOriginalFreshResidual n T s e b 0 (pre.length+mid.length) 0 q 0
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M i j σ*
              (G.canonicalOriginalQSource M f).restProduct σ)|≤
            C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cp,Cr,hCp,hCr,HR⟩:=low_b0_second_low_inherited_canonical_saved_cubic
    a Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cg,hCg,HG⟩:=low_b0_second_low_inherited_scalar_gamma_bound
    Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cg*Cr,hCp,mul_pos hCg hCr,?_⟩
  filter_upwards [HR,HG] with n hnR hnG
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnR M hs0 hsxs HS hxs hcompare L us hus hret hmesh,
    hnG M hs0 hsxs HS hxs L us hus hret hmesh] with k hkR hkG
  dsimp only at hkR hkG ⊢
  intro pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz
    G f initial x hxsx hxW hmassG i j hij hmassLow
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  by_cases hsame : s=e
  · subst e
    simp only [nativeOriginalFreshResidual_same_zero,mul_zero,abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCg.le hCr.le)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (mul_nonneg hW.le (sq_nonneg M.xs))
        (mul_nonneg (pow_nonneg hCp.le _) (mul_nonneg (pow_nonneg (M.hxs.trans_le hxsx).le _) (pow_nonneg hW.le _))))
  · have HK:=hcut.symm ▸ hkG
    have Hgamma:=HK T U (by omega) s e hsame
      (by simpa only [hcut,hvr] using (le_max_left _ _).trans hWv)
      (by simpa only [hcut,hvr] using (show M.z≤v by have hv:=hW.trans_le hWv;linarith))
    have Hgamma' : |fullScalarCutGamma T U
        (nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k)) s e|≤Cg*v := by
      simpa only [hcut,hvr] using Hgamma
    exact hkR pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz
      G f initial x hxsx hxW hmassG i j hij hmassLow _ Cg hCg.le Hgamma'

private theorem low_b0_second_low_inherited_signed_fresh_high_row_saved_cubic
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (c b fslot : T.Slot)
          (useNew : Bool) (U : ℕ),0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex c b=pre.length ∨ T.splitIndex c b=pre.length+mid.length) →
          T.splitIndex c fslot≤pre.length+mid.length →
          W≤M.sweepRadius (partitionPoint 0 as U) →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length))≤M.sweepRadius (partitionPoint 0 as U)/2 →
          M.z≤M.sweepRadius (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          |nativeCanonicalObservedFreshHighRow_original_q n a M T (pre.length+mid.length) U c b fslot useNew
            G forms q (nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf as)|≤
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=low_b0_second_low_inherited_gamma_canonical_saved_cubic
    a Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,C,hCp,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot useNew U hmid hU hT hcb hcf hWU hstar hz G forms initial x hxsx hxW hmassG
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
  let K:=nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf as
  let B:=C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial))
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hB : 0≤B:=mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (mul_nonneg (mul_nonneg hW.le (sq_nonneg M.xs))
      (mul_nonneg (pow_nonneg hCp.le _) (mul_nonneg (pow_nonneg (M.hxs.trans_le hxsx).le _) (pow_nonneg hW.le _))))
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      |(if U≤p.tree.splitIndex (p.embed c) p.mark then
        fullScalarCutGamma p.tree U K (p.embed c) p.mark*
          nativeOriginalFreshResidual n p.tree (p.embed c) p.mark (p.embed b) 0 (pre.length+mid.length) 0 q 0
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M
              (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
              (G.canonicalOriginalQSource M forms).restProduct (p.restRestrict σ)) else 0)|≤B := by
    split_ifs with hhigh
    · have hhc : U≤p.tree.splitIndex p.mark (p.embed c):=by rwa [p.tree.splitIndex_symm]
      have hSource:=hT.observedHigh (by omega) hU 0 p hp c hhc
      have hsplitb : p.tree.splitIndex (p.embed c) (p.embed b)=pre.length ∨
          p.tree.splitIndex (p.embed c) (p.embed b)=pre.length+mid.length := by
        rw [(T.markedAttach_embed_preserves 0 p hp).2]
        exact hcb
      have hsplitf : p.tree.splitIndex (nativeObservedRemainingTarget c p useNew) (p.embed fslot)=
          T.splitIndex c fslot := by
        cases useNew
        · exact (T.markedAttach_embed_preserves 0 p hp).2 _ _
        · change p.tree.splitIndex p.mark (p.embed fslot)=_
          rw [p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed fslot) hhc (by
            rw [(T.markedAttach_embed_preserves 0 p hp).2];omega)]
          exact (T.markedAttach_embed_preserves 0 p hp).2 _ _
      have hneq : nativeObservedRemainingTarget c p useNew≠p.embed fslot := by
        intro heq
        rw [heq,p.tree.splitIndex_self] at hsplitf
        have hlen:=p.tree.splitIndex_le_clockLength (p.embed c) p.mark
        omega
      have hlowmass : partitionPoint 0 (pre++(mid++tail))
          (p.tree.splitIndex (nativeObservedRemainingTarget c p useNew) (p.embed fslot))≤Cmass*W := by
        rw [hsplitf]
        exact (partitionPoint_mono _ ho hcf).trans (by simpa only [hcut] using hmass)
      have hrad : M.sweepRadius (partitionPoint 0 as U)≤
          M.sweepRadius (partitionPoint 0 as (p.tree.splitIndex (p.embed c) p.mark)) :=
        M.R_monotone (partitionPoint_mono as (finiteCutMasses_ordered us hus k) hhigh)
      have Hrow:=hk pre mid tail hcut hmass p.tree (p.embed c) p.mark (p.embed b) U hmid hU
        hSource hhigh hsplitb _ (hWU.trans hrad) rfl (by linarith) (by linarith)
        (G.retainOnMarked 0 p hp) forms initial x hxsx hxW (fun e=>by
          simpa only [G.retained_source_mass] using hmassG e)
        (nativeObservedRemainingTarget c p useNew) (p.embed fslot) hneq hlowmass
      simpa only [ActualNaturalBoundaryShape.retained_canonical_restProduct_original_q] using Hrow
    · simpa only [abs_zero] using hB
  have Hsum:=marked_list_weight_abs_le (T.markedAttach 0) _ hrow
  rw [T.markedAttach_variation ho,sub_zero] at Hsum
  dsimp only [B,K,q,as,W] at Hsum
  simpa only [nativeCanonicalObservedFreshHighRow_original_q,mul_assoc] using Hsum

theorem eventually_actual_minimum_inherited_second_low_observed_affine_saved_rate_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0<Cp ∧ 0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (c b fslot : T.Slot)
          (useNew : Bool) (U : ℕ),0 < mid.length → pre.length+mid.length<U → U≤as.length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex c b=pre.length ∨ T.splitIndex c b=pre.length+mid.length) →
          T.splitIndex c fslot≤pre.length+mid.length →
          W≤M.sweepRadius (partitionPoint 0 as U) →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length))≤M.sweepRadius (partitionPoint 0 as U)/2 →
          M.z≤M.sweepRadius (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          |nativeCanonicalObservedFreshAffineRow_original_q n a M T (pre.length+mid.length) U c b fslot useNew
            G forms q (nativeSecondLowInheritedSavedMixedClock n M.sweepBf M.sweepHf as)|≤
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=low_b0_second_low_inherited_signed_fresh_high_row_saved_cubic
    a Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,(Temp+1)*C,hCp,mul_pos (by linarith) hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot useNew U hmid hU hlen hT hcb hcf hWU hstar hz G forms initial x hxsx hxW hmassG
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hcbLow : T.splitIndex c b≤pre.length+mid.length := by rcases hcb with Hcb|Hcb <;> omega
  have Hrow:=hk pre mid tail hcut hmass T c b fslot useNew U hmid hU hT hcb hcf hWU hstar hz G forms initial x hxsx hxW hmassG
  rw [native_canonical_observed_fresh_affine_row_eq_high_original_q n a M T ho (pre.length+mid.length) U
      (by simpa only [hcut] using hlen) c b fslot useNew G forms,
    native_canonical_observed_fresh_affine_row_eq_bond_mul_original_q n a M T ho (pre.length+mid.length) U hU
      c b fslot useNew hcbLow G forms,abs_mul]
  have Hbond:=HS _ (partitionPoint_mem (pre++(mid++tail)) ho (T.splitIndex c b))
  have Hbondabs : |(M.sweepBf (partitionPoint 0 (pre++(mid++tail)) (T.splitIndex c b)):ℝ)|≤Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact Hbond.1
  have Hbound:=mul_le_mul Hbondabs Hrow (abs_nonneg _) hTemp
  apply Hbound.trans
  have Hscale : 0≤(2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))*M.xs^2*
        (Cp^a*sourceMonomialScale x (max M.xs (Real.sqrt
          (laplaceComparisonStrength M.data.d M.lam M.xs))) initial)) := by
    have hxspos : 0<M.xs:=M.hxs
    have hxpos : 0<x:=M.hxs.trans_le hxsx
    have hmaxpos : 0 < max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs)):=
      M.hxs.trans_le (le_max_left _ _)
    unfold sourceMonomialScale
    positivity
  have Hextra:=mul_le_mul_of_nonneg_right (show Temp≤Temp+1 by linarith) Hscale
  convert Hextra using 1
  ring

end OAI.SKFluctuations.Cavity
