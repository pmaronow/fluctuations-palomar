module

public import ComparisonSignedCavityInitialInheritedAllDegreeMoment
public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavitySecondLowOriginalCanonicalTransport
public import ComparisonSignedCavityInheritedRawLowAtomBudget
public import ComparisonSignedCavitySecondLowInheritedRawAtomBudget
public import ComparisonSignedCavitySecondLowInheritedErrorWordBudgets
public import ComparisonSignedCavitySecondLowSoleRootTargetCutSource
public import ComparisonSignedCavitySecondLowTargetFixedErrorBudget
public import ComparisonSignedCavitySecondLowInheritedMovingLiteralEntryBudget
public import ComparisonSignedCavitySecondLowActualSoleRootTargetB0Budget
public import ComparisonSignedCavitySecondLowSoleRootTargetDensityIntegral
public import ComparisonSignedCavitySecondLowActualSoleRootTargetIntegralBudget
public import ComparisonActualHighOnlyOriginalTargetReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 44000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

private theorem high_only_sole_root_abs_add_four (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d| :=
  (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

theorem eventually_actual_minimum_inherited_canonical_continuum_even_all_degree_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0≤Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighOnlySource M forms).product σ|^(2*dOrder)) 0≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale x W initial)^(2*dOrder) := by
  by_cases ha : 0<aDegree
  · exact eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
      (D:=D) aDegree dOrder rBound ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt
  · have hz : aDegree=0:=by omega
    subst aDegree
    refine ⟨1,by norm_num,Filter.Eventually.of_forall (fun n=>?_)⟩
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    refine Filter.Eventually.of_forall (fun jGrid=>?_)
    dsimp only
    intro U T l t hl ht hT G forms initial x W hxsx hxW hmass
    have ho : MassOrdered 0 (finiteCutMasses us jGrid):=finiteCutMasses_ordered us hus jGrid
    have Hp0 : sourceMonomialScale x W initial=1 := by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    simp_rw [native_canonical_source_zero_degree_product_high_only]
    simp only [abs_one,one_pow,pow_zero,mul_one,Hp0]
    rw [T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
    apply one_le_pow₀
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _)
      (by positivity)

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem retained_canonical_restProduct_high_only {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) (σ : p.tree.cavityLeft.Assignment) :
    ((G.retainOnMarked r p hp).canonicalHighOnlySource M f).restProduct σ=
      (G.canonicalHighOnlySource M f).restProduct (p.restRestrict σ) := by
  rw [←(G.canonicalHighOnlySource M f).retained_restProduct r p hp σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalHighOnlySource,retainOnMarked,sourceLowMass,
    (T.markedAttach_embed_preserves r p hp).2]

end ActualNaturalBoundaryShape

theorem native_second_low_canonical_old_shape_rest_product_high_only
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n × Bool) as}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a → NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) (τ : t.tree.cavityLeft.Assignment) :
    ((nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht).canonicalHighOnlySource M forms).restProduct τ =
      nativeSecondLowOldTest (G.canonicalHighOnlySource M forms).restProduct p r s t τ := by
  simp only [nativeSecondLowCanonicalOldShape,ActualNaturalBoundaryShape.retained_canonical_restProduct_high_only,
    nativeSecondLowOldTest]

theorem eventually_actual_minimum_inherited_raw_low_atom_budget_high_only
    (aDegree aRows rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp Cr : ℝ,0<Cp ∧ 0<Cr ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<U →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,s i≠w i) →
          let p0:=sourceMonomialScale x W initial
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*p0
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            C*d*(∏i,r i) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_even_all_degree_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,hCp,hCr,?_⟩
  filter_upwards [HP,HR] with n hnP hnR
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnR M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridP hgridR
  dsimp only at hgridP hgridR ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hmass
    u z huz site v s w hv hne
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  let r:=fun e=>nativeSmallCutOrdinaryScale M.xs Cr as (site e) (T.splitIndex (s e) (w e))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le)
  have Hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hne : u≠z:=by
    intro H
    rw [H,T.splitIndex_self] at huz
    omega
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|(G.canonicalHighOnlySource M forms).product σ|^4) 0≤C^4:=
    hgridP U T l t hl ht hT G forms initial x W hxsx hxW hmass
  have Herror : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K) (T.splitIndex u z)
        (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) 0≤d^2:=by
    rw [native_small_cut_old_error_eq_original_profile]
    change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z)≤d^2
    rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
    apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_high_only M Temp Cf hTemp hCf hsource hxs
      ho U hl ht (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
    rw [ite_eq_left huz] at H
    exact H
  have HE e : (ClockTree.pairClock as (T.splitIndex (s e) (w e))).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))
        (T.splitIndex (s e) (w e)) (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).1
        (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).2|^(4*(aRows+1))) 0≤(r e)^(4*(aRows+1)):=by
    cases hsite : site e
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,Bool.false_eq_true,ite_false]
      rw [native_small_cut_moving_kernel_eq_original_profile]
      simpa only [←Nat.mul_assoc,law,q,b,h,S,K,as] using
        hgridR U l t (v e) hl ht (hv e) (T.splitIndex (s e) (w e)) (T.splitIndex_le_clockLength _ _)
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,ite_true,native_small_cut_site_row_abs_one,one_pow]
      exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
  have H:=ClockTree.native_initial_observed_error_product_abs_le (fullWeight_pos n) (fullFeature n) T ho
    0 law 0 (G.canonicalHighOnlySource M forms).product HC Hd HPmoment
    (nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K)) u z Hne Herror
    (fun e=>nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))) s w hne
    r (fun e=>native_small_cut_ordinary_scale_pos M.hxs hCr ho (site e) _) HE
  change |T.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) u z
      (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0|≤C*d*(∏e,r e)
  unfold nativeOldInitialRowProduct
  simp_rw [(G.canonicalHighOnlySource M forms).product_eq_restProduct] at H
  exact H

theorem eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<U →
        ∀(s0 w0 s1 w1 : T.Slot) (vOrd : ℝ),
          T.splitIndex s0 w0<U → s0≠w0 → s1≠w1 → vOrd∈Icc (0:ℝ) 1 →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![vOrd,0] i))
              ![s0,s1] ![w0,w1]) 0|≤C*d*(M.xs+partitionPoint 0 as (T.splitIndex s0 w0))*p0 := by
  obtain ⟨Cp,Cr,hCp,hCr,HD⟩:=
    eventually_actual_minimum_inherited_raw_low_atom_budget_high_only (D:=D)
      aDegree 2 rBound Bclock Temp Cf Cmass hTemp hCf hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let A:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree
  let C:=A*Cr
  have hA : 0<A:=by dsimp [A];positivity
  refine ⟨C,mul_pos hA hCr,?_⟩
  filter_upwards [HD] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hmass
    u z huz s0 w0 s1 w1 vOrd hsmall hne0 hne1 hvOrd
  let as:=finiteCutMasses us jGrid
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hv : ∀i : Fin 2, (![vOrd,0] i)∈Icc (0:ℝ) 1:=by
    intro i
    fin_cases i
    · change vOrd∈Icc (0:ℝ) 1
      exact hvOrd
    · change (0:ℝ)∈Icc (0:ℝ) 1
      exact ⟨le_rfl,zero_le_one⟩
  have hne : ∀i : Fin 2, (![s0,s1] i)≠(![w0,w1] i):=by
    intro i
    fin_cases i
    · change s0≠w0
      exact hne0
    · change s1≠w1
      exact hne1
  have HR:=hgrid U T l t hU hl ht hT G forms initial x W hxsx hxW hmass
    u z huz (![false,true]) (![vOrd,0]) (![s0,s1]) (![w0,w1]) hv hne
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    nativeSmallCutOrdinaryScale,Bool.false_eq_true,ite_false,ite_true,mul_one] at HR
  apply HR.trans
  change A*p0*d*(Cr*(M.xs+partitionPoint 0 as (T.splitIndex s0 w0)))≤_
  apply le_of_eq
  dsimp [C]
  ring

theorem eventually_actual_minimum_inherited_second_low_error_word_budgets_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),
          U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
        ∀(r : MarkedPlacement p.tree),r∈p.tree.markedAttach 0 →
        ∀(s : MarkedPlacement r.tree),s∈r.tree.markedAttach 0 →
        ∀(t : MarkedPlacement s.tree),t∈s.tree.markedAttach 0 →
          r.tree.splitIndex (r.embed p.mark) r.mark<U →
          t.tree.splitIndex (t.embed s.mark) t.mark<U →
          let p0:=sourceMonomialScale x W initial
          (|nativeSecondLowFirstErrorWord n q U b h K (G.canonicalHighOnlySource M forms).restProduct a z p r s t|≤
            C*(actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+1/(n+1:ℕ)))*
              (M.xs+partitionPoint 0 as (t.tree.splitIndex (t.embed s.mark) t.mark))*p0) ∧
          (|nativeSecondLowSecondErrorWord n q U b h K (G.canonicalHighOnlySource M forms).restProduct a z p r s t|≤
            C*(actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+1/(n+1:ℕ)))*
              (M.xs+partitionPoint 0 as (r.tree.splitIndex (r.embed p.mark) r.mark))*p0) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget_high_only
    (D:=D) aDegree (rBound+4) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hmass a z haz
    p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let Gfinal:=nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht
  let af:=t.embed (s.embed (r.embed (p.embed a)))
  let zf:=t.embed (s.embed (r.embed (p.embed z)))
  let f:=t.embed (s.embed (r.embed p.mark))
  let c:=t.embed (s.embed r.mark)
  let e:=t.embed s.mark
  let d:=t.mark
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hfinal : t.tree.leaves≤rBound+4:=
    (native_second_low_four_mark_leaves_le p hp r hr s hs t ht).trans (by omega)
  have hfinalmass : ∀i,Gfinal.sourceLowMass i≤Cmass*sourceFactorScale x W initial i:=by
    intro i
    rw [native_second_low_canonical_old_shape_source_mass]
    exact hmass i
  have Hfc : t.tree.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    dsimp only [f,c]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  have Hf : t.tree.splitIndex f c<U:=by rw [Hfc];exact Hfirst
  have He : t.tree.splitIndex e d<U:=Hsecond
  have Ha : t.tree.splitIndex af zf<U:=by
    dsimp only [af,zf]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have Hne (u v : t.tree.Slot) (H : t.tree.splitIndex u v<U) : u≠v:=by
    intro HH
    rw [HH,t.tree.splitIndex_self] at H
    omega
  have Hfn : f≠c:=Hne f c Hf
  have Hen : e≠d:=Hne e d He
  have Han : af≠zf:=Hne af zf Ha
  have hzero : (0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have hone : (1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
  have Bfirst:=hgrid U t.tree 0 0 hU hzero hzero hfinal
    Gfinal forms initial x W hxsx hxW hfinalmass f c Hf e d af zf 1 He Hen Han hone
  have Bsecond:=hgrid U t.tree 0 0 hU hzero hzero hfinal
    Gfinal forms initial x W hxsx hxW hfinalmass e d He f c af zf 0 Hf Hfn Han hzero
  have HP : (Gfinal.canonicalHighOnlySource M forms).restProduct=
      nativeSecondLowOldTest (G.canonicalHighOnlySource M forms).restProduct p r s t:=by
    funext τ
    exact native_second_low_canonical_old_shape_rest_product_high_only M G forms p hp r hr s hs t ht τ
  rw [HP] at Bfirst Bsecond
  rw [Hfc] at Bfirst Bsecond
  exact ⟨Bfirst,Bsecond⟩

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_cut_error_words_high_only
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),U≤as.length → i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀(p : MarkedPlacement g.tree),p∈g.tree.markedAttach 0 →
        ∀(r : MarkedPlacement p.tree),r∈p.tree.markedAttach 0 →
        ∀(s : MarkedPlacement r.tree),s∈r.tree.markedAttach 0 →
        ∀(t : MarkedPlacement s.tree),t∈s.tree.markedAttach 0 →
          r.tree.splitIndex (r.embed p.mark) r.mark<U → t.tree.splitIndex (t.embed s.mark) t.mark<U →
          (|nativeSecondLowFirstErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t|≤
            C*x*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+1/(n+1:ℕ))) ∧
          (|nativeSecondLowSecondErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t|≤
            C*x*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+1/(n+1:ℕ))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_error_word_budgets_high_only
    (D:=D) 0 2 Bclock Temp Cf 0 hTemp hCf le_rfl hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C*(1+Couter),mul_pos hC (by linarith),?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U x hU hi hxsx _hxW houter p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let G:=nativeSecondLowEmptyOldShape n g.tree
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have Hmass : ∀e,G.sourceLowMass e≤(0:ℝ)*sourceFactorScale x x (∅ : Finset (Fin 0)) e:=by
    intro e
    exact Fin.elim0 e
  have Hproduct : (G.canonicalHighOnlySource M forms).restProduct=(fun _=>1):=by
    funext τ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have Htarget : g.tree.splitIndex (g.embed (singleSlot as)) g.mark<U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hi
  have HB:=hk U g.tree hU Hleaves G forms ∅ x x hxsx le_rfl Hmass (g.embed (singleSlot as)) g.mark Htarget
    p hp r hr s hs t ht Hfirst Hsecond
  rw [Hproduct] at HB
  have Hscale : sourceMonomialScale x x (∅ : Finset (Fin 0))=1:=by
    simp only [sourceMonomialScale,Finset.card_empty,Nat.sub_self,pow_zero,mul_one]
  rw [Hscale,mul_one,mul_one] at HB
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HCerr : 0≤actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp:=
    actualLowErrorComparisonConstant_nonneg _ hTemp
  have Hother (j : ℕ) (hj : j<U) : M.xs+partitionPoint 0 as j≤(1+Couter)*x:=by
    have HM:=(partitionPoint_mono as ho hj.le).trans houter
    nlinarith only [HM,hxsx]
  have HR (j : ℕ) : 0≤nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ):=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  constructor
  · apply HB.1.trans
    have HH:=mul_le_mul_of_nonneg_left (Hother _ Hsecond)
      (mul_nonneg hC.le (mul_nonneg HCerr (HR (r.tree.splitIndex (r.embed p.mark) r.mark))))
    convert HH using 1
    ring
  · apply HB.2.trans
    have HH:=mul_le_mul_of_nonneg_left (Hother _ Hfirst)
      (mul_nonneg hC.le (mul_nonneg HCerr (HR (t.tree.splitIndex (t.embed s.mark) t.mark))))
    convert HH using 1
    ring

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_fixed_error_budget_high_only
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ) (hU : U≤as.length),i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀(j : Fin 8) (firstError : Bool),
          |nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
            (g.embed (singleSlot as)) g.mark j firstError/2|≤
            C*x^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_cut_error_words_high_only
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨480*(1+Couter)*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U x hU hi hxsx hxW houter j firstError
  let as:=finiteCutMasses us k
  let b:=fun l=>(M.bf (partitionPoint 0 as l):ℝ)
  let h:=fun l=>(M.hf (partitionPoint 0 as l):ℝ)
  let K:=fun l=>h l+b l*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as l)
  let q : ℕ→RestCoordinate n→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let F:=nativeSecondLowFixedErrorUnobservedWord n q i U b h K hU (fun _=>1)
    (g.embed (singleSlot as)) g.mark j firstError
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Drow:=C*x*Cerr*di
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hDrow : 0≤Drow:=by dsimp [Drow];positivity
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have HF : ∀p∈g.tree.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t|≤Drow := by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
    split_ifs with Hindex _Hpath
    · by_cases Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark<U
      · by_cases Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark<U
        · have HB:=hk i U x hU hi hxsx hxW houter p hp r hr s hs t ht Hfirst Hsecond
          cases firstError
          · simp only [nativeSecondLowErrorCut,Bool.false_eq_true,ite_false] at Hindex
            rw [Hindex] at HB
            exact HB.2
          · simp only [nativeSecondLowErrorCut,ite_true] at Hindex
            rw [Hindex] at HB
            exact HB.1
        · rw [native_second_low_error_word_zero_second_high n q U b h K (fun _=>1)
            (g.embed (singleSlot as)) g.mark firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using hDrow
      · rw [native_second_low_error_word_zero_first_high n q U b h K (fun _=>1)
          (g.embed (singleSlot as)) g.mark firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using hDrow
    · simpa only [abs_zero] using hDrow
    · simpa only [abs_zero] using hDrow
  have HE:=native_second_low_entry_four_average_abs_le g.tree U hU ho Hleaves
    (nativeSecondLowFirstMiddleIsFirst j) F hDrow HF
  rw [←native_second_low_fixed_error_unobserved_class_eq_entry n q i U b h K g.tree hU (fun _=>1)
    (g.embed (singleSlot as)) g.mark j firstError] at HE
  have Hpos : 0≤480*partitionPoint 0 as U*Drow:=by
    have HM:=(partitionPoint_mem as ho U).1
    positivity
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤(480*partitionPoint 0 as U*Drow)/2:=by
      have HH:=div_le_div_of_nonneg_right HE (by norm_num : (0:ℝ)≤2)
      norm_num only [Nat.cast_ofNat] at HH
      convert HH using 1
    _≤480*partitionPoint 0 as U*Drow:=by nlinarith
    _≤480*(Couter*x)*Drow:=by gcongr
    _≤480*((1+Couter)*x)*Drow:=by gcongr;linarith
    _=_:=by dsimp [Drow,di,Cerr];ring

theorem eventually_actual_minimum_inherited_second_low_unobserved_moving_literal_entry_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCouter : 0 ≤ Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length),
          i ≤ star → star<U → NativePersistentLowForks i star U T →
          T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as U ≤ Couter*W →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(j : Fin 8) (firstError : Bool),
          let p0:=sourceMonomialScale x W initial
          let density:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i star U
          |nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T
            hU (G.canonicalHighOnlySource M forms).restProduct a z j firstError/2| ≤ C*W*actualLowErrorComparisonConstant Mclock Temp*density*p0 := by
  obtain ⟨Cword,hCword,HW⟩:=eventually_actual_minimum_inherited_second_low_error_word_budgets_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Poly:ℝ:=(rBound+1)*(rBound+2)*(rBound+3)
  let C:=Poly*Cword*(1+Couter)
  have hPoly:0<Poly:=by dsimp [Poly];positivity
  have hC:0<C:=mul_pos (mul_pos hPoly hCword) (by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [HW] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i star U T hU hi hstar hpersistent hT G forms initial x W hxsx hxW hmass houter
    a z haz j firstError
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let rho:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i star U
  let f:=nativeSecondLowMovingOriginalEntryRadius n M.bf M.hf as i star U
  let anchor:=nativeSecondLowErrorEntryAnchor a z j firstError
  let F:=nativeSecondLowMovingErrorUnobservedWord n q i star U b h K hU
    (G.canonicalHighOnlySource M forms).restProduct a z j firstError
  let Drow:=Cword*(1+Couter)*W*actualLowErrorComparisonConstant Mclock Temp*p0
  have hp0:0 ≤ p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have HCerr:0 ≤ actualLowErrorComparisonConstant Mclock Temp:=actualLowErrorComparisonConstant_nonneg Mclock hTemp
  have hW:0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hDrow:0 ≤ Drow:=by dsimp [Drow];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hf:∀k,0 ≤ f k:=by
    intro k
    dsimp [f,nativeSecondLowMovingOriginalEntryRadius]
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have HDensity:=native_second_low_unobserved_varying_entry_le_literal_density n M.bf M.hf as i star U T ho hU hpersistent anchor
  have hrho:0 ≤ rho:=by
    have Hsum:0 ≤ ((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| *
        f (p.tree.splitIndex (p.embed anchor) p.mark))).sum:=by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨p,_hp,rfl⟩:=List.mem_map.mp hx
      exact mul_nonneg (abs_nonneg _) (hf _)
    exact Hsum.trans HDensity
  have Hother (k : ℕ) (hk : k<U):M.xs+partitionPoint 0 as k ≤ (1+Couter)*W:=by
    have Hmass:partitionPoint 0 as k ≤ Couter*W:=(partitionPoint_mono as ho hk.le).trans houter
    nlinarith only [Hmass,hxsx,hxW]
  have HF:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,
        |F p r s t| ≤ Drow*f (nativeSecondLowEntryDepartureCut anchor j p r):=by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowMovingErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
    split_ifs with Hmoving Hpath
    · by_cases Hfirst:r.tree.splitIndex (r.embed p.mark) r.mark<U
      · by_cases Hsecond:t.tree.splitIndex (t.embed s.mark) t.mark<U
        · let k:=nativeSecondLowErrorCut firstError p r s t
          have hk:k<U:=by
            cases firstError
            · exact Hsecond
            · exact Hfirst
          have HE:=native_second_low_original_error_cut_eq_entry_departure T U hU a z j firstError
            p r hr s hs t ht Hpath.1 Hfirst Hsecond
          have Hf:f (nativeSecondLowEntryDepartureCut anchor j p r)=
              nativeOriginalCutLowErrorRadius n M.bf M.hf as k+1/(n+1:ℕ):=by
            rw [←HE]
            change (if k<U ∧ k≠i ∧ k≠star then
              nativeOriginalCutLowErrorRadius n M.bf M.hf as k+1/(n+1:ℕ) else 0)=_
            rw [ite_eq_left ⟨hk,Hmoving⟩]
          have HB:=hgrid U T hU hT G forms initial x W hxsx hxW hmass a z haz
            p hp r hr s hs t ht Hfirst Hsecond
          have hd:0 ≤ actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as k+1/(n+1:ℕ)):=
            mul_nonneg HCerr (add_nonneg (Real.sqrt_nonneg _) (by positivity))
          have Hbound:|nativeSecondLowErrorWord n q U b h K
              (G.canonicalHighOnlySource M forms).restProduct a z firstError p r s t| ≤ Cword*(actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.bf M.hf as k+1/(n+1:ℕ)))*((1+Couter)*W)*p0:=by
            cases firstError
            · exact HB.2.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Hother _ Hfirst) (mul_nonneg hCword.le hd)) hp0)
            · exact HB.1.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Hother _ Hsecond) (mul_nonneg hCword.le hd)) hp0)
          rw [Hf]
          apply Hbound.trans_eq
          dsimp [Drow]
          ring
        · rw [native_second_low_error_word_zero_second_high n q U b h K
            (G.canonicalHighOnlySource M forms).restProduct a z firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using mul_nonneg hDrow (hf _)
      · rw [native_second_low_error_word_zero_first_high n q U b h K
          (G.canonicalHighOnlySource M forms).restProduct a z firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using mul_nonneg hDrow (hf _)
    · simpa only [abs_zero] using mul_nonneg hDrow (hf _)
    · simpa only [abs_zero] using mul_nonneg hDrow (hf _)
  have Hclass:|nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU
      (G.canonicalHighOnlySource M forms).restProduct a z j firstError| ≤ 2*Poly*Drow*rho:=by
    rw [native_second_low_moving_error_unobserved_class_eq_entry]
    cases HM:nativeSecondLowFirstMiddleIsFirst j
    · let R:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
        f (r.tree.splitIndex (r.embed (p.embed anchor)) r.mark)
      let allowed:=fun p : MarkedPlacement T=>U ≤ p.tree.splitIndex
        (p.embed (if j.val<4 then a else z)) p.mark
      have HF2:∀p∈T.markedAttach 0,allowed p → ∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ Drow*R p r:=by
        intro p hp _HA r hr s hs t ht
        simpa only [nativeSecondLowEntryDepartureCut,HM,Bool.false_eq_true,ite_false,R] using HF p hp r hr s hs t ht
      have Hzero:∀p∈T.markedAttach 0,¬allowed p → ∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,F p r s t=0:=by
        intro p _hp HA r hr s hs t ht
        dsimp only [F,nativeSecondLowMovingErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
        split_ifs with _Hmoving Hpath
        · exact (HA (native_second_low_word_path_second_entry_first_mark_HIGH T U hU a z p r hr s hs t ht
            j Hpath.1 HM)).elim
        · rfl
        · rfl
      have Hcost:∀p∈T.markedAttach 0,allowed p →
          ((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>|r.coeff| * R p r)).sum ≤ rho:=by
        intro p hp HA
        have Hnew:=hpersistent.observedHigh hi hstar 0 p hp (if j.val<4 then a else z)
          (by rwa [p.tree.splitIndex_symm])
        exact native_second_low_unobserved_varying_entry_le_literal_density n M.bf M.hf as i star U p.tree ho hU Hnew (p.embed anchor)
      have HH:=native_second_low_second_entry_four_average_profile_abs_le T U ho hT F R allowed
        (fun p _hp r _hr=>hf _) hDrow hrho HF2 Hzero Hcost
      apply HH.trans
      have Hcoef:2*(rBound:ℝ)*(rBound+2)*(rBound+3) ≤ 2*Poly:=by
        have Hnat:(rBound:ℝ) ≤ rBound+1:=by linarith
        have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hnat (by norm_num : (0:ℝ) ≤ 2))
          (show 0 ≤ (rBound+2:ℝ)*(rBound+3) by positivity)
        convert HC using 1 <;> (try dsimp [Poly]) <;> ring
      have HC:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg hDrow hrho)
      convert HC using 1 <;> ring
    · let R:=fun p : MarkedPlacement T=>f (p.tree.splitIndex (p.embed anchor) p.mark)
      have HF1:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ Drow*R p:=by
        intro p hp r hr s hs t ht
        simpa only [nativeSecondLowEntryDepartureCut,HM,ite_true,R] using HF p hp r hr s hs t ht
      have HH:=native_second_low_first_entry_four_average_profile_abs_le T U ho hT F R
        (fun p _hp=>hf _) hDrow HF1
      exact HH.trans (by
        calc
          _ ≤ (2*(rBound+1:ℝ)*(rBound+2)*(rBound+3)*Drow)*rho:=
            mul_le_mul_of_nonneg_left HDensity (by positivity)
          _=2*Poly*Drow*rho:=by dsimp [Poly];ring)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_of_nonneg_right Hclass (by norm_num)).trans_eq
  dsimp [C,Drow,Poly,rho,p0,Mclock]
  ring

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_B0_budget_high_only
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),U≤as.length → i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        let density:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U
        |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2|≤
          C*x^2*Cerr*di+C*x*Cerr*density := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_fixed_error_budget_high_only
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cm,hCm,HM⟩:=eventually_actual_minimum_inherited_second_low_unobserved_moving_literal_entry_budget_high_only
    (D:=D) 0 2 Bclock Temp Cf 0 Couter hTemp hCf le_rfl hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨16*(Ci+Cm),by positivity,?_⟩
  filter_upwards [HI,HM] with n hnI hnM
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hnI M hs0 hsxs HS hxs L us hus hret hmesh,hnM M hs0 hsxs HS hxs L us hus hret hmesh] with k hgridI hgridM
  dsimp only at hgridI hgridM ⊢
  intro i U x hU hi hxsx hxW houter
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let G:=nativeSecondLowEmptyOldShape n g.tree
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let rho:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U
  have Hmass : ∀e,G.sourceLowMass e≤(0:ℝ)*sourceFactorScale x x (∅ : Finset (Fin 0)) e:=by
    intro e
    exact Fin.elim0 e
  have Hproduct : (G.canonicalHighOnlySource M forms).restProduct=(fun _=>1):=by
    funext τ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have Hscale : sourceMonomialScale x x (∅ : Finset (Fin 0))=1:=by
    simp only [sourceMonomialScale,Finset.card_empty,Nat.sub_self,pow_zero,mul_one]
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have Htarget : g.tree.splitIndex (g.embed (singleSlot as)) g.mark<U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hi
  have HPersistent : NativePersistentLowForks i i U g.tree:=
    (native_single_persistentLowForks i i U hU).freshStar 0 (singleSlot as)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hrho : 0≤rho:=by
    unfold rho nativeSecondLowLiteralMovingEntryDensity
    apply edgeBudget_nonneg ho
    intro j
    unfold nativeSecondLowMovingOriginalEntryRadius
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have Hmoving (j : Fin 8) (firstError : Bool) :
      |nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
        (g.embed (singleSlot as)) g.mark j firstError/2|≤Cm*x*Cerr*rho:=by
    have H:=hgridM i i U g.tree hU le_rfl hi HPersistent Hleaves G forms ∅ x x hxsx le_rfl Hmass
      houter (g.embed (singleSlot as)) g.mark Htarget j firstError
    rw [Hproduct,Hscale,mul_one] at H
    exact H
  have Hpoint (j : Fin 8) :
      |nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2|≤2*Ci*x^2*Cerr*di+2*Cm*x*Cerr*rho:=by
    apply (high_only_sole_root_abs_add_four _ _ _ _).trans
    apply (add_le_add (add_le_add (add_le_add
      (hgridI i U x hU hi hxsx hxW houter j true) (hgridI i U x hU hi hxsx hxW houter j false))
      (Hmoving j true)) (Hmoving j false)).trans_eq
    ring
  rw [native_second_low_sole_root_target_cut_joint_half_eq_fixed_and_moving n q i U b h K as ho hU hi]
  have Hsum:=Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 8)))=>Hpoint j)
  apply (Finset.abs_sum_le_sum_abs _ _).trans (Hsum.trans _)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have Hnon1 : 0≤x^2*Cerr*di:=by positivity
  have Hnon2 : 0≤x*Cerr*rho:=by positivity
  have H1:=mul_le_mul_of_nonneg_right (show 16*Ci≤16*(Ci+Cm) by linarith) Hnon1
  have H2:=mul_le_mul_of_nonneg_right (show 16*Cm≤16*(Ci+Cm) by linarith) Hnon2
  convert add_le_add H1 H2 using 1 <;> ring

theorem actual_second_low_literal_moving_density_target_integral_on_every_final_net_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Couter : ℝ) (hCouter : 0≤Couter) (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) :
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      ∀(i U : ℕ) (x : ℝ),U≤as.length → M.xs≤x → partitionPoint 0 as U≤Couter*x →
        nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U≤
          (∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
            (orderedPathS (n+1) M.bf M.hf u)^2))+(1+Couter)*x/(n+1:ℕ) := by
  have hb:=M.bf_monotone
  have hh:=M.hf_monotone
  let A:=3*physicalBApproximationConstant n M.bf M.hf+1
  have Hlim : Tendsto (fun k=>Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)) atTop (𝓝 0):=by
    have H:=(uniformMasses_mesh_tendsto.mul_const A).sqrt
    simpa only [zero_mul,Real.sqrt_zero] using H
  have HE:=Hlim.eventually (eventually_le_nhds (div_pos M.hxs (by positivity : 0<((n+1:ℕ):ℝ))))
  filter_upwards [HE] with k hk
  dsimp only
  intro i U x hU hxsx houter
  let as:=finiteCutMasses us k
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hm:partitionPoint 0 as U∈Icc (0:ℝ) 1:=partitionPoint_mem as ho U
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hq : min (Couter*x) 1∈Icc (0:ℝ) 1:=⟨le_min (mul_nonneg hCouter hx.le) zero_le_one,min_le_right _ _⟩
  have Hcut : partitionPoint 0 as U ≤ min (Couter*x) 1:=le_min houter hm.2
  have HP:=native_second_low_literal_moving_density_le_original_prefix_integral n M.bf M.hf as ho i U hU
  have HF:=physicalSampledCutLowError_integral_error n M.bf M.hf hb hh as ho
    (finiteCutMasses_end us hus k) (finiteCutMasses_mesh us hus k) hm
  have Hupper:=(abs_le.mp HF).2
  have Hsample : (∫u in 0..partitionPoint 0 as U,
      Real.sqrt (physicalSampledCutLowErrorSecond n M.bf M.hf as ho u))≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2))+M.xs/(n+1:ℕ):=by
    have HH:=Hupper
    change _≤Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A) at HH
    linarith
  have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable (physicalOrderedThermal_intervalIntegrable n M.bf M.hf hb hh)
  have HIq:=HI.mono_set (by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have Hmono:=intervalIntegral.integral_mono_interval le_rfl hm.1 Hcut
    (ae_of_all _ (fun u=>Real.sqrt_nonneg (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))) HIq
  have Hsite : M.xs/(n+1:ℕ)+partitionPoint 0 as U/(n+1:ℕ)≤(1+Couter)*x/(n+1:ℕ):=by
    rw [←add_div]
    apply (div_le_div_of_nonneg_right (add_le_add hxsx houter) (by positivity : (0:ℝ)≤(n+1:ℕ))).trans_eq
    ring
  apply (HP.trans (add_le_add Hsample (le_refl (partitionPoint 0 as U/(n+1:ℕ))))).trans
  have HH:=add_le_add Hmono Hsite
  simpa only [add_assoc] using HH

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget_high_only
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),U≤as.length → i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2|≤
          C*x^2*Cerr*di+C*x*Cerr*
            (∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
              (orderedPathS (n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_budget_high_only
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C*(2+Couter),mul_pos hC (by linarith),?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh,
    actual_second_low_literal_moving_density_target_integral_on_every_final_net_high_only M Couter hCouter us hus] with k hk hD
  dsimp only at hk hD ⊢
  intro i U x hU hi hxsx hxW houter
  have HB:=hk i U x hU hi hxsx hxW houter
  have HD:=hD i U x hU hxsx houter
  let as:=finiteCutMasses us k
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2))
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hR : 0≤nativeOriginalCutLowErrorRadius n M.bf M.hf as i:=Real.sqrt_nonneg _
  have hdi : 0≤di:=add_nonneg hR (by positivity)
  have hsite : (1/(n+1:ℕ):ℝ)≤di:=le_add_of_nonneg_left hR
  have hI : 0≤I:=by
    apply intervalIntegral.integral_nonneg (le_min (mul_nonneg hCouter hx.le) zero_le_one)
    intro u _
    exact Real.sqrt_nonneg _
  apply HB.trans
  have HM:=mul_le_mul_of_nonneg_left HD (show 0≤C*x*Cerr by positivity)
  apply (add_le_add le_rfl HM).trans
  have HsiteCost:=mul_le_mul_of_nonneg_left hsite (show 0≤C*(1+Couter)*x^2*Cerr by positivity)
  have HIcost:=mul_le_mul_of_nonneg_right (show C≤C*(2+Couter) by nlinarith) (show 0≤x*Cerr*I by positivity)
  dsimp only [di,I,Cerr,as] at HsiteCost HIcost ⊢
  simp only [div_eq_mul_inv] at HsiteCost HIcost ⊢
  nlinarith

end OAI.SKFluctuations.Cavity
