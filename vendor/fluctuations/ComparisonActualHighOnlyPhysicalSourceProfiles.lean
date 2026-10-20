module

public import ComparisonSignedCavityInheritedCanonicalRestMoments
public import ComparisonSignedCavityInheritedCanonicalRestFactorMoments
public import ComparisonSignedCavityInheritedRestRawMoments
public import ComparisonSignedCavityInheritedErrorTransport
public import ComparisonSignedCavityCanonicalLowFactor
public import ComparisonSignedCavityCanonicalUnbondedLowFactor
public import ComparisonSignedCavityInheritedBondedLowFactor
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowFactor
public import ComparisonSignedCavityInheritedUnbondedLowFactor
public import ComparisonSignedCavityInheritedBondedTwoHighLowBudget
public import ComparisonSignedCavityInheritedWorkingScaleBondedTwoHighLowBudget
public import ComparisonSignedCavityInheritedBondedLowGHighProfile
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowGHighProfile
public import ComparisonSignedCavityInheritedUnbondedLowGHighProfile
public import ComparisonSignedCavityInheritedBondedLowGLowProfile
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowGLowProfile
public import ComparisonSignedCavityInheritedUnbondedLowGLowProfile
public import ComparisonActualHighOnlyContinuumSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
open Classical
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false

theorem eventually_actual_minimum_inherited_canonical_rest_even_moment_high_only
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (fun σ=>|(G.canonicalHighOnlySource M f).restProduct σ|^(2*d)) 0≤
            (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_square_even_moment_high_only
    a d ha hd Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W hxsx hxW hmass
  rw [(G.canonicalHighOnlySource M f).rest_moment_eq_full_decoupled
    (finiteCutMasses_ordered us hus k) _ _ 0 (2*d)]
  exact hk 0 T 0 0 (by norm_num) (by norm_num) G f initial x W hxsx hxW hmass

theorem eventually_actual_minimum_inherited_canonical_rest_factor_moments_high_only
    (d : ℕ) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(a : ℕ) (T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
        ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>|(G.canonicalHighOnlySource M f).restFactor e σ|^(2*d)) 0≤
            (C*sourceFactorScale x W initial e)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_high_only
    1 d (by norm_num) hd Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro a T G f initial x W hxsx hxW hmass e
  let r:=sourceFactorScale x W initial e
  have hr : M.xs≤r:=hxsx.trans (source_factor_scale_ge_initial hxW initial e)
  have He:=hk T (G.edgeShape e) (fun _=>f e) ∅ r r hr le_rfl (by
    intro j
    simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.edgeShape,
      r,sourceFactorScale,Finset.notMem_empty,↓reduceIte] using hmass e)
  simpa [ActualNaturalBoundaryShape.restProduct,ActualNaturalBoundaryShape.restFactor,
    ActualNaturalBoundaryShape.canonicalHighOnlySource,ActualNaturalBoundaryShape.edgeShape,
    ActualNaturalBoundaryShape.sourceLowMass,sourceMonomialScale] using He

theorem eventually_actual_minimum_inherited_rest_even_bound_high_only
    (l : ℕ) (hl : 0 < l) (Bclock Temp Cf : ℝ) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀j ≤ as.length,
          (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
            (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
            (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
              (ClockTree.pairSpin as j σ).2|^(2*l)) 0 ≤
            (C*(M.xs+partitionPoint 0 as j))^(2*l) := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_high_only_deleted_raw_on_retained_net
    (D:=D) l hl Bclock (4*Cf+2*Temp) Temp hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*Cd,by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro j hj
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HC:=native_small_source_clock_full_square_budget_high_only M Temp Cf hCf hsource hxs as ho
  have HB:=(hsource _ (partitionPoint_mem as ho as.length)).1
  have HRj:=hk j hj HC HB
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>M.bf_monotone hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>M.hf_monotone hx hy hxy) as ho
  have H:=native_original_rest_even_le_raw n l hn0 ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left HRj (by positivity : (0:ℝ) ≤ (2:ℝ)^(2*l))
  convert HH using 1
  simp only [mul_pow]
  ring

theorem native_small_source_continuum_square_clock_budget_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hCf : 0 ≤ Cf) (hsource : ActualHighOnlySmallSourceClocks M Temp Cf)
    (hxs : M.xs ≤ 1) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    h as.length+b as.length*S as.length+b as.length+h as.length ≤ 4*Cf+2*Temp := by
  dsimp only
  have hu:=partitionPoint_mem as ho as.length
  have HC:=hsource _ hu
  have Hfield : (M.hf (partitionPoint 0 as as.length):ℝ) ≤ 2*Cf:=by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [hu.2]) hCf
    exact HC.2.trans (by linarith only [H])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) hu).2
  have Hmul:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  nlinarith [HC.1]

theorem actual_minimum_inherited_current_low_error_radius_le_original_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K) j ≤
      if j<U then actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) else 0 := by
  dsimp only
  have hbond k (_hk : k ≤ as.length) : (M.bf (partitionPoint 0 as k):ℝ) ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho k)).1
  exact native_actual_low_error_radius_le_original n U M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) ho hl ht hTemp hbond
    (native_small_source_continuum_square_clock_budget_high_only M Temp Cf hCf hsource hxs as ho) j hj

theorem actual_minimum_inherited_current_high_error_radius_le_original_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) j ≤
      nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp j := by
  dsimp only
  have hbond k (_hk : k ≤ as.length) : (M.bf (partitionPoint 0 as k):ℝ) ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho k)).1
  exact native_actual_high_error_radius_le_original n U M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) ho hl ht hTemp hbond
    (native_small_source_continuum_square_clock_budget_high_only M Temp Cf hCf hsource hxs as ho) j hj

theorem actual_minimum_inherited_current_high_profile_le_original_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {e : ℝ} (he : 0 ≤ e) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T e ≤
      T.forkCost (fun j=>(R j)^e)+ClockTree.edgeBudget 0 as (fun j=>(R j)^e) := by
  dsimp only
  rw [nativeWholeLawProfileCost_eq_budget n ho]
  have H (j : ℕ) (hj : j ≤ as.length):=Real.rpow_le_rpow
    (nativeWholeLawErrorRadius_nonneg n as _ _ j)
    (actual_minimum_inherited_current_high_error_radius_le_original_high_only M Temp Cf hTemp hCf
      hsource hxs ho U hl ht j hj) he
  exact add_le_add (native_forkCost_mono_on_clock T H) (actual_low_edgeBudget_mono ho H)

theorem canonical_source_prepend_bond_product_high_only {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f : Fin a→NativeSourceFactorForm) (c d : T.Slot) (hcd : c≠d) (σ : T.Assignment) :
    ((G.prependSourceEdge c d hcd).canonicalHighOnlySource M (Fin.cases .bondCentered f)).product σ=
      (M.bf (partitionPoint 0 as (T.splitIndex c d)):ℝ)*
        (deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d))-
          pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
            (partitionPoint 0 as (T.splitIndex c d)))*(G.canonicalHighOnlySource M f).product σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_succ]
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource,
    ActualNaturalBoundaryShape.prependSourceEdge,ActualNaturalBoundaryShape.sourceLowMass,
    Fin.cases_zero,Fin.cases_succ,NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope]
  congr 1
  unfold fullBoundaryAffineFactor
  have HE : deletedOverlap n (joinSpin (T.atSlot σ d)) (joinSpin (T.atSlot σ c))=
      deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d)) := by
    simp only [deletedOverlap,mul_comm]
  rw [HE]
  ring

theorem canonical_source_prepend_centered_product_high_only {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f : Fin a→NativeSourceFactorForm) (c d : T.Slot) (hcd : c≠d) (σ : T.Assignment) :
    ((G.prependSourceEdge c d hcd).canonicalHighOnlySource M (Fin.cases .centered f)).product σ=
      (deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d))-
          pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
            (partitionPoint 0 as (T.splitIndex c d)))*(G.canonicalHighOnlySource M f).product σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_succ]
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource,
    ActualNaturalBoundaryShape.prependSourceEdge,ActualNaturalBoundaryShape.sourceLowMass,
    Fin.cases_zero,Fin.cases_succ,NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope]
  congr 1
  unfold fullBoundaryAffineFactor
  have HE : deletedOverlap n (joinSpin (T.atSlot σ d)) (joinSpin (T.atSlot σ c))=
      deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d)) := by
    simp only [deletedOverlap,mul_comm]
  rw [HE]
  ring

theorem eventually_actual_minimum_inherited_canonical_low_factor_even_moment_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighOnlySource M f).product σ*
              (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))|^(2*dOrder)) 0 ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
              (W*sourceMonomialScale M.xs W initial))^(2*dOrder) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
    (D:=D) (aDegree+1) dOrder rBound (by omega) hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T l t hl ht hT G f initial W hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone)
    (partitionPoint_mem as ho (T.splitIndex c d))
  have Hgeo : ∀e,(G.prependSourceEdge c d hcd).sourceLowMass e ≤
      Cmass*sourceFactorScale M.xs W (sourceInitialAfterStar initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_zero,source_factor_scale_after_star_zero] using hmassNew
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_succ,source_factor_scale_after_star_succ] using hmass e
  have H:=hgridP U T l t hl ht hT (G.prependSourceEdge c d hcd)
    (Fin.cases .bondCentered f) (sourceInitialAfterStar initial) M.xs W le_rfl hxW Hgeo
  simp_rw [canonical_source_prepend_bond_product_high_only] at H
  rw [←Hcenter] at H
  rw [source_monomial_scale_after_star] at H
  simpa only [mul_assoc,mul_left_comm,mul_comm] using H

theorem eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale xScale W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighOnlySource M f).product σ*
              (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))|^(2*dOrder)) 0 ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
              (W*sourceMonomialScale xScale W initial))^(2*dOrder) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
    (D:=D) (aDegree+1) dOrder rBound (by omega) hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T l t hl ht hT G f initial xScale W hxsScale hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone)
    (partitionPoint_mem as ho (T.splitIndex c d))
  have Hgeo : ∀e,(G.prependSourceEdge c d hcd).sourceLowMass e ≤
      Cmass*sourceFactorScale xScale W (sourceInitialAfterStar initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_zero,source_factor_scale_after_star_zero] using hmassNew
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_succ,source_factor_scale_after_star_succ] using hmass e
  have H:=hgridP U T l t hl ht hT (G.prependSourceEdge c d hcd)
    (Fin.cases .bondCentered f) (sourceInitialAfterStar initial) xScale W hxsScale hxW Hgeo
  simp_rw [canonical_source_prepend_bond_product_high_only] at H
  rw [←Hcenter] at H
  rw [source_monomial_scale_after_star] at H
  simpa only [mul_assoc,mul_left_comm,mul_comm] using H

theorem eventually_actual_minimum_inherited_canonical_unbonded_low_factor_even_moment_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighOnlySource M f).product σ*
              (deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d))|^(2*dOrder)) 0 ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
              (W*sourceMonomialScale x W initial))^(2*dOrder) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
    (D:=D) (aDegree+1) dOrder rBound (by omega) hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T l t hl ht hT G f initial x W hxsx hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone)
    (partitionPoint_mem as ho (T.splitIndex c d))
  have Hgeo : ∀e,(G.prependSourceEdge c d hcd).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (sourceInitialAfterStar initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_zero,source_factor_scale_after_star_zero] using hmassNew
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_succ,source_factor_scale_after_star_succ] using hmass e
  have H:=hgridP U T l t hl ht hT (G.prependSourceEdge c d hcd)
    (Fin.cases .centered f) (sourceInitialAfterStar initial) x W hxsx hxW Hgeo
  simp_rw [canonical_source_prepend_centered_product_high_only] at H
  rw [←Hcenter] at H
  rw [source_monomial_scale_after_star] at H
  simpa only [mul_assoc,mul_left_comm,mul_comm] using H

theorem eventually_actual_minimum_inherited_canonical_two_high_low_factor_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          |cutFrozenLowHighJet n q U b h K T
            (fun σ=>(G.canonicalHighOnlySource M f).product σ*
              (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))) 0 0 2 t| ≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                (W*sourceMonomialScale M.xs W initial))*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_low_factor_even_moment_high_only
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T t ht hT G f initial W hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let J:=fun σ=>(G.canonicalHighOnlySource M f).product σ*
    (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
      (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.bf_monotone) (M.hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho j)).1
  have HC : 0 ≤ C := by
    dsimp only [C]
    rw [←source_factor_scale_product]
    apply mul_nonneg (by positivity)
    apply mul_nonneg (M.hxs.trans_le hxW).le
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have Hraw:=hgridP U T 0 t (by norm_num) ht hT G f initial W hxW hmass c d hcd hmassNew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,Mclock,law,q,b,h,S,K,as] using Hraw
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have Hclock j (_hj : j≤as.length) : |b j| ≤ Mclock ∧ |h j| ≤ Mclock ∧ |K j| ≤ Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have HH:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [HH])
    have HK : K j ≤ 2*Cf+Temp := by
      have HT:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hb j]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hb j],by linarith,by linarith⟩
  have H:=cutFrozenLowHighJet_twoError_wholeLaw_moment_budget n q U b h K T ho J 0 ht
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT
    (k:=0) (rho:=1) HC (by norm_num) HM (show 0 ≤ 2*Temp by positivity) hp Hmoment Hclock
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro j _
      have HE:=(ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0
      simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero] using HE.le)
  simpa only [C,J,Mclock,law,q,A,K,b,h,S,as,ClockTree.absJetVariation,pow_zero,mul_one,
    nativeWholeLawProfileCost] using H

theorem eventually_actual_minimum_inherited_canonical_working_scale_two_high_low_factor_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale xScale W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          |cutFrozenLowHighJet n q U b h K T
            (fun σ=>(G.canonicalHighOnlySource M f).product σ*
              (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))) 0 0 2 t| ≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                (W*sourceMonomialScale xScale W initial))*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment_high_only
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T t ht hT G f initial xScale W hxsScale hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let J:=fun σ=>(G.canonicalHighOnlySource M f).product σ*
    (b (T.splitIndex c d)*(deletedOverlap n (joinSpin (T.atSlot σ c))
      (joinSpin (T.atSlot σ d))-S (T.splitIndex c d)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.bf_monotone) (M.hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho j)).1
  have HC : 0 ≤ C := by
    dsimp only [C]
    rw [←source_factor_scale_product]
    apply mul_nonneg (by positivity)
    apply mul_nonneg (M.hxs.trans_le (hxsScale.trans hxW)).le
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
  have Hraw:=hgridP U T 0 t (by norm_num) ht hT G f initial xScale W hxsScale hxW hmass c d hcd hmassNew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,Mclock,law,q,b,h,S,K,as] using Hraw
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have Hclock j (_hj : j≤as.length) : |b j| ≤ Mclock ∧ |h j| ≤ Mclock ∧ |K j| ≤ Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have HH:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [HH])
    have HK : K j ≤ 2*Cf+Temp := by
      have HT:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hb j]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hb j],by linarith,by linarith⟩
  have H:=cutFrozenLowHighJet_twoError_wholeLaw_moment_budget n q U b h K T ho J 0 ht
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT
    (k:=0) (rho:=1) HC (by norm_num) HM (show 0 ≤ 2*Temp by positivity) hp Hmoment Hclock
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
    (fun j _=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    (by
      intro j _
      have HE:=(ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0
      simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero] using HE.le)
  simpa only [C,J,Mclock,law,q,A,K,b,h,S,as,ClockTree.absJetVariation,pow_zero,mul_one,
    nativeWholeLawProfileCost] using H

theorem eventually_actual_minimum_inherited_low_factor_G_high_profile_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
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
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let A:=cutTSlope n U 0 b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) A] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale M.xs W initial))*
                (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law A (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law A T (2/p)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_low_factor_even_moment_high_only
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hU hl ht hT G forms initial W hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=M.hxs.trans_le hxW
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs HW initial e).le))
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale M.xs W initial e := by
    apply (hmass e).trans
    apply mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos M.hxs HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have Hraw:=hgrid U T l t hl ht hT G forms initial W hxW Hmass' u z huz Hnew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,law,q,b,h,S,K,Mclock,as] using Hraw
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  exact native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J a c e f hef A
    HC hp (show 0≤2*Temp by positivity) (show 0≤2*Temp by positivity) Hmoment
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_high_profile_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
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
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let A:=cutTSlope n U 0 b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) A] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale xScale W initial))*
                (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law A (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law A T (2/p)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment_high_only
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hU hl ht hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=M.hxs.trans_le (hxsScale.trans hxW)
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le))
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale xScale W initial e := by
    apply (hmass e).trans
    apply mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have Hraw:=hgrid U T l t hl ht hT G forms initial xScale W hxsScale hxW Hmass' u z huz Hnew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,law,q,b,h,S,K,Mclock,as] using Hraw
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  exact native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J a c e f hef A
    HC hp (show 0≤2*Temp by positivity) (show 0≤2*Temp by positivity) Hmoment
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)

theorem eventually_actual_minimum_inherited_unbonded_low_G_high_profile_high_only
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
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
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x →x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let A:=cutTSlope n U 0 b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) A] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale x W initial))*
                (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law A (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law A T (2/p)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_unbonded_low_factor_even_moment_high_only
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=(M.hxs.trans_le hxsx).trans_le hxW
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) HW initial e).le))
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale x W initial e := by
    apply (hmass e).trans
    apply mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsx) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have Hraw:=hgrid U T l t hl ht hT G forms initial x W hxsx hxW Hmass' u z huz Hnew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,law,q,b,h,S,K,Mclock,as] using Hraw
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  exact native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J a c e f hef A
    HC hp (show 0≤2*Temp by positivity) (show 0≤2*Temp by positivity) Hmoment
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)

theorem eventually_actual_minimum_inherited_low_factor_G_low_profile_high_only
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale M.xs W initial))*
                nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*
                (Cq*(1+Ccut)*W)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_low_factor_even_moment_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms initial W hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let rho:=Cq*(1+Ccut)*W
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=M.hxs.trans_le hxW
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs HW initial e).le))
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale M.xs W initial e := by
    apply (hmass e).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos M.hxs HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^4) 0≤C^4 := hgrid U T l t hl ht hT G forms initial W hxW Hmass' u z huz Hnew
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t 1 hl ht (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_original_G_finite_raw_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J
    a c e f hef (cutLSlope n U 1 b h K) HC Hrho HPmoment HQmoment

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_low_profile_high_only
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale xScale W initial))*
                nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*
                (Cq*(1+Ccut)*W)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let rho:=Cq*(1+Ccut)*W
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=M.hxs.trans_le (hxsScale.trans hxW)
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le))
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale xScale W initial e := by
    apply (hmass e).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^4) 0≤C^4 := hgrid U T l t hl ht hT G forms initial xScale W hxsScale hxW Hmass' u z huz Hnew
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t 1 hl ht (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxsScale,hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_original_G_finite_raw_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J
    a c e f hef (cutLSlope n U 1 b h K) HC Hrho HPmoment HQmoment

theorem eventually_actual_minimum_inherited_unbonded_low_G_low_profile_high_only
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x →x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
            (deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale x W initial))*
                nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*
                (Cq*(1+Ccut)*W)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_unbonded_low_factor_even_moment_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let rho:=Cq*(1+Ccut)*W
  let J:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*
    (deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=(M.hxs.trans_le hxsx).trans_le hxW
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) HW initial e).le))
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale x W initial e := by
    apply (hmass e).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsx) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^4) 0≤C^4 := hgrid U T l t hl ht hT G forms initial x W hxsx hxW Hmass' u z huz Hnew
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t 1 hl ht (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxsx,hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_original_G_finite_raw_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J
    a c e f hef (cutLSlope n U 1 b h K) HC Hrho HPmoment HQmoment

end OAI.SKFluctuations.Cavity
