module

public import ComparisonActualHighOnlyCanonicalSourceMoments
public import ComparisonSignedCavityInheritedContinuumLowProfile
public import ComparisonSignedCavityWholeLawScalarClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

theorem eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
    (aDegree d rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < d)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighOnlySource M f).product σ|^(2*d)) 0  ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_square_even_moment_high_only
    (D:=D) aDegree d ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T l t hl ht hT G f initial x W hxs hxW hmassOld
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let Kfinite:=finitePhysicalMixedClock (n+1) as b h
  let Mclock:=4*Cf+2*Temp
  let E:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)
  let P:=(G.canonicalHighOnlySource M f).product
  let q:=cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K
  let A:=cutLowError n U b h K
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)  ≤  M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)  ≤  M.hf v from M.hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.bf_monotone) (M.hf_monotone)) as ho
  have hS0 j : 0  ≤  S j:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho j)).1
  have hK0 j : 0  ≤  K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 j))
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (hS0 i) (NNReal.coe_nonneg _))
  have hKfinite0:=finitePhysicalMixedClock_nonneg (n+1) as b h
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
  have hKfinitem:=finitePhysicalMixedClock_monotone (n+1) ho b h hbm hhm (fun _=>NNReal.coe_nonneg _)
  have Hsource:=hsource _ (partitionPoint_mem as ho as.length)
  have hfield : h as.length  ≤  2*Cf := by
    have HH:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [(partitionPoint_mem as ho as.length).2]) hCf
    exact Hsource.2.trans (by linarith only [HH])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) (partitionPoint_mem as ho as.length)).2
  have Hcur:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have Hfin:=mul_le_mul_of_nonneg_left (finitePhysicalMean_le_one (n+1) ho b h as.length)
    (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have hclock : K as.length+Kfinite as.length  ≤  Mclock := by
    dsimp only [K,Kfinite,finitePhysicalMixedClock,Mclock,b,h,S] at *
    linarith [Hsource.1]
  have hscale : 0  ≤  Cp^aDegree*sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hCp.le _) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxs) ((M.hxs.trans_le hxs).trans_le hxW) initial e).le)
  have Hraw:=hgridP U T l t hl ht G f initial x W hxs hxW hmassOld
  have HPcur:=native_wholeLaw_scalar_clock_nat_moment_le n U rBound (2*d) (by omega) T ho
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K Kfinite
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    hbm hhm hKm hKfinitem (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    hK0 hKfinite0 hl ht
    P (Cp^aDegree*sourceMonomialScale x W initial) Mclock hscale
    (by dsimp [Mclock];positivity) hT hclock
    (by
      change T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|P σ|^(2*d)) 0  ≤  _
      simpa only [P,b,h,as] using Hraw)
  simpa only [P,E,q,mul_assoc] using HPcur

theorem actual_high_only_one_pair_centered_product
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (j : ℕ) (hj : j ≤ as.length)
    (sigma : (pairClock (S:=Spin n×Bool) as j).Assignment) :
    ((nativeOnePairCenteredShape n as j).canonicalHighOnlySource M (fun _=>.centered)).product sigma=
      deletedOverlap n (joinSpin (pairSpin as j sigma).1)
        (joinSpin (pairSpin as j sigma).2)-nativePhysicalResourceCenter n M.bf M.hf as j := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_one]
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource,
    NativeSourceFactorForm.intercept,
    NativeSourceFactorForm.slope]
  rw [native_one_pair_shape_low_mass n as j hj]
  simp only [nativeOnePairCenteredShape,pairLeft_atSlot,pairRight_atSlot,fullBoundaryAffineFactor]
  change -nativePhysicalResourceCenter n M.bf M.hf as j+
    1*deletedOverlap n (joinSpin (pairSpin as j sigma).1) (joinSpin (pairSpin as j sigma).2)=_
  ring

theorem eventually_actual_minimum_inherited_continuum_centered_pair_moment_high_only
    (order : ℕ) (horder : 0<order) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cd : ℝ,0<Cd ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀j,j ≤ as.length →
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
              (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^(2*order)) 0 ≤
            (Cd*(M.xs+partitionPoint 0 as j))^(2*order) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_high_only
    (D:=D) 1 order 2 (by norm_num) horder Bclock Temp Cf 1 hTemp hCf (by norm_num)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cd:=Real.exp (wholeLawRowComparisonConstant 2*(4*Cf+2*Temp))*Cp
  have hCd : 0<Cd:=by dsimp [Cd];positivity
  refine ⟨Cd,hCd,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U l t hl ht j hj
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let natural:=M.xs+partitionPoint 0 as j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hu:=partitionPoint_mem as ho j
  have hnat : 0<natural:=add_pos_of_pos_of_nonneg M.hxs hu.1
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) hu
  have Hcpair:=hgridP U (ClockTree.pairClock as j) l t hl ht
    (by rw [ClockTree.pairClock_leaves]) (nativeOnePairCenteredShape n as j) (fun _=>.centered)
    ∅ natural natural (by dsimp [natural];linarith [hu.1]) le_rfl (by
      intro e
      have He : e=(0:Fin 1):=Subsingleton.elim _ _
      subst e
      rw [native_one_pair_shape_low_mass n as j hj]
      simp only [sourceFactorScale,Finset.notMem_empty,ite_false,one_mul]
      dsimp [natural]
      linarith [M.hxs])
  simp_rw [actual_high_only_one_pair_centered_product M as j hj] at Hcpair
  have Hdelta : (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^(2*order)) 0 ≤ (Cd*natural)^(2*order) := by
    simpa only [nativePhysicalResourceCenter,Hcenter.symm,source_monomial_scale_star,pow_one,
      Cd,mul_assoc,S,b,h,K,natural,as] using Hcpair
  exact Hdelta

theorem eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (order : ℕ) (horder : 0<order) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (l t s : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
        ∀j,j ≤ as.length →
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
              (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order)) 0 ≤
            (Cq*(M.xs+partitionPoint 0 as j))^(2*order) := by
  obtain ⟨Cd,hCd,HP⟩:=eventually_actual_minimum_inherited_continuum_centered_pair_moment_high_only
    (D:=D) order horder Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_only_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs
  have hCk : 0 ≤ Ck:=by dsimp [Ck];positivity
  refine ⟨2*(Ck+Temp*Cd+1),by positivity,?_⟩
  filter_upwards [HP,(tendsto_add_atTop_nat 1).eventually HS] with n hnP hnS
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U l t s hl ht hs j hj
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let natural:=M.xs+partitionPoint 0 as j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hu:=partitionPoint_mem as ho j
  have hnat : 0<natural:=add_pos_of_pos_of_nonneg M.hxs hu.1
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) hu
  have Hdelta:=hgridP U l t hl ht j hj
  have Hsource:=hsource _ hu
  have HSu : |S j| ≤ Cs*natural := by
    dsimp only [S]
    rw [Hcenter]
    exact hnS M hs0 hsxs _ hu
  have HK : |h j+b j*S j| ≤ Ck*natural := by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_mul,abs_of_nonneg (NNReal.coe_nonneg _)]
    have HB:=mul_le_mul Hsource.1 HSu (abs_nonneg _) hTemp
    dsimp only [Ck,natural]
    nlinarith [Hsource.2]
  exact native_continuum_low_kernel_moment_le n U (2*order) (by omega) ho _ b h S hs j
    hCk hTemp hCd.le hnat HK (by rw [abs_of_nonneg (NNReal.coe_nonneg _)];exact Hsource.1) Hdelta

end OAI.SKFluctuations.Cavity
