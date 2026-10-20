module

public import ComparisonSignedCavityInheritedRetainedPairedHighBudget
public import ComparisonSignedCavityInheritedPairedNearHigh
public import ComparisonSignedCavityInheritedPairedGammaRows
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
theorem actual_minimum_inherited_retained_first_high_rest_L2_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U rBound : ℕ) (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) (fun σ=>P σ^2) 0 ≤ C^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
      (4*Cf+2*Temp) Temp
    |retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []| ≤
      pairForkVariation rBound*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  apply (native_retained_first_high_rest_L2_bound n U rBound _ _ _ _ T ho hT P hC hP).trans
  have HE:=actual_minimum_inherited_current_high_profile_le_original_high_only M Temp Cf hTemp hCf hsource hxs
    T ho U (l:=0) (t:=0) (by norm_num) (by norm_num) (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HE
  exact mul_le_mul_of_nonneg_left HE (mul_nonneg (pairForkVariation_nonneg _) hC)

theorem eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound_high_only
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
      ∀(as : List PositiveMass) (_ho : MassOrdered 0 as)
        (T : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U →
      ∀(s e : T.Slot),s≠e →
        let K:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
          (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        |fullScalarCutGamma T U K s e| ≤ Cg*(M.xs+partitionPoint 0 as (T.splitIndex s e)) := by
  obtain ⟨B,hB,HB⟩:=ActualHighOnlyOverlapMinimum.eventually_actual_high_only_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+Cf+Temp*B,by positivity,?_⟩
  filter_upwards [HB] with n hn
  intro M hs0 hsxs hsource as ho T U hU s e hse
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone M.mass_mean_monotone as ho
  have hS0 j : 0 ≤ S j:=M.mass_mean_nonneg (partitionPoint_mem as ho j)
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 j))
  have hKm : Monotone K:=by
    intro j k hjk
    exact add_le_add (hhm hjk) (mul_le_mul (hbm hjk) (hSm hjk) (hS0 j) (NNReal.coe_nonneg _))
  have Hmean j : S j ≤ B*(M.xs+partitionPoint 0 as j) := by
    by_cases hz : partitionPoint 0 as j=0
    · simp only [S,hz,orderedPathS,orderedPathPair_zero]
      have hx:=M.hxs
      positivity
    · exact hn M hs0 hsxs _ ⟨lt_of_le_of_ne (partitionPoint_mem as ho j).1 (Ne.symm hz),
        (partitionPoint_mem as ho j).2⟩
  have Hclock j : K j ≤ (1+Cf+Temp*B)*(M.xs+partitionPoint 0 as j) := by
    have HC:=hsource _ (partitionPoint_mem as ho j)
    have Hmul:=mul_le_mul HC.1 (Hmean j) (hS0 j) hTemp
    have Hfield:=HC.2
    have Hpos : 0 ≤ M.xs+partitionPoint 0 as j:=add_nonneg M.hxs.le (partitionPoint_mem as ho j).1
    change h j ≤ Cf*(M.xs+partitionPoint 0 as j) at Hfield
    change b j*S j ≤ Temp*(B*(M.xs+partitionPoint 0 as j)) at Hmul
    dsimp only [K]
    nlinarith only [Hfield,Hmul,Hpos]
  exact native_full_scalar_gamma_abs_le_clock n T ho U hU K hKm hK0 s e hse (Hclock _)

theorem eventually_actual_minimum_inherited_canonical_paired_near_high_high_only
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs Cp : ℝ,0 < Cs ∧ 0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (W : ℝ),
          M.xs ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*W →
        let H:=G₀.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalHighOnlySource M f
        let P':=(G.retarget j' hne).canonicalHighOnlySource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        let Cpair:=4*Cs*W*(Cp^a*sourceMonomialScale M.xs W initial)
        (T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>paired σ^2) 0 ≤ Cpair^2) ∧
        ∀(U rBound : ℕ),T.leaves ≤ rBound →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
            (4*Cf+2*Temp) Temp
          |retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            pairForkVariation rBound*Cpair*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_high_only
    (D:=D) a 2 ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_high_only
    (D:=D) 1 2 (by norm_num) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [HP,HS] with n hnP hnS
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnS M hs0 hsxs hsource hxs L us hus hret hmesh] with k hkP hkS
  dsimp only at hkP hkS ⊢
  intro T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hxspos:=M.hxs
  have hscale : 0 < Cp^a*sourceMonomialScale M.xs W initial := by
    unfold sourceMonomialScale
    positivity
  have HP:=hkP T G f initial M.xs W le_rfl hxW hmass
  have HQ:=hkP T (G.retarget j' hne) f initial M.xs W le_rfl hxW (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  have HS:=hkS T G₀ (fun _=>NativeSourceFactorForm.centered) ∅ W W hxW le_rfl (by
    intro e
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  have HS':=hkS T (G₀.retarget j₀' hne₀) (fun _=>NativeSourceFactorForm.centered) ∅ W W hxW le_rfl (by
    intro e
    rw [G₀.retarget_sourceLowMass j₀' hne₀ hlow₀]
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,one_mul,Nat.sub_zero,pow_one] at HS HS'
  have H:=native_rest_two_differences_square n T (finiteCutMasses_ordered us hus k) _ _ _ _ _
    (mul_pos hCs hW) hscale HS HS' HP HQ
  have HE : 4*(Cs*W)*(Cp^a*sourceMonomialScale M.xs W initial)=
      4*Cs*W*(Cp^a*sourceMonomialScale M.xs W initial):=by ring
  rw [HE] at H
  refine ⟨H,?_⟩
  intro U rBound hT
  exact actual_minimum_inherited_retained_first_high_rest_L2_bound_high_only M Temp Cf hTemp hCf hsource hxs
    T (finiteCutMasses_ordered us hus k) U rBound hT _ (by positivity) H

theorem eventually_actual_minimum_inherited_canonical_paired_near_gamma_row_high_only
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Cnear : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCnear : 0 ≤ Cnear)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (W : ℝ),
          M.xs ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*W →
        let H:=G₀.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalHighOnlySource M f
        let P':=(G.retarget j' hne).canonicalHighOnlySource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        ∀(U rBound : ℕ),0 < U → T.leaves ≤ rBound →
        ∀(s e : T.Slot),s≠e → partitionPoint 0 as (T.splitIndex s e) ≤ Cnear*W →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
            (4*Cf+2*Temp) Temp
          |fullScalarCutGamma T U K s e*
            retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            C*sourceMonomialScale M.xs W initial*W^2*pairForkVariation rBound*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cs,Cp,hCs,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_paired_near_high_high_only
    (D:=D) a ha Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound_high_only
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Cg*(1+Cnear)*4*Cs*Cp^a
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HG] with n hnP hnG
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀ U rBound hU hT s e hse hnear
  have hW : 0 < W:=M.hxs.trans_le hxW
  let K:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)+
    (M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)*
      orderedPathS (n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
  have HG:=hnG M hs0 hsxs hsource (finiteCutMasses us k) (finiteCutMasses_ordered us hus k) T U hU s e hse
  have HG' : |fullScalarCutGamma T U K s e| ≤ Cg*(1+Cnear)*W := by
    apply HG.trans
    nlinarith only [hxW,hnear,hCg]
  have HB:=(hk T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀).2 U rBound hT
  rw [abs_mul]
  apply (mul_le_mul HG' HB (abs_nonneg _) (by positivity : 0 ≤ Cg*(1+Cnear)*W)).trans_eq
  dsimp only [C]
  ring

end OAI.SKFluctuations.Cavity
