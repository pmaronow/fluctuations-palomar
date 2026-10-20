module

public import SKProof.Port.ComparisonActualOriginalQNaturalSourceCalibration
public import ComparisonSignedCavityFullSquareRepeatedBudget
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

def ActualOriginalQSmallSourceClocks {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (Temp Cf : ℝ) : Prop :=
  ∀u∈Icc (0:ℝ) 1,(M.sweepBf u:ℝ) ≤ Temp ∧ (M.sweepHf u:ℝ) ≤ Cf*(M.xs+u)

namespace ActualNaturalBoundaryShape
def canonicalOriginalQSource {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (G : ActualNaturalBoundaryShape n a T)
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f : Fin a→NativeSourceFactorForm) : ActualNaturalBoundaryShape n a T :=
  { G with
    α:=fun e=>(f e).intercept (M.sweepBf (G.sourceLowMass e)) (M.sweepHf (G.sourceLowMass e))
      (pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (G.sourceLowMass e))
    β:=fun e=>(f e).slope (M.sweepBf (G.sourceLowMass e)) }
end ActualNaturalBoundaryShape

theorem eventually_actual_minimum_source_centered_square_forest_product_original_q
    (a : ℕ) (ha : 0 < a) (Bclock Btotal Bbond Cmass Ch Cb : ℝ)
    (hCm : 0 ≤ Cmass) (hCh : 0 ≤ Ch) (hCb : 0 ≤ Cb)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
            l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          ∀(G : ActualNaturalBoundaryShape n a T) (initial : Finset (Fin a))
            (x W : ℝ) (field : Fin a→ℝ),M.xs ≤ x → x ≤ W →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (∀e,partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)) ≤
              Cmass*sourceFactorScale x W initial e) →
            (∀e,|field e| ≤ Ch*sourceFactorScale x W initial e) →
            (∀e,|G.β e| ≤ Cb) →
            (∀e,G.α e=field e-G.β e*pathPairMoment (uniformWeight (n+1))
              (finiteFeature (n+1)) (completedPathClock (n+1) M.sweepBf M.sweepHf)
              (orderedOverlap (n+1)) (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            T.disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>G.product σ^2) 0 ≤
              (C^a*sourceMonomialScale x W initial)^2 := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_deleted_raw_on_retained_net_original_q
    (D:=D) a ha Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_continuum_center_bound_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ca:=Ch+Cb*Cs*(1+Cmass)
  let Cr:=Cd*(1+Cmass)
  refine ⟨2*(Ca+Cb*Cr+1),by dsimp [Ca,Cr];positivity,?_⟩
  filter_upwards [HR,(tendsto_add_atTop_nat 1).eventually HS] with n hn hns
  intro M hs hsxs L us hus hret hmesh
  filter_upwards [hn M hs hsxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G initial x W field hxs hxW hclock hbond hmass hfield hβ hαeq
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let mass:=fun e=>partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hx : 0 < x:=M.hxs.trans_le hxs
  have hW : 0 < W:=hx.trans_le hxW
  have hcenter:=hns M hs hsxs
  have hc : ∀e,|pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (mass e)| ≤ Cs*(M.xs+mass e) := by
    intro e
    exact hcenter _ (partitionPoint_mem as ho _)
  have hα : ∀e,|G.α e| ≤ Ca*sourceFactorScale x W initial e := by
    intro e
    rw [hαeq e]
    exact source_centered_affine_intercept_le hxs hxW hx.le hCm hCs.le hCb initial mass
      field G.β (fun e=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (mass e))
      hmass hfield hβ hc e
  have hraw : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e)) ≤ (Cr*sourceFactorScale x W initial e)^(2*a) := by
    intro e
    have H:=hk _ (G.lowInGrid e) hclock hbond
    have hne:= (source_factor_scale_pos hx hW initial e).le
    have Hmass : M.xs+mass e ≤ (1+Cmass)*sourceFactorScale x W initial e := by
      have Hx:=source_factor_scale_ge_initial hxW initial e
      have Hm:=hmass e
      nlinarith
    apply H.trans
    apply pow_le_pow_left₀ (mul_nonneg hCd.le (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1))
    simpa only [Cr,mul_assoc] using mul_le_mul_of_nonneg_left Hmass hCd.le
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.sweepBf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>M.sweep_bf_monotone hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.sweepHf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>M.sweep_hf_monotone hx hy hxy) as ho
  exact actual_source_square_forest_product_square_le n U a ha T ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hl ht G initial hx hW
    (by dsimp [Ca];positivity) hCb (by dsimp [Cr];positivity) hα hβ hraw

theorem eventually_actual_minimum_source_centered_square_repeated_forest_product_original_q
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Btotal Bbond Cmass Ch Cb : ℝ)
    (hCm : 0 ≤ Cmass) (hCh : 0 ≤ Ch) (hCb : 0 ≤ Cb)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
            l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          ∀(G : ActualNaturalBoundaryShape n a T) (initial : Finset (Fin a))
            (x W : ℝ) (field : Fin a→ℝ),M.xs ≤ x → x ≤ W →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (∀e,partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)) ≤
              Cmass*sourceFactorScale x W initial e) →
            (∀e,|field e| ≤ Ch*sourceFactorScale x W initial e) →
            (∀e,|G.β e| ≤ Cb) →
            (∀e,G.α e=field e-G.β e*pathPairMoment (uniformWeight (n+1))
              (finiteFeature (n+1)) (completedPathClock (n+1) M.sweepBf M.sweepHf)
              (orderedOverlap (n+1)) (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            T.disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|G.product σ|^(2*d)) 0 ≤
              (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_source_centered_square_forest_product_original_q
    (D:=D) (a*d) (Nat.mul_pos ha hd) Bclock Btotal Bbond Cmass Ch Cb
    hCm hCh hCb hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs hsxs L us hus hret hmesh
  filter_upwards [hn M hs hsxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G initial x W field hxs hxW hclock hbond hmass hfield hβ hαeq
  have H:=hk U T l t hl ht (G.repeatFactors d) (sourceRepeatedResources initial d) x W
    (fun e=>field (finProdFinEquiv.symm e).1) hxs hxW hclock hbond
    (fun e=>by
      rw [source_repeated_factor_scale_eq]
      exact hmass (finProdFinEquiv.symm e).1)
    (fun e=>by
      rw [source_repeated_factor_scale_eq]
      exact hfield (finProdFinEquiv.symm e).1)
    (fun e=>hβ (finProdFinEquiv.symm e).1)
    (fun e=>hαeq (finProdFinEquiv.symm e).1)
  simp_rw [actual_repeated_shape_product_eq] at H
  rw [repeated_source_budget_eq] at H
  have HE : (fun σ=>(G.product σ^d)^2)=(fun σ=>|G.product σ|^(2*d)) := by
    funext σ
    exact (abs_even_repeat_square (G.product σ) d).symm
  rw [HE] at H
  exact H

theorem native_small_source_clock_full_square_budget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hCf : 0 ≤ Cf) (hsource : ActualOriginalQSmallSourceClocks M Temp Cf)
    (hxs : M.xs ≤ 1) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    finitePhysicalMixedClock n as b h as.length+b as.length+h as.length ≤ 4*Cf+2*Temp := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  have hu:=partitionPoint_mem as ho as.length
  have HC:=hsource _ hu
  have Hfield : h as.length ≤ 2*Cf:=by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [hu.2]) hCf
    exact HC.2.trans (by linarith only [H])
  have Hmean:=finitePhysicalMean_le_one n ho b h as.length
  have Hmul:=mul_le_mul_of_nonneg_left Hmean (NNReal.coe_nonneg (M.sweepBf (partitionPoint 0 as as.length)))
  change h as.length+b as.length*finitePhysicalMean n as b h as.length+b as.length+h as.length ≤ _
  nlinarith [HC.1]

theorem eventually_actual_minimum_inherited_canonical_square_even_moment_original_q
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ)
    (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>|(G.canonicalOriginalQSource M f).product σ|^(2*d)) 0 ≤
            (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_continuum_center_bound_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ch:=(Cf+Temp*Cs)*(1+Cmass)
  have hCh : 0 ≤ Ch:=by dsimp only [Ch];positivity
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product_original_q
    a d ha hd Bclock (4*Cf+2*Temp) Temp Cmass Ch (1+Temp) hCm hCh (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,(tendsto_add_atTop_nat 1).eventually HS] with n hn hcenterRate
  intro M hs hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs hsxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G f initial x W hxs hxW hmass
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun e=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (G.sourceLowMass e)
  let field:=fun e=>(f e).field (M.sweepBf (G.sourceLowMass e)) (M.sweepHf (G.sourceLowMass e)) (S e)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hclock:=native_small_source_clock_full_square_budget_original_q M Temp Cf hCf hsource hxs1 as ho
  have HC (e : Fin a):=hsource (G.sourceLowMass e) (partitionPoint_mem as ho _)
  have hbond:=(hsource _ (partitionPoint_mem as ho as.length)).1
  have hc:=hcenterRate M hs hsxs
  have hfield : ∀e,|field e| ≤ Ch*sourceFactorScale x W initial e:=by
    intro e
    have Hu:=partitionPoint_mem as ho (T.splitIndex (G.i e) (G.j e))
    have Hs : |S e| ≤ Cs*(M.xs+G.sourceLowMass e):=hc _ Hu
    have H:=native_source_field_bound (f e) (NNReal.coe_nonneg _) (HC e).1 (NNReal.coe_nonneg _)
      hCf hCs.le (add_nonneg M.hxs.le Hu.1) (HC e).2 Hs
    have Hmass : M.xs+G.sourceLowMass e ≤ (1+Cmass)*sourceFactorScale x W initial e:=by
      have Hx:=source_factor_scale_ge_initial hxW initial e
      nlinarith [hmass e]
    have H':=mul_le_mul_of_nonneg_left Hmass (show 0 ≤ Cf+Temp*Cs by positivity)
    exact H.trans (by simpa only [Ch,mul_assoc,ActualNaturalBoundaryShape.sourceLowMass] using H')
  have hbeta : ∀e,|(G.canonicalOriginalQSource M f).β e| ≤ 1+Temp:=by
    intro e
    exact native_source_slope_bound (f e) (NNReal.coe_nonneg _) (HC e).1
  have halpha : ∀e,(G.canonicalOriginalQSource M f).α e=field e-
      (G.canonicalOriginalQSource M f).β e*S e:=fun e=>native_source_intercept_center (f e) _ _ _
  exact hk U T l t hl ht (G.canonicalOriginalQSource M f) initial x W field hxs hxW
    hclock hbond hmass hfield hbeta halpha

end OAI.SKFluctuations.Cavity
