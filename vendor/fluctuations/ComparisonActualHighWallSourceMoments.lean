module

public import ComparisonActualHighWallSourceClockBudget
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem eventually_actual_high_wall_finite_overlap_on_retained_net
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀ u∈us,u.val ≤ 1) → (∀ u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
        ∀ᶠ k : ℕ in atTop,
          let q := completedPathClock n a.bf a.hf
          let as := finiteCutMasses us k
          let steps := sampleClockSteps q 0 as
          ∀ j ≤ as.length,
            physicalOverlapMoment n (ell+1) steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
              id measurable_id j ≤ K*(a.xs+physicalCutMass 0 steps j)^(2*(ell+1)) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_high_wall_overlap_moment_normalized ell Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*K*(2:ℝ)^(2*(ell+1)),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro a L us hus hret hmesh
  exact actual_finite_overlap_natural_calibration_on_retained_net n (ell+1) a.data.hn a.bf a.hf
    (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha) L us hus hret a.hxs hK hmesh (hn a)

theorem eventually_actual_high_wall_inverse_size_le_scale
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,∀a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      1/(n:ℝ)≤a.xs := by
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm] with n hn
  intro a
  exact (hn a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans a.hscale

theorem eventually_actual_high_wall_deleted_raw_on_retained_net
    (a : ℕ) (ha : 0<a) (Bclock Btotal Bbond : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀ low≤as.length,
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤Btotal →
            b as.length≤Bbond →
            finitePhysicalDeletedRawBudget n a as b h low≤
              (Cd*(M.xs+partitionPoint 0 as low))^(2*a) := by
  obtain ⟨K,hK,hraw⟩ := eventually_actual_high_wall_finite_overlap_on_retained_net
    (D:=D) (a-1) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HE := (tendsto_add_atTop_nat 1).eventually hraw
  have HS := (tendsto_add_atTop_nat 1).eventually
    (eventually_actual_high_wall_inverse_size_le_scale (D:=D) (delta:=delta)
      (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hC0)
  refine ⟨actualNaturalDeletedConstant K Btotal Bbond,
    actualNaturalDeletedConstant_pos hK.le,?_⟩
  filter_upwards [HE,HS] with n hn hsite
  intro M L us hus hret hmesh
  have hb := M.data.bf_monotone M.alpha
  have hh := M.data.hf_monotone M.alpha
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro low hlow hclock hbond
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hpoint : 0≤partitionPoint 0 as low:=(partitionPoint_mem as ho low).1
  have hnat : 0 < M.xs+partitionPoint 0 as low:=add_pos_of_pos_of_nonneg M.hxs hpoint
  have hsize : 1/(n+1:ℕ)≤M.xs+partitionPoint 0 as low:=
    (hsite M).trans (le_add_of_nonneg_right hpoint)
  have hdiag:=actual_sampled_completed_diagonal_steps_eq (n+1) M.bf M.hf hb hh as ho
  have hq:=actual_sampled_completed_clock_eq (n+1) M.bf M.hf hb hh as ho
  have hz (i : FeatureIndex (n+1)) : physicalCompletedClock (n+1) b h 0 i=
      (completedPathClock (n+1) M.bf M.hf 0 i:ℝ) := by
    have H:=congrFun (congrFun hq.symm 0) i
    simpa only [stepClockValues_zero] using H
  have hroot : (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))=
      Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) M.bf M.hf 0 i) := by
    congr 1
    funext i
    rw [hz,Real.toNNReal_coe]
  have Hmom:=hk low hlow
  have ha' : a-1+1=a := by omega
  rw [ha'] at Hmom
  have Hmom' : physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun j=>physicalCompletedClock (n+1) b h (j+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id low≤K*(M.xs+partitionPoint 0 as low)^(2*a) := by
    rw [hdiag,hroot]
    simpa only [physicalCutMass_sampleClockSteps _ _ _ low hlow] using Hmom
  exact actual_deleted_raw_budget_from_overlap n a ha as b h low hK.le hnat hclock hbond hsize Hmom'

theorem eventually_actual_high_wall_continuum_center_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs : ℝ,0<Cs ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Icc (0:ℝ) 1,
        |pathPairMoment (uniformWeight n) (finiteFeature n)
          (completedPathClock n M.bf M.hf) (orderedOverlap n) u|≤Cs*(M.xs+u) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_high_wall_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M
  apply continuum_center_bound_closed_interval n M.bf M.hf M.hxs.le (by positivity)
  intro u hu
  exact actual_continuum_center_le_of_second_moment n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu M.hxs (by
      simpa only [Nat.zero_add,Nat.mul_one] using hn M u hu)

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def canonicalPhysicalSource (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) :
    ActualNaturalBoundaryShape n a T :=
  { G with
    α:=fun e=>(f e).intercept (bf (G.sourceLowMass e)) (hf (G.sourceLowMass e))
      (pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (G.sourceLowMass e))
    β:=fun e=>(f e).slope (bf (G.sourceLowMass e)) }

abbrev canonicalHighWallSource {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) :=
  G.canonicalPhysicalSource M.bf M.hf f

end ActualNaturalBoundaryShape

theorem eventually_actual_high_wall_canonical_square_even_moment
    (a p : ℕ) (ha : 0<a) (hp : 0<p) (Bclock Cmass : ℝ) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e≤Cmass*M.data.d) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>|(G.canonicalHighWallSource M f).product σ|^(2*p)) 0≤
            (C^a*M.data.d^a)^(2*p) := by
  let B:=max Bclock 0
  have hB : 0≤B := le_max_right _ _
  obtain ⟨Cd,hCd,HR⟩ := eventually_actual_high_wall_deleted_raw_on_retained_net
    (D:=D) (a*p) (Nat.mul_pos ha hp) Bclock (2*B) B
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩ := eventually_actual_high_wall_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ch:=(1+B*Cs)*(1+Cmass)
  let Cb:=1+B
  let Ca:=Ch+Cb*Cs*(1+Cmass)
  let Cr:=Cd*(1+Cmass)
  let C:=2*(Ca+Cb*Cr+1)
  have hCh : 0≤Ch := by dsimp only [Ch];positivity
  have hCb : 0≤Cb := by dsimp only [Cb];positivity
  have hCa : 0≤Ca := by dsimp only [Ca];positivity
  have hCr : 0≤Cr := by dsimp only [Cr];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,(tendsto_add_atTop_nat 1).eventually HS] with n hn hs
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G f hmass
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let P:=G.canonicalHighWallSource M f
  let center:=fun e=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (G.sourceLowMass e)
  let field:=fun e=>(f e).field (M.bf (G.sourceLowMass e))
    (M.hf (G.sourceLowMass e)) (center e)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hT : M.data.T≤B:=M.hT.trans (le_max_left _ _)
  have hclock : finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤2*B :=
    (M.data.full_square_clock_budget M.alpha as ho).trans (by linarith)
  have HC (e : Fin a) : (M.bf (G.sourceLowMass e):ℝ)≤B ∧
      (M.hf (G.sourceLowMass e):ℝ)≤M.xs+G.sourceLowMass e := by
    have HH:=M.data.small_source_clock_budget M.alpha (by rw [hwork] : M.data.d≤M.xs)
      (partitionPoint_mem as ho (T.splitIndex (G.i e) (G.j e)))
    exact ⟨HH.1.trans hT,HH.2⟩
  have hbond : b as.length≤B := by
    have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho as.length)
    change (M.bf (partitionPoint 0 as as.length):ℝ)≤B
    linarith [(M.hf (partitionPoint 0 as as.length)).coe_nonneg]
  have hnatural (e : Fin a) : M.xs+G.sourceLowMass e≤(1+Cmass)*M.data.d := by
    rw [hwork]
    nlinarith [hmass e]
  have hc (e : Fin a) : |center e|≤Cs*(M.xs+G.sourceLowMass e) :=
    hs M _ (partitionPoint_mem as ho _)
  have hfield (e : Fin a) : |field e|≤Ch*M.data.d := by
    have HH:=native_source_field_bound (f e) (NNReal.coe_nonneg _) (HC e).1
      (NNReal.coe_nonneg _) (by norm_num : (0:ℝ)≤1) hCs.le
      (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1)
      (by simpa only [one_mul,ActualNaturalBoundaryShape.sourceLowMass] using (HC e).2) (hc e)
    exact HH.trans (by
      simpa only [Ch,mul_assoc,ActualNaturalBoundaryShape.sourceLowMass] using mul_le_mul_of_nonneg_left (hnatural e)
        (show 0≤1+B*Cs by positivity))
  have hβ (e : Fin a) : |P.β e|≤Cb := native_source_slope_bound (f e)
    (NNReal.coe_nonneg _) (HC e).1
  have hα (e : Fin a) : |P.α e|≤Ca*M.data.d := by
    have heq : P.α e=field e-P.β e*center e := native_source_intercept_center (f e) _ _ _
    rw [heq]
    have HH:=abs_sub (field e) (P.β e*center e)
    rw [abs_mul] at HH
    have Hcenter : |center e|≤Cs*(1+Cmass)*M.data.d :=
      (hc e).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hnatural e) hCs.le)
    have Hmul:=mul_le_mul (hβ e) Hcenter (abs_nonneg _) hCb
    dsimp only [Ca]
    nlinarith [hfield e]
  have hraw (e : Fin a) : finitePhysicalDeletedRawBudget n (a*p) as b h
      (T.splitIndex (G.i e) (G.j e))≤(Cr*M.data.d)^(2*(a*p)) := by
    apply (hk _ (G.lowInGrid e) hclock hbond).trans
    apply pow_le_pow_left₀ (mul_nonneg hCd.le (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1))
    simpa only [Cr,mul_assoc,ActualNaturalBoundaryShape.sourceLowMass] using mul_le_mul_of_nonneg_left (hnatural e) hCd.le
  have hb : Monotone b := comp_partitionPoint_monotone
    (fun x hx y hy hxy=>M.data.bf_monotone M.alpha hx hy hxy) as ho
  have hh : Monotone h := comp_partitionPoint_monotone
    (fun x hx y hy hxy=>M.data.hf_monotone M.alpha hx hy hxy) as ho
  have H:=actual_source_square_forest_product_square_le n U (a*p) (Nat.mul_pos ha hp)
    T ho b h hb hh (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hl ht
    (P.repeatFactors p) Finset.univ M.data.hd M.data.hd hCa hCb hCr
    (fun e=>by
      simpa only [ActualNaturalBoundaryShape.repeatFactors,sourceFactorScale,ite_self]
        using hα (finProdFinEquiv.symm e).1)
    (fun e=>hβ (finProdFinEquiv.symm e).1)
    (fun e=>by
      simpa only [ActualNaturalBoundaryShape.repeatFactors,sourceFactorScale,ite_self,
        P,ActualNaturalBoundaryShape.canonicalHighWallSource,ActualNaturalBoundaryShape.canonicalPhysicalSource]
        using hraw (finProdFinEquiv.symm e).1)
  simp_rw [actual_repeated_shape_product_eq] at H
  have Hscale : sourceMonomialScale M.data.d M.data.d (Finset.univ : Finset (Fin (a*p)))=
      M.data.d^(a*p) := by
    rw [←source_factor_scale_product]
    simp [sourceFactorScale]
  rw [Hscale] at H
  have Hbudget : ((2*(Ca+Cb*Cr+1))^(a*p)*M.data.d^(a*p))^2=
      (C^a*M.data.d^a)^(2*p) := by
    dsimp only [C]
    rw [pow_mul,pow_mul,←mul_pow,←pow_mul,Nat.mul_comm p 2]
  rw [Hbudget] at H
  have HE : (fun σ=>(P.product σ^p)^2)=(fun σ=>|P.product σ|^(2*p)) := by
    funext σ
    exact (abs_even_repeat_square (P.product σ) p).symm
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
