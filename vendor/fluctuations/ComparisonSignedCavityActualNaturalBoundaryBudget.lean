module

public import ComparisonSignedCavityActualBoundaryLayerBudget
public import ComparisonSignedCavityActualFactorRawCalibration
public import ComparisonSignedCavityActualAllHighResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

structure ActualNaturalBoundaryShape (n a : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) where
  α : Fin a→ℝ
  β : Fin a→ℝ
  i : Fin a→T.Slot
  j : Fin a→T.Slot
  distinct : ∀e,i e≠j e
  lowInGrid : ∀e,T.splitIndex (i e) (j e)≤as.length

def ActualNaturalBoundaryShape.product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (σ : T.Assignment) : ℝ :=
  fullBoundaryAffineProduct n G.α G.β
    (fun e=>T.atSlot σ (G.j e)) (fun e=>T.atSlot σ (G.i e))

def ActualNaturalBoundaryShape.calibratedForest {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (b h : ℕ→ℝ) (ha : 0<a) (natural : Fin a→ℝ) (hnat : ∀e,0 < natural e)
    (Ca Cb Cd : ℝ) (hCa : 0≤Ca) (hCb : 0≤Cb) (hCd : 0≤Cd)
    (hα : ∀e,|G.α e|≤Ca*natural e) (hβ : ∀e,|G.β e|≤Cb)
    (hDeleted : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e))≤(Cd*natural e)^(2*a)) :
    ActualMixedBoundaryForest n a T b h where
  α:=G.α
  β:=G.β
  i:=G.i
  j:=G.j
  k:=G.j
  distinctLeft:=G.distinct
  distinctRight:=G.distinct
  sameLow:=fun _=>rfl
  retainedHigh:=fun _ H=>(H rfl).elim
  lowInGrid:=G.lowInGrid
  rho:=fun e=>2*(Ca+Cb*Cd+1)*natural e
  rhoPos:=fun e=>by have H:=hnat e;positivity
  raw:=fun e=>actual_affine_boundary_raw_budget_le n a ha as b h _ (hnat e)
    hCa hCb hCd (hα e) (hβ e) (hDeleted e)

theorem actual_calibrated_boundary_shape_product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (b h : ℕ→ℝ) (ha : 0<a) (natural : Fin a→ℝ) (hnat : ∀e,0 < natural e)
    (Ca Cb Cd : ℝ) (hCa : 0≤Ca) (hCb : 0≤Cb) (hCd : 0≤Cd)
    (hα : ∀e,|G.α e|≤Ca*natural e) (hβ : ∀e,|G.β e|≤Cb)
    (hDeleted : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e))≤(Cd*natural e)^(2*a)) :
    (∏e,(G.calibratedForest b h ha natural hnat Ca Cb Cd hCa hCb hCd hα hβ hDeleted).rho e)=
      (2*(Ca+Cb*Cd+1))^a*(∏e,natural e) := by
  simp only [ActualNaturalBoundaryShape.calibratedForest,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]

theorem actual_saved_exterior_calibrated_first (C0 xs W v : ℝ) :
    savedExteriorScale (C0*xs) W v=C0^3*savedExteriorScale xs W v := by
  unfold savedExteriorScale
  rw [mul_pow]
  ring

def actualNaturalDeletedConstant (K Btotal Bbond : ℝ) : ℝ :=
  actualBoundaryScalarConstant 1 (Real.exp (220*Btotal)) (Real.exp (110*Bbond)) 1*(K+1)

theorem actualNaturalDeletedConstant_pos {K Btotal Bbond : ℝ} (hK : 0≤K) :
    0<actualNaturalDeletedConstant K Btotal Bbond := by
  unfold actualNaturalDeletedConstant actualBoundaryScalarConstant
  positivity

theorem actual_deleted_raw_budget_from_overlap (n a : ℕ) (ha : 0<a)
    (as : List PositiveMass) (b h : ℕ→ℝ) (low : ℕ)
    {K Btotal Bbond natural : ℝ} (hK : 0≤K) (hnat : 0<natural)
    (hclock : finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤Btotal)
    (hbond : b as.length≤Bbond) (hsite : 1/(n+1:ℕ)≤natural)
    (hoverlap : physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun k=>physicalCompletedClock (n+1) b h (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id low≤K*natural^(2*a)) :
    finitePhysicalDeletedRawBudget n a as b h low≤
      (actualNaturalDeletedConstant K Btotal Bbond*natural)^(2*a) := by
  let s:=(K+1)*natural
  have hs : 0<s := by dsimp [s];positivity
  have hKpow : K≤(2*(K+1))^(2*a) := by
    apply (show K≤2*(K+1) by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show 1≤2*(K+1) by linarith) (show 1≤2*a by omega)
  have hmoment : physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun k=>physicalCompletedClock (n+1) b h (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id low≤(2*s)^(2*a) := by
    apply hoverlap.trans
    simpa only [s,mul_pow,mul_assoc] using mul_le_mul_of_nonneg_right hKpow (by positivity)
  have hsite' : (1:ℝ)/(n+1:ℕ)≤2*s := hsite.trans (by dsimp [s];nlinarith)
  have hrow : Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+
      b as.length+h as.length))≤Real.exp (220*Btotal) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hcomp : Real.exp (110*b as.length)≤Real.exp (110*Bbond) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have H := actual_boundary_scalar_budget_le a ha
    (by norm_num : (0:ℝ)≤1) (Real.exp_nonneg _) (Real.exp_nonneg _) (by norm_num : (0:ℝ)<1)
    hnat (le_of_eq (one_mul natural)) hs.le (by norm_num : |(1:ℝ)|≤1)
    (Real.exp_nonneg _) hrow (Real.exp_nonneg _) hcomp
    (by positivity : (0:ℝ)≤1/(n+1:ℕ)) hsite'
  simp only [abs_one,one_pow,one_mul] at H
  have hcomp0 : 0≤Real.exp (110*b as.length) := Real.exp_nonneg _
  have H' := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hmoment hcomp0)
      (le_refl ((1/(n+1:ℕ):ℝ)^(2*a))))
    (show 0≤Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+
      b as.length+h as.length))*(2:ℝ)^(2*a-1) by positivity)
  apply H'.trans
  rw [div_mul_cancel₀
    (actualBoundaryScalarConstant 1 (Real.exp (220*Btotal)) (Real.exp (110*Bbond)) 1*s)
    hnat.ne'] at H
  simpa only [actualNaturalDeletedConstant,s,mul_assoc] using H

theorem actual_sampled_completed_clock_eq (n : ℕ)
    (bf hf : ℝ→ℝ≥0) (hb : MonotoneOn bf (Icc (0:ℝ) 1))
    (hh : MonotoneOn hf (Icc (0:ℝ) 1)) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    stepClockValues (fun i=>(completedPathClock n bf hf 0 i:ℝ))
      (sampleClockSteps (completedPathClock n bf hf) 0 as)=
    physicalCompletedClock n (fun j=>(bf (partitionPoint 0 as j):ℝ))
      (fun j=>(hf (partitionPoint 0 as j):ℝ)) := by
  funext j i
  rw [sampleClockSteps_values _ (completedPathClock_monotone n hb hh) as ho,
    partitionValues_point]
  cases i <;> rfl

theorem actual_sampled_completed_diagonal_steps_eq (n : ℕ)
    (bf hf : ℝ→ℝ≥0) (hb : MonotoneOn bf (Icc (0:ℝ) 1))
    (hh : MonotoneOn hf (Icc (0:ℝ) 1)) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    diagonalBoundarySteps as
      (physicalCompletedClock n (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ)) 0)
      (fun k=>physicalCompletedClock n (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ)) (k+1))=
      sampleClockSteps (completedPathClock n bf hf) 0 as := by
  rw [←actual_sampled_completed_clock_eq n bf hf hb hh as ho,←clockSteps_cumulative]
  exact sampled_clockSteps_native n (completedPathClock n bf hf) as ho

theorem eventually_actual_minimum_deleted_raw_on_retained_net
    (a : ℕ) (ha : 0<a) (Bclock Btotal Bbond : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
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
  obtain ⟨K,hK,hraw⟩ := eventually_actual_minimum_finite_overlap_on_retained_net
    (D:=D) (a-1) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HE := (tendsto_add_atTop_nat 1).eventually hraw
  have HS := (tendsto_add_atTop_nat 1).eventually
    (eventually_actual_minimum_inverse_size_le_scale (D:=D) (delta:=delta)
      (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) Bclock hm hC0)
  refine ⟨actualNaturalDeletedConstant K Btotal Bbond,
    actualNaturalDeletedConstant_pos hK.le,?_⟩
  filter_upwards [HE,HS] with n hn hsite
  intro M L us hus hret hmesh
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hb := toNNReal_monotoneOn had.1
  have hh := toNNReal_monotoneOn had.2.1
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

theorem actual_full_boundary_forest_product_square_le (n U a : ℕ) (ha : 0<a)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0≤b j) (hh0 : ∀j,0≤h j) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (G : ActualMixedBoundaryForest n a T b h) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>G.product σ^2) 0≤(∏e,G.rho e)^2 := by
  let q:=finitePhysicalCavityVariance n U as b h t
  let f:=fun e σ=>fullBoundaryAffineFactor n (G.α e) (G.β e)
    (T.atSlot σ (G.j e)) (T.atSlot σ (G.i e))
  apply finite_weighted_product_square_scales ha
    (fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0) f
    (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0).1
    G.rho G.rhoPos
  intro e
  change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|f e σ|^(2*a)) 0≤_
  rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
    (G.i e) (G.j e) (G.distinctLeft e)
    (fun d c=>|fullBoundaryAffineFactor n (G.α e) (G.β e) c d|^(2*a))]
  exact (actual_full_mixed_pair_moment_le n a U ho ht b h hb hh hb0 hh0 _
    (G.lowInGrid e) (G.α e) (G.β e)).trans (G.raw e)

theorem eventually_actual_minimum_natural_forest_product
    (a : ℕ) (ha : 0<a) (Bclock Btotal Bbond Ca Cb : ℝ)
    (hCa : 0≤Ca) (hCb : 0≤Cb)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀ (U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),t∈Icc (0:ℝ) 1 →
          ∀ (G : ActualNaturalBoundaryShape n a T) (scale : ℝ),0 < scale →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤Btotal →
            b as.length≤Bbond →
            (∀e,|G.α e|≤Ca*max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            (∀e,|G.β e|≤Cb) →
            T.disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavityVariance n U as b h t) (fun σ=>G.product σ^2) 0≤
              ((2*(Ca+Cb*Cd+1))^a*
                (∏e,max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))))^2 := by
  obtain ⟨Cd,hCd,Hraw⟩ := eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) a ha Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cd,hCd,?_⟩
  filter_upwards [Hraw] with n hn
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T t ht G scale hscale hclock hbond hα hβ
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let natural:=fun e=>max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))
  have hnat : ∀e,0 < natural e:=fun e=>hscale.trans_le (le_max_left _ _)
  have hr : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e))≤(Cd*natural e)^(2*a) := by
    intro e
    apply (hk _ (G.lowInGrid e) hclock hbond).trans
    apply pow_le_pow_left₀
      (mul_nonneg hCd.le (add_nonneg M.hxs.le (partitionPoint_mem as
        (finiteCutMasses_ordered us hus k) _).1))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hCd.le) _
  let P:=G.calibratedForest b h ha natural hnat Ca Cb Cd hCa hCb hCd.le hα hβ hr
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as
    (finiteCutMasses_ordered us hus k)
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as
    (finiteCutMasses_ordered us hus k)
  have H:=actual_full_boundary_forest_product_square_le n U a ha T
    (finiteCutMasses_ordered us hus k) b h hb hh (fun _=>NNReal.coe_nonneg _)
    (fun _=>NNReal.coe_nonneg _) ht P
  have Hprod:=actual_calibrated_boundary_shape_product G b h ha natural hnat Ca Cb Cd
    hCa hCb hCd.le hα hβ hr
  change T.disorderExpect (fullWeight n) (fullFeature n) 0
    (finitePhysicalCavityVariance n U as b h t) (fun σ=>G.product σ^2) 0≤
    ((2*(Ca+Cb*Cd+1))^a*(∏e,natural e))^2
  rw [←Hprod]
  exact H

theorem eventually_actual_minimum_natural_boundary_clone_budget
    (a N : ℕ) (ha : 0<a) (Bclock Btotal Bbond Ca Cb Ccal Rmacro F : ℝ)
    (hBt : 0≤Btotal) (hBb : 0≤Bbond) (hCa : 0≤Ca) (hCb : 0≤Cb)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCcal : 1≤Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀ (u : PositiveMass),u.val≤1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val≤1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val≤1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
          ∀ (U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),t∈Icc (0:ℝ) 1 →
          ∀ (G : ActualNaturalBoundaryShape n a T) (target : T.Slot) (cut : ℕ),
            (∀e,T.splitIndex target (G.i e)<cut) → cut≤as.length →
            (ClockTree.nativeCloneBlockAtSlot T target cut).tree.leaves≤N →
          ∀ (scale : ℝ),0 < scale →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤Btotal →
            b as.length≤Bbond → W≤Rmacro/2 → 0 < partitionPoint 0 as cut →
            4*W≤M.R (partitionPoint 0 as cut) →
            M.z ≤ min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
            (∀e,cut≤T.splitIndex target (G.j e) →
              M.R (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))≤
                min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4)) →
            (∀e,|G.α e|≤Ca*max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            (∀e,|G.β e|≤Cb) →
            zeroContinuation (Measure.pi fun i=>gaussianReal 0
              (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
              (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
                (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
                  (fun j=>finitePhysicalCavityVariance n U as b h t (j+1)))
                (fun σ τ=>(G.product σ-G.product τ)^2)) 0≤
              ((a:ℝ)*(actualBoundaryScalarConstant Cb
                (actualBoundaryUniformRowFactor N Btotal)
                (actualBoundaryUniformRowFactor N (Bbond/2)) 1*
                ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale (C0*M.xs) W (partitionPoint 0 as cut)/scale)*
                ((2*(Ca+Cb*Cd+1))^a*
                  (∏e,max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))))))^2 := by
  obtain ⟨Cd,hCd,Hraw⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) a ha Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=(tendsto_add_atTop_nat 1).eventually
    (eventually_native_minimum_calibrated_all_high_boundary_resampling (D:=D)
      (a-1) Bclock Ccal Rmacro F hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hCcal hmacro hRhalf hFmass hFradius)
  have HE:=(tendsto_add_atTop_nat 1).eventually
    (eventually_omitted_site_le_saved_boundary (show eta<1/2+3*m by linarith)
      (show 0 < Rmacro/2 by positivity))
  refine ⟨Cd,hCd,?_⟩
  filter_upwards [Hraw,HS,HE] with n hn hsave hsite
  intro M hcompare u hu extra hextra
  obtain ⟨L,hL⟩:=exists_nat_one_div_lt M.hxs
  let net:=uniformMasses L
  have hnet : ∀v∈net,v.val≤1:=(uniformMasses_ordered L).members_le_one
  have hmesh : ((L+1:ℕ):ℝ)⁻¹≤M.xs:=by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hL.le
  obtain ⟨us,hus,huus,hextraus,hfinite⟩:=hsave M hcompare u hu (extra++net)
    (fun v hv=>by rcases List.mem_append.mp hv with hv|hv;exact hextra v hv;exact hnet v hv)
  have hret : ∀v∈uniformMasses L,v∈us:=fun v hv=>hextraus v (List.mem_append_right extra hv)
  refine ⟨us,hus,huus,(fun v hv=>hextraus v (List.mem_append_left net hv)),?_⟩
  filter_upwards [hfinite,hn M L us hus hret hmesh] with k hk hraw
  dsimp only at hk hraw ⊢
  intro U T t ht G target cut hout hcut hleaves scale hscale hclock hbond
    hWmacro hv hhigh hzs hlow hα hβ
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let v:=partitionPoint 0 as cut
  let natural:=fun e=>max scale (M.xs+partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))
  have hnat : ∀e,0 < natural e:=fun e=>hscale.trans_le (le_max_left _ _)
  have hDeleted : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e))≤(Cd*natural e)^(2*a) := by
    intro e
    apply (hraw _ (G.lowInGrid e) hclock hbond).trans
    apply pow_le_pow_left₀
      (mul_nonneg hCd.le (add_nonneg M.hxs.le (partitionPoint_mem as
        (finiteCutMasses_ordered us hus k) _).1))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hCd.le) _
  let A:=G.calibratedForest b h ha natural hnat Ca Cb Cd hCa hCb hCd.le hα hβ hDeleted
  let p:=ClockTree.nativeCloneBlockAtSlot T target cut
  let P:=A.cloneAt target cut hout
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbM:=toNNReal_monotoneOn had.1
  have hhM:=toNNReal_monotoneOn had.2.1
  have hb : Monotone b:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>hbM hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>hhM hx hy hxy) as ho
  have hQ:=actual_sampled_completed_clock_eq (n+1) M.bf M.hf hbM hhM as ho
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hr : 0 < C0*M.xs:=mul_pos hC0 M.hxs
  have hcrit:=native_minimum_original_boundary_critical_radius hC0 M
  let save:=((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale (C0*M.xs) W v
  have hsavepos : 0 < save:=mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (div_pos (pow_pos hr _) (Real.sqrt_pos.2 (by positivity)))
  have hsite' : 2/(n+1:ℕ)≤2*save:=by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (hsite (C0*M.xs) W v hr hW hv hWmacro (partitionPoint_mem as ho cut).2 hcrit)
      (by norm_num : (0:ℝ)≤2)
  let Cr:=actualBoundaryUniformRowFactor N Btotal
  let Cc:=actualBoundaryUniformRowFactor N (Bbond/2)
  let Cs:=actualBoundaryScalarConstant Cb Cr Cc 1
  have hCs : 0 < Cs:=by unfold Cs actualBoundaryScalarConstant Cr Cc actualBoundaryUniformRowFactor;positivity
  have hRow:=native_boundary_row_factor_le_of_bounded_clock n N p.tree b h hBt hleaves hclock
  have hComp:=native_boundary_completion_factor_le_of_bounded_clock n N p.tree b
    (show 0≤Bbond/2 by positivity) hleaves (by linarith)
  have hRho : ∀e,1*scale≤P.rho e:=by
    intro e
    change 1*scale≤2*(Ca+Cb*Cd+1)*natural e
    have hne : scale≤natural e:=le_max_left _ _
    nlinarith [hCd.le,hnat e,mul_nonneg hCb hCd.le]
  have Hmoment : p.tree.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>P.difference σ^2) 0≤
      ((a:ℝ)*(Cs*save/scale)*(∏e,P.rho e))^2 := by
    apply actual_full_mixed_forest_from_physical_resampling n U p.tree ho b h hb hh
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) ht ha
      P.α P.β P.i P.j P.k P.distinctLeft P.distinctRight P.sameLow P.retainedHigh P.lowInGrid
      P.rho P.rhoPos (div_pos (mul_pos hCs hsavepos) hscale) P.raw
    intro e he
    have hin : cut≤T.splitIndex target (G.j e):=by
      by_contra H
      exact he (ClockTree.nativeCloneBlockAtSlot_exterior_shared T target cut (G.j e) (by omega))
    have HG:=ClockTree.nativeCloneBlockAtSlot_boundary_geometry T target (G.j e) (G.i e) cut hin (hout e)
    have H:=hk (T.splitIndex (G.i e) (G.j e)) cut hcut hWmacro hhigh hzs (hlow e hin)
    rw [hQ] at H
    have ha' : a-1+1=a:=by omega
    rw [ha'] at H
    have H' : originalBoundaryResamplingMoment (n+1) a as (physicalCompletedClock (n+1) b h)
        (T.splitIndex (G.i e) (G.j e)) cut≤(2*save)^(2*a):=by
      simpa only [save,mul_assoc] using H
    have Hdom:=actual_boundary_scalar_budget_le a ha hCb (by dsimp [Cr,actualBoundaryUniformRowFactor];positivity)
      (by dsimp [Cc,actualBoundaryUniformRowFactor];positivity) (by norm_num : (0:ℝ)<1)
      hscale (hRho e) hsavepos.le (hβ e)
      (by unfold nativeBoundaryRowFactor;positivity) hRow
      (by unfold nativeBoundaryCompletionFactor;positivity) hComp (by positivity) hsite'
    apply le_trans _ (by simpa only [Cs,save,mul_assoc] using Hdom)
    unfold nativeMixedBoundaryReplacementBudget
    change _*_*_*(_*originalBoundaryResamplingMoment (n+1) a as (physicalCompletedClock (n+1) b h)
      (p.tree.splitIndex (p.oldEmbed (G.i e)) (p.oldEmbed (G.j e)))
      (p.tree.splitIndex (p.oldEmbed (G.j e)) (p.newEmbed (G.j e)))+_)≤_
    rw [HG.2.1,HG.2.2.2]
    have hcomp0 : 0≤nativeBoundaryCompletionFactor n p.tree b:=by unfold nativeBoundaryCompletionFactor;positivity
    have hcoef0 : 0≤|P.β e|^(2*a)*nativeBoundaryRowFactor n p.tree b h*(2:ℝ)^(2*a-1):=by
      unfold nativeBoundaryRowFactor
      positivity
    have HM:=mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left H' hcomp0) (le_refl ((2/(n+1:ℕ):ℝ)^(2*a)))) hcoef0
    simpa only [save,mul_assoc,P,ActualMixedBoundaryForest.cloneAt,A,
      ActualNaturalBoundaryShape.calibratedForest] using HM
  have Hprod:=actual_calibrated_boundary_shape_product G b h ha natural hnat Ca Cb Cd
    hCa hCb hCd.le hα hβ hDeleted
  have Hlaw:=actual_original_cloned_boundary_forest_moment_eq n U a T ho b h t A target cut hout
  have heq : A.product=G.product:=rfl
  rw [heq] at Hlaw
  rw [Hlaw]
  rw [show (∏e,P.rho e)=(2*(Ca+Cb*Cd+1))^a*(∏e,natural e) from Hprod] at Hmoment
  simpa only [Cs,Cr,Cc,save,mul_assoc] using Hmoment

end OAI.SKFluctuations.Cavity
