module

public import ComparisonSignedCavityWholeLawScalarClock
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def scalarPhysicalSquareLowKernel (n U : ℕ) (b h K : ℕ→ℝ) (s : ℝ) :
    ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ :=
  ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K)

theorem scalarPhysicalSquareLowKernel_abs_low_eq_affine (n U : ℕ) (b h K : ℕ→ℝ)
    (s : ℝ) {j : ℕ} (hj : j<U) (σ τ : Spin n×Bool) :
    |scalarPhysicalSquareLowKernel n U b h K s j σ τ|=
      |fullBoundaryAffineFactor n ((1-s)*K j+s*h j) (s*b j) σ τ| := by
  rw [scalarPhysicalSquareLowKernel,coordinateProfile_eq_rowCovarianceKernel,
    cutLSlope,ite_eq_left hj,fullVariance_row_covariance]
  simp only [abs_mul,abs_spinValue,one_mul]
  congr 1
  unfold fullBoundaryAffineFactor
  ring

theorem scalarPhysicalSquareLowKernel_at_high (n U : ℕ) (b h K : ℕ→ℝ)
    (s : ℝ) {j : ℕ} (hj : ¬j<U) (σ τ : Spin n×Bool) :
    scalarPhysicalSquareLowKernel n U b h K s j σ τ=0 := by
  simp only [scalarPhysicalSquareLowKernel,ReplicaTree.coordinateProfile,cutLSlope,hj,ite_false,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem scalarPhysicalSquareLow_finite_moment_le_natural (n p U : ℕ) (hp : 0<p)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t s : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (b h K : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (j : ℕ) (hj : j ≤ as.length)
    {Ch Ck Cb Cd natural : ℝ} (hCh : 0 ≤ Ch) (hCk : 0 ≤ Ck)
    (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hnat : 0<natural)
    (hfield : j<U → |h j| ≤ Ch*natural) (hscalar : j<U → |K j| ≤ Ck*natural)
    (hbond : b j ≤ Cb)
    (hraw : finitePhysicalDeletedRawBudget n p as b h j ≤ (Cd*natural)^(2*p)) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|scalarPhysicalSquareLowKernel n U b h K s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p)) 0 ≤
      (2*(Ch+Ck+Cb*Cd+1)*natural)^(2*p) := by
  by_cases hlow : j<U
  · let α:=(1-s)*K j+s*h j
    let β:=s*b j
    have hα : |α| ≤ (Ch+Ck)*natural := by
      calc
        |α| ≤ |(1-s)*K j|+|s*h j| := abs_add_le _ _
        _ = (1-s)*|K j|+s*|h j| := by
          rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
        _ ≤ |K j|+|h j| := add_le_add
          (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hs.1]))
          (mul_le_of_le_one_left (abs_nonneg _) hs.2)
        _ ≤ Ck*natural+Ch*natural := add_le_add (hscalar hlow) (hfield hlow)
        _ = _ := by ring
    have hβ : |β| ≤ Cb := by
      rw [abs_of_nonneg (mul_nonneg hs.1 (hb0 j))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (hb0 j)]
    have H:=actual_full_square_mixed_pair_moment_le n p U ho hl ht b h hb hh hb0 hh0 j hj α β
    have HB:=actual_affine_boundary_raw_budget_le n p hp as b h j hnat
      (add_nonneg hCh hCk) hCb hCd hα hβ hraw
    have hsym (σ τ : Spin (n+1)) : deletedOverlap n σ τ=deletedOverlap n τ σ := by
      unfold deletedOverlap
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have HE : (fun σ=>|scalarPhysicalSquareLowKernel n U b h K s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p))=
      (fun σ=>|fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).2
        (ClockTree.pairSpin as j σ).1|^(2*p)) := by
      funext σ
      rw [scalarPhysicalSquareLowKernel_abs_low_eq_affine n U b h K s hlow]
      change |fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^(2*p)=_
      congr 2
      unfold fullBoundaryAffineFactor
      rw [hsym]
    rw [HE]
    exact H.trans HB
  · simp_rw [scalarPhysicalSquareLowKernel_at_high n U b h K s hlow,
      abs_zero,zero_pow (by omega : 2*p≠0)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    exact pow_nonneg (by positivity) _

theorem eventually_actual_minimum_bare_scalar_wholeLaw_low_profile_moment
    (p : ℕ) (hp : 0 < p) (Bclock Temp Bscalar Cscalar : ℝ)
    (hTemp : 0 ≤ Temp) (hBscalar : 0 ≤ Bscalar) (hCscalar : 0 ≤ Cscalar)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cq : ℝ,0 < Cq ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (K : ℕ→ℝ) (l t s : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
          Monotone K → (∀j,0 ≤ K j) → K as.length ≤ Bscalar →
        ∀j,j ≤ as.length → (j<U → |K j| ≤ Cscalar*(M.xs+partitionPoint 0 as j)) →
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|scalarPhysicalSquareLowKernel n U b h K s j
              (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p)) 0 ≤
            (Cq*(M.xs+partitionPoint 0 as j))^(2*p) := by
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  let Btotal:=4*Cf+2*Temp
  have hCf : 0 ≤ Cf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  have hBtotal : 0 ≤ Btotal:=by dsimp [Btotal];positivity
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) p hp Bclock Btotal Temp hm hdelta hroom hcl hcu hAz hC0 hCt
  let E:=Real.exp (wholeLawRowComparisonConstant 2*(Bscalar+Btotal))
  let Cfinite:=2*(Cf+Cscalar+Temp*Cd+1)
  have hCfinite : 0<Cfinite:=by dsimp [Cfinite];positivity
  refine ⟨E*Cfinite,mul_pos (Real.exp_pos _) hCfinite,?_⟩
  filter_upwards [HR] with n hn
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U K l t s hl ht hs hKm hK0 hKbound j hj hKlocal
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let Kfinite:=finitePhysicalMixedClock (n+1) as b h
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have hb0 : ∀j,0 ≤ b j:=fun _=>NNReal.coe_nonneg _
  have hh0 : ∀j,0 ≤ h j:=fun _=>NNReal.coe_nonneg _
  have hKfinite0 : ∀j,0 ≤ Kfinite j:=finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0
  have hKfinitem : Monotone Kfinite:=finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0
  have Hclock:=M.bare_sampled_full_square_clock_budget hcl hAz Temp hbareb hbareh hxs1 as ho
  have Hend:=M.bare_source_clock_bounds hcl hAz Temp hbareb hbareh (partitionPoint_mem as ho as.length)
  have Hj:=M.bare_source_clock_bounds hcl hAz Temp hbareb hbareh (partitionPoint_mem as ho j)
  have Hraw:=hgrid j hj Hclock Hend.2.1
  have hnat : 0 < M.xs+partitionPoint 0 as j:=
    add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho j).1
  have Hfinite:=scalarPhysicalSquareLow_finite_moment_le_natural n p U hp ho hl ht hs
    b h K hb hh hb0 hh0 j hj hCf hCscalar hTemp hCd.le
    hnat
    (fun _=>by rw [abs_of_nonneg Hj.2.2.1];exact Hj.2.2.2) hKlocal Hj.2.1 Hraw
  have HKfinite : Kfinite as.length ≤ Btotal := by
    have H1:=hb0 as.length
    have H2:=hh0 as.length
    dsimp only [Kfinite] at ⊢
    change finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal at Hclock
    linarith
  have H:=native_wholeLaw_scalar_clock_nat_moment_le n U 2 (2*p) (by omega)
    (ClockTree.pairClock as j) ho (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K Kfinite
    (fun i=>by cases i <;> first | exact hb | exact hh)
    (fun j i=>by cases i <;> first | exact hb0 j | exact hh0 j)
    hb hh hKm hKfinitem hb0 hh0 hK0 hKfinite0 hl ht
    (fun σ=>scalarPhysicalSquareLowKernel n U b h K s j
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
    (Cfinite*(M.xs+partitionPoint 0 as j)) (Bscalar+Btotal)
    (mul_nonneg hCfinite.le hnat.le) (add_nonneg hBscalar hBtotal)
    (by simp only [ClockTree.pairClock_leaves];exact le_rfl) (add_le_add hKbound HKfinite) Hfinite
  simpa only [E,mul_assoc] using H

end OAI.SKFluctuations.Cavity
