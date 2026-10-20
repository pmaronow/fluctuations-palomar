module

public import ComparisonSignedCavityWholeLawProfileBudgets

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def finitePhysicalSquareLowKernel (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (t : ℝ) : ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ :=
  ReplicaTree.coordinateProfile (fullFeature n)
    (cutLSlope n U t b h (finitePhysicalMixedClock (n+1) as b h))

theorem finitePhysicalSquareLowKernel_abs_low_eq_affine (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (t : ℝ) {j : ℕ} (hj : j < U) (σ τ : Spin n×Bool) :
    |finitePhysicalSquareLowKernel n U as b h t j σ τ|=
      |fullBoundaryAffineFactor n ((1-t)*finitePhysicalMixedClock (n+1) as b h j+t*h j)
        (t*b j) σ τ| := by
  rw [finitePhysicalSquareLowKernel,coordinateProfile_eq_rowCovarianceKernel,
    cutLSlope,ite_eq_left hj,fullVariance_row_covariance]
  simp only [abs_mul,abs_spinValue,one_mul]
  congr 1
  unfold fullBoundaryAffineFactor
  ring

theorem finitePhysicalSquareLowKernel_at_high (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (t : ℝ) {j : ℕ} (hj : ¬j < U) (σ τ : Spin n×Bool) :
    finitePhysicalSquareLowKernel n U as b h t j σ τ=0 := by
  simp only [finitePhysicalSquareLowKernel,ReplicaTree.coordinateProfile,cutLSlope,hj,ite_false,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem finitePhysicalSquareLow_moment_le_natural (n p U : ℕ) (hp : 0 < p)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t s : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (j : ℕ) (hj : j ≤ as.length)
    {Ch Cb Cd natural : ℝ} (hCh : 0 ≤ Ch) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hnat : 0 < natural)
    (hfield : j < U → |h j| ≤ Ch*natural) (hbond : b j ≤ Cb)
    (hraw : finitePhysicalDeletedRawBudget n p as b h j ≤ (Cd*natural)^(2*p)) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p)) 0 ≤
      (2*(Ch+2*Cb*Cd+1)*natural)^(2*p) := by
  by_cases hlow : j < U
  · let K:=finitePhysicalMixedClock (n+1) as b h
    let α:=(1-s)*K j+s*h j
    let β:=s*b j
    have hS:=finitePhysicalMean_le_of_deleted_raw n p hp ho b h j hj hb0 hh0
      (mul_nonneg hCd hnat.le) hraw
    have hSn:=finitePhysicalMean_nonneg (n+1) as b h j
    have hKge : h j ≤ K j:=by dsimp [K,finitePhysicalMixedClock];nlinarith [mul_nonneg (hb0 j) hSn]
    have hKle : K j ≤ (Ch+Cb*Cd)*natural := by
      have Hf: h j ≤ Ch*natural:=(le_abs_self _).trans (hfield hlow)
      have Hm:=mul_le_mul hbond hS hSn hCb
      dsimp [K,finitePhysicalMixedClock]
      nlinarith
    have hαn : 0 ≤ α:=add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2)
      (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0 j)) (mul_nonneg hs.1 (hh0 j))
    have hα : |α| ≤ (Ch+Cb*Cd)*natural:=by
      rw [abs_of_nonneg hαn]
      dsimp [α]
      nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hKge)]
    have hβ : |β| ≤ Cb:=by
      rw [abs_of_nonneg (mul_nonneg hs.1 (hb0 j))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (hb0 j)]
    have H:=actual_full_square_mixed_pair_moment_le n p U ho hl ht b h hb hh hb0 hh0 j hj α β
    have HB:=actual_affine_boundary_raw_budget_le n p hp as b h j hnat
      (show 0 ≤ Ch+Cb*Cd by positivity) hCb hCd hα hβ hraw
    have hsym (σ τ : Spin (n+1)) : deletedOverlap n σ τ=deletedOverlap n τ σ := by
      unfold deletedOverlap
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have HE : (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p))=
      (fun σ=>|fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).2
        (ClockTree.pairSpin as j σ).1|^(2*p)) := by
      funext σ
      rw [finitePhysicalSquareLowKernel_abs_low_eq_affine n U as b h s hlow]
      change |fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^(2*p)=_
      congr 2
      unfold fullBoundaryAffineFactor
      rw [hsym]
    rw [HE]
    apply H.trans
    convert HB using 1
    ring
  · simp_rw [finitePhysicalSquareLowKernel_at_high n U as b h s hlow,
      abs_zero,zero_pow (by omega : 2*p≠0)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    exact pow_nonneg (by positivity) _

theorem eventually_actual_minimum_wholeLaw_low_profile_moment
    (p : ℕ) (hp : 0 < p) (Bclock Btotal Bbond Ch : ℝ) (hBbond : 0 ≤ Bbond) (hCh : 0 ≤ Ch)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cq : ℝ,0 < Cq ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (l t s : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
          ∀j,j ≤ as.length →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (j < U → |h j| ≤ Ch*(M.xs+partitionPoint 0 as j)) →
            (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t)
              (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
                (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*p)) 0 ≤
              (Cq*(M.xs+partitionPoint 0 as j))^(2*p) := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) p hp Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*(Ch+2*Bbond*Cd+1),by positivity,?_⟩
  filter_upwards [HR] with n hn
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U l t s hl ht hs j hj hclock hbond hfield
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  exact finitePhysicalSquareLow_moment_le_natural n p U hp ho hl ht hs b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj hCh hBbond hCd.le
    (add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho j).1) hfield
    ((hb hj).trans hbond) (hk j hj hclock hbond)

end OAI.SKFluctuations.Cavity
