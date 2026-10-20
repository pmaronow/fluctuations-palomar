module

public import ComparisonSignedCavityInheritedContinuumPairMoment
public import CavityAttachedTree
public import ComparisonSignedCavityFreshGraft

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 14000000

theorem eventually_actual_minimum_inherited_original_target_pair_rms
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        ∀(T : ClockTree (Spin n×Bool) as) (s z : T.Slot),s≠z→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as (T.splitIndex s z) ≤ Ccut*x→
          Real.sqrt (T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>(deletedOverlap n (joinSpin (T.atSlot σ s))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex s z))^2) 0) ≤ C*x := by
  obtain ⟨Cd,hCd,H⟩:=eventually_actual_minimum_inherited_continuum_centered_pair_moment
    (D:=D) 1 (by norm_num) Bclock Temp Cf hTemp hCf
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cd*(1+Ccut),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hsource hxs1 L us hus hret hmesh] with jGrid hk
  dsimp only at hk ⊢
  intro U l t hl ht T s z hsz x hxs hmass
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hu:=partitionPoint_mem (finiteCutMasses us jGrid) ho (T.splitIndex s z)
  have Hpair:=hk U l t hl ht (T.splitIndex s z) (T.splitIndex_le_clockLength s z)
  rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 _ 0
    s z hsz (fun u v=>(deletedOverlap n (joinSpin u) (joinSpin v)-
      orderedPathS (n+1) M.bf M.hf
        (partitionPoint 0 (finiteCutMasses us jGrid) (T.splitIndex s z)))^2)]
  apply (Real.sqrt_le_iff).2
  constructor
  · have hx:=M.hxs.trans_le hxs
    positivity
  · apply (show _ ≤ (Cd*(M.xs+partitionPoint 0 (finiteCutMasses us jGrid)
        (T.splitIndex s z)))^2 by simpa only [Nat.mul_one,sq_abs] using Hpair).trans
    apply pow_le_pow_left₀ (mul_nonneg hCd.le (add_nonneg M.hxs.le Hu.1))
    have Hscale : M.xs+partitionPoint 0 (finiteCutMasses us jGrid) (T.splitIndex s z) ≤
        (1+Ccut)*x := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hscale hCd.le

end OAI.SKFluctuations.Cavity
