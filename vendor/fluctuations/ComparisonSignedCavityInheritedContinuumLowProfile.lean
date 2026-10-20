module

public import ComparisonSignedCavityInheritedContinuumPairMoment

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_continuum_low_profile_moment
    (order : ℕ) (horder : 0<order) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
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
  obtain ⟨Cd,hCd,HP⟩:=eventually_actual_minimum_inherited_continuum_centered_pair_moment
    (D:=D) order horder Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs
  have hCk : 0 ≤ Ck:=by dsimp [Ck];positivity
  refine ⟨2*(Ck+Temp*Cd+1),by positivity,?_⟩
  filter_upwards [HP,(tendsto_add_atTop_nat 1).eventually HS] with n hnP hnS
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hsource hxs1 L us hus hret hmesh] with jGrid hgridP
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
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
  have Hdelta:=hgridP U l t hl ht j hj
  have Hsource:=hsource _ hu
  have HSu : |S j| ≤ Cs*natural := by
    dsimp only [S]
    rw [Hcenter]
    exact continuum_center_bound_closed_interval (n+1) M.bf M.hf M.hxs.le hCs.le (hnS M) _ hu
  have HK : |h j+b j*S j| ≤ Ck*natural := by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_mul,abs_of_nonneg (NNReal.coe_nonneg _)]
    have HB:=mul_le_mul Hsource.1 HSu (abs_nonneg _) hTemp
    dsimp only [Ck,natural]
    nlinarith [Hsource.2]
  exact native_continuum_low_kernel_moment_le n U (2*order) (by omega) ho _ b h S hs j
    hCk hTemp hCd.le hnat HK (by rw [abs_of_nonneg (NNReal.coe_nonneg _)];exact Hsource.1) Hdelta

end OAI.SKFluctuations.Cavity
