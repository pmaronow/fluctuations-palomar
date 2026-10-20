module

public import ComparisonActualHighWallLowCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_full_LOW_cost_bigO
    (rBound : ℕ) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U i star : ℕ) (T : ClockTree (Spin n×Bool) as)
          (part : NativeTransientLowErrorPart) (l t : ℝ),U ≤ as.length →
          T.leaves ≤ rBound → partitionPoint 0 as U ≤ Ccut*M.data.d →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
            (nativeTransientLowErrorPartDirection n U i star b h K part)
          T.forkCost R+edgeBudget 0 as R ≤ C*M.data.d := by
  obtain ⟨Cf,hCf,HF⟩:=eventually_actual_high_wall_current_LOW_radius_bigO (D:=D)
    Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ce,hCe,HE⟩:=eventually_actual_high_wall_current_low_density_bigO (D:=D)
    Bclock Ccut hm hdelta hroom hcl hcu hAz hC0 hCt hCcut
  let C:=(rBound:ℝ)*Cf+Ce+1
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HF,HE] with n hnF hnE
  intro M hwork L us hus hret hmesh
  filter_upwards [hnF M hwork L us hus hret hmesh,hnE M hwork us hus] with jGrid hjF hjE
  dsimp only at hjF hjE ⊢
  intro U i star T part l t hU hT hcut hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K part)
  let Rlow:=nativeWholeLawErrorRadius n as law (cutLowError n U b h K)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hmono j : R j ≤ Rlow j:=native_transient_low_part_radius_le n U i star b h K as law part j
  have Hfork := T.native_forkCost_le_pair_bound R (Cf*M.data.d) (fun a z _=>
    (Hmono (T.splitIndex a z)).trans (hjF U (T.splitIndex a z) l t hU
      (T.splitIndex_le_clockLength _ _) hcut hl ht))
  have hleaves : (T.leaves:ℝ) ≤ rBound:=by exact_mod_cast hT
  have Hfork' : T.forkCost R ≤ (rBound:ℝ)*Cf*M.data.d :=
    Hfork.trans (by nlinarith only [hleaves,mul_nonneg hCf.le M.data.hd.le])
  have Hedges := actual_low_edgeBudget_mono ho (fun j _=>Hmono j)
  have Hcut : partitionPoint 0 as U ≤ min (Ccut*M.data.d) 1:=
    le_min hcut (partitionPoint_mem as ho U).2
  have Hlow := hjE U hU Hcut l t hl ht
  have Hedges' : edgeBudget 0 as R ≤ Ce*M.data.d :=
    Hedges.trans (Hlow.trans (mul_le_mul_of_nonneg_left
      (show M.data.d^2≤M.data.d by nlinarith only [M.data.hd.le,M.data.hd1]) hCe.le))
  have Hsum:=add_le_add Hfork' Hedges'
  exact Hsum.trans (by dsimp only [C];nlinarith only [M.data.hd.le])

end OAI.SKFluctuations.Cavity
