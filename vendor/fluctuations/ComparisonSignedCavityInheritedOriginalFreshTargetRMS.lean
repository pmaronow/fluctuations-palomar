module

public import ComparisonSignedCavityInheritedOriginalTargetPairRMS

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 14000000

theorem eventually_actual_minimum_inherited_original_fresh_target_rms
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
        ∀(T : ClockTree (Spin n×Bool) as) (s : T.Slot) (i : ℕ),i ≤ as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let g:=nativeFreshAtSlot T 0 s i
          Real.sqrt (g.tree.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
              (joinSpin (g.spin σ))-S i)^2) 0) ≤ C*x := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_original_target_pair_rms
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hsource hxs1 L us hus hret hmesh] with jGrid hk
  dsimp only at hk ⊢
  intro U l t hl ht T s i hi x hxs hmass
  let g:=nativeFreshAtSlot T 0 s i
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=i := by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hi]
  have Hpair:=hk U l t hl ht g.tree (g.embed s) g.mark
    (nativeFreshAtSlot_distinct T 0 s i s).symm x hxs (by simpa only [Hsplit] using hmass)
  change Real.sqrt (g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 _
    (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
      (joinSpin (g.spin σ))-orderedPathS (n+1) M.bf M.hf
        (partitionPoint 0 (finiteCutMasses us jGrid) i))^2) 0) ≤ C*x
  simp_rw [g.restrict_at,g.spin_at]
  simpa only [Hsplit] using Hpair

end OAI.SKFluctuations.Cavity
