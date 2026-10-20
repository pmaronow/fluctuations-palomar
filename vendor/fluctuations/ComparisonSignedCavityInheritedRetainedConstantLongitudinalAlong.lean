module

public import ComparisonSignedCavityInheritedRetainedConstantLongitudinal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
theorem eventually_actual_shell_history_retained_constant_longitudinal_rate_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp) → M.h 0=0 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeRetainedLongitudinalPairing (dim n) q U b h K T (fun _=>1) a| ≤
            (M.context.N^(-(1:ℝ)/3)+C*M.context.N^(-(actualMassSavingExponent m delta/256)))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_retained_constant_longitudinal_rate
    (D:=D) (Cs:=Cs) rBound Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

theorem native_constant_calibration_fresh_tree_HIGH_fork_free
    {S : Type*} (as : List PositiveMass) (star U : ℕ) (hs : star < U)
    (f : ℕ→ℝ) (hlo : ∀j,j < U → f j=0) :
    (nativeFreshAtSlot (ClockTree.single (S:=S) as) 0 (singleSlot as) star).tree.forkCost f=0 := by
  rw [nativeFreshAtSlot_high_forkCost _ _ _ hs f hlo,single_forkCost]

end OAI.SKFluctuations.Cavity
