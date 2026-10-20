module

public import ComparisonSignedCavityOriginalGRestorationLinearity
public import ComparisonSignedCavityInheritedUnbondedLowGPairRestoration
public import ComparisonSignedCavityPairedCurrentForkLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

 theorem native_canonical_G_projected_displacement_source
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a → NativeSourceFactorForm) (s : T.Slot) (star : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (S : ℕ → ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    let GP:=(G.nativeCMarkedLift g (nativeFreshAtSlot_mem T 0 s star)).nativeCMarkedLift p hp
    nativeRestProjectedDisplacementTest T s star
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
      (G.canonicalMinimumSource M forms).restProduct p=
      fun σ=>
        (GP.canonicalMinimumSource M forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star)-
        (GP.canonicalMinimumSource M forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed (g.embed s))),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star) := by
  dsimp only
  funext σ
  rw [ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct,
    ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct]
  unfold nativeRestProjectedDisplacementTest MarkedPlacement.restSpin
  dsimp only
  rw [(nativeFreshAtSlot T 0 s star).restRestrict_at,p.restRestrict_at,p.restRestrict_at]
  ring

 theorem native_forkCost_test_linear {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (f g : ℕ → ℝ) (α β : ℝ) :
    T.forkCost (fun j=>α*f j+β*g j)=α*T.forkCost f+β*T.forkCost g := by
  induction T generalizing f g with
  | leaf=>simp only [forkCost];ring
  | step a T ih=>exact ih _ _
  | fork T U ihT ihU=>simp only [forkCost,ihT,ihU];ring

 theorem native_edgeBudget_test_linear (as : List PositiveMass) (a : ℝ)
    (f g : ℕ → ℝ) (α β : ℝ) :
    edgeBudget a as (fun j=>α*f j+β*g j)=α*edgeBudget a as f+β*edgeBudget a as g := by
  induction as generalizing a f g with
  | nil=>simp only [edgeBudget];ring
  | cons b bs ih=>simp only [edgeBudget,ih];ring

 theorem native_current_restoring_rows_two_profiles_le
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) {star U r : ℕ} (hs : star < U)
    (hr : T.leaves ≤ r) (f g : ℕ → ℝ) (hf : ∀j,0 ≤ f j) (hg : ∀j,0 ≤ g j)
    (hflo : ∀j,j < U → f j=0) (hglo : ∀j,j < U → g j=0)
    (E : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0,
      |E p| ≤ A*(p.tree.forkCost f+edgeBudget 0 as f)+B*(p.tree.forkCost g+edgeBudget 0 as g)) :
    |(((nativeFreshAtSlot T 0 s star).tree.markedAttach 0).map
      (fun p=>p.coeff*E p)).sum| ≤
      (4*((r:ℝ)+1)+1)*(A*(T.forkCost f+edgeBudget 0 as f)+B*(T.forkCost g+edgeBudget 0 as g)) := by
  let F:=fun j=>A*f j+B*g j
  have HF j : 0 ≤ F j:=add_nonneg (mul_nonneg hA (hf j)) (mul_nonneg hB (hg j))
  have Hlo j (hj : j < U) : F j=0:=by dsimp only [F];rw [hflo j hj,hglo j hj];ring
  have HH:=native_paired_current_rows_high_profile_le T ho s hs hr F HF Hlo E
    (C:=1) (by norm_num) (by
      intro p hp
      rw [one_mul,native_forkCost_test_linear,native_edgeBudget_test_linear]
      convert hE p hp using 1; ring)
  rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num),
    native_forkCost_test_linear,native_edgeBudget_test_linear] at HH
  nlinarith only [HH]

end OAI.SKFluctuations.Cavity
