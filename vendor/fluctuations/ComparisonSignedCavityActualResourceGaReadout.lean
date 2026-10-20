module

public import ComparisonSignedCavityCurrentGOriginalLawRestoration
public import ComparisonSignedCavityActualFourFirstHighReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem native_original_signed_jets_const_mul_test
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    (As : List (ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (es : List T.Slot) (c : ℝ) :
    nativeOriginalSignedJets n v q x U K As T (fun σ=>c*P σ) es=
      c*nativeOriginalSignedJets n v q x U K As T P es := by
  induction As generalizing as T with
  | nil =>
    simp only [nativeOriginalSignedJets,ClockTree.disorderExpect,mul_left_comm,
      ←Finset.mul_sum]
    ring
  | cons A As ih =>
    have H (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
        profilePairTest (fun σ=>c*P σ) A p r=
          fun σ=>c*profilePairTest P A p r σ := by
      funext σ
      dsimp only [profilePairTest]
      ring
    simp only [nativeOriginalSignedJets,H,ih]
    simp only [mul_left_comm,List.sum_map_mul_left]
    ring

theorem native_original_connected_high_const_mul_test
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (z : ℝ) :
    nativeOriginalConnectedHighResponse n v q x U K b C T (fun σ=>z*P σ) a c=
      z*nativeOriginalConnectedHighResponse n v q x U K b C T P a c := by
  simp only [nativeOriginalConnectedHighResponse,native_original_signed_jets_const_mul_test]
  ring

theorem native_original_G_resampling_affine_test
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) (z d : ℝ) :
    nativeActualOriginalGProjectedResampling T s star U K b C v q x A (fun σ=>z*P σ-d)=
      z*nativeActualOriginalGProjectedResampling T s star U K b C v q x A P := by
  unfold nativeActualOriginalGProjectedResampling
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have H : (fun σ : p.tree.Assignment=>
      (A (p.spin σ) ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ))-
        A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s)
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)))*
        ((z*P ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))-d)-
          (z*P (nativeReplaceAtSlot T s ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))
            (p.spin σ))-d)))=
      fun σ=>z*((A (p.spin σ) ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ))-
        A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s)
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)))*
        (P ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))
            (p.spin σ)))) := by
    funext σ
    ring
  rw [H,native_original_connected_high_const_mul_test]
  ring

theorem native_original_G_resampling_affine_kernel
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) (z d : ℝ) :
    nativeActualOriginalGProjectedResampling T s star U K b C v q x (fun σ τ=>z*(A σ τ-d)) P=
      z*nativeActualOriginalGProjectedResampling T s star U K b C v q x A P := by
  unfold nativeActualOriginalGProjectedResampling
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have H : (fun σ : p.tree.Assignment=>
      (z*(A (p.spin σ) ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ))-d)-
        z*(A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s)
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ))-d))*
        (P ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))
            (p.spin σ))))=
      fun σ=>z*((A (p.spin σ) ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ))-
        A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ)) s)
          ((nativeFreshAtSlot T 0 s star).spin (p.restrict σ)))*
        (P ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s ((nativeFreshAtSlot T 0 s star).restrict (p.restrict σ))
            (p.spin σ)))) := by
    funext σ
    ring
  rw [H,native_original_connected_high_const_mul_test]
  ring

def nativeActualResourceOriginalScalar {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  P.scalar (fullWeight n) (fullFeature n) 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0

def nativeActualResourceGa {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar M U P*
    nativeActualCoupledGProjectedResampling T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))

def nativeActualResourceGaCurrent {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar M U P*
    nativeActualDecoupledGProjectedResampling T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))

def nativeActualResourceGaRestoration {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar M U P*
    nativeActualGProjectedRestoration T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))

theorem actual_minimum_resource_Ga_eq_current_add_restoration
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    nativeActualResourceGa M U P=nativeActualResourceGaCurrent M U P+
      2*nativeActualResourceGaRestoration M U P := by
  unfold nativeActualResourceGa nativeActualResourceGaCurrent nativeActualResourceGaRestoration
  rw [native_actual_current_G_coupled_eq_decoupled_add_restoration hP hi hs ho M]
  ring

end OAI.SKFluctuations.Cavity
