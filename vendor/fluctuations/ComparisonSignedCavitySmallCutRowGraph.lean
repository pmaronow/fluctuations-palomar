module

public import ComparisonSignedCavitySmallCutParity
public import CavityAttachmentCoordinateProjection
public import CavityCutErrorMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeRestRowKernel (n : ℕ) (C : ℕ → Spin n → Spin n → ℝ)
    (j : ℕ) (σ τ : Spin n×Bool) : ℝ :=
  C j σ.1 τ.1*spinValue σ.2*spinValue τ.2

theorem native_deletedOverlap_row_independent (n : ℕ) (σ τ : Spin n×Bool) :
    deletedOverlap n (joinSpin σ) (joinSpin τ)=
      deletedOverlap n (joinSpin (σ.1,false)) (joinSpin (τ.1,false)) := by
  simp only [deletedOverlap,joinSpin_old]

theorem native_cutLSlope_rest_row_kernel (n U : ℕ) (b h K : ℕ → ℝ)
    (t : ℝ) :
    ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) =
      nativeRestRowKernel n (fun j σ τ => if j<U then
        (1-t)*K j+t*(h j+b j*deletedOverlap n (joinSpin (σ,false))
          (joinSpin (τ,false))) else 0) := by
  funext j σ τ
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutLSlope nativeRestRowKernel
  split_ifs with hj
  · simp only [hj,↓reduceIte]
    rw [fullVariance_row_covariance,native_deletedOverlap_row_independent]
    ring
  · simp only [hj,↓reduceIte,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem native_cutLowError_rest_row_kernel (n U : ℕ) (b h K : ℕ → ℝ) :
    ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) =
      nativeRestRowKernel n (fun j σ τ => if j<U then
        h j+b j*deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-K j else 0) := by
  funext j σ τ
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutLowError nativeRestRowKernel
  split_ifs with hj
  · simp only [hj,↓reduceIte]
    rw [rowInterpolationSlope_covariance,native_deletedOverlap_row_independent]
    ring
  · simp only [hj,↓reduceIte,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem native_siteMonomial_edge_product {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (σ : T.Assignment) (edges : List (T.Slot×T.Slot)) :
    siteMonomial T σ (edges.flatMap (fun e => [e.1,e.2]))=
      (edges.map (fun e => spinValue (T.atSlot σ e.1).2*spinValue (T.atSlot σ e.2).2)).prod := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,siteMonomial,
      List.map_cons,List.prod_cons,ih]
    ring

def nativeOldInitialRowProduct (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment → ℝ)
    (A : ℕ → Spin n → Spin n → ℝ) (u z : T.Slot)
    {a : ℕ} (C : Fin a → ℕ → Spin n → Spin n → ℝ) (s t : Fin a → T.Slot)
    (σ : T.Assignment) : ℝ :=
  P (T.cavityAssignment σ).1*
    nativeRestRowKernel n A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
    (∏ i,nativeRestRowKernel n (C i) (T.splitIndex (s i) (t i))
      (T.atSlot σ (s i)) (T.atSlot σ (t i)))

theorem nativeOldInitialRowProduct_eq_graph (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment → ℝ)
    (A : ℕ → Spin n → Spin n → ℝ) (u z : T.Slot)
    {a : ℕ} (C : Fin a → ℕ → Spin n → Spin n → ℝ) (s t : Fin a → T.Slot) :
    nativeOldInitialRowProduct n T P A u z C s t = fun σ =>
      (P (T.cavityAssignment σ).1*
        A (T.splitIndex u z) (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (ClockTree.cavityLeftSlot T u))
          (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (ClockTree.cavityLeftSlot T z))*
        (∏ i,C i (T.splitIndex (s i) (t i))
          (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (ClockTree.cavityLeftSlot T (s i)))
          (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (ClockTree.cavityLeftSlot T (t i))))) *
      siteMonomial T σ ([u,z]++(List.ofFn (fun i => (s i,t i))).flatMap (fun e => [e.1,e.2])) := by
  funext σ
  simp only [ClockTree.atSlot_cavityLeft,siteMonomial,List.cons_append,List.nil_append,
    native_siteMonomial_edge_product,List.map_ofFn,List.prod_ofFn,
    nativeOldInitialRowProduct,nativeRestRowKernel,Function.comp_def,Finset.prod_mul_distrib]
  ring

theorem native_old_initial_row_product_restore (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) (hV0 : 0<V) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hV : V≤as.length) (P : T.cavityLeft.Assignment → ℝ)
    (A : ℕ → Spin n → Spin n → ℝ) (u z : T.Slot) (huz : T.splitIndex u z<V)
    {a : ℕ} (C : Fin a → ℕ → Spin n → Spin n → ℝ) (s t : Fin a → T.Slot)
    (hst : ∀ i,V ≤ T.splitIndex (s i) (t i))
    (x : FullCoordinate n → ℝ) (hs : ∀ i,x (.inl (.inr i))=0) (hr : ∀ i,x (.inr i)=0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {l t' : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t'∈Icc (0:ℝ) 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t' b h K)
      (nativeOldInitialRowProduct n T P A u z C s t) x =
      ∫ r in (0:ℝ)..1,cutLowJet n q V (relocatedClock U l b) (relocatedClock U l h)
        (relocatedClock U l K) T (nativeOldInitialRowProduct n T P A u z C s t) x 1 r t' := by
  rw [nativeOldInitialRowProduct_eq_graph]
  let Prest := fun τ : T.cavityLeft.Assignment => P τ*
    A (T.splitIndex u z) (T.cavityLeft.atSlot τ (ClockTree.cavityLeftSlot T u))
      (T.cavityLeft.atSlot τ (ClockTree.cavityLeftSlot T z))*
    (∏ i,C i (T.splitIndex (s i) (t i))
      (T.cavityLeft.atSlot τ (ClockTree.cavityLeftSlot T (s i)))
      (T.cavityLeft.atSlot τ (ClockTree.cavityLeftSlot T (t i))))
  exact native_small_cut_graph_restore n q U V hV0 b h K T ho hV u _
    (native_old_initial_pair_degree_odd T V hV u z huz
      (List.ofFn (fun i => (s i,t i))) (by
        intro e he
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
        exact hst i))
    Prest x hs hr hq0 hq hb hh hK hbm hhm hKm hl ht

end OAI.SKFluctuations.Cavity
