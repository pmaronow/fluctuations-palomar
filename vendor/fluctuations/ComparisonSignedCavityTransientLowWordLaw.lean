module

public import ComparisonSignedCavityTransientAllocationSelector
public import ComparisonSignedCavitySmallCutRowGraph

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem native_offDiagonalJets_add_test (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P Q : T.Assignment → ℝ) :
    disorderOffDiagonalJets w φ v q x Ks T (fun σ => P σ+Q σ)=
      disorderOffDiagonalJets w φ v q x Ks T P+disorderOffDiagonalJets w φ v q x Ks T Q := by
  induction Ks generalizing T with
  | nil => simp only [disorderOffDiagonalJets,disorderExpect,mul_add,Finset.sum_add_distrib]
  | cons K Ks ih => simp only [disorderOffDiagonalJets,profilePairTest_add,ih,mul_add,
      List.sum_map_add,add_div]

theorem native_offDiagonalJets_add_kernel (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (pre post : List (ℕ → S → S → ℝ)) (A B : ℕ → S → S → ℝ)
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderOffDiagonalJets w φ v q x (pre++(fun j σ τ => A j σ τ+B j σ τ)::post) T P=
      disorderOffDiagonalJets w φ v q x (pre++A::post) T P+
        disorderOffDiagonalJets w φ v q x (pre++B::post) T P := by
  induction pre generalizing T P with
  | nil => simp only [List.nil_append,disorderOffDiagonalJets,native_profilePairTest_add_kernel,
      native_offDiagonalJets_add_test,mul_add,List.sum_map_add,add_div]
  | cons K pre ih => simp only [List.cons_append,disorderOffDiagonalJets,ih,mul_add,
      List.sum_map_add,add_div]

theorem native_offDiagonalJets_low_word_sum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (pre : List (ℕ → S → S → ℝ)) (Lsmall Llarge : ℕ → S → S → ℝ)
    (k : ℕ) (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderOffDiagonalJets w φ v q x
      (pre++List.replicate k (fun j σ τ => Lsmall j σ τ+Llarge j σ τ)) T P =
      ((nativeLowAllocationWords Lsmall Llarge k).map
        (fun word => disorderOffDiagonalJets w φ v q x (pre++word) T P)).sum := by
  induction k generalizing pre with
  | zero => simp only [List.replicate_zero,List.append_nil,nativeLowAllocationWords,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  | succ k ih =>
    simp only [List.replicate_succ]
    rw [native_offDiagonalJets_add_kernel]
    have hs := ih (pre++[Lsmall])
    have hl := ih (pre++[Llarge])
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hs hl
    rw [hs,hl]
    simp only [nativeLowAllocationWords,List.map_append,List.sum_append,List.map_map,Function.comp_def]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeTransientLowSmall (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    ℕ → (Spin n×Bool) → (Spin n×Bool) → ℝ := fun j σ τ =>
  if j<V then ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ else 0

def nativeTransientLowLarge (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    ℕ → (Spin n×Bool) → (Spin n×Bool) → ℝ := fun j σ τ =>
  if j<V then 0 else ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ

theorem nativeTransientLow_partition (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K)=fun j σ τ =>
      nativeTransientLowSmall n U V b h K t j σ τ+nativeTransientLowLarge n U V b h K t j σ τ := by
  funext j σ τ
  by_cases H : j<V <;> simp only [nativeTransientLowSmall,nativeTransientLowLarge,H,↓reduceIte,
    zero_add,add_zero]

theorem nativeTransientLowLarge_rest_row_kernel (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    nativeTransientLowLarge n U V b h K t=nativeRestRowKernel n (fun j σ τ =>
      if j<V then 0 else if j<U then (1-t)*K j+t*(h j+b j*deletedOverlap n
        (joinSpin (σ,false)) (joinSpin (τ,false))) else 0) := by
  funext j σ τ
  unfold nativeTransientLowLarge
  rw [native_cutLSlope_rest_row_kernel]
  by_cases hv : j<V <;> simp only [hv,↓reduceIte,nativeRestRowKernel,zero_mul]

theorem nativeTransientLowSmall_rest_row_kernel (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ) :
    nativeTransientLowSmall n U V b h K t=nativeRestRowKernel n (fun j σ τ =>
      if j<V then (if j<U then (1-t)*K j+t*(h j+b j*deletedOverlap n
        (joinSpin (σ,false)) (joinSpin (τ,false))) else 0) else 0) := by
  funext j σ τ
  unfold nativeTransientLowSmall
  rw [native_cutLSlope_rest_row_kernel]
  by_cases hv : j<V <;> simp only [hv,↓reduceIte,nativeRestRowKernel,zero_mul]

theorem nativeTransientLowSmall_power_le (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ)
    (j m : ℕ) (σ τ : Spin n×Bool) :
    |nativeTransientLowSmall n U V b h K t j σ τ|^m ≤
      |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ|^m := by
  unfold nativeTransientLowSmall
  split_ifs
  · exact le_refl _
  · simp only [abs_zero]
    exact pow_le_pow_left₀ (le_refl (0:ℝ)) (abs_nonneg _) m

theorem nativeTransientLowLarge_power_le (n U V : ℕ) (b h K : ℕ → ℝ) (t : ℝ)
    (j m : ℕ) (σ τ : Spin n×Bool) :
    |nativeTransientLowLarge n U V b h K t j σ τ|^m ≤
      |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ|^m := by
  unfold nativeTransientLowLarge
  split_ifs
  · simp only [abs_zero]
    exact pow_le_pow_left₀ (le_refl (0:ℝ)) (abs_nonneg _) m
  · exact le_refl _

theorem nativeTransientLowErrorJet_eq_offDiagonal_words (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U V : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientLowErrorJet n q U b h K T P x k l t=
      ((ClockTree.nativeLowAllocationWords (nativeTransientLowSmall n U V b h K t)
        (nativeTransientLowLarge n U V b h K t) k).map (fun word =>
          ClockTree.disorderOffDiagonalJets (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K) x
            (ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)::word) T P)).sum := by
  rw [nativeTransientLowErrorJet_errorFirst n q U b h K T ho hq0 hq hb hh hK hbm hhm hKm P x k hl ht]
  rw [ClockTree.native_profileJets_allOffDiagonal_without_budget (fullWeight_pos n) (fullFeature n)
    (fun i => (fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i)
    T ho 0 (cutFullVariance n q U l t b h K)
    (fun i => cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 i)]
  simp only [List.map_cons,List.map_replicate]
  rw [nativeTransientLow_partition n U V b h K t]
  exact ClockTree.native_offDiagonalJets_low_word_sum (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U l t b h K) x
    [ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K)]
    (nativeTransientLowSmall n U V b h K t) (nativeTransientLowLarge n U V b h K t) k T P

end OAI.SKFluctuations.Cavity
