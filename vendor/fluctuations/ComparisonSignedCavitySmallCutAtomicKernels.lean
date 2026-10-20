module

public import ComparisonSignedCavityActualSmallCutCanonicalOldMoment
public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

def nativeSmallCutMovingRestKernel (n U : ℕ) (b h K : ℕ→ℝ)
    (v : ℝ) (j : ℕ) (σ τ : Spin n) : ℝ :=
  if j<U then (1-v)*K j+v*(h j+b j*deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))) else 0

def nativeSmallCutOldErrorRestKernel (n U : ℕ) (b h K : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n) : ℝ :=
  if j<U then h j+b j*deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-K j else 0

def nativeSmallCutOrdinaryRestKernel (n U : ℕ) (b h K : ℕ→ℝ)
    (site : Bool) (v : ℝ) : ℕ→Spin n→Spin n→ℝ :=
  if site then fun _ _ _=>1 else nativeSmallCutMovingRestKernel n U b h K v

def nativeSmallCutOrdinaryScale (x Cr : ℝ) (as : List PositiveMass)
    (site : Bool) (j : ℕ) : ℝ :=
  if site then 1 else Cr*(x+partitionPoint 0 as j)

theorem native_small_cut_moving_kernel_eq_original_profile (n U : ℕ) (b h K : ℕ→ℝ) (v : ℝ) :
    nativeRestRowKernel n (nativeSmallCutMovingRestKernel n U b h K v)=
      ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U v b h K) := by
  exact (native_cutLSlope_rest_row_kernel n U b h K v).symm

theorem native_small_cut_old_error_eq_original_profile (n U : ℕ) (b h K : ℕ→ℝ) :
    nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K)=
      ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) := by
  exact (native_cutLowError_rest_row_kernel n U b h K).symm

theorem native_small_cut_ordinary_scale_pos {x Cr : ℝ} (hx : 0<x) (hCr : 0<Cr)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (site : Bool) (j : ℕ) :
    0<nativeSmallCutOrdinaryScale x Cr as site j := by
  unfold nativeSmallCutOrdinaryScale
  split_ifs
  · norm_num
  · exact mul_pos hCr (add_pos_of_pos_of_nonneg hx (partitionPoint_mem as ho j).1)

theorem native_small_cut_site_row_abs_one (n : ℕ) (j : ℕ) (σ τ : Spin n×Bool) :
    |nativeRestRowKernel n (fun _ _ _=>1) j σ τ|=1 := by
  simp only [nativeRestRowKernel,one_mul,abs_mul,abs_spinValue,mul_one]

end OAI.SKFluctuations.Cavity
