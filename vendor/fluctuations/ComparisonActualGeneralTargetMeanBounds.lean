module

public import ComparisonActualGeneralTargetMeanReadout
public import ComparisonActualHighWallSourceIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
variable {n : ℕ}

theorem actual_general_target_mean_gap_abs_le_four_parts
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length) (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n bf hf as i-nativeOriginalScalarPairMean as K i|≤
      |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U|+
      2*(bf (partitionPoint 0 as i):ℝ)*chi*|actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i V|+
      |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U V|+
      |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U| := by
  dsimp only
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  rw [actual_general_target_mean_eq_correction_response_transport_taylor bf hf hbf hhf as i U V hi hU ho]
  have Hcoef : 0≤2*(bf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0:=by
    exact mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1
  have Habs (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d|:=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  apply (Habs _ _ _ _).trans_eq
  rw [abs_mul,abs_of_nonneg Hcoef]

theorem actual_general_target_mean_gap_abs_le_of_bounds
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (Emean R Etransport Etaylor : ℝ)
    (Hmean : |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U|≤Emean)
    (Hresponse : |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i V|≤R)
    (Htransport : |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U V|≤Etransport)
    (Htaylor : |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U|≤Etaylor) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n bf hf as i-nativeOriginalScalarPairMean as K i|≤
      Emean+2*(bf (partitionPoint 0 as i):ℝ)*chi*R+Etransport+Etaylor := by
  dsimp only
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  apply (actual_general_target_mean_gap_abs_le_four_parts bf hf hbf hhf as i U V hi hU ho).trans
  exact add_le_add (add_le_add (add_le_add Hmean
    (mul_le_mul_of_nonneg_left Hresponse
      (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1))) Htransport) Htaylor

theorem actual_general_target_mean_cubic_of_original_reader_prices
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d Cmean Cresponse Ctransport Ctaylor : ℝ} (hd : 0≤d) (hR : 0≤Cresponse)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (Hmean : |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U|≤Cmean*d^3)
    (Hresponse : |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i V|≤Cresponse*d^3)
    (Htransport : |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U V|≤Ctransport*d^3)
    (Htaylor : |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U|≤Ctaylor*d^3) :
    |nativePhysicalResourceCenter n bf hf as i-nativeOriginalScalarPairMean as
      (nativeContinuumMixedClock n bf hf as) i|≤
      (Cmean+2*Temp*Cresponse+Ctransport+Ctaylor)*d^3 := by
  have H:=actual_general_target_mean_gap_abs_le_of_bounds bf hf hbf hhf as i U V hi hU ho
    _ _ _ _ Hmean Hresponse Htransport Htaylor
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  have Hb : (bf (partitionPoint 0 as i):ℝ)≤Temp:=by
    have HH:=htotal _ (partitionPoint_mem as ho i)
    linarith [(hf (partitionPoint 0 as i)).coe_nonneg]
  have Hcoef : 2*(bf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0≤2*Temp:=by
    nlinarith only [Hchi.2,Hb,mul_nonneg (NNReal.coe_nonneg (bf (partitionPoint 0 as i))) (sub_nonneg.mpr Hchi.2)]
  have Hp:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg hR (pow_nonneg hd 3))
  apply H.trans
  nlinarith only [Hp]

theorem actual_general_target_mean_original_center_gap_tendsto
    {Temp : ℝ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hTemp : 0<Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>
      let as:=finiteCutMasses us k
      nativePhysicalResourceCenter n bf hf as (retainedMassPrefixIndex u.val as)-
        nativeOriginalScalarPairMean as (nativeContinuumMixedClock n bf hf as) (retainedMassPrefixIndex u.val as))
      atTop (𝓝 (orderedPathS (n+1) bf hf u.val-
        scalarCovarianceResponse hTemp (actualMixedMassProfile hTemp (n+1) (by omega) bf hf hbf hhf htotal)
          (actualMixedClock (n+1) bf hf u.val))) := by
  have HS:=continuum_retained_scalar_pair_tendsto n bf hf hbf hhf hroot hTemp htotal us hus u hu
  have Hcenter (k : ℕ) :
      nativePhysicalResourceCenter n bf hf (finiteCutMasses us k)
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))=orderedPathS (n+1) bf hf u.val:=by
    let as:=finiteCutMasses us k
    have ho:=finiteCutMasses_ordered us hus k
    unfold nativePhysicalResourceCenter
    rw [←native_ordered_source_center_eq_completed n bf hf hbf hhf (partitionPoint_mem as ho _)]
    change orderedPathS (n+1) bf hf (partitionPoint 0 as (retainedMassPrefixIndex u.val as))=orderedPathS (n+1) bf hf u.val
    rw [nativeRetainedCut_partitionPoint as ho u (finiteCutMasses_nodes us k hu)]
  apply ((tendsto_const_nhds (x:=orderedPathS (n+1) bf hf u.val)).sub HS).congr'
  filter_upwards [] with k
  dsimp only
  rw [Hcenter]

theorem actual_general_target_mean_continuum_cubic_of_finite_reader_prices
    {Temp d Cmean Cresponse Ctransport Ctaylor : ℝ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hTemp : 0<Temp) (hd : 0≤d) (hR : 0≤Cresponse)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (U V : ℕ→ℕ)
    (Hprice : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i<U k ∧ U k≤as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i (U k)|≤Cmean*d^3 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i (V k)|≤Cresponse*d^3 ∧
      |actualGeneralTargetMeanTransportError (n:=n) bf hf as i (U k) (V k)|≤Ctransport*d^3 ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i (U k)|≤Ctaylor*d^3) :
    |orderedPathS (n+1) bf hf u.val-
      scalarCovarianceResponse hTemp (actualMixedMassProfile hTemp (n+1) (by omega) bf hf hbf hhf htotal)
        (actualMixedClock (n+1) bf hf u.val)|≤
      (Cmean+2*Temp*Cresponse+Ctransport+Ctaylor)*d^3 := by
  have Hlim:=(actual_general_target_mean_original_center_gap_tendsto (n:=n) bf hf hbf hhf hroot hTemp htotal us hus u hu).abs
  apply le_of_tendsto_of_tendsto Hlim tendsto_const_nhds
  filter_upwards [Hprice] with k hk
  exact actual_general_target_mean_cubic_of_original_reader_prices bf hf hbf hhf hd hR htotal
    _ _ _ _ hk.1 hk.2.1 (finiteCutMasses_ordered us hus k) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2

end OAI.SKFluctuations.Cavity
