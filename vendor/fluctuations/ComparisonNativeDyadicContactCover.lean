module

public import ComparisonNativeCanonicalBandGeometry
public import ComparisonNativeWholeCapErrorCover
public import ComparisonPhysicalDyadicSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

def comparisonMassDyadicIndices (U : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (Real.log (1/U)/Real.log 2)+1)).filter (fun j=>U*(2:ℝ)^j ≤ 1)

theorem comparison_mass_dyadic_mem {U : ℝ} (hU : 0 < U) {j : ℕ}
    (hscale : U*(2:ℝ)^j ≤ 1) : j ∈ comparisonMassDyadicIndices U := by
  have hp : (2:ℝ)^j ≤ 1/U := (le_div_iff₀ hU).mpr (by nlinarith)
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) j) hp
  rw [Real.log_pow] at hl
  have hi := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hl
  have hj : j ≤ Nat.ceil (Real.log (1/U)/Real.log 2) := by
    exact_mod_cast hi.trans (Nat.le_ceil _)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hscale⟩

theorem comparison_mass_dyadic_scale {U : ℝ} (hU : 0 < U)
    (j : comparisonMassDyadicIndices U) :
    0 < U*(2:ℝ)^(j:ℕ) ∧ U ≤ U*(2:ℝ)^(j:ℕ) ∧ U*(2:ℝ)^(j:ℕ) ≤ 1 := by
  refine ⟨mul_pos hU (pow_pos (by norm_num) _),?_,(Finset.mem_filter.mp j.property).2⟩
  have hh : (1:ℝ) ≤ 2^(j:ℕ) := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
  nlinarith

theorem comparison_mass_dyadic_cover {U u : ℝ} (hU : 0 < U)
    (hUu : U ≤ u) (hu1 : u ≤ 1) :
    ∃j : comparisonMassDyadicIndices U,
      U*(2:ℝ)^(j:ℕ) ≤ u ∧ u < 2*(U*(2:ℝ)^(j:ℕ)) := by
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near ((one_le_div hU).mpr hUu) (by norm_num : (1:ℝ) < 2)
  have hleft : U*(2:ℝ)^j ≤ u := by
    have hh := (le_div_iff₀ hU).mp hj
    nlinarith
  have hright : u < 2*(U*(2:ℝ)^j) := by
    have hh := (div_lt_iff₀ hU).mp hj'
    rw [pow_succ] at hh
    nlinarith
  exact ⟨⟨j,comparison_mass_dyadic_mem hU (hleft.trans hu1)⟩,hleft,hright⟩

structure NativeDyadicBandFamily (m : NativeBandModel) where
  model : comparisonMassDyadicIndices m.U → NativeBandModel
  quantile : ∀j,(model j).R=m.R
  potential : ∀j,(model j).H=m.H
  error : ∀j,(model j).comparisonErrorDensity=m.comparisonErrorDensity
  left : ∀j,(model j).ag=m.R (m.U*(2:ℝ)^(j:ℕ)/2)
  right : ∀j,(model j).zg=m.R (min (16*(m.U*(2:ℝ)^(j:ℕ))) 1)

namespace NativeDyadicBandFamily

theorem contact_mem_group {m : NativeBandModel} (g : NativeDyadicBandFamily m)
    {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (hUu : m.U ≤ u) (hzero : m.H (m.R u)=0) :
    ∃j,m.R u ∈ (g.model j).ordinarySupport := by
  obtain ⟨j,hlo,hhi⟩ := comparison_mass_dyadic_cover m.hU hUu hu.2.le
  have hv := comparison_mass_dyadic_scale m.hU j
  let v := m.U*(2:ℝ)^(j:ℕ)
  have hvp : 0 < v := hv.1
  have hv1 : v ≤ 1 := hv.2.2
  have hmassLo : v/2 < u := by dsimp [v] at *;linarith
  have hmassHi : u < min (16*v) 1 := lt_min (by dsimp [v] at *;linarith) hu.2
  have hpointLo : v/2 ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hpointHi : min (16*v) 1 ∈ Icc (0:ℝ) 1 :=
    ⟨(lt_min (by linarith) zero_lt_one).le,min_le_right _ _⟩
  have hleft := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
    hpointLo (Ioo_subset_Icc_self hu) hmassLo
  have hright := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
    (Ioo_subset_Icc_self hu) hpointHi hmassHi
  refine ⟨j,⟨?_,Or.inr ?_⟩⟩
  · rw [g.left,g.right]
    exact ⟨hleft,hright⟩
  · change (g.model j).H (m.R u)=0
    rw [g.potential]
    exact hzero

theorem contact_cover {m : NativeBandModel} (g : NativeDyadicBandFamily m)
    {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (hzero : m.H (m.R u)=0) :
    m.R u ∈ nativeBroadNearZero m ∨ ∃j,m.R u ∈ (g.model j).ordinarySupport := by
  by_cases hUu : m.U ≤ u
  · exact Or.inr (g.contact_mem_group hu hUu hzero)
  · apply Or.inl
    have hv : min (8*m.U) 1 ∈ Icc (0:ℝ) 1 :=
      ⟨(lt_min (by linarith [m.hU]) zero_lt_one).le,min_le_right _ _⟩
    apply (native_mass_slice_quantile_mem m (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
      hv (Ioo_subset_Icc_self hu)).mpr
    exact ⟨hu.1,lt_min (by linarith [m.hU,lt_of_not_ge hUu]) hu.2⟩

theorem contact_error_le_sum {m : NativeBandModel} (g : NativeDyadicBandFamily m) :
    (∫u in 0..1,(nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      (∑j:comparisonMassDyadicIndices m.U,
        ∫u in 0..1,(g.model j).ordinaryMask ((g.model j).R u)*(g.model j).comparisonErrorDensity u)+
      (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) := by
  let f := fun j : comparisonMassDyadicIndices m.U=>fun u=>
    (g.model j).ordinaryMask ((g.model j).R u)*(g.model j).comparisonErrorDensity u
  let low := fun u=>(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u
  have hi j : IntervalIntegrable (f j) volume 0 1 := by
    exact intervalIntegrable_bounded_measurable_mul (g.model j).ordinaryMask_composed_measurable zero_le_one
      (fun u _=>by unfold NativeBandModel.ordinaryMask;by_cases h:(g.model j).R u ∈ (g.model j).ordinarySupport <;> simp [h])
      (nativeActualError_intervalIntegrable (g.model j))
  have hiSum : IntervalIntegrable (fun u=>∑j,f j u) volume 0 1 := by
    have heq : (fun u=>∑j,f j u)=∑j,f j := by
      funext u
      simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun j _=>hi j)
  have hiLow : IntervalIntegrable low volume 0 1 := nativeActualError_mask_integrable m _ measurableSet_Ioo
  have hiContact := nativeActualError_mask_integrable m _ (nativeActualContactSet_measurable m)
  have hpoint : ∀ᵐ u∂volume.restrict (Ioc (0:ℝ) 1),
      (nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u ≤
        (∑j,f j u)+low u := by
    have hne : ∀ᵐ u∂volume.restrict (Ioc (0:ℝ) 1),u ≠ 1 :=
      ae_restrict_of_ae (volume.ae_ne 1)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hne] with u hu hune
    have herror := nativeActualError_nonneg m hu
    have hnon j : 0 ≤ f j u := by
      dsimp [f]
      rw [g.quantile,g.error]
      have hm : 0 ≤ (g.model j).ordinaryMask (m.R u) := by
        unfold NativeBandModel.ordinaryMask
        by_cases h:m.R u ∈ (g.model j).ordinarySupport <;> simp [h]
      exact mul_nonneg hm herror
    have hlow : 0 ≤ low u := by
      dsimp [low]
      by_cases h:m.R u ∈ nativeBroadNearZero m <;> simp [h,herror]
    by_cases hcontact:m.R u ∈ nativeActualContactSet m
    · have hzero : m.H (m.R u)=0 := hcontact.2
      rcases g.contact_cover ⟨hu.1,lt_of_le_of_ne hu.2 hune⟩ hzero with hl|⟨j,hj⟩
      · have heq : low u=m.comparisonErrorDensity u := by simp [low,hl]
        have hs := Finset.sum_nonneg (fun j (_:j∈Finset.univ)=>hnon j)
        simp only [indicator_of_mem hcontact,one_mul]
        linarith
      · have hjEq : f j u=m.comparisonErrorDensity u := by
          dsimp [f]
          rw [g.quantile,g.error]
          simp [NativeBandModel.ordinaryMask,hj]
        have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>f j u)
          (fun j _=>hnon j) (Finset.mem_univ j)
        rw [hjEq] at hs
        simp only [indicator_of_mem hcontact,one_mul]
        linarith
    · simp only [indicator_of_notMem hcontact,zero_mul]
      exact add_nonneg (Finset.sum_nonneg (fun j _=>hnon j)) hlow
  have hb : (∫u in 0..1,(nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      ∫u in 0..1,(∑j,f j u)+low u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiContact)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hiSum.add hiLow)) hpoint
  rw [intervalIntegral.integral_add hiSum hiLow,intervalIntegral.integral_finsetSum (fun j _=>hi j)] at hb
  exact hb

end NativeDyadicBandFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
