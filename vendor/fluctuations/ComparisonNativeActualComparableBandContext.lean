module

public import ComparisonNativeActualCavityClockContext
public import ComparisonNativeActualComparableBandClocks
public import ComparisonNativeActualSequentialBareErrorAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}

 theorem NativeSequentialComparableBandClocks.comp
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : NativeSequentialComparableBandClocks M T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    NativeSequentialComparableBandClocks (fun n=>M (phi n)) T := by
  intro y hy hay c C eps hc hC heps
  let z:=Function.extend phi y (fun n=>(M n).xs)
  have hz : Tendsto z atTop (𝓝 0) := tendsto_subsequence_extend hphi hy hx
  have haz : ∀ᶠn in atTop,
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ z n :=
    eventually_subsequence_extend hphi
      (fun n v=>comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ v)
      hay (Eventually.of_forall (fun n=>(M n).hscale))
  have Hresult:=hphi.tendsto_atTop.eventually (H z hz haz c C eps hc hC heps)
  filter_upwards [Hresult] with n hn
  simpa only [z,hphi.injective.extend_apply] using hn

 structure NativeActualComparableBandContext
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) extends NativeActualCavityClockContext M T where
  comparable : NativeSequentialComparableBandClocks M T

namespace NativeActualComparableBandContext
variable {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

 def comp (G : NativeActualComparableBandContext M T) (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    NativeActualComparableBandContext (fun n=>M (phi n)) T where
  toNativeActualCavityClockContext:=G.toNativeActualCavityClockContext.comp phi hphi.tendsto_atTop
  comparable:=G.comparable.comp G.xs_zero phi hphi

 theorem positive_band_clocks (G : NativeActualComparableBandContext M T)
    (c C epsilon : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠn in atTop,∀u∈Icc (c*(M n).xs) (min (C*(M n).xs) 1),
      |(M n).b u-T| ≤ epsilon*(M n).xs^2 ∧ |(M n).h u| ≤ epsilon*(M n).xs^3 :=
  G.comparable _ G.xs_zero (Eventually.of_forall (fun n=>(M n).hscale))
    c C epsilon hc hC hepsilon

 theorem initial_field_clock (G : NativeActualComparableBandContext M T)
    (C epsilon : ℝ) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),
      |(M n).h u| ≤ epsilon*(M n).xs^3 := by
  have Hunit : ∀ᶠn in atTop,C*(M n).xs ≤ 1 :=
    ((G.xs_zero.const_mul C).eventually (eventually_le_nhds (by simp : C*(0:ℝ)<1)))
  filter_upwards [G.positive_band_clocks C C epsilon hC hC.le hepsilon,Hunit] with n hn hnunit u hu
  have ht : C*(M n).xs∈Icc (C*(M n).xs) (min (C*(M n).xs) 1):=
    ⟨le_rfl,by rw [min_eq_left hnunit]⟩
  have hu1 : u∈Icc (0:ℝ) 1:=⟨hu.1,hu.2.trans hnunit⟩
  have hnonneg : 0 ≤ (M n).h u:=
    (M n).hh0.trans ((M n).hh (by norm_num) hu1 hu.1)
  rw [abs_of_nonneg hnonneg]
  exact ((M n).hh hu1 ⟨(mul_pos hC (M n).hxs).le,hnunit⟩ hu.2).trans
    ((le_abs_self _).trans (hn _ ht).2)

 theorem positive_band_bare_error
    (G : NativeActualComparableBandContext M T)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hdim : Tendsto dim atTop atTop)
    (F : ℕ→Set ParisiFinite.OrderPoint) (hF : ∀n,MeasurableSet (F n))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hband : ∀n w,w∈F n → c*(M n).xs ≤ (w:ℝ) ∧ (w:ℝ) ≤ C*(M n).xs) :
    let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(M n).xs^3) (nu n)) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(M n).xs^3|
        ∂nu n) atTop (𝓝 0) := by
  apply actual_inherited_restricted_bare_error_of_vanishing_clocks_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) F hF C hC (fun n w hw=>(hband n w hw).2)
  intro epsilon hepsilon
  filter_upwards [G.positive_band_clocks c C epsilon hc hC.le hepsilon] with n hn w hw
  exact hn w ⟨(hband n w hw).1,le_min (hband n w hw).2 w.property.2⟩

end NativeActualComparableBandContext
end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
