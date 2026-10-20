module

public import ComparisonActualHighOnlyWeakComparableClocks
public import ComparisonNativeActualComparableBandContext
public import ComparisonActualHighWallBarePullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

def HighOnlyActualSmallSourceClocks {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T Cf : ℝ) : Prop :=
  ∀u∈Icc (0:ℝ) 1,(M.bf u:ℝ) ≤ T ∧ (M.hf u:ℝ) ≤ Cf*(M.xs+u)

structure HighOnlyActualComparableBandContext
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) where
  hT : 0 < T
  xs_zero : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)
  omission_ratio : Tendsto (fun n=>(M n).data.s/comparisonLowerScale
    (M n).context.N (M n).context.E (M n).context.d) atTop (𝓝 0)
  pullback : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1
  total_root : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0
  Cf : ℝ
  hCf : 0 ≤ Cf
  source : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,((M n).bf u:ℝ) ≤ T ∧
    ((M n).hf u:ℝ) ≤ Cf*((M n).xs+u)
  comparable : HighOnlySequentialComparableBandClocks M T

 theorem HighOnlySequentialComparableBandClocks.comp
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : HighOnlySequentialComparableBandClocks M T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    HighOnlySequentialComparableBandClocks (fun n=>M (phi n)) T := by
  intro y hy hay c C eps hc hC heps
  let z:=Function.extend phi y (fun n=>(M n).xs)
  have hz : Tendsto z atTop (𝓝 0) := NativeOverlapMinimum.tendsto_subsequence_extend hphi hy hx
  have haz : ∀ᶠn in atTop,
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ z n :=
    NativeOverlapMinimum.eventually_subsequence_extend hphi
      (fun n v=>comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ v)
      hay (Eventually.of_forall (fun n=>(M n).hscale))
  have Hresult:=hphi.tendsto_atTop.eventually (H z hz haz c C eps hc hC heps)
  filter_upwards [Hresult] with n hn
  simpa only [z,hphi.injective.extend_apply] using hn

namespace HighOnlyActualComparableBandContext
variable {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

def comp (G : HighOnlyActualComparableBandContext M T) (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    HighOnlyActualComparableBandContext (fun n=>M (phi n)) T where
  hT:=G.hT
  xs_zero:=G.xs_zero.comp hphi.tendsto_atTop
  omission_ratio:=G.omission_ratio.comp hphi.tendsto_atTop
  pullback:=hphi.tendsto_atTop.eventually G.pullback
  total_root:=hphi.tendsto_atTop.eventually G.total_root
  Cf:=G.Cf
  hCf:=G.hCf
  source:=hphi.tendsto_atTop.eventually G.source
  comparable:=G.comparable.comp G.xs_zero phi hphi

theorem positive_band_clocks (G : HighOnlyActualComparableBandContext M T)
    (c C epsilon : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠn in atTop,∀u∈Icc (c*(M n).xs) (min (C*(M n).xs) 1),
      |(M n).b u-T| ≤ epsilon*(M n).xs^2 ∧ |(M n).h u| ≤ epsilon*(M n).xs^3 :=
  G.comparable _ G.xs_zero (Eventually.of_forall (fun n=>(M n).hscale))
    c C epsilon hc hC hepsilon

theorem omission_over_test_zero (G : HighOnlyActualComparableBandContext M T) :
    Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0) := by
  apply squeeze_zero (fun n=>div_nonneg (M n).data.hs.1 (M n).hxs.le) _ G.omission_ratio
  intro n
  exact div_le_div_of_nonneg_left (M n).data.hs.1
    (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).context.hN) (M n).context.hE) (M n).context.hd)
    (M n).hscale

theorem positive_bands_high (G : HighOnlyActualComparableBandContext M T)
    (c : ℝ) (hc : 0 < c) : ∀ᶠn in atTop,(M n).data.s ≤ c*(M n).xs := by
  filter_upwards [G.omission_over_test_zero.eventually (eventually_le_nhds hc)] with n hn
  exact (div_le_iff₀ (M n).hxs).mp hn

theorem initial_field_clock (G : HighOnlyActualComparableBandContext M T)
    (C epsilon : ℝ) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),|(M n).h u| ≤ epsilon*(M n).xs^3 := by
  have Hunit : ∀ᶠn in atTop,C*(M n).xs ≤ 1 :=
    ((G.xs_zero.const_mul C).eventually (eventually_le_nhds (by simp : C*(0:ℝ)<1)))
  filter_upwards [G.positive_band_clocks C C epsilon hC hC.le hepsilon,Hunit] with n hn hnunit u hu
  have ht : C*(M n).xs∈Icc (C*(M n).xs) (min (C*(M n).xs) 1):=
    ⟨le_rfl,by rw [min_eq_left hnunit]⟩
  have hu1 : u∈Icc (0:ℝ) 1:=⟨hu.1,hu.2.trans hnunit⟩
  have hnonneg : 0 ≤ (M n).h u:=(M n).hh0.trans ((M n).hh (by norm_num) hu1 hu.1)
  rw [abs_of_nonneg hnonneg]
  exact ((M n).hh hu1 ⟨(mul_pos hC (M n).hxs).le,hnunit⟩ hu.2).trans
    ((le_abs_self _).trans (hn _ ht).2)

theorem eventually_geometric_gates (G : HighOnlyActualComparableBandContext M T) :
    ∀ᶠn in atTop,(M n).data.s ≤ (M n).xs ∧ (M n).data.s ≤ (1:ℝ)/4 := by
  filter_upwards [G.positive_bands_high 1 zero_lt_one,
    G.xs_zero.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))] with n hn hnx
  simp only [one_mul] at hn
  exact ⟨hn,hn.trans hnx⟩

end HighOnlyActualComparableBandContext

 theorem small_source_clocks_of_bare_field
    {n : ℕ} (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {C : ℝ} (hC : 0 ≤ C)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    (hfield : ∀u∈Icc (0:ℝ) 1,M.h u ≤ C*(comparisonLowerScale M.context.N M.context.E M.context.d+u)) :
    ∀u∈Icc (0:ℝ) 1,(M.bf u:ℝ) ≤ T ∧ (M.hf u:ℝ) ≤
      (C+D^2*(Az+1/cl))*(M.xs+u) := by
  intro u hu
  have Htotal:=M.inherited_total_clock_le htotal u hu
  refine ⟨by linarith [(M.hf u).coe_nonneg],?_⟩
  rw [(M.inherited_clock_coe hu).2]
  have Hb:=(hfield u hu).trans (mul_le_mul_of_nonneg_left (add_le_add M.hscale le_rfl) hC)
  have HR:=M.inverse_radius_le_source_mass hcl hAz hu
  have hr:=(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u).1
  have he : M.coefficient u ≤ D^2 := (M.coefficient_le_lam u).trans
    (M.hld.trans (pow_le_pow_left₀ M.context.hd.le M.hdD 2))
  have Hmul:=mul_le_mul he HR hr (sq_nonneg D)
  nlinarith only [Hb,Hmul]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
