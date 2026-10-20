module

public import ComparisonNativeMinimumBandModel
public import ComparisonNativeOuterPhysicalBand
public import ComparisonNativeInnerStrengthDistortion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

structure CommonBandGeometry
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (p : a.Potential) where
  clockRegularity : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1
  capSet : Set ℝ
  hopen : IsOpen capSet
  hcapSet : capSet ⊆ Ioo (0:ℝ) 1
  hnegative : ∀r∈capSet,p.H r < 0
  hcomponent : ∀r∈capSet,p.H (sInf (ordConnectedComponent capSet r))=0 ∧
    (p.H (sSup (ordConnectedComponent capSet r))=0 ∨ sSup (ordConnectedComponent capSet r)=1)

theorem R_positive {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) : 0 < a.R u := by
  have hs := comparisonSweepQuantile_strictMono_native_geometry a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) (Ioc_subset_Icc_self hu) hu.1
  have hR0 : a.R 0=0 := by
    simpa only [a.alpha.property.1] using comparisonSweepQuantile_inverse a.context.hc a.context.hk
      a.context.hkc a.context.hm a.context.hM a.alpha (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  change a.R 0 < a.R u at hs
  simpa only [hR0] using hs

theorem canonical_radius_facts
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    0 < a.R (v/4) ∧ a.R (v/4) ≤ a.R (v/2) ∧
      a.R (v/2) ≤ a.R (min (16*v) 1) ∧ a.R (min (16*v) 1) ≤ 1 ∧
      a.alpha.val.val (a.R (v/4))=v/4 ∧
      a.alpha.val.val (a.R (v/2))=v/2 ∧
      a.alpha.val.val (a.R (min (16*v) 1))=min (16*v) 1 := by
  have hlo : v/4∈Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hmid : v/2∈Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hhi : min (16*v) 1∈Icc (0:ℝ) 1 := ⟨(lt_min (by linarith) zero_lt_one).le,min_le_right _ _⟩
  have hm := comparisonSweepQuantile_monotone a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
  exact ⟨a.R_positive ⟨by linarith,hlo.2⟩,hm (by linarith),hm (le_min (by linarith) hmid.2),
    (comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha _).2,
    comparisonSweepQuantile_spec a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha hlo,
    comparisonSweepQuantile_spec a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha hmid,
    comparisonSweepQuantile_spec a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha hhi⟩

def CommonBandGeometry.canonical
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (l : ℕ) (hl : 2 < l) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside) : a.BandGeometry p where
  ag := a.R (v/2)
  zg := a.R (min (16*v) 1)
  lo := v/2
  hi := min (16*v) 1
  Ko := 32
  cutRadius := a.R (v/4)
  hag := a.R_positive ⟨by linarith,by linarith⟩
  hagz := (a.canonical_radius_facts hv hv1).2.2.1
  hzg := (a.canonical_radius_facts hv hv1).2.2.2.1
  hlo := by linarith
  hKo := by norm_num
  hband := by linarith [min_le_left (16*v) 1,a.context.hU]
  hcut := (a.canonical_radius_facts hv hv1).1
  hcut1 := (comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha _).2
  clockRegularity := g.clockRegularity.restrict
    (a.R_positive (u:=v/2) ⟨by linarith,by linarith⟩).le
    (a.canonical_radius_facts hv hv1).2.2.2.1
  capSet := g.capSet
  hopen := g.hopen
  hcapSet := g.hcapSet
  hnegative := g.hnegative
  hcomponent := g.hcomponent
  l := l
  hl := hl
  y := a.xs+min (16*v) 1
  Q := Q
  Lside := Lside
  hy := add_pos a.hxs (lt_min (by linarith) zero_lt_one)
  hQ := hQ
  hLside := hLside
  bandMass := 16*v
  hbandMass := by linarith

theorem CommonBandGeometry.canonical_model_facts
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (l : ℕ) (hl : 2 < l) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) :
    let b := (g.canonical v hv hv1 l hl Q Lside hQ hLside).toModel dphys e hlog hnd
    b.cutRadius ≤ b.ag ∧ b.xs+b.alpha.val.val b.zg ≤ b.y ∧
      b.alpha.val.val b.zg-b.alpha.val.val b.ag ≤ b.bandMass ∧
      b.rho=v/4 ∧ b.bandMass/b.rho=64 ∧ b.P=b.N*laplaceComparisonStrength b.d b.lam b.zg := by
  dsimp only
  have hf := a.canonical_radius_facts hv hv1
  refine ⟨hf.2.1,?_,?_,hf.2.2.2.2.1,?_,?_⟩
  · change a.xs+a.alpha.val.val (a.R (min (16*v) 1)) ≤ a.xs+min (16*v) 1
    rw [hf.2.2.2.2.2.2]
  · change a.alpha.val.val (a.R (min (16*v) 1))-a.alpha.val.val (a.R (v/2)) ≤ 16*v
    rw [hf.2.2.2.2.2.2,hf.2.2.2.2.2.1]
    linarith [min_le_left (16*v) 1]
  · change (16*v)/a.alpha.val.val (a.R (v/4))=64
    rw [hf.2.2.2.2.1]
    field_simp
    norm_num
  · simp only [NativeBandModel.P,BandGeometry.toModel,NativeOverlapContext.N,Nat.cast_add,Nat.cast_one]

theorem CommonBandGeometry.canonical_local_scales
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (l : ℕ) (hl : 2 < l) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hUv : a.context.U ≤ v) :
    let b := (g.canonical v hv hv1 l hl Q Lside hQ hLside).toModel dphys e hlog hnd
    let q := b.lo+b.U
    0 < q ∧ b.hi-b.lo ≤ 32*q ∧ q ≤ 32*b.bandMass ∧ b.bandMass ≤ 32*q ∧ b.U ≤ b.bandMass := by
  dsimp [CommonBandGeometry.canonical,BandGeometry.toModel]
  have hU := a.context.hU
  have hh := min_le_left (16*v) 1
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem canonical_outer_radii
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (houter : 4*cu*Az*a.xs ≤ v) :
    a.z ≤ a.R (v/2) ∧ v/(2*cu) ≤ a.R (v/2) ∧
      a.R (min (16*v) 1) ≤ 16*v/cl := by
  have hf := a.canonical_radius_facts hv hv1
  have hmass : a.alpha.val.val (a.R (v/2))=v/2 := hf.2.2.2.2.2.1
  have hzreg := a.regular a.z ⟨le_rfl,a.hz.2⟩
  have hlarge : a.alpha.val.val a.z < v/2 := by
    have hh := mul_le_mul_of_nonneg_left a.hzxs hcu.le
    nlinarith
  have hzlo : a.z ≤ a.R (v/2) := by
    by_contra hh
    have hlo := a.alpha.val.property.2 (lt_of_not_ge hh).le
    rw [hmass] at hlo
    linarith
  have hleft := a.regular (a.R (v/2)) ⟨hzlo,hf.2.2.1.trans hf.2.2.2.1⟩
  have hright := a.regular (a.R (min (16*v) 1)) ⟨hzlo.trans hf.2.2.1,hf.2.2.2.1⟩
  refine ⟨hzlo,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hcu)).mpr
    rw [hmass] at hleft
    nlinarith
  · apply (le_div_iff₀ hcl).mpr
    rw [hf.2.2.2.2.2.2] at hright
    linarith [min_le_left (16*v) 1]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
