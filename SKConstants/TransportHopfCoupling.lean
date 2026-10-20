module
public import Mathlib

/-!
Adapted from OpenAI/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Original source: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI
License: Apache-2.0. Namespaces and module exports were adapted for the
pinned SK development; the analytic proofs are retained.
-/

@[expose] public section

/- Original module: Geometry/WeakHessian/Transport/CompactBounded.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
variable {Z : Type*} [MetricSpace Z]

def compactToBounded : C_c(Z,ℝ) →ₗ[ℝ] (Z →ᵇ ℝ) where
  toFun := CompactlySupportedContinuousMap.toBoundedContinuousFunction
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] lemma compactToBounded_apply (f : C_c(Z,ℝ)) (x : Z) : compactToBounded f x = f x := rfl

variable [ProperSpace Z]

lemma compact_thickenedIndicator {s : Set Z} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  have hc : IsCompact (Metric.cthickening δ s) := hs.cthickening
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.thickening_subset_cthickening δ s
  by_contra h
  exact hx (by simp only [thickenedIndicator_zero hδ s h, NNReal.coe_zero])

def ballCutoff (o : Z) (n : ℕ) : C_c(Z,ℝ) :=
  ⟨⟨fun x => (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n) x : ℝ),
    NNReal.continuous_coe.comp (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n)).continuous⟩,
    compact_thickenedIndicator (isCompact_closedBall o n) (by norm_num)⟩

lemma ballCutoff_nonneg (o : Z) (n : ℕ) (x : Z) : 0 ≤ ballCutoff o n x := NNReal.coe_nonneg _
lemma ballCutoff_le_one (o : Z) (n : ℕ) (x : Z) : ballCutoff o n x ≤ 1 :=
  NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
lemma ballCutoff_eq_one (o : Z) (n : ℕ) {x : Z} (hx : x ∈ Metric.closedBall o n) :
    ballCutoff o n x = 1 := by
  change (thickenedIndicator _ _ x : ℝ) = 1
  rw [thickenedIndicator_one _ _ hx]
  rfl

lemma tendsto_ballCutoff (o : Z) (x : Z) : Tendsto (fun n => ballCutoff o n x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (dist x o)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (ballCutoff_eq_one o n (hN.le.trans (Nat.cast_le.mpr hn))).symm

def boundedMulCompact (f : Z →ᵇ ℝ) (η : C_c(Z,ℝ)) : C_c(Z,ℝ) :=
  ⟨⟨fun x => f x*η x, f.continuous.mul η.continuous⟩,
    η.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right⟩

variable [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

lemma exists_finite_measure_le_positive_functional
    (g : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure Z, IsFiniteMeasure q ∧
      (∀ f : C_c(Z,ℝ), (∫ x, f x ∂q) = g (compactToBounded f)) ∧
      (∀ f : Z →ᵇ ℝ, (∀ x, 0 ≤ f x) → (∫ x, f x ∂q) ≤ g f) := by
  let Λ : C_c(Z,ℝ) →ₚ[ℝ] ℝ :=
    { g.comp compactToBounded with monotone' := fun f h hfh => hg (fun x => hfh x) }
  let q := RealRMK.rieszMeasure Λ
  let o : Z := Classical.arbitrary Z
  have hCc (f : C_c(Z,ℝ)) : (∫ x, f x ∂q) = g (compactToBounded f) :=
    RealRMK.integral_rieszMeasure Λ f
  have hb (n : ℕ) : q (Metric.closedBall o n) ≤
      ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    exact (RealRMK.rieszMeasure_le_of_eq_one Λ (ballCutoff_nonneg o n)
      (isCompact_closedBall o n) (fun x hx => ballCutoff_eq_one o n hx)).trans
      (ENNReal.ofReal_le_ofReal (hg (fun x => ballCutoff_le_one o n x)))
  have huniv : (⋃ n : ℕ, Metric.closedBall o (n:ℝ)) = univ := by
    ext x
    simp only [mem_iUnion,Metric.mem_closedBall,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (dist x o)
    exact ⟨n,hn.le⟩
  have hmon : Monotone (fun n : ℕ => Metric.closedBall o (n:ℝ)) :=
    fun n k hnk => Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnk)
  have htotal : q univ ≤ ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    rw [← huniv,hmon.directed_le.measure_iUnion]
    exact iSup_le hb
  have hfinite : IsFiniteMeasure q := ⟨htotal.trans_lt ENNReal.ofReal_lt_top⟩
  let := hfinite
  refine ⟨q,hfinite,hCc,?_⟩
  intro f hf
  have hi (n : ℕ) : (∫ x, boundedMulCompact f (ballCutoff o n) x ∂q) ≤ g f := by
    rw [hCc]
    apply hg
    intro x
    exact mul_le_of_le_one_right (hf x) (ballCutoff_le_one o n x)
  have hl : Tendsto (fun n => ∫ x, boundedMulCompact f (ballCutoff o n) x ∂q)
      atTop (𝓝 (∫ x, f x ∂q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (boundedMulCompact f (ballCutoff o n)).continuous.aestronglyMeasurable
    · exact integrable_const ‖f‖
    · intro n
      exact ae_of_all _ fun x => by
        change ‖f x*ballCutoff o n x‖ ≤ ‖f‖
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg o n x)]
        exact (mul_le_of_le_one_right (norm_nonneg _) (ballCutoff_le_one o n x)).trans
          (f.norm_coe_le_norm x)
    · exact ae_of_all _ fun x => by
        change Tendsto (fun n => f x*ballCutoff o n x) atTop (𝓝 (f x))
        simpa only [mul_one] using (tendsto_const_nhds.mul (tendsto_ballCutoff o x))
  exact le_of_tendsto' hl hi
end WeakHessianTransport

end

end SKConstants

/- Original module: Geometry/WeakHessian/Transport/UpperEnvelope.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set

namespace WeakHessianTransport
variable {A E : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup E] [Module ℝ E]

lemma exists_sublinear_support (N : E → ℝ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, N (r • x) = r * N x)
    (hadd : ∀ x y, N (x+y) ≤ N x + N y) (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, g x = N x ∧ ∀ y, g y ≤ N y := by
  have hzero : N 0 = 0 := by
    have H := hhom 2 (by norm_num) 0
    simp only [smul_zero] at H
    linarith
  have hcompat : ∀ r : ℝ, r • x = 0 → r • N x = 0 := by
    intro r hr
    rcases smul_eq_zero.mp hr with hr | hx
    · simp [hr]
    · simp [hx,hzero]
  let p : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (N x) hcompat
  have hdom : ∀ y : p.domain, p y ≤ N y := by
    rintro ⟨y,hy⟩
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    change LinearPMap.mkSpanSingleton' x (N x) hcompat ⟨r • x, _⟩ ≤ N (r • x)
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rcases lt_trichotomy 0 r with hr | hr | hr
    · rw [hhom r hr x]
    · simp [← hr,hzero]
    · have H := hadd x (-x)
      rw [add_neg_cancel, hzero] at H
      have heq : r • x = (-r) • (-x) := by simp
      rw [heq, hhom (-r) (by linarith) (-x)]
      have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ -r by linarith)
      nlinarith
  obtain ⟨g,hgp,hg⟩ := exists_extension_of_le_sublinear p N hhom hadd hdom
  refine ⟨g, ?_, hg⟩
  have hx : x ∈ p.domain := Submodule.mem_span_singleton_self x
  have H := hgp ⟨x,hx⟩
  simpa only [p, LinearPMap.mkSpanSingleton'_apply_self] using H

variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]

def upperEnvelope (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  sInf {r | ∃ a : A, x ≤ T a ∧ r = c a}

variable (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (l : E →ₗ[ℝ] ℝ)
  (hl : Monotone l) (hcomp : ∀ a, l (T a) = c a)
  (hmajor : ∀ x : E, ∃ a : A, x ≤ T a)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_nonempty (x : E) : {r | ∃ a : A, x ≤ T a ∧ r = c a}.Nonempty := by
  obtain ⟨a,ha⟩ := hmajor x
  exact ⟨c a, a, ha, rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_bddBelow (x : E) : BddBelow {r | ∃ a : A, x ≤ T a ∧ r = c a} := by
  refine ⟨l x, ?_⟩
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma lower_le_envelope (x : E) : l x ≤ upperEnvelope T c x := by
  apply le_csInf (envelope_nonempty T c hmajor x)
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_le (x : E) (a : A) (ha : x ≤ T a) : upperEnvelope T c x ≤ c a :=
  csInf_le (envelope_bddBelow T c l hl hcomp x) ⟨a,ha,rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_image (a : A) : upperEnvelope T c (T a) = c a := by
  exact le_antisymm (envelope_le T c l hl hcomp _ a le_rfl)
    (by simpa only [hcomp] using lower_le_envelope T c l hl hcomp hmajor (T a))

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_zero : upperEnvelope T c (0 : E) = 0 := by
  simpa only [map_zero] using envelope_image T c l hl hcomp hmajor 0

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_mono : Monotone (upperEnvelope T c) := by
  intro x y hxy
  apply le_csInf (envelope_nonempty T c hmajor y)
  rintro r ⟨a,ha,rfl⟩
  exact envelope_le T c l hl hcomp x a (hxy.trans ha)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_lt {x : E} {r : ℝ} (hr : upperEnvelope T c x < r) :
    ∃ a : A, x ≤ T a ∧ c a < r := by
  obtain ⟨s,⟨a,ha,rfl⟩,hs⟩ := exists_lt_of_csInf_lt (envelope_nonempty T c hmajor x) hr
  exact ⟨a,ha,hs⟩

omit [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_add (x y : E) :
    upperEnvelope T c (x+y) ≤ upperEnvelope T c x + upperEnvelope T c y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x) (r := upperEnvelope T c x+ε/2) (by linarith)
  obtain ⟨b,hb,hbr⟩ := envelope_lt T c hmajor (x := y) (r := upperEnvelope T c y+ε/2) (by linarith)
  have H := envelope_le T c l hl hcomp (x+y) (a+b) (by simpa only [map_add] using add_le_add ha hb)
  rw [map_add] at H
  linarith

omit [IsOrderedAddMonoid E] in
include hl hcomp hmajor in
lemma envelope_smul (r : ℝ) (hr : 0 < r) (x : E) :
    upperEnvelope T c (r • x) = r * upperEnvelope T c x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x)
      (r := upperEnvelope T c x+ε/r) (lt_add_of_pos_right _ (div_pos hε hr))
    have H := envelope_le T c l hl hcomp (r • x) (r • a)
      (by simpa only [map_smul] using smul_le_smul_of_nonneg_left ha hr.le)
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_lt_mul_of_pos_left har hr
    have heq : r*(upperEnvelope T c x+ε/r) = r*upperEnvelope T c x+ε := by field_simp
    rw [heq] at H'
    linarith
  · apply le_csInf (envelope_nonempty T c hmajor (r • x))
    rintro s ⟨a,ha,rfl⟩
    have hax : x ≤ T (r⁻¹ • a) := by
      have H := smul_le_smul_of_nonneg_left ha (inv_nonneg.mpr hr.le)
      simpa only [map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using H
    have H := envelope_le T c l hl hcomp x (r⁻¹ • a) hax
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_le_mul_of_nonneg_left H hr.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using H'

include hl hcomp hmajor in

lemma exists_envelope_support (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, Monotone g ∧ (∀ a, g (T a) = c a) ∧
      g x = upperEnvelope T c x := by
  obtain ⟨g,hgx,hg⟩ := exists_sublinear_support (upperEnvelope T c)
    (envelope_smul T c l hl hcomp hmajor) (envelope_add T c l hl hcomp hmajor) x
  have hpos : ∀ y : E, 0 ≤ y → 0 ≤ g y := by
    intro y hy
    have H := hg (-y)
    have H' := envelope_mono T c l hl hcomp hmajor (neg_nonpos.mpr hy)
    rw [envelope_zero T c l hl hcomp hmajor] at H'
    rw [map_neg] at H
    linarith
  refine ⟨g, ?_, ?_, hgx⟩
  · intro y z hyz
    have H := hpos (z-y) (sub_nonneg.mpr hyz)
    rw [map_sub] at H
    linarith
  · intro a
    have H := hg (T a)
    have H' := hg (T (-a))
    rw [envelope_image T c l hl hcomp hmajor] at H H'
    rw [map_neg, map_neg, map_neg] at H'
    linarith

end WeakHessianTransport

open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end SKConstants

/- Original module: Geometry/WeakHessian/Transport/BoundedMarginalSum.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def boundedMarginalSum : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X×Y) →ᵇ ℝ) where
  toFun fg := fg.1.compContinuous ⟨Prod.fst,continuous_fst⟩ +
    fg.2.compContinuous ⟨Prod.snd,continuous_snd⟩
  map_add' a b := by ext p; change (a.1 p.1+b.1 p.1)+(a.2 p.2+b.2 p.2) = _; simp; ring
  map_smul' r a := by ext p; change r*a.1 p.1+r*a.2 p.2 = r*(a.1 p.1+a.2 p.2); ring

@[simp] lemma boundedMarginalSum_apply (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (p : X×Y) :
    boundedMarginalSum fg p = fg.1 p.1 + fg.2 p.2 := rfl

lemma exists_boundedMarginal_majorant (f : (X×Y) →ᵇ ℝ) :
    ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ), f ≤ boundedMarginalSum fg := by
  refine ⟨(BoundedContinuousFunction.const X ‖f‖,0),fun p => ?_⟩
  change f p ≤ ‖f‖+0
  simpa only [add_zero] using (le_abs_self (f p)).trans (f.norm_coe_le_norm p)

def compactTensor (f : C_c(X,ℝ)) (g : C_c(Y,ℝ)) : C_c(X×Y,ℝ) :=
  ⟨⟨fun p => f p.1*g p.2,by fun_prop⟩, by
    apply (f.hasCompactSupport.prod g.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport g))
    intro p hp
    exact ⟨subset_closure (fun h => hp (by simp [h])),subset_closure (fun h => hp (by simp [h]))⟩⟩

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

def boundedIntegral (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' r f := integral_smul r f

lemma boundedIntegral_mono (μ : Measure X) [IsFiniteMeasure μ] :
    Monotone (boundedIntegral μ) := fun f g hfg => integral_mono (f.integrable μ) (g.integrable μ) hfg

def boundedMarginalIntegral (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ :=
  (boundedIntegral μ).comp (LinearMap.fst ℝ _ _) + (boundedIntegral ν).comp (LinearMap.snd ℝ _ _)

@[simp] lemma boundedMarginalIntegral_apply (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedMarginalIntegral μ ν fg = (∫ x,fg.1 x ∂μ)+(∫ y,fg.2 y ∂ν) := rfl

variable [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]

lemma integral_boundedMarginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedIntegral (μ.prod ν) (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg := by
  change (∫ p,boundedMarginalSum fg p ∂μ.prod ν) = _
  rw [integral_prod _ ((boundedMarginalSum fg).integrable _)]
  simp only [boundedMarginalSum_apply,boundedMarginalIntegral_apply]
  have H (x : X) : (∫ y,fg.1 x+fg.2 y ∂ν) = fg.1 x+∫ y,fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) (fg.2.integrable ν)]; simp
  simp_rw [H]
  rw [integral_add (fg.1.integrable μ) (integrable_const _)]
  simp

variable [ProperSpace X] [ProperSpace Y]

lemma exists_probability_of_positive_marginal_functional
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : ((X×Y) →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g)
    (hmarg : ∀ fg, g (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      ∀ f : (X×Y) →ᵇ ℝ, (∫ p,f p ∂q) = g f := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  obtain ⟨q,hq,hCc,hle⟩ := exists_finite_measure_le_positive_functional g hg
  let := hq
  have hc (r : ℝ) : g (BoundedContinuousFunction.const (X×Y) r) = r := by
    have H := hmarg (BoundedContinuousFunction.const X r,0)
    have he : boundedMarginalSum (BoundedContinuousFunction.const X r,(0 : Y →ᵇ ℝ)) =
        BoundedContinuousFunction.const (X×Y) r := by ext; simp
    rw [he] at H
    simpa only [boundedMarginalIntegral_apply,BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,integral_zero,add_zero,integral_const,probReal_univ,
      one_smul] using H
  have hup : q.real univ ≤ 1 := by
    simpa [hc] using hle (BoundedContinuousFunction.const (X×Y) 1) (fun _ => zero_le_one)
  let a : X := Classical.arbitrary X
  let b : Y := Classical.arbitrary Y
  have hcut (n : ℕ) : (∫ x,ballCutoff a n x ∂μ)+(∫ y,ballCutoff b n y ∂ν)-1 ≤ q.real univ := by
    have H := hg (show boundedMarginalSum (compactToBounded (ballCutoff a n),
        compactToBounded (ballCutoff b n))-BoundedContinuousFunction.const (X×Y) 1 ≤
        compactToBounded (compactTensor (ballCutoff a n) (ballCutoff b n)) from by
      intro p
      change ballCutoff a n p.1+ballCutoff b n p.2-1 ≤ ballCutoff a n p.1*ballCutoff b n p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr (ballCutoff_le_one a n p.1))
        (sub_nonneg.mpr (ballCutoff_le_one b n p.2))])
    rw [map_sub,hmarg,hc,←hCc] at H
    apply H.trans
    have HI := integral_mono (μ := q) (compactTensor (ballCutoff a n) (ballCutoff b n)).integrable
      (integrable_const (1:ℝ)) (fun p => show ballCutoff a n p.1*ballCutoff b n p.2 ≤ 1 from
        (mul_le_of_le_one_right (ballCutoff_nonneg a n p.1) (ballCutoff_le_one b n p.2)).trans
          (ballCutoff_le_one a n p.1))
    simpa using HI
  have hlimX : Tendsto (fun n => ∫ x,ballCutoff a n x ∂μ) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1:ℝ))
      (fun n => (ballCutoff a n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun x => by change ‖ballCutoff a n x‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg a n x)]; exact ballCutoff_le_one a n x)
      (ae_of_all _ fun x => tendsto_ballCutoff a x)
    simpa using H
  have hlimY : Tendsto (fun n => ∫ y,ballCutoff b n y ∂ν) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : Y => (1:ℝ))
      (fun n => (ballCutoff b n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun y => by change ‖ballCutoff b n y‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg b n y)]; exact ballCutoff_le_one b n y)
      (ae_of_all _ fun y => tendsto_ballCutoff b y)
    simpa using H
  have hlo : 1 ≤ q.real univ := by simpa using le_of_tendsto' ((hlimX.add hlimY).sub_const 1) hcut
  have hprob : IsProbabilityMeasure q := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top q univ) (by simp)).mp
    simpa only [ENNReal.toReal_one,Measure.real] using le_antisymm hup hlo⟩
  let := hprob
  refine ⟨q,hprob,?_⟩
  intro f
  have H := hle (f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).1
    linarith)
  have I := hle (-f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ -f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).2
    linarith)
  rw [map_add,hc] at H
  rw [map_add,map_neg,hc] at I
  change (∫ p,f p+‖f‖ ∂q) ≤ _ at H
  change (∫ p,-f p+‖f‖ ∂q) ≤ _ at I
  rw [integral_add (f.integrable q) (integrable_const _)] at H
  rw [show (∫ p,-f p+‖f‖ ∂q) = (∫ p,-f p ∂q)+(∫ _ : X×Y,‖f‖ ∂q) from
    integral_add (show Integrable (fun p => -f p) q from (f.integrable q).neg) (integrable_const _),integral_neg] at I
  simp only [integral_const,probReal_univ,one_smul] at H I
  linarith

end WeakHessianTransport

end
end InlinedFile0

end SKConstants

/- Original module: Geometry/WeakHessian/Transport/HopfObjective.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]

def hopfObjective (f : X → ℝ) (t : ℝ) (x y : X) : ℝ :=
  f y + dist x y ^ 2 / (2*t)

def hopfLax (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sInf (Set.range (hopfObjective f t x))

lemma hopfObjective_bddBelow {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    BddBelow (Set.range (hopfObjective f t x)) := by
  refine ⟨B, ?_⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma hopfLax_le_objective {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x y : X) :
    hopfLax f t x ≤ hopfObjective f t x y :=
  csInf_le (hopfObjective_bddBelow hf ht x) (mem_range_self y)

lemma hopfLax_le_self {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : hopfLax f t x ≤ f x := by
  simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    using hopfLax_le_objective hf ht x x

lemma lower_le_hopfLax {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : B ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma continuous_hopfObjective {f : X → ℝ} (hf : Continuous f) (t : ℝ) (x : X) :
    Continuous (hopfObjective f t x) := by
  unfold hopfObjective
  fun_prop

lemma hopfLax_mono_function {f g : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (hfg : ∀ y, f y ≤ g y) (ht : 0 < t) (x : X) :
    hopfLax f t x ≤ hopfLax g t x := by
  apply le_csInf ⟨hopfObjective g t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  exact (hopfLax_le_objective hf ht x y).trans (add_le_add_left (hfg y) _)

lemma hopfLax_antitone_time {f : X → ℝ} {B s t : ℝ}
    (hf : ∀ y, B ≤ f y) (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f t x ≤ hopfLax f s x := by
  apply le_csInf ⟨hopfObjective f s x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  apply (hopfLax_le_objective hf (hs.trans_le hst) x y).trans
  change f y + dist x y ^ 2 / (2*t) ≤ f y + dist x y ^ 2 / (2*s)
  gcongr

lemma exists_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    ∃ y : X, hopfObjective f t x y = hopfLax f t x := by
  let R := Real.sqrt (2*t*(f x-B+1))
  have hnon : 0 ≤ 2*t*(f x-B+1) := by nlinarith [hlower x]
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*t*(f x-B+1) := Real.sq_sqrt hnon
  obtain ⟨y,hy,hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, by simpa using hR⟩ (continuous_hopfObjective hf t x).continuousOn
  have hyall : ∀ z : X, hopfObjective f t x y ≤ hopfObjective f t x z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall x R
    · exact hmin hz
    · have hdist : R < dist x z := by
        simpa only [Metric.mem_closedBall, not_le, dist_comm] using hz
      have hsq : R^2 < dist x z ^ 2 := sq_lt_sq₀ hR (dist_nonneg) |>.mpr hdist
      have hcost : f x < hopfObjective f t x z := by
        dsimp [hopfObjective]
        have hdiv : f x-B+1 < dist x z^2/(2*t) := by
          apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
          nlinarith
        linarith [hlower z]
      have hym : hopfObjective f t x y ≤ f x := by
        simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div,
          add_zero] using (show hopfObjective f t x y ≤ hopfObjective f t x x from
            hmin (show x ∈ Metric.closedBall x R by simpa using hR))
      exact hym.trans hcost.le
  refine ⟨y, le_antisymm ?_ (hopfLax_le_objective hlower ht x y)⟩
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨z,rfl⟩
  exact hyall z

lemma hopf_minimizer_distance_sq {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    dist x y ^ 2 ≤ 2*t*(f x-B) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have hdiv : dist x y^2/(2*t) ≤ f x-B := by
    dsimp [hopfObjective] at H
    linarith [hlower y]
  have H' := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hdiv
  nlinarith

lemma hopf_spatial_increment {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) (z : X) :
    hopfLax f t z - hopfLax f t x ≤
      dist x y / t * dist z x + dist z x ^ 2 / (2*t) := by
  have H := hopfLax_le_objective hlower ht z y
  rw [← hy]
  have hd := dist_triangle z x y
  have hs : dist z y ^ 2 ≤ (dist z x + dist x y) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr hd
  have hcost : dist z y^2/(2*t) - dist x y^2/(2*t) ≤
      dist x y / t * dist z x + dist z x^2/(2*t) := by
    rw [div_sub_div_same]
    have heq : dist x y / t * dist z x + dist z x ^ 2 / (2*t) =
        (2 * dist x y * dist z x + dist z x ^ 2) / (2*t) := by
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  dsimp [hopfObjective] at *
  linarith

lemma hopf_minimizer_distance_le {f : X → ℝ} {B U t R : ℝ}
    (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U) (ht : 0 < t)
    (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ R := by
  apply (sq_le_sq₀ dist_nonneg hR).mp
  exact (hopf_minimizer_distance_sq hlower ht hy).trans
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right (hupper x) B) (by positivity)).trans hR2)

lemma hopf_spatial_abs_increment [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) (x z : X) :
    |hopfLax f t z - hopfLax f t x| ≤ R/t * dist z x + dist z x^2/(2*t) := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
  have hyR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hy
  have hwR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hw
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ R/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ R/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma hopfLax_lipschitz_radius [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) :
    LipschitzWith ⟨R/t + 1/(2*t) + (U-B), by positivity⟩ (hopfLax f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  change |hopfLax f t z - hopfLax f t x| ≤ (R/t+1/(2*t)+(U-B))*dist z x
  by_cases hd : dist z x ≤ 1
  · have H := hopf_spatial_abs_increment hf hlower hupper ht hR hR2 x z
    have hs : dist z x^2 ≤ dist z x := by nlinarith [dist_nonneg (x := z) (y := x)]
    have I := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*t)
    have J : 0 ≤ (U-B)*dist z x := by positivity
    simp only [div_eq_mul_inv, one_mul] at H I ⊢
    nlinarith
  · have hzlo := lower_le_hopfLax hlower ht z
    have hxlo := lower_le_hopfLax hlower ht x
    have hzup := (hopfLax_le_self hlower ht z).trans (hupper z)
    have hxup := (hopfLax_le_self hlower ht x).trans (hupper x)
    have H : |hopfLax f t z-hopfLax f t x| ≤ U-B := abs_le.mpr ⟨by linarith, by linarith⟩
    have I : U-B ≤ (U-B)*dist z x := by nlinarith
    have J : 0 ≤ (R/t+1/(2*t))*dist z x := by positivity
    nlinarith

lemma hopfLax_continuous [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) : Continuous (hopfLax f t) := by
  apply (hopfLax_lipschitz_radius hf hlower hupper hBU ht (Real.sqrt_nonneg (2*t*(U-B))) ?_).continuous
  exact (Real.sq_sqrt (by positivity)).ge

lemma hopf_time_increment {f : X → ℝ} {B s t : ℝ}
    (hlower : ∀ y, B ≤ f y) (hs : 0 < s) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    hopfLax f s x - hopfLax f t x ≤ dist x y^2*(t-s)/(2*s*t) := by
  have H := hopfLax_le_objective hlower hs x y
  rw [← hy]
  have heq : dist x y^2/(2*s) - dist x y^2/(2*t) = dist x y^2*(t-s)/(2*s*t) := by
    field_simp
  dsimp [hopfObjective] at *
  linarith

lemma hopf_time_increment_bound [ProperSpace X] {f : X → ℝ} {B U s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  apply (hopf_time_increment hlower hs ht hy).trans
  have H : dist x y^2 ≤ 2*t*(U-B) :=
    (hopf_minimizer_distance_sq hlower ht hy).trans (by gcongr; exact hupper x)
  calc
    dist x y^2*(t-s)/(2*s*t) ≤ (2*t*(U-B))*(t-s)/(2*s*t) := by gcongr
    _ = (U-B)*(t-s)/s := by field_simp

lemma hopf_time_abs_bound [ProperSpace X] {f : X → ℝ} {B U a s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) (x : X) :
    |hopfLax f s x - hopfLax f t x| ≤ (U-B)/a * |s-t| := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have hs0 := ha.trans_le hs
  have ht0 := ha.trans_le ht
  rw [abs_of_nonneg (sub_nonneg.mpr (hopfLax_antitone_time hlower hs0 hst x)),
    abs_of_nonpos (sub_nonpos.mpr hst)]
  have H := hopf_time_increment_bound hf hlower hupper hs0 hst x
  calc
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := H
    _ ≤ (U-B)*(t-s)/a := by gcongr
    _ = (U-B)/a * -(s-t) := by ring

lemma hopfLax_time_continuousAt [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) :
    ContinuousAt (fun s => hopfLax f s x) t := by
  have hLip : LipschitzOnWith ⟨(U-B)/(t/2), by positivity⟩
      (fun s => hopfLax f s x) (Ici (t/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    change |hopfLax f s x-hopfLax f r x| ≤ (U-B)/(t/2)*|s-r|
    exact hopf_time_abs_bound hf hlower hupper hBU (by positivity : 0 < t/2) hs hr x
  exact hLip.continuousOn.continuousAt (Ici_mem_nhds (by linarith))

lemma hopfLax_ge_lipschitz {f : X → ℝ} {L : ℝ≥0} {t : ℝ}
    (hf : LipschitzWith L f) (ht : 0 < t) (x : X) :
    f x - t*(L:ℝ)^2/2 ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  have H := hf.dist_le_mul x y
  rw [Real.dist_eq] at H
  have H' := (abs_le.mp H).2
  change f x - t*(L:ℝ)^2/2 ≤ f y + dist x y^2/(2*t)
  have Hsq := sq_nonneg (dist x y - t*(L:ℝ))
  have Hdiv : (L:ℝ)*dist x y - t*(L:ℝ)^2/2 ≤ dist x y^2/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith
  linarith

lemma hopf_minimizer_distance_lipschitz {f : X → ℝ} {L : ℝ≥0} {B t : ℝ}
    (hf : LipschitzWith L f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ 2*t*(L:ℝ) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have Hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at Hd
  have Hd' := (abs_le.mp Hd).2
  have Hdiv : dist x y^2/(2*t) ≤ (L:ℝ)*dist x y := by
    dsimp [hopfObjective] at H
    linarith
  have Hmul := (div_le_iff₀ (by positivity : 0 < 2*t)).mp Hdiv
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  · have hd0 : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    apply le_of_mul_le_mul_left (a := dist x y) _ hd0
    convert Hmul using 1 <;> ring

def IsFarthestHopfMinimizer (f : X → ℝ) (t : ℝ) (x y : X) : Prop :=
  hopfObjective f t x y = hopfLax f t x ∧
  ∀ z, hopfObjective f t x z = hopfLax f t x → dist x z ≤ dist x y

lemma hopf_minimizers_compact [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) :
    IsCompact {y | hopfObjective f t x y = hopfLax f t x} := by
  let R := Real.sqrt (2*t*(U-B))
  apply (isCompact_closedBall x R).of_isClosed_subset
    (isClosed_eq (continuous_hopfObjective hf t x) continuous_const)
  intro y hy
  rw [Metric.mem_closedBall, dist_comm]
  exact hopf_minimizer_distance_le hlower hupper ht (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)).ge hy

lemma exists_farthest_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) : ∃ y, IsFarthestHopfMinimizer f t x y := by
  obtain ⟨y,hy,hmax⟩ := (hopf_minimizers_compact hf hlower hupper hBU ht x).exists_isMaxOn
    (exists_hopf_minimizer hf hlower ht x) (continuous_const.dist continuous_id).continuousOn
  exact ⟨y,hy, fun z hz => hmax hz⟩

lemma eventually_hopf_minimizer_distance_lt [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y)
    {r : ℝ} (hr : dist x y < r) :
    ∀ᶠ z in 𝓝 x, ∀ w, hopfObjective f t z w = hopfLax f t z → dist z w < r := by
  let R := Real.sqrt (2*t*(U-B))
  let C := Metric.closedBall x (R+1)
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall x (R+1))
  let S : Set (X × C) := {p | hopfObjective f t p.1 p.2 = hopfLax f t p.1 ∧ r ≤ dist p.1 p.2}
  have hobj : Continuous (fun p : X × C => hopfObjective f t p.1 p.2) := by
    dsimp [hopfObjective]
    fun_prop
  have hdist : Continuous (fun p : X × C => dist p.1 p.2) := by fun_prop
  have hS : IsClosed S := (isClosed_eq hobj
    ((hopfLax_continuous hf hlower hupper hBU ht).comp continuous_fst)).inter
      (isClosed_le continuous_const hdist)
  have hclosed : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  have hx : x ∉ Prod.fst '' S := by
    rintro ⟨⟨z,w⟩,⟨hmin,hd⟩,hpair⟩
    dsimp at hpair
    subst z
    exact (not_le_of_gt (lt_of_le_of_lt (hy.2 w hmin) hr)) hd
  have hne : ∀ᶠ z in 𝓝 x, z ∉ Prod.fst '' S := hclosed.isOpen_compl.mem_nhds hx
  have hball : ∀ᶠ z in 𝓝 x, dist z x < 1 := Metric.ball_mem_nhds x (by norm_num)
  filter_upwards [hne, hball] with z hz hzx
  intro w hw
  have hwR : dist z w ≤ R := hopf_minimizer_distance_le hlower hupper ht
    (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity)).ge hw
  have hwC : w ∈ C := by
    change dist w x ≤ R+1
    calc
      dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ ≤ R+1 := by rw [dist_comm w z]; linarith
  by_contra hrw
  apply hz
  exact ⟨(z, ⟨w, hwC⟩), ⟨hw, le_of_not_gt hrw⟩, rfl⟩

lemma hopf_time_derivative_at_minimizer {f : X → ℝ} {B t v : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x)
    (hv : HasDerivAt (fun s => hopfLax f s x) v t) :
    v = -(dist x y^2/(2*t^2)) := by
  have ho : HasDerivAt (fun s => hopfObjective f s x y)
      (-(dist x y^2/(2*t^2))) t := by
    convert (hasDerivAt_const t (f y)).add
      ((hasDerivAt_const t (dist x y^2)).div
        ((hasDerivAt_id t).const_mul 2) (by positivity : 2*t ≠ 0)) using 1
    <;> first | rfl | (simp only [id_eq]; ring)
  have hmax : IsLocalMax (fun s => hopfLax f s x - hopfObjective f s x y) t := by
    change ∀ᶠ s in 𝓝 t, hopfLax f s x - hopfObjective f s x y ≤
      hopfLax f t x - hopfObjective f t x y
    rw [hy, sub_self]
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact sub_nonpos.mpr (hopfLax_le_objective hlower hs x y)
  have H := hmax.hasDerivAt_eq_zero (hv.sub ho)
  linarith

lemma hopf_spatial_quotient_bound {f : X → ℝ} {B t r : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x z y w : X}
    (hy : hopfObjective f t x y = hopfLax f t x)
    (hw : hopfObjective f t z w = hopfLax f t z)
    (hyr : dist x y ≤ r) (hwr : dist z w ≤ r) (hzx : z ≠ x) :
    |hopfLax f t z - hopfLax f t x| / dist z x ≤ r/t + dist z x/(2*t) := by
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ r/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ r/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  have Ha : |hopfLax f t z-hopfLax f t x| ≤ r/t*dist z x + dist z x^2/(2*t) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply (div_le_iff₀ (dist_pos.mpr hzx)).mpr
  apply Ha.trans_eq
  ring

lemma hopf_localSlope_le [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y) :
    Filter.limsup (fun z => ENNReal.ofReal
      (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤
      ENNReal.ofReal (dist x y/t) := by
  by_cases hbot : (𝓝[≠] x) = ⊥
  · simp [hbot]
  have : NeBot (𝓝[≠] x) := ⟨hbot⟩
  have H : ∀ r : ℝ, dist x y < r →
      Filter.limsup (fun z => ENNReal.ofReal
        (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤ ENNReal.ofReal (r/t) := by
    intro r hr
    have he := eventually_hopf_minimizer_distance_lt hf hlower hupper hBU ht hy hr
    have hb : ∀ᶠ z in 𝓝[≠] x, ENNReal.ofReal (|hopfLax f t z-hopfLax f t x|/dist z x) ≤
        ENNReal.ofReal (r/t+dist z x/(2*t)) := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzx
      obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
      apply ENNReal.ofReal_le_ofReal
      exact hopf_spatial_quotient_bound hlower ht hy.1 hw hr.le (hz w hw).le hzx
    have hc : Tendsto (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) (𝓝[≠] x)
        (𝓝 (ENNReal.ofReal (r/t))) := by
      have hc' : ContinuousAt (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) x :=
        ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
      simpa using hc'.tendsto.mono_left nhdsWithin_le_nhds
    exact (limsup_le_limsup hb).trans_eq hc.limsup_eq
  have hc : Tendsto (fun r : ℝ => ENNReal.ofReal (r/t)) (𝓝[>] dist x y)
      (𝓝 (ENNReal.ofReal (dist x y/t))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_id.div_const t)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact H r hr

lemma hopf_hamiltonJacobi_at [ProperSpace X] {f : X → ℝ} {B U t v : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X)
    (hv : HasDerivAt (fun s => hopfLax f s x) v t) :
    v + (Filter.limsup (fun z => ENNReal.ofReal
      (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x)).toReal^2/2 ≤ 0 := by
  obtain ⟨y,hy⟩ := exists_farthest_hopf_minimizer hf hlower hupper hBU ht x
  have hd := hopf_time_derivative_at_minimizer hlower ht hy.1 hv
  have hs := hopf_localSlope_le hf hlower hupper hBU ht hy
  have hsr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist x y/t)] at hsr
  have hs2 := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity : 0 ≤ dist x y/t)).mpr hsr
  have heq : (dist x y/t)^2/2 = dist x y^2/(2*t^2) := by ring
  linarith

lemma hopf_hamiltonJacobi_ae [ProperSpace X] {f : X → ℝ} {B U : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (x : X) :
    ∀ᵐ t : ℝ, 0 < t → DifferentiableAt ℝ (fun s => hopfLax f s x) t ∧
      deriv (fun s => hopfLax f s x) t +
        (Filter.limsup (fun z => ENNReal.ofReal
          (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x)).toReal^2/2 ≤ 0 := by
  have hLip (n : ℕ) : LipschitzOnWith ⟨(U-B)/(1/(n+1:ℝ)), by positivity⟩
      (fun s => hopfLax f s x) (Ici (1/(n+1:ℝ))) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    exact hopf_time_abs_bound hf hlower hupper hBU (by positivity) hs hr x
  have ha := MeasureTheory.ae_all_iff.mpr
    (fun n => (hLip n).ae_differentiableWithinAt_of_mem_real)
  filter_upwards [ha] with t ht ht0
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt ht0
  have hd : DifferentiableAt ℝ (fun s => hopfLax f s x) t :=
    (ht n hn.le).differentiableAt (Ici_mem_nhds hn)
  exact ⟨hd, hopf_hamiltonJacobi_at hf hlower hupper hBU ht0 x hd.hasDerivAt⟩

end WeakHessianTransport

end
end InlinedFile0

end SKConstants

/- Original module: Geometry/WeakHessian/Transport/TruncatedQuadraticCost.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
open Set MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance boundedPosSMulMono : PosSMulMono ℝ ((X×Y) →ᵇ ℝ) where
  smul_le_smul_of_nonneg_left scalar nonneg left right pointwise := fun point =>
    mul_le_mul_of_nonneg_left (a := scalar) (b := left point) (c := right point)
      (pointwise point) nonneg

lemma bounded_marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)} [IsFiniteMeasure q]
    (hq : ∀ fg, (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (compactToBounded f,0)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero,integral_zero] using H
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (0,compactToBounded f)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,zero_add,integral_zero] using H

lemma bounded_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : (X×Y) →ᵇ ℝ) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
        boundedMarginalSum fg ≤ cost ∧
        (∫ p,cost p ∂q) < boundedMarginalIntegral μ ν fg+ε := by
  let T := boundedMarginalSum (X := X) (Y := Y)
  let c := boundedMarginalIntegral μ ν
  let l := boundedIntegral (μ.prod ν)
  have hl : Monotone l := boundedIntegral_mono _
  have hcomp : ∀ fg,l (T fg) = c fg := integral_boundedMarginalSum μ ν
  have hmajor : ∀ f,∃ fg,f ≤ T fg := exists_boundedMarginal_majorant
  obtain ⟨g,hg,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hq,hgq⟩ := exists_probability_of_positive_marginal_functional μ ν g hg hgmarg
  let := hq
  have hqsum (fg) : (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg :=
    (hgq (T fg)).trans (hgmarg fg)
  obtain ⟨h0,h1⟩ := bounded_marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p,cost p ∂q) = -upperEnvelope T c (-cost) := by
    have H := (hgq (-cost)).trans hgcost
    change (∫ p,-cost p ∂q) = _ at H
    rw [integral_neg] at H
    linarith
  refine ⟨q,hq,h0,h1,?_⟩
  intro ε hε
  obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
    (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
  refine ⟨-fg,?_,?_⟩
  · change T (-fg) ≤ cost
    rw [map_neg]
    simpa only [neg_neg] using neg_le_neg hfg
  · change (∫ p,cost p ∂q) < c (-fg)+ε
    rw [hcq,map_neg]
    linarith
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma bounded_lipschitz_dual_improvement {t : ℝ} (ht : 0 < t)
    (a b : X →ᵇ ℝ) (hab : ∀ x y, a x+b y ≤ dist x y^2/(2*t)) :
    ∃ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) ∧
      (∀ x, |f x| ≤ ‖a‖) ∧
      (∀ x, a x ≤ hopfLax f t x) ∧ (∀ y, f y ≤ -b y) := by
  let B := ‖a‖
  have ha : ∀ x, |a x| ≤ B := fun x => a.norm_coe_le_norm x
  have hlo : ∀ x, -B ≤ -a x := fun x => by linarith [(abs_le.mp (ha x)).2]
  have hup : ∀ x, -a x ≤ B := fun x => by linarith [(abs_le.mp (ha x)).1]
  have hBU : -B ≤ B := by dsimp [B]; linarith [norm_nonneg a]
  have hlip := hopfLax_lipschitz_radius a.continuous.neg hlo hup hBU ht
    (Real.sqrt_nonneg (2*t*(B-(-B))))
    (Real.sq_sqrt (show 0 ≤ 2*t*(B-(-B)) by positivity)).ge
  let f : X → ℝ := fun y => -hopfLax (fun x => -a x) t y
  have hfbound : ∀ y, |f y| ≤ B := by
    intro y
    have H := lower_le_hopfLax hlo ht y
    have I := (hopfLax_le_self hlo ht y).trans (hup y)
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  refine ⟨f, ⟨_, hlip.neg⟩, hfbound, ?_, ?_⟩
  · intro x
    apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
    rintro r ⟨y,rfl⟩
    have H := hopfLax_le_objective hlo ht y x
    dsimp [hopfObjective, f] at *
    rw [dist_comm y x] at H
    linarith
  · intro y
    suffices b y ≤ hopfLax (fun x => -a x) t y by
      dsimp [f]
      linarith
    apply le_csInf ⟨hopfObjective (fun x => -a x) t y y, mem_range_self y⟩
    rintro r ⟨x,rfl⟩
    have H := hab x y
    change a x + b y ≤ dist x y^2/(2*t) at H
    dsimp [hopfObjective]
    rw [dist_comm y x]
    linarith

omit [MeasurableSpace X] [BorelSpace X] in
def truncatedQuadraticCost (n : ℕ) : (X×X) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => min (dist p.1 p.2^2/2) (n:ℝ))
    (by fun_prop) n (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (by positivity) (Nat.cast_nonneg n))]
      exact min_le_right _ _)

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma truncatedQuadraticCost_apply (n : ℕ) (p : X×X) :
    truncatedQuadraticCost n p = min (dist p.1 p.2^2/2) (n:ℝ) := rfl

variable [TopologicalSpace.SeparableSpace X]

lemma exists_coupling_truncatedCost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) (n : ℕ) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫ p,truncatedQuadraticCost n p ∂q) ≤ B/2 := by
  obtain ⟨q,hq,h0,h1,hql⟩ := bounded_kantorovich_duality μ ν (truncatedQuadraticCost n)
  let := hq
  refine ⟨q,hq,h0,h1,?_⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨⟨a,b⟩,hab,habI⟩ := hql ε hε
  have hab' (x y : X) : a x+b y ≤ dist x y^2/(2*(1:ℝ)) := by
    have H := hab (x,y)
    change a x+b y ≤ min (dist x y^2/2) (n:ℝ) at H
    simpa only [mul_one] using H.trans (min_le_left _ _)
  obtain ⟨f,⟨L,hf⟩,hB,haf,hfb⟩ := bounded_lipschitz_dual_improvement (by norm_num : (0:ℝ)<1) a b hab'
  let f' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous ‖a‖
    (fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hd := hdual f' ⟨L,hf⟩
  have hlo (x : X) : -‖a‖ ≤ f x := (abs_le.mp (hB x)).1
  have hup (x : X) : f x ≤ ‖a‖ := (abs_le.mp (hB x)).2
  have hc : Continuous (hopfLax f 1) := hopfLax_continuous hf.continuous hlo hup
    (by linarith [norm_nonneg a]) (by norm_num)
  have hi : Integrable (hopfLax f 1) μ := Integrable.of_bound hc.aestronglyMeasurable ‖a‖
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨lower_le_hopfLax hlo (by norm_num) x,
        (hopfLax_le_self hlo (by norm_num) x).trans (hup x)⟩)
  have HA := integral_mono (a.integrable μ) hi haf
  have HB := integral_mono (f'.integrable ν) (b.integrable ν).neg hfb
  change (∫ x,f x ∂ν) ≤ ∫ x,-b x ∂ν at HB
  rw [integral_neg] at HB
  change (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2 at hd
  change (∫ p,truncatedQuadraticCost n p ∂q) < (∫ x,a x ∂μ)+(∫ x,b x ∂ν)+ε at habI
  linarith
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

end
end InlinedFile0

end SKConstants

/- Original module: Geometry/WeakHessian/Transport/ProbabilityTightMarginals.lean -/

namespace SKConstants

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

lemma probability_isTight_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (ProbabilityMeasure (X×Y)))
    (h0 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.snd = ν) :
    IsTightMeasureSet {((q:ProbabilityMeasure (X×Y)) : Measure (X×Y)) | q ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hh : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K,hK,hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ)) (ε/2) hh
  obtain ⟨L,hL,hLm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν)) (ε/2) hh
  refine ⟨K×ˢL,hK.prod hL,?_⟩
  rintro _ ⟨q,hq,rfl⟩
  have he : (K×ˢL)ᶜ = (Prod.fst ⁻¹' Kᶜ) ∪ (Prod.snd ⁻¹' Lᶜ) := by ext p; simp only [mem_compl_iff,mem_prod,not_and_or,mem_union,mem_preimage]
  calc
    (q:Measure (X×Y)) (K×ˢL)ᶜ ≤ (q:Measure (X×Y)) (Prod.fst ⁻¹' Kᶜ)+(q:Measure (X×Y)) (Prod.snd ⁻¹' Lᶜ) := by rw [he]; exact measure_union_le _ _
    _ = μ Kᶜ+ν Lᶜ := by rw [←Measure.map_apply measurable_fst hK.measurableSet.compl,
        ←Measure.map_apply measurable_snd hL.measurableSet.compl,h0 q hq,h1 q hq]
    _ ≤ ε/2+ε/2 := add_le_add (hKm μ (mem_singleton μ)) (hLm ν (mem_singleton ν))
    _ = ε := ENNReal.add_halves ε

lemma exists_coupling_limit (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (qs : ℕ → ProbabilityMeasure (X×Y))
    (h0 : ∀ n,(qs n : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ n,(qs n : Measure (X×Y)).map Prod.snd = ν) :
    ∃ q : ProbabilityMeasure (X×Y), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q) ∧
      (q:Measure (X×Y)).map Prod.fst = μ ∧ (q:Measure (X×Y)).map Prod.snd = ν := by
  have ht := probability_isTight_of_marginals μ ν (range qs)
    (by rintro _ ⟨n,rfl⟩; exact h0 n) (by rintro _ ⟨n,rfl⟩; exact h1 n)
  obtain ⟨q,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨q,φ,hφ,hlim,?_,?_⟩
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_fst : Continuous (Prod.fst : X×Y → X))
    have he : (fun n => (qs (φ n)).map Prod.fst) = fun _ : ℕ => (⟨μ,inferInstance⟩ : ProbabilityMeasure X) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h0 (φ n)
    change Tendsto (fun n => (qs (φ n)).map Prod.fst) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_snd : Continuous (Prod.snd : X×Y → Y))
    have he : (fun n => (qs (φ n)).map Prod.snd) = fun _ : ℕ => (⟨ν,inferInstance⟩ : ProbabilityMeasure Y) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h1 (φ n)
    change Tendsto (fun n => (qs (φ n)).map Prod.snd) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_proper_coupling_cost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) ≤ ENNReal.ofReal B := by
  choose qs hp h0 h1 hc using exists_coupling_truncatedCost_of_hopf_bound μ ν B hdual
  let ps : ℕ → ProbabilityMeasure (X×X) := fun n => ⟨qs n,hp n⟩
  obtain ⟨q,φ,hφ,hlim,hq0,hq1⟩ := exists_coupling_limit μ ν ps h0 h1
  have hcost (k : ℕ) : (∫ p,truncatedQuadraticCost k p ∂(q:Measure (X×X))) ≤ B/2 := by
    have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (truncatedQuadraticCost k)
    apply le_of_tendsto H
    filter_upwards [eventually_ge_atTop k] with n hn
    have hk : k ≤ φ n := hn.trans (hφ.id_le n)
    have hi (p : X×X) : truncatedQuadraticCost k p ≤ truncatedQuadraticCost (φ n) p := by
      exact min_le_min_left _ (Nat.cast_le.mpr hk)
    let := hp (φ n)
    exact (integral_mono ((truncatedQuadraticCost k).integrable (qs (φ n)))
      ((truncatedQuadraticCost (φ n)).integrable (qs (φ n))) hi).trans (hc (φ n))
  have hnn (k : ℕ) (p : X×X) : 0 ≤ truncatedQuadraticCost k p :=
    le_min (by positivity) (Nat.cast_nonneg k)
  have heavg : (∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) ≤ ENNReal.ofReal (B/2) := by
    have hs (p : X×X) : ENNReal.ofReal (dist p.1 p.2^2/2) =
        ⨆ n : ℕ, ENNReal.ofReal (truncatedQuadraticCost n p) := by
      apply le_antisymm
      · obtain ⟨n,hn⟩ := exists_nat_gt (dist p.1 p.2^2/2)
        exact (le_iSup_of_le n (by simp only [truncatedQuadraticCost_apply, min_eq_left hn.le]; exact le_rfl))
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [hs]
    rw [lintegral_iSup (fun n => (truncatedQuadraticCost n).continuous.measurable.ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal ((truncatedQuadraticCost n).integrable (q:Measure (X×X)))
        (ae_of_all _ (hnn n))]
      exact ENNReal.ofReal_le_ofReal (hcost n)
    · intro a b hab p
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hab))
  refine ⟨q,inferInstance,hq0,hq1,?_⟩
  calc
    (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) =
        ∫⁻ p : X×X, (2:ℝ≥0∞)*ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X)) := by
      apply lintegral_congr
      intro p
      rw [edist_dist,←ENNReal.ofReal_pow dist_nonneg]
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    _ = 2*(∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ 2*ENNReal.ofReal (B/2) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

end
end InlinedFile0

end SKConstants
