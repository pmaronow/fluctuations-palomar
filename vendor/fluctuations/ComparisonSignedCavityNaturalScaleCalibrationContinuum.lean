module

public import ComparisonSignedCavityNaturalScaleCalibrationGenerated

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem abs_pathPairMoment_le_absolute {S ι : Type*}
    [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ] ℝ)
    (q : ℝ→ι→ℝ≥0) (hq : ∀i,MonotoneOn (fun u=>q u i) (Icc (0:ℝ) 1))
    (P : S→S→ℝ) {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    |pathPairMoment w φ q P u| ≤ pathPairMoment w φ q (fun σ τ=>|P σ τ|) u := by
  apply abs_le.mpr
  constructor
  · have H:=pathPairMoment_mono_test hw φ q hq
      (P:=fun σ τ=>(-1)*P σ τ) (Q:=fun σ τ=>|P σ τ|)
      (fun σ τ=>by simpa using neg_le_abs (P σ τ)) hu
    rw [pathPairMoment_const_mul hw φ q hq P (-1) hu] at H
    linarith
  · exact pathPairMoment_mono_test hw φ q hq (fun σ τ=>le_abs_self (P σ τ)) hu

theorem actual_continuum_center_le_of_second_moment (n : ℕ)
    (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) {u xs K : ℝ}
    (hu : u∈Ioc (0:ℝ) 1) (hxs : 0 < xs)
    (hmoment : pathPairMoment (uniformWeight n) (finiteFeature n)
      (completedPathClock n b h) (fun σ τ=>|orderedOverlap n σ τ|^2) u ≤ K*(xs+u)^2) :
    |pathPairMoment (uniformWeight n) (finiteFeature n)
      (completedPathClock n b h) (orderedOverlap n) u| ≤ (1+K)*(xs+u) := by
  have hq:=completedPathClock_monotone n hb hh
  have H:=pathPairMoment_rpow_from_nat (uniformWeight_pos n) (finiteFeature n)
    (completedPathClock n b h) hq (fun σ τ=>|orderedOverlap n σ τ|)
    (fun σ τ=>abs_nonneg _) hu (add_pos hxs hu.1) (p:=1) (by norm_num)
    2 (by norm_num) hmoment
  have H':pathPairMoment (uniformWeight n) (finiteFeature n)
      (completedPathClock n b h) (fun σ τ=>|orderedOverlap n σ τ|) u ≤ (1+K)*(xs+u) := by
    simpa only [Real.rpow_one] using H
  exact (abs_pathPairMoment_le_absolute (uniformWeight_pos n) (finiteFeature n)
    (completedPathClock n b h) hq (orderedOverlap n) hu).trans H'

theorem eventually_actual_minimum_continuum_center_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cs : ℝ,0 < Cs ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
        |pathPairMoment (uniformWeight n) (finiteFeature n)
          (completedPathClock n M.bf M.hf) (orderedOverlap n) u| ≤ Cs*(M.xs+u) := by
  obtain ⟨K,hK,HK⟩:=eventually_actual_minimum_overlap_natural_moment
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [HK] with n hn
  intro M u hu
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact actual_continuum_center_le_of_second_moment n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu M.hxs (hn M u hu)

theorem continuum_center_bound_closed_interval (n : ℕ)
    (b h : ℝ→ℝ≥0) {xs Cs : ℝ} (hxs : 0 ≤ xs) (hCs : 0 ≤ Cs)
    (hbound : ∀u∈Ioc (0:ℝ) 1,
      |pathPairMoment (uniformWeight n) (finiteFeature n)
        (completedPathClock n b h) (orderedOverlap n) u| ≤ Cs*(xs+u)) :
    ∀u∈Icc (0:ℝ) 1,
      |pathPairMoment (uniformWeight n) (finiteFeature n)
        (completedPathClock n b h) (orderedOverlap n) u| ≤ Cs*(xs+u) := by
  intro u hu
  by_cases hp : 0 < u
  · exact hbound u ⟨hp,hu.2⟩
  · have hz : u=0:=by linarith [hu.1]
    subst u
    simp only [pathPairMoment,lt_self_iff_false,dite_false,abs_zero,add_zero]
    exact mul_nonneg hCs hxs

theorem source_centered_affine_intercept_le {a : ℕ}
    {xs x W Cmass Cs Ch Cb : ℝ} (hxs : xs ≤ x) (hxW : x ≤ W)
    (hx : 0 ≤ x) (hCm : 0 ≤ Cmass) (hCs : 0 ≤ Cs) (hCb : 0 ≤ Cb)
    (initial : Finset (Fin a)) (mass field bond center : Fin a→ℝ)
    (hmass : ∀e,mass e ≤ Cmass*sourceFactorScale x W initial e)
    (hfield : ∀e,|field e| ≤ Ch*sourceFactorScale x W initial e)
    (hbond : ∀e,|bond e| ≤ Cb)
    (hcenter : ∀e,|center e| ≤ Cs*(xs+mass e)) :
    ∀e,|field e-bond e*center e| ≤
      (Ch+Cb*Cs*(1+Cmass))*sourceFactorScale x W initial e := by
  intro e
  have hm : xs+mass e ≤ (1+Cmass)*sourceFactorScale x W initial e :=
    (le_max_right xs _).trans (source_natural_factor_le hxs hxW hx hCm initial mass hmass
      (fun f=>hxs.trans (source_factor_scale_ge_initial hxW initial f)) e)
  have hc : |center e| ≤ Cs*(1+Cmass)*sourceFactorScale x W initial e := by
    exact (hcenter e).trans (by nlinarith [mul_le_mul_of_nonneg_left hm hCs])
  calc
    _ ≤ |field e| + |bond e*center e|:=abs_sub _ _
    _ = |field e| + |bond e| * |center e|:=by rw [abs_mul]
    _ ≤ Ch*sourceFactorScale x W initial e+
      Cb*(Cs*(1+Cmass)*sourceFactorScale x W initial e):=add_le_add (hfield e)
        (mul_le_mul (hbond e) hc (abs_nonneg _) hCb)
    _ = _:=by ring

theorem actual_finite_root_center_le_of_deleted_raw (n a : ℕ) (ha : 0 < a)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ→ℝ)
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) {B : ℝ} (hB : 0 ≤ B)
    (hraw : finitePhysicalDeletedRawBudget n a as b h 0 ≤ B^(2*a)) :
    |finitePhysicalMean (n+1) as b h 0| ≤ B := by
  rw [abs_of_nonneg (finitePhysicalMean_nonneg (n+1) as b h 0)]
  exact finitePhysicalMean_le_of_deleted_raw n a ha ho b h 0
    (Nat.zero_le _) hb hh hB hraw

theorem eventually_actual_minimum_finite_root_center_bound
    (Bclock Btotal Bbond : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cr : ℝ,0 < Cr ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
          b as.length ≤ Bbond →
          |finitePhysicalMean (n+1) as b h 0| ≤ Cr*M.xs := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) 1 (by omega) Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cr,hCr,?_⟩
  filter_upwards [HR] with n hn
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro hclock hbond
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have Hraw:=hk 0 (Nat.zero_le _) hclock hbond
  apply actual_finite_root_center_le_of_deleted_raw n 1 (by omega)
    (finiteCutMasses_ordered us hus k) b h
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) (mul_nonneg hCr.le M.hxs.le)
  simpa only [b,h,as,partitionPoint,partitionValues_zero,id_eq,add_zero] using Hraw

end OAI.SKFluctuations.Cavity
