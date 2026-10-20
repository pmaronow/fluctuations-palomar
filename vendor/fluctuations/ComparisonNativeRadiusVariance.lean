module

public import ComparisonNativeVarianceBinGeometry
public import ComparisonNativeCovarianceTransport
public import PhysicalFiniteWeightedTrace
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

namespace MassCellAveraging

def average (f : ℝ→ℝ) (a b : ℝ) : ℝ := (∫u in a..b,f u)/(b-a)

def sample (f : ℝ→ℝ) : ℝ→List PositiveMass→ℝ→ℝ
  | _,[],_=>0
  | a,b::bs,u=>if u<b.val then average f a b.val else sample f b.val bs u

theorem sample_integrable_comp (f : ℝ→ℝ) (a : ℝ) (as : List PositiveMass)
    (phi : ℝ→ℝ) (c d : ℝ) : IntervalIntegrable (fun u=>phi (sample f a as u)) volume c d := by
  induction as generalizing a with
  | nil=>exact (intervalIntegrable_const (μ:=volume) (c:=phi 0))
  | cons b bs ih=>
    apply intervalIntegrable_iff.mpr
    have hpc := Integrable.piecewise (measurableSet_Iio (a:=b.val))
        ((intervalIntegrable_const (a:=c) (b:=d) (μ:=volume) (c:=phi (average f a b.val))).def'.integrableOn)
        ((ih b.val).def'.integrableOn)
    apply hpc.congr
    exact ae_of_all _ (fun u=>by
      by_cases hu : u<b.val
      · simp [sample,Set.piecewise,hu]
      · simp [sample,Set.piecewise,hu])

theorem sample_memLp_two (f : ℝ→ℝ) (a : ℝ) (as : List PositiveMass) :
    MemLp (sample f a as) 2 (volume.restrict (Ioc (0:ℝ) 1)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (sample_integrable_comp f a as id 0 1)
  have hs := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (sample_integrable_comp f a as (fun z=>z^2) 0 1)
  exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr hs

theorem average_square_le (f : ℝ→ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hfs : IntervalIntegrable (fun u=>(f u)^2) volume a b) :
    (b-a)*(average f a b)^2 ≤ ∫u in a..b,(f u)^2 := by
  by_cases he : a=b
  · subst b;simp [average]
  have hp : 0<b-a := sub_pos.mpr (lt_of_le_of_ne hab he)
  let mu := volume.restrict (Ioc a b)
  have hIa : Integrable (fun u=>|f u|) mu := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf.abs
  have hIs : Integrable (fun u=>|f u|^2) mu := by
    simpa only [mu,sq_abs,IntegrableOn] using (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hfs
  have hJ := integral_pow_le_mass mu (Eventually.of_forall (fun u=>abs_nonneg (f u))) hIa
    (by norm_num : 0<(2:ℕ)) hIs
  have hm : mu.real univ=b-a := by simp [mu,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hp.le]
  rw [hm] at hJ
  simp only [Nat.sub_self,show 2-1=1 by decide,pow_one,sq_abs] at hJ
  rw [←intervalIntegral.integral_of_le hab,←intervalIntegral.integral_of_le hab] at hJ
  have hA := intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=f) hab
  have habs0 : 0 ≤ ∫u in a..b,|f u| := intervalIntegral.integral_nonneg_of_ae hab
    (Eventually.of_forall (fun u=>abs_nonneg (f u)))
  have hsq : (∫u in a..b,f u)^2 ≤ (b-a)*(∫u in a..b,(f u)^2) := by
    have hsqA := mul_self_le_mul_self (abs_nonneg (∫u in a..b,f u)) hA
    nlinarith [sq_abs (∫u in a..b,f u)]
  have hcancel : (b-a)*average f a b=∫u in a..b,f u := by
    unfold average
    field_simp
  have hsC := congrArg (fun t : ℝ=>t^2) hcancel
  nlinarith

theorem sample_square_contraction (f : ℝ→ℝ) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (he : partitionEnd a as=1)
    (hf : IntervalIntegrable f volume a 1) (hfs : IntervalIntegrable (fun u=>(f u)^2) volume a 1) :
    (∫u in a..1,(sample f a as u)^2) ≤ ∫u in a..1,(f u)^2 := by
  induction as generalizing a with
  | nil=>simp only [partitionEnd] at he;subst a;simp
  | cons b bs ih=>
    have ha := massOrdered_bounds ho
    have hb := massOrdered_bounds ho.2.2
    have hf0 := hf.mono_set (by rw [uIcc_of_le ho.2.1,uIcc_of_le ha.2];exact Icc_subset_Icc_right hb.2)
    have hf1 := hf.mono_set (by rw [uIcc_of_le hb.2,uIcc_of_le ha.2];exact Icc_subset_Icc_left ho.2.1)
    have hs0 := hfs.mono_set (by rw [uIcc_of_le ho.2.1,uIcc_of_le ha.2];exact Icc_subset_Icc_right hb.2)
    have hs1 := hfs.mono_set (by rw [uIcc_of_le hb.2,uIcc_of_le ha.2];exact Icc_subset_Icc_left ho.2.1)
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (sample_integrable_comp f a (b::bs) (fun z=>z^2) a b.val)
      (sample_integrable_comp f a (b::bs) (fun z=>z^2) b.val 1),
      ←intervalIntegral.integral_add_adjacent_intervals hs0 hs1]
    have h0 : (∫u in a..b.val,(sample f a (b::bs) u)^2)=(b.val-a)*(average f a b.val)^2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le ho.2.1
        (fun u hu=>by rw [sample,ite_eq_left hu.2]),intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have h1 : (∫u in b.val..1,(sample f a (b::bs) u)^2)=
        ∫u in b.val..1,(sample f b.val bs u)^2 :=
      intervalIntegral.integral_congr_Ioo_of_le hb.2
        (fun u hu=>by rw [sample,ite_eq_right (not_lt.mpr hu.1.le)])
    rw [h0,h1]
    exact add_le_add (average_square_le f ho.2.1 hf0 hs0) (ih ho.2.2 he hf1 hs1)

theorem sample_sub (f g : ℝ→ℝ) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hf : IntervalIntegrable f volume a 1)
    (hg : IntervalIntegrable g volume a 1) (u : ℝ) :
    sample (fun t=>f t-g t) a as u=sample f a as u-sample g a as u := by
  induction as generalizing a with
  | nil=>simp [sample]
  | cons b bs ih=>
    have ha := massOrdered_bounds ho
    have hb := massOrdered_bounds ho.2.2
    have hf0 := hf.mono_set (by rw [uIcc_of_le ho.2.1,uIcc_of_le ha.2];exact Icc_subset_Icc_right hb.2)
    have hg0 := hg.mono_set (by rw [uIcc_of_le ho.2.1,uIcc_of_le ha.2];exact Icc_subset_Icc_right hb.2)
    have hf1 := hf.mono_set (by rw [uIcc_of_le hb.2,uIcc_of_le ha.2];exact Icc_subset_Icc_left ho.2.1)
    have hg1 := hg.mono_set (by rw [uIcc_of_le hb.2,uIcc_of_le ha.2];exact Icc_subset_Icc_left ho.2.1)
    simp only [sample]
    split_ifs
    · simp only [average,intervalIntegral.integral_sub hf0 hg0,sub_div]
    · exact ih ho.2.2 hf1 hg1

theorem average_sub_const_abs_le (g : ℝ→ℝ) {a b u eta : ℝ} (hab : a<b)
    (hg : IntervalIntegrable g volume a b) (heta : 0 ≤ eta)
    (hclose : ∀t ∈ Icc a b,|g t-g u| ≤ eta) : |average g a b-g u| ≤ eta := by
  have he : average g a b-g u=(∫t in a..b,g t-g u)/(b-a) := by
    rw [intervalIntegral.integral_sub hg intervalIntegrable_const,intervalIntegral.integral_const]
    simp only [smul_eq_mul,average]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=fun t=>g t-g u) hab.le
  have hi := intervalIntegral.integral_mono_on hab.le (hg.sub intervalIntegrable_const).abs
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>eta) volume a b)
    (fun t ht=>hclose t ht)
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  exact hnorm.trans (by simpa only [mul_comm] using hi)

theorem sample_continuous_eventually_uniform (g : ℝ→ℝ) (hg : Continuous g)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0))
    {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ j in atTop,∀u ∈ Ico (0:ℝ) 1,|sample g 0 (as j) u-g u| ≤ eta := by
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) eta heta
  filter_upwards [(tendsto_order.mp hlim).2 delta hdelta] with j hj
  have hprove {a : ℝ} (bs : List PositiveMass) (ho : MassOrdered a bs)
      (hm : PartitionMesh (mesh j) a bs) (he : partitionEnd a bs=1) :
      ∀u ∈ Ico a 1,|sample g a bs u-g u| ≤ eta := by
    induction bs generalizing a with
    | nil=>simp only [partitionEnd] at he;subst a;exact fun u hu=>False.elim (not_lt_of_ge hu.1 hu.2)
    | cons b bs ih=>
      intro u hu
      by_cases hub : u<b.val
      · rw [sample,ite_eq_left hub]
        have hab : a<b.val := hu.1.trans_lt hub
        apply average_sub_const_abs_le g hab (hg.intervalIntegrable _ _) heta.le
        intro t ht
        have hti : t ∈ Icc (0:ℝ) 1 := ⟨(massOrdered_bounds ho).1.trans ht.1,ht.2.trans (massOrdered_bounds ho.2.2).2⟩
        have hui : u ∈ Icc (0:ℝ) 1 := ⟨(massOrdered_bounds ho).1.trans hu.1,hu.2.le⟩
        have hdist : dist t u<delta := by
          rw [Real.dist_eq]
          have hb : |t-u| ≤ b.val-a := abs_le.mpr ⟨by linarith [ht.1,hub],by linarith [ht.2,hu.1]⟩
          exact hb.trans_lt (hm.1.trans_lt hj)
        simpa only [Real.dist_eq] using (hclose t hti u hui hdist).le
      · rw [sample,ite_eq_right hub]
        exact ih ho.2.2 hm.2 he u ⟨le_of_not_gt hub,hu.2⟩
  exact hprove (as j) (ho j) (hm j) (he j)

theorem sample_memLp_two_eventually_square (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ j in atTop,(∫u in (0:ℝ)..1,(sample f 0 (as j) u-f u)^2) ≤ epsilon := by
  let rho := volume.restrict (Ioc (0:ℝ) 1)
  have hf' : MemLp f (ENNReal.ofReal (2:ℝ)) rho := by simpa [rho] using hf
  obtain ⟨g,hgerr,hgL⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le
    (by norm_num : 0<(2:ℝ)) (by linarith : 0<epsilon/12)
  have hfg : MemLp (fun u=>f u-g u) 2 rho := by
    convert hf'.sub hgL using 1 <;> norm_num
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  have hiG : IntervalIntegrable (fun u=>g u) volume 0 1 := g.continuous.intervalIntegrable _ _
  have hiFG := hiF.sub hiG
  have hiFGsq : IntervalIntegrable (fun u=>(f u-g u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hfg.integrable_sq
  have herror : (∫u in (0:ℝ)..1,(f u-g u)^2) ≤ epsilon/12 := by
    simpa only [rho,Real.rpow_two,Real.norm_eq_abs,sq_abs,intervalIntegral.integral_of_le zero_le_one] using hgerr
  have hsqrt : 0<Real.sqrt (epsilon/12) := Real.sqrt_pos.2 (by linarith)
  filter_upwards [sample_continuous_eventually_uniform (fun u=>g u) g.continuous as mesh ho hm he hlim hsqrt]
    with j hj
  have hP := sample_square_contraction (fun u=>f u-g u) (as j) (ho j) (he j) hiFG hiFGsq
  have hU : (∫u in (0:ℝ)..1,(sample (fun u=>g u) 0 (as j) u-g u)^2) ≤ epsilon/12 := by
    have hiSq : IntervalIntegrable (fun u=>(sample (fun u=>g u) 0 (as j) u-g u)^2) volume 0 1 := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      exact ((sample_memLp_two (fun u=>g u) 0 (as j)).sub (by simpa [rho] using hgL)).integrable_sq
    have ht := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hiSq
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>epsilon/12) volume 0 1)
      (by
        intro u huI
        have hb := hj u ⟨huI.1.le,huI.2⟩
        have hs := Real.sq_sqrt (by linarith : 0≤epsilon/12)
        nlinarith [abs_nonneg (sample (fun u=>g u) 0 (as j) u-g u),sq_abs (sample (fun u=>g u) 0 (as j) u-g u)])
    simpa using ht
  have hPoint u : (sample f 0 (as j) u-f u)^2 ≤
      3*((sample (fun u=>f u-g u) 0 (as j) u)^2+
        (sample (fun u=>g u) 0 (as j) u-g u)^2+(g u-f u)^2) := by
    rw [sample_sub f (fun u=>g u) (as j) (ho j) hiF hiG u]
    nlinarith [sq_nonneg (sample f 0 (as j) u-sample (fun u=>g u) 0 (as j) u-
      (sample (fun u=>g u) 0 (as j) u-g u)),
      sq_nonneg (sample f 0 (as j) u-sample (fun u=>g u) 0 (as j) u-(g u-f u)),
      sq_nonneg (sample (fun u=>g u) 0 (as j) u-g u-(g u-f u))]
  have hiErr : IntervalIntegrable (fun u=>(sample f 0 (as j) u-f u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((sample_memLp_two f 0 (as j)).sub hf).integrable_sq
  have hiPFG := sample_integrable_comp (fun u=>f u-g u) 0 (as j) (fun z=>z^2) 0 1
  have hiGG : IntervalIntegrable (fun u=>(g u-f u)^2) volume 0 1 := by
    simpa only [sub_sq_comm] using hiFGsq
  have hiU : IntervalIntegrable (fun u=>(sample (fun u=>g u) 0 (as j) u-g u)^2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact ((sample_memLp_two (fun u=>g u) 0 (as j)).sub (by simpa [rho] using hgL)).integrable_sq
  have hbound := intervalIntegral.integral_mono_on zero_le_one hiErr
    (((hiPFG.add hiU).add hiGG).const_mul 3) (fun u _=>hPoint u)
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hiPFG hiU,
    intervalIntegral.integral_add (hiPFG.add hiU) hiGG] at hbound
  have hGG : (∫u in (0:ℝ)..1,(g u-f u)^2) ≤ epsilon/12 := by simpa only [sub_sq_comm] using herror
  linarith

end MassCellAveraging
theorem physical_radius_weight_variance_le_source_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (w : Fin (steps.length+1)→ℝ)
    {a : ℝ} (ha0 : 0<a)
    (hcut : ∀i:Fin (steps.length+1),w i ≠ 0→a ≤ physicalCutMass 0 steps i.val) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 w z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤
      (∑i,pathMassDifferences steps 0 i*(w i)^2*
        ∫z,physicalCutSourceSquareTrace n steps id i.val z
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)/a := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let dim := Fintype.card (Fin (steps.length+1) × FeatureIndex n)
  let e : Fin dim ≃ Fin (steps.length+1) × FeatureIndex n := (Fintype.equivFin _).symm
  have hvar := physical_planted_variance_le q0 steps ha e w
  dsimp only [Function.uncurry] at hvar
  have hpair (z:PhysicalPathState (FeatureIndex n→ℝ) n steps) :
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 w z.1 z.2).2=
        ∑i,pathMassDifferences steps 0 i*(w i)^2*physicalCutSusceptibility n steps id i.val z :=
    physicalPinnedPair_snd_eq_sum n steps ha w id z
  simp_rw [hpair] at hvar
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hI i : Integrable (fun z=>pathMassDifferences steps 0 i*(w i)^2*
      physicalCutSusceptibility n steps id i.val z) mu :=
    ((physicalCutSusceptibility_memLp n steps ha id measurable_id mu i.val 1).integrable le_rfl).const_mul _
  rw [integral_finsetSum Finset.univ (fun i _=>hI i)] at hvar
  simp only [integral_const_mul] at hvar
  apply hvar.trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hw : w i=0
  · simp only [hw,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_mul,zero_div,le_refl]
  · have hW := physicalCutSusceptibility_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hw)
    try simp only [←rootedHierarchyPathLaw_eq_physical] at hW
    have hm : 0 ≤ pathMassDifferences steps 0 i*(w i)^2 :=
      mul_nonneg (pathMassDifferences_nonneg steps ha i) (sq_nonneg _)
    simpa only [mu,mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id] using
      mul_le_mul_of_nonneg_left hW hm

end OAI.SKFluctuations.LaplaceWindowFormalization
