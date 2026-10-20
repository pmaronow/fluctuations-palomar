module

public import ComparisonSignedCavityTwoLevelWeightedAnchor

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

private theorem two_level_smooth_sqrt_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Type*} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → E) (hx : Measurable x) {A : E → ℝ}
    (hA : BddSmooth 0 A) (_hAn : ∀ y,0 ≤ A y) :
    MemLp (fun p=>Real.sqrt (A (x p))) 2 μ := by
  obtain ⟨R,_,hR⟩ := hA.bound
  apply MemLp.of_bound ((hA.continuous.measurable.comp hx).sqrt).aestronglyMeasurable (Real.sqrt R)
  apply Eventually.of_forall
  intro p
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Function.comp_apply] using hR (x p))

theorem native_two_level_weighted_anchor_integral_moment (n l : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es : ClockTree (Spin n) sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P → RestCoordinate n → ℝ) (hxi : Measurable xi) (hxs : Measurable xs) :
    (∫ z,‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs (xi z) (xs z)‖^(4*l) ∂μ) ≤
      Real.sqrt (∫ z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
        (fun η ζ=>|H η ζ|^(8*l)) (xi z) (xs z) ∂μ)*
      Real.sqrt (∫ z,(Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
        |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
          (joinSpin (Ei.atSlot η.2 s,false))|^(4*l)) (xi z) ∂μ) := by
  let A := fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ)=>
    nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
      (fun η ζ=>|H η ζ|^(8*l)) z.1 z.2
  let B := fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ)=>
    (Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
      |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
        (joinSpin (Ei.atSlot η.2 s,false))|^(4*l)) z.1
  let x := fun p=>(xi p,xs p)
  have hx : Measurable x := hxi.prodMk hxs
  have hAn z : 0 ≤ A z := by
    unfold A nativeExteriorForestMean ClockTree.expect
    apply Finset.sum_nonneg
    intro η _
    apply mul_nonneg ((Ei.weight_probability (restWeight_pos n) (restFeature n) hoi qi z.1).1 η)
    exact Finset.sum_nonneg fun ζ _=>mul_nonneg
      ((Es.weight_probability (restWeight_pos n) (restFeature n) hos qs z.2).1 ζ) (by positivity)
  have hBn z : 0 ≤ B z := Finset.sum_nonneg fun η _=>mul_nonneg
    (((Ei.fork Ei).weight_probability (restWeight_pos n) (restFeature n) hoi qi z.1).1 η)
    (by positivity)
  have hAs : BddSmooth 0 A := nativeExteriorForestMean_smooth_joint
    (restWeight_pos n) (restFeature n) Ei Es hoi hos qi qs (fun η ζ=>|H η ζ|^(8*l)) 0
  have hBs : BddSmooth 0 B :=
    ((Ei.fork Ei).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n) hoi qi (fun η=>
      |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
        (joinSpin (Ei.atSlot η.2 s,false))|^(4*l)) 0).compCLM
      (ContinuousLinearMap.fst ℝ (RestCoordinate n → ℝ) (RestCoordinate n → ℝ))
  have hAf := two_level_smooth_sqrt_memLp μ x hx hAs hAn
  have hBf := two_level_smooth_sqrt_memLp μ x hx hBs hBn
  have hprod : MemLp (fun p=>Real.sqrt (A (x p))*Real.sqrt (B (x p))) 1 μ := hAf.mul hBf
  have hpoint p : ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs (xi p) (xs p)‖^(4*l) ≤
      Real.sqrt (A (x p))*Real.sqrt (B (x p)) := by
    apply le_trans _ (Real.sqrt_mul (hAn _) _).le
    apply (Real.le_sqrt (by positivity) (mul_nonneg (hAn _) (hBn _))).mpr
    have hp := native_two_level_weighted_anchor_moment n (2*l) Ei Es hoi hos H s qi qs (xi p) (xs p)
    simpa only [A,B,x,←pow_mul,show 4*(2*l)=8*l by omega,
      show 2*(2*l)=4*l by omega,show (4*l)*2=8*l by omega] using hp
  have hi := integral_mono_of_nonneg (Eventually.of_forall fun _=>by positivity)
    (memLp_one_iff_integrable.mp hprod) (Eventually.of_forall hpoint)
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun p=>Real.sqrt_nonneg (A (x p)))
    (Eventually.of_forall fun p=>Real.sqrt_nonneg (B (x p))) (by simpa using hAf) (by simpa using hBf)
  simp only [Real.rpow_two,Real.sq_sqrt (hAn _),Real.sq_sqrt (hBn _)] at hc
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hc
  exact hi.trans hc

theorem native_two_level_weighted_anchor_integral_scale (n l : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es : ClockTree (Spin n) sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P → RestCoordinate n → ℝ) (hxi : Measurable xi) (hxs : Measurable xs)
    {p sj : ℝ} (hp : 0 ≤ p) (hsj : 0 ≤ sj)
    (hH : (∫ z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
      (fun η ζ=>|H η ζ|^(8*l)) (xi z) (xs z) ∂μ) ≤ p^(8*l))
    (hR : (∫ z,(Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
      |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
        (joinSpin (Ei.atSlot η.2 s,false))|^(4*l)) (xi z) ∂μ) ≤ sj^(4*l)) :
    (∫ z,‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs (xi z) (xs z)‖^(4*l) ∂μ) ≤
      (p*Real.sqrt sj)^(4*l) := by
  apply (native_two_level_weighted_anchor_integral_moment n l Ei Es hoi hos H s qi qs μ xi xs hxi hxs).trans
  apply (mul_le_mul (Real.sqrt_le_sqrt hH) (Real.sqrt_le_sqrt hR)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  have h1 : Real.sqrt (p^(8*l))=p^(4*l) := by
    rw [show 8*l=(4*l)*2 by omega,pow_mul,Real.sqrt_sq (pow_nonneg hp _)]
  have h2 : Real.sqrt (sj^(4*l))=sj^(2*l) := by
    rw [show 4*l=(2*l)*2 by omega,pow_mul,Real.sqrt_sq (pow_nonneg hsj _)]
  rw [h1,h2,mul_pow]
  congr 1
  calc
    sj^(2*l)=((Real.sqrt sj)^2)^(2*l) := by rw [Real.sq_sqrt hsj]
    _ = (Real.sqrt sj)^(4*l) := by rw [←pow_mul]; congr 1; omega

end OAI.SKFluctuations.Cavity
