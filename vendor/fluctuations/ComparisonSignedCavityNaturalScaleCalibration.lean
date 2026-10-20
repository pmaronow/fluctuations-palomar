module

public import ComparisonSignedCavityActualNaturalBoundaryBudget
public import ComparisonSignedCavityGeneratedBoundaryMembership

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def sourceFactorScale {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) (e : Fin a) : ℝ :=
  if e ∈ initial then x else W

def sourceMonomialScale {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) : ℝ :=
  x^initial.card * W^(a-initial.card)

theorem source_factor_scale_pos {a : ℕ} {x W : ℝ} (hx : 0<x) (hW : 0<W)
    (initial : Finset (Fin a)) (e : Fin a) : 0<sourceFactorScale x W initial e := by
  unfold sourceFactorScale
  split_ifs <;> assumption

theorem source_factor_scale_product {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) :
    (∏e,sourceFactorScale x W initial e)=sourceMonomialScale x W initial := by
  classical
  unfold sourceFactorScale sourceMonomialScale
  rw [Finset.prod_ite]
  have hI : (Finset.univ.filter fun e : Fin a=>e∈initial)=initial := by ext e;simp
  have hIc : (Finset.univ.filter fun e : Fin a=>e∉initial)=Finset.univ\initial := by
    ext e;simp
  rw [hI,hIc]
  simp only [Finset.prod_const,Finset.card_sdiff_of_subset (Finset.subset_univ initial),
    Finset.card_univ,Fintype.card_fin]

theorem source_monomial_scale_star {a : ℕ} (x W : ℝ) :
    sourceMonomialScale (a:=a) x W ∅=W^a := by simp [sourceMonomialScale]

theorem source_monomial_scale_initial {a : ℕ} (x W : ℝ) (initial : Finset (Fin a))
    (hI : initial.card=1) : sourceMonomialScale x W initial=x*W^(a-1) := by
  simp [sourceMonomialScale,hI]

theorem source_factor_scale_ge_initial {a : ℕ} {x W : ℝ} (hxW : x ≤ W)
    (initial : Finset (Fin a)) (e : Fin a) : x ≤ sourceFactorScale x W initial e := by
  unfold sourceFactorScale
  split_ifs <;> simp_all

theorem source_natural_factor_le {a : ℕ} {xs x W Cmass scale : ℝ}
    (hxs : xs ≤ x) (hxW : x ≤ W) (hx : 0 ≤ x) (hCm : 0 ≤ Cmass)
    (initial : Finset (Fin a)) (lowMass : Fin a→ℝ)
    (hmass : ∀e,lowMass e ≤ Cmass*sourceFactorScale x W initial e)
    (hscale : ∀e,scale ≤ sourceFactorScale x W initial e) (e : Fin a) :
    max scale (xs+lowMass e) ≤ (1+Cmass)*sourceFactorScale x W initial e := by
  have hxe:=source_factor_scale_ge_initial hxW initial e
  have hne : 0 ≤ sourceFactorScale x W initial e:=hx.trans hxe
  apply max_le
  · exact (hscale e).trans (by nlinarith [mul_nonneg hCm hne])
  · have H:=hmass e
    nlinarith

theorem source_natural_product_le {a : ℕ} {xs x W Cmass scale : ℝ}
    (hxs : xs ≤ x) (hxW : x ≤ W) (hx : 0 ≤ x) (hCm : 0 ≤ Cmass)
    (initial : Finset (Fin a)) (lowMass : Fin a→ℝ)
    (hmass : ∀e,lowMass e ≤ Cmass*sourceFactorScale x W initial e)
    (hscale : ∀e,scale ≤ sourceFactorScale x W initial e)
    (hnat : ∀e,0 ≤ max scale (xs+lowMass e)) :
    (∏e,max scale (xs+lowMass e)) ≤ (1+Cmass)^a*sourceMonomialScale x W initial := by
  calc
    _  ≤  ∏e,(1+Cmass)*sourceFactorScale x W initial e :=
      Finset.prod_le_prod₀ (fun e _=>hnat e)
        (fun e _=>source_natural_factor_le hxs hxW hx hCm initial lowMass hmass hscale e)
    _ = _ := by
      rw [Finset.prod_mul_distrib,source_factor_scale_product]
      simp

theorem finitePhysicalMean_le_of_overlap_moment (n a : ℕ) (ha : 0<a)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ→ℝ)
    (j : ℕ) (hj : j ≤ as.length) {B : ℝ} (hB : 0 ≤ B)
    (hmoment : physicalOverlapMoment n a
      (diagonalBoundarySteps as (physicalCompletedClock n b h 0)
        (fun k=>physicalCompletedClock n b h (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock n b h 0 i)))
      id measurable_id j ≤ B^(2*a)) : finitePhysicalMean n as b h j ≤ B := by
  rw [physicalOverlapMoment_eq_actual_pair n a as ho _ j hj] at hmoment
  have H:=(ClockTree.pairClock as j).disorderExpect_rpow_moment_le
    (uniformWeight_pos n) (finiteFeature n) ho 0 (physicalCompletedClock n b h) 0
    (fun σ=>orderedOverlap n (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
    (p:=1) (r:=(2*a:ℕ)) (by norm_num) (by exact_mod_cast (show 1 ≤ 2*a by omega)) hB
    (by simpa only [Real.rpow_natCast] using hmoment)
  simp only [Real.rpow_one] at H
  rw [finitePhysicalMean_eq_actual_pair n ho b h j hj]
  apply le_trans _ H
  unfold ClockTree.disorderExpect
  exact Finset.sum_le_sum fun σ _=>mul_le_mul_of_nonneg_left (le_abs_self _)
    (((ClockTree.pairClock as j).disorderWeight_probability
      (uniformWeight_pos n) (finiteFeature n) ho 0 (physicalCompletedClock n b h) 0).1 σ)

theorem physical_overlap_moment_le_deleted_raw (n a : ℕ) (_ha : 0<a)
    (as : List PositiveMass) (b h : ℕ→ℝ) (j : ℕ)
    (hb : ∀k,0 ≤ b k) (hh : ∀k,0 ≤ h k) :
    physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun k=>physicalCompletedClock (n+1) b h (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id j ≤ finitePhysicalDeletedRawBudget n a as b h j := by
  let z:=physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun k=>physicalCompletedClock (n+1) b h (k+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id j
  have hz : 0 ≤ z:=integral_nonneg fun p=>conditionalPathAverage_nonneg _ _ _ _ _
    (fun q=>pow_nonneg (abs_nonneg _) _) p
  have hc : 1 ≤ Real.exp (110*b as.length):=Real.one_le_exp_iff.mpr (by nlinarith [hb as.length])
  have hr : 1 ≤ Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+
      b as.length+h as.length)):=Real.one_le_exp_iff.mpr (by
    have H:=finitePhysicalMixedClock_nonneg (n+1) as b h hb hh as.length
    nlinarith [hb as.length,hh as.length])
  have hp : (1:ℝ) ≤ (2:ℝ)^(2*a-1):=one_le_pow₀ (by norm_num)
  have hcoef : 1 ≤ Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+
      b as.length+h as.length))*(2:ℝ)^(2*a-1):=by nlinarith
  unfold finitePhysicalDeletedRawBudget
  change z ≤ _*(_*z+_)
  have H1 : z ≤ Real.exp (110*b as.length)*z:=by nlinarith
  have H2 : 0 ≤ Real.exp (110*b as.length)*z+(1/(n+1:ℕ):ℝ)^(2*a):=by positivity
  have H3:=mul_nonneg (sub_nonneg.mpr hcoef) H2
  nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1/(n+1:ℕ)) (2*a)]

theorem finitePhysicalMean_le_of_deleted_raw (n a : ℕ) (ha : 0<a)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ→ℝ)
    (j : ℕ) (hj : j ≤ as.length) (hb : ∀k,0 ≤ b k) (hh : ∀k,0 ≤ h k)
    {B : ℝ} (hB : 0 ≤ B) (hraw : finitePhysicalDeletedRawBudget n a as b h j ≤ B^(2*a)) :
    finitePhysicalMean (n+1) as b h j ≤ B :=
  finitePhysicalMean_le_of_overlap_moment (n+1) a ha ho b h j hj hB
    ((physical_overlap_moment_le_deleted_raw n a ha as b h j hb hh).trans hraw)

end OAI.SKFluctuations.Cavity
