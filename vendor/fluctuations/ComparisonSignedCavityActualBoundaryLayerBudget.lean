module

public import ComparisonSignedCavityMixedForest
public import CavityLocalForkLayer
public import ComparisonSignedCavityActualGroupedLayers
public import ComparisonSignedCavityActualBoundaryScalarRates
public import ComparisonSignedCavityRetainedSubtreeClone
public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem actual_original_root_gram_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A B C : Ω → ℝ} {c : ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ)
    (hAn : ∀ z, 0 ≤ A z) (hBn : ∀ z, 0 ≤ B z)
    (hCB : ∀ z, (C z)^2 ≤ c^2*A z*B z) :
    (∫ z, C z ∂μ)^2 ≤ c^2*(∫ z, A z ∂μ)*(∫ z, B z ∂μ) := by
  have hpos (t : ℝ) (z : Ω) :
      0 ≤ A z*(t*t)+(2*C z)*t+c^2*B z := by
    obtain hAz | hAz := (hAn z).eq_or_lt
    · have hCBz := hCB z
      rw [←hAz] at hCBz
      have hCz : C z=0 := by nlinarith [hCBz, sq_nonneg (C z)]
      rw [←hAz,hCz]
      simpa using mul_nonneg (sq_nonneg c) (hBn z)
    · have hh : 0 ≤ A z*(A z*(t*t)+(2*C z)*t+c^2*B z) := by
        nlinarith [sq_nonneg (A z*t+C z), hCB z]
      exact (mul_nonneg_iff_of_pos_left hAz).mp hh
  have hposI (t : ℝ) : 0 ≤
      (∫ z, A z ∂μ)*(t*t)+(2*(∫ z, C z ∂μ))*t+
        c^2*(∫ z, B z ∂μ) := by
    have hh : 0 ≤ ∫ z, (A z*(t*t)+(2*C z)*t+c^2*B z) ∂μ := by
      apply integral_nonneg
      intro z
      exact hpos t z
    have hi₁ := integral_add ((hA.const_mul (t*t)).add
      (hC.const_mul (2*t))) (hB.const_mul (c^2))
    have hi₂ := integral_add (hA.const_mul (t*t)) (hC.const_mul (2*t))
    have he : (fun z => A z*(t*t)+(2*C z)*t+c^2*B z) =
        fun z => (t*t)*A z+(2*t)*C z+c^2*B z := by funext z; ring
    rw [he] at hh
    simp only [Pi.add_apply] at hi₁ hi₂
    rw [hi₁,hi₂,integral_const_mul,integral_const_mul,integral_const_mul] at hh
    nlinarith
  have hd := discrim_le_zero hposI
  dsimp only [discrim] at hd
  nlinarith

theorem actual_incoming_law_shared_exterior_layer_sq_le
    {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
    {steps : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (A E : ReplicaTree ι S steps)
    {a v z : ℝ} (ho : OrderedSteps a steps) (hav : a≤v) (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ)
    (μ : Measure (ι→ℝ)) [IsProbabilityMeasure μ] :
    (∫ x,actualSharedExteriorLayer A E w φ a v z P F x ∂μ)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*
        (∫ x,actualSharedExteriorOldMoment A E w φ P x ∂μ)*
        (∫ x,actualSharedExteriorNewMoment E w φ F x ∂μ) := by
  classical
  have hIP : Integrable (actualSharedExteriorOldMoment A E w φ P) μ := by
    simpa only [zero_add] using
      (actualSharedExteriorOldMoment_smooth hw φ A E ho P 0).integrable_zero_shift (ν:=μ) 0
  have hIF : Integrable (actualSharedExteriorNewMoment E w φ F) μ := by
    simpa only [zero_add] using
      (actualSharedExteriorNewMoment_smooth hw φ E ho F 0).integrable_zero_shift (ν:=μ) 0
  have hIL : Integrable (actualSharedExteriorLayer A E w φ a v z P F) μ := by
    simpa only [zero_add] using
      (actualSharedExteriorLayer_smooth hw φ A E ho v z P F 0).integrable_zero_shift (ν:=μ) 0
  apply actual_original_root_gram_sq_le μ hIP hIF hIL
  · intro x
    unfold actualSharedExteriorOldMoment
    exact (E.fork (A.fork A)).expect_nonneg hw φ ho (fun _=>sq_nonneg _) x
  · intro x
    unfold actualSharedExteriorNewMoment
    exact (E.fork ((ReplicaTree.single steps).fork (ReplicaTree.single steps))).expect_nonneg
      hw φ ho (fun _=>sq_nonneg _) x
  · intro x
    exact actualSharedExteriorLayer_sq_le hw φ A E ho hav hvz hz P F x

theorem actual_incoming_law_retained_exterior_layer_sq_le
    {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
    {steps : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (pre : List (GaussianStep ι))
    (A : ReplicaTree ι S steps) (E : ReplicaTree ι S (pre++steps))
    {a v z : ℝ} (ho : OrderedSteps a (pre++steps))
    (hp : ∀ st∈pre,st.1≤v) (hav : a≤v) (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ)
    (μ : Measure (ι→ℝ)) [IsProbabilityMeasure μ] :
    (∫ x,actualInheritedExteriorLayer pre A E w φ a v z P F x ∂μ)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*
        (∫ x,actualRetainedExteriorOldMoment pre A E w φ P x ∂μ)*
        (∫ x,actualRetainedExteriorNewMoment pre E w φ F x ∂μ) := by
  classical
  have hIP : Integrable (actualRetainedExteriorOldMoment pre A E w φ P) μ := by
    have H := actualRetainedExteriorOldMoment_smooth hw φ pre A E ho P 0
    simpa only [zero_add] using H.integrable_zero_shift (ν:=μ) 0
  have hIF : Integrable (actualRetainedExteriorNewMoment pre E w φ F) μ := by
    have H := actualRetainedExteriorNewMoment_smooth hw φ pre E ho F 0
    simpa only [zero_add] using H.integrable_zero_shift (ν:=μ) 0
  have hIL : Integrable (actualInheritedExteriorLayer pre A E w φ a v z P F) μ := by
    have H := actualInheritedExteriorLayer_smooth hw φ pre A E ho hp hvz P F 0
    simpa only [zero_add] using H.integrable_zero_shift (ν:=μ) 0
  apply actual_original_root_gram_sq_le μ hIP hIF hIL
  · intro x
    unfold actualRetainedExteriorOldMoment
    exact (E.fork (prependReplicaTree pre (A.fork A))).expect_nonneg hw φ ho
      (fun _=>sq_nonneg _) x
  · intro x
    unfold actualRetainedExteriorNewMoment
    exact (E.fork (prependReplicaTree pre
      ((ReplicaTree.single steps).fork (ReplicaTree.single steps)))).expect_nonneg hw φ ho
      (fun _=>sq_nonneg _) x
  · intro x
    exact actualInheritedExteriorLayer_sq_le hw φ pre A E ho hp hav hvz hz P F x

theorem original_boundary_tail_ordered (n : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ)
    (low : ℕ) (hlow : low≤as.length) :
    OrderedSteps (physicalCutMass 0
      (clockSteps as (cumulativeIncrements (q 0) (fun k=>q (k+1)))) low)
      (originalBoundaryTailSteps n as q low) := by
  let inc := cumulativeIncrements (q 0) (fun k=>q (k+1))
  have hlen : (clockSteps (as.take low) inc).length=low := by
    rw [length_clockSteps,List.length_take_of_le hlow]
  have htail : (clockSteps as inc).drop low=originalBoundaryTailSteps n as q low := by
    have hdrop : (clockSteps (as.take low) inc).drop low=[] :=
      List.drop_eq_nil_of_le hlen.le
    rw [clockSteps_take_drop as inc low hlow,List.drop_append,hdrop,hlen,
      Nat.sub_self,List.drop_zero,List.nil_append]
    rfl
  have H := orderedSteps_drop_cutMass (clockSteps as inc) (clockSteps_ordered ho inc) low
  rw [htail] at H
  exact H

theorem actual_original_prefix_shared_exterior_layer_sq_le (n : ℕ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ)
    (low : ℕ) (hlow : low≤as.length)
    (A E : ReplicaTree (FeatureIndex n) (Spin n) (originalBoundaryTailSteps n as q low))
    {v z : ℝ}
    (hav : physicalCutMass 0 (clockSteps as
      (cumulativeIncrements (q 0) (fun k=>q (k+1)))) low≤v)
    (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→Spin n→ℝ) :
    (∫ x,actualSharedExteriorLayer A E (uniformWeight n) (finiteFeature n)
      (physicalCutMass 0 (clockSteps as (cumulativeIncrements (q 0) (fun k=>q (k+1)))) low)
      v z P F x ∂originalBoundaryPrefixLaw n as q low)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*
        (∫ x,actualSharedExteriorOldMoment A E (uniformWeight n) (finiteFeature n) P x
          ∂originalBoundaryPrefixLaw n as q low)*
        (∫ x,actualSharedExteriorNewMoment E (uniformWeight n) (finiteFeature n) F x
          ∂originalBoundaryPrefixLaw n as q low) := by
  haveI := originalBoundaryPrefixLaw_probability n as ho q low hlow
  exact actual_incoming_law_shared_exterior_layer_sq_le (uniformWeight_pos n) (finiteFeature n)
    A E (original_boundary_tail_ordered n as ho q low hlow) hav hvz hz P F _

theorem actual_original_prefix_retained_exterior_layer_sq_le (n : ℕ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ)
    (low : ℕ) (hlow : low≤as.length)
    (pre steps : List (GaussianStep (FeatureIndex n)))
    (hfull : pre++steps=originalBoundaryTailSteps n as q low)
    (A : ReplicaTree (FeatureIndex n) (Spin n) steps)
    (E : ReplicaTree (FeatureIndex n) (Spin n) (pre++steps))
    {v z : ℝ} (hp : ∀ st∈pre,st.1≤v)
    (hav : physicalCutMass 0 (clockSteps as
      (cumulativeIncrements (q 0) (fun k=>q (k+1)))) low≤v)
    (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→Spin n→ℝ) :
    (∫ x,actualInheritedExteriorLayer pre A E (uniformWeight n) (finiteFeature n)
      (physicalCutMass 0 (clockSteps as (cumulativeIncrements (q 0) (fun k=>q (k+1)))) low)
      v z P F x ∂originalBoundaryPrefixLaw n as q low)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*
        (∫ x,actualRetainedExteriorOldMoment pre A E (uniformWeight n) (finiteFeature n) P x
          ∂originalBoundaryPrefixLaw n as q low)*
        (∫ x,actualRetainedExteriorNewMoment pre E (uniformWeight n) (finiteFeature n) F x
          ∂originalBoundaryPrefixLaw n as q low) := by
  haveI := originalBoundaryPrefixLaw_probability n as ho q low hlow
  have horder := original_boundary_tail_ordered n as ho q low hlow
  rw [←hfull] at horder
  exact actual_incoming_law_retained_exterior_layer_sq_le (uniformWeight_pos n) (finiteFeature n)
    pre A E horder hp hav hvz hz P F _

structure ActualMixedBoundaryForest (n a : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b h : ℕ→ℝ) where
  α : Fin a→ℝ
  β : Fin a→ℝ
  i : Fin a→T.Slot
  j : Fin a→T.Slot
  k : Fin a→T.Slot
  distinctLeft : ∀ e,i e ≠ j e
  distinctRight : ∀ e,i e ≠ k e
  sameLow : ∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e)
  retainedHigh : ∀ e,j e ≠ k e → T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e)
  lowInGrid : ∀ e,T.splitIndex (i e) (j e) ≤ as.length
  rho : Fin a→ℝ
  rhoPos : ∀ e,0<rho e
  raw : ∀ e,nativeMixedBoundaryRawBudget n a as b h
    (T.splitIndex (i e) (j e)) (α e) (β e) ≤ (rho e)^(2*a)

def ActualMixedBoundaryForest.difference {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (σ : T.Assignment) : ℝ :=
  fullBoundaryAffineProduct n D.α D.β
      (fun e=>T.atSlot σ (D.j e)) (fun e=>T.atSlot σ (D.i e))-
    fullBoundaryAffineProduct n D.α D.β
      (fun e=>T.atSlot σ (D.k e)) (fun e=>T.atSlot σ (D.i e))

def ActualMixedBoundaryForest.product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (σ : T.Assignment) : ℝ :=
  fullBoundaryAffineProduct n D.α D.β
    (fun e=>T.atSlot σ (D.j e)) (fun e=>T.atSlot σ (D.i e))

theorem actual_affine_boundary_raw_budget_le (n a : ℕ) (ha : 0<a)
    (as : List PositiveMass) (b h : ℕ→ℝ) (low : ℕ)
    {α β natural Ca Cb Cd : ℝ} (hnat : 0<natural)
    (hCa : 0≤Ca) (hCb : 0≤Cb) (hCd : 0≤Cd)
    (hα : |α|≤Ca*natural) (hβ : |β|≤Cb)
    (hraw : finitePhysicalDeletedRawBudget n a as b h low≤(Cd*natural)^(2*a)) :
    nativeMixedBoundaryRawBudget n a as b h low α β≤
      (2*(Ca+Cb*Cd+1)*natural)^(2*a) := by
  let C:=Ca+Cb*Cd+1
  have hC : 0≤C := by dsimp [C];positivity
  have hα' : |α|≤C*natural := hα.trans
    (mul_le_mul_of_nonneg_right (by dsimp [C];nlinarith) hnat.le)
  have hβraw : |β|^(2*a)*finitePhysicalDeletedRawBudget n a as b h low≤
      (C*natural)^(2*a) := by
    calc
      _ ≤ |β|^(2*a)*(Cd*natural)^(2*a) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ Cb^(2*a)*(Cd*natural)^(2*a) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hβ _) (by positivity)
      _ = (Cb*Cd*natural)^(2*a) := by simp only [mul_pow];ring
      _ ≤ (C*natural)^(2*a) := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right (by dsimp [C];nlinarith) hnat.le) _
  unfold nativeMixedBoundaryRawBudget
  calc
    _ ≤ (2:ℝ)^(2*a-1)*((C*natural)^(2*a)+(C*natural)^(2*a)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (pow_le_pow_left₀ (abs_nonneg _) hα' _) hβraw) (by positivity)
    _ = (2:ℝ)^(2*a)*(C*natural)^(2*a) := by
      conv_rhs =>
        arg 1
        rw [show 2*a=(2*a-1)+1 by omega,pow_succ]
      ring
    _ = _ := by dsimp only [C];simp only [mul_pow];ring

def ActualMixedBoundaryForest.withNaturalScales {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (ha : 0<a)
    (natural : Fin a→ℝ) (hnat : ∀ e,0<natural e)
    (Ca Cb Cd : ℝ) (hCa : 0≤Ca) (hCb : 0≤Cb) (hCd : 0≤Cd)
    (hα : ∀ e,|D.α e|≤Ca*natural e) (hβ : ∀ e,|D.β e|≤Cb)
    (hraw : ∀ e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (D.i e) (D.j e))≤(Cd*natural e)^(2*a)) :
    ActualMixedBoundaryForest n a T b h :=
  { D with
    rho := fun e=>2*(Ca+Cb*Cd+1)*natural e
    rhoPos := fun e=>by have H:=hnat e;positivity
    raw := fun e=>actual_affine_boundary_raw_budget_le n a ha as b h _ (hnat e)
      hCa hCb hCd (hα e) (hβ e) (hraw e) }

theorem actual_natural_boundary_forest_scale_product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (ha : 0<a)
    (natural : Fin a→ℝ) (hnat : ∀ e,0<natural e)
    (Ca Cb Cd : ℝ) (hCa : 0≤Ca) (hCb : 0≤Cb) (hCd : 0≤Cd)
    (hα : ∀ e,|D.α e|≤Ca*natural e) (hβ : ∀ e,|D.β e|≤Cb)
    (hraw : ∀ e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (D.i e) (D.j e))≤(Cd*natural e)^(2*a)) :
    (∏ e,(D.withNaturalScales ha natural hnat Ca Cb Cd hCa hCb hCd hα hβ hraw).rho e)=
      (2*(Ca+Cb*Cd+1))^a*(∏ e,natural e) := by
  simp only [ActualMixedBoundaryForest.withNaturalScales,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]

def ActualMixedBoundaryForest.cloneAt {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (s : T.Slot) (cut : ℕ)
    (hout : ∀ e,T.splitIndex s (D.i e)<cut) :
    ActualMixedBoundaryForest n a (ClockTree.nativeCloneBlockAtSlot T s cut).tree b h where
  α := D.α
  β := D.β
  i := fun e=>(ClockTree.nativeCloneBlockAtSlot T s cut).oldEmbed (D.i e)
  j := fun e=>(ClockTree.nativeCloneBlockAtSlot T s cut).oldEmbed (D.j e)
  k := fun e=>(ClockTree.nativeCloneBlockAtSlot T s cut).newEmbed (D.j e)
  distinctLeft := by
    intro e H
    exact D.distinctLeft e ((ClockTree.nativeCloneBlockAtSlot_embed_injective T s cut).1 H)
  distinctRight := by
    intro e H
    rw [ClockTree.nativeCloneBlockAtSlot_exterior_shared T s cut (D.i e) (hout e)] at H
    exact D.distinctLeft e ((ClockTree.nativeCloneBlockAtSlot_embed_injective T s cut).2 H)
  sameLow := by
    intro e
    by_cases hin : cut≤T.splitIndex s (D.j e)
    · have H := ClockTree.nativeCloneBlockAtSlot_boundary_geometry T s (D.j e) (D.i e)
        cut hin (hout e)
      exact H.2.1.trans H.2.2.1.symm
    · rw [ClockTree.nativeCloneBlockAtSlot_exterior_shared T s cut (D.j e) (by omega)]
  retainedHigh := by
    intro e he
    by_cases hin : cut≤T.splitIndex s (D.j e)
    · have H := ClockTree.nativeCloneBlockAtSlot_boundary_geometry T s (D.j e) (D.i e)
        cut hin (hout e)
      rw [H.2.1,H.2.2.2]
      exact ClockTree.nativeCloneBlockAtSlot_exterior_low_lt T s (D.j e) (D.i e)
        cut hin (hout e)
    · exact (he (ClockTree.nativeCloneBlockAtSlot_exterior_shared T s cut (D.j e)
        (by omega))).elim
  lowInGrid := fun e=>(ClockTree.nativeCloneBlockAtSlot T s cut).tree.splitIndex_le_clockLength _ _
  rho := D.rho
  rhoPos := D.rhoPos
  raw := by
    intro e
    rw [(ClockTree.nativeCloneBlockAtSlot_within_copy_splits T s cut (D.i e) (D.j e)).1]
    exact D.raw e

theorem actual_cloned_boundary_forest_difference_eq {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (s : T.Slot) (cut : ℕ)
    (hout : ∀ e,T.splitIndex s (D.i e)<cut)
    (σ : (ClockTree.nativeCloneBlockAtSlot T s cut).tree.Assignment) :
    (D.cloneAt s cut hout).difference σ=
      D.product ((ClockTree.nativeCloneBlockAtSlot T s cut).oldRestrict σ)-
        D.product ((ClockTree.nativeCloneBlockAtSlot T s cut).newRestrict σ) := by
  let p:=ClockTree.nativeCloneBlockAtSlot T s cut
  have hanchor : (fun e=>p.tree.atSlot σ (p.newEmbed (D.i e)))=
      fun e=>p.tree.atSlot σ (p.oldEmbed (D.i e)) := by
    funext e
    rw [ClockTree.nativeCloneBlockAtSlot_exterior_shared T s cut (D.i e) (hout e)]
  change fullBoundaryAffineProduct n D.α D.β
      (fun e=>p.tree.atSlot σ (p.oldEmbed (D.j e)))
      (fun e=>p.tree.atSlot σ (p.oldEmbed (D.i e)))-
    fullBoundaryAffineProduct n D.α D.β
      (fun e=>p.tree.atSlot σ (p.newEmbed (D.j e)))
      (fun e=>p.tree.atSlot σ (p.oldEmbed (D.i e)))=
        D.product (p.oldRestrict σ)-D.product (p.newRestrict σ)
  simp only [ActualMixedBoundaryForest.product,p.old_at,p.new_at]
  rw [hanchor]

theorem actual_original_cloned_boundary_forest_moment_eq (n U a : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (t : ℝ) (D : ActualMixedBoundaryForest n a T b h)
    (s : T.Slot) (cut : ℕ) (hout : ∀ e,T.splitIndex s (D.i e)<cut) :
    zeroContinuation (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
      (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T s cut
        (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
          (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
        (fun σ τ=>(D.product σ-D.product τ)^2)) 0=
    (ClockTree.nativeCloneBlockAtSlot T s cut).tree.disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>(D.cloneAt s cut hout).difference σ^2) 0 := by
  have H := ClockTree.nativeRetainedCloneCut_disorderLaw (fullWeight_pos n) (fullFeature n)
    T ho s cut 0 (finitePhysicalCavityVariance n U as b h t)
    (fun σ τ=>(D.product σ-D.product τ)^2) 0
  simp only [Pi.zero_apply,sub_zero] at H
  rw [H]
  congr 1
  funext σ
  rw [actual_cloned_boundary_forest_difference_eq D s cut hout σ]

theorem eventually_actual_mixed_forest_square_from_schedules
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0 ≤ b z) → (∀ z,0 ≤ h z) →
    ∀ (t : ℝ),t ∈ Icc (0:ℝ) 1 →
    ∀ (D : ActualMixedBoundaryForest n a T b h) (r W xi : ℝ) (v : Fin a→ℝ),
      0<r → 0<W → 0<xi → (∀ e,0<v e) →
      ((n+1:ℕ) : ℝ)^(-(1:ℝ)/6+m) ≤ r →
      (∀ e,D.j e ≠ D.k e → OriginalBoundaryPrimitiveInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (D.i e) (D.j e))
        (T.splitIndex (D.j e) (D.k e)) B A Cq H₀ c₀ r W (v e)) →
      (∀ e,D.j e ≠ D.k e → |D.β e|^(2*a)*nativeBoundaryRowFactor n T b h*
        (2:ℝ)^(2*a-1)*(nativeBoundaryCompletionFactor n T b*
          (2*((n+1:ℕ) : ℝ)^(-delta)*savedExteriorScale r W (v e))^(2*a)+
          (2/(n+1:ℕ):ℝ)^(2*a)) ≤ (xi*D.rho e)^(2*a)) →
      T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t)
        (fun σ=>D.difference σ^2) 0 ≤ ((a:ℝ)*xi*(∏ e,D.rho e))^2 := by
  filter_upwards [eventually_actual_full_mixed_forest_from_primitives a dc dq ha
    B A Cq H₀ c₀ hA hCq hH₀ hc₀ hgap] with n hn
  intro U as T ho b h hb hh hb0 hh0 t ht D r W xi v hr hW hxi hv hscale I hdom
  exact hn U as T ho b h hb hh hb0 hh0 t ht D.α D.β D.i D.j D.k
    D.distinctLeft D.distinctRight D.sameLow D.retainedHigh D.lowInGrid
    D.rho r W xi v D.rhoPos hr hW hxi hv hscale D.raw I hdom

theorem actual_full_two_forest_expectation_sq_le (n U a d : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (t : ℝ) (P : ActualMixedBoundaryForest n a T b h)
    (F : ActualMixedBoundaryForest n d T b h) (sP sF : ℝ)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>P.difference σ^2) 0 ≤ sP^2)
    (hF : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>F.difference σ^2) 0 ≤ sF^2) :
    (T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>P.difference σ*F.difference σ) 0)^2 ≤ (sP*sF)^2 := by
  have hCS := T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavityVariance n U as b h t) P.difference F.difference 0
  have hFn : 0 ≤ T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>F.difference σ^2) 0 := by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg
      ((T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0
        (finitePhysicalCavityVariance n U as b h t) 0).1 σ) (sq_nonneg _)
  calc
    _ ≤ _ := hCS
    _ ≤ sP^2*T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t) (fun σ=>F.difference σ^2) 0 :=
      mul_le_mul_of_nonneg_right hP hFn
    _ ≤ sP^2*sF^2 := mul_le_mul_of_nonneg_left hF (sq_nonneg _)
    _ = _ := by ring

structure ActualMixedBoundaryForest.PrimitiveRates {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {b h : ℕ→ℝ}
    (D : ActualMixedBoundaryForest n a T b h) (dc dq : ℕ)
    (B A Cq H₀ c₀ r W xi delta : ℝ) (v : Fin a→ℝ) where
  clocks : ∀ e,D.j e ≠ D.k e → OriginalBoundaryPrimitiveInput (n+1) (a-1) dc dq as
    (physicalCompletedClock (n+1) b h) (T.splitIndex (D.i e) (D.j e))
    (T.splitIndex (D.j e) (D.k e)) B A Cq H₀ c₀ r W (v e)
  scalarDomination : ∀ e,D.j e ≠ D.k e → |D.β e|^(2*a)*nativeBoundaryRowFactor n T b h*
    (2:ℝ)^(2*a-1)*(nativeBoundaryCompletionFactor n T b*
      (2*((n+1:ℕ) : ℝ)^(-delta)*savedExteriorScale r W (v e))^(2*a)+
      (2/(n+1:ℕ):ℝ)^(2*a)) ≤ (xi*D.rho e)^(2*a)

theorem eventually_actual_full_two_forest_from_schedules
    (a d dc dq : ℕ) (ha : 0<a) (hd : 0<d) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0 ≤ b z) → (∀ z,0 ≤ h z) →
    ∀ (t : ℝ),t ∈ Icc (0:ℝ) 1 →
    ∀ (P : ActualMixedBoundaryForest n a T b h) (F : ActualMixedBoundaryForest n d T b h)
      (r W xiP xiF : ℝ) (vP : Fin a→ℝ) (vF : Fin d→ℝ),
      0<r → 0<W → 0<xiP → 0<xiF → (∀ e,0<vP e) → (∀ e,0<vF e) →
      ((n+1:ℕ) : ℝ)^(-(1:ℝ)/6+m) ≤ r →
      P.PrimitiveRates dc dq B A Cq H₀ c₀ r W xiP delta vP →
      F.PrimitiveRates dc dq B A Cq H₀ c₀ r W xiF delta vF →
      |T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t)
        (fun σ=>P.difference σ*F.difference σ) 0| ≤
          ((a:ℝ)*xiP*(∏ e,P.rho e))*((d:ℝ)*xiF*(∏ e,F.rho e)) := by
  filter_upwards [eventually_actual_mixed_forest_square_from_schedules a dc dq ha
    B A Cq H₀ c₀ hA hCq hH₀ hc₀ hgap,
    eventually_actual_mixed_forest_square_from_schedules d dc dq hd
    B A Cq H₀ c₀ hA hCq hH₀ hc₀ hgap] with n hnP hnF
  intro U as T ho b h hb hh hb0 hh0 t ht P F r W xiP xiF vP vF
    hr hW hxiP hxiF hvP hvF hscale hP hF
  have HP := hnP U as T ho b h hb hh hb0 hh0 t ht P r W xiP vP
    hr hW hxiP hvP hscale hP.clocks hP.scalarDomination
  have HF := hnF U as T ho b h hb hh hb0 hh0 t ht F r W xiF vF
    hr hW hxiF hvF hscale hF.clocks hF.scalarDomination
  have H := actual_full_two_forest_expectation_sq_le n U a d T ho b h t P F _ _ HP HF
  have hsP : 0 ≤ (a:ℝ)*xiP*(∏ e,P.rho e) := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hxiP.le) (Finset.prod_nonneg fun e _=>(P.rhoPos e).le)
  have hsF : 0 ≤ (d:ℝ)*xiF*(∏ e,F.rho e) := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hxiF.le) (Finset.prod_nonneg fun e _=>(F.rhoPos e).le)
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hsP hsF)).mp (by simpa only [sq_abs] using H)

structure FullOriginalBoundaryScheduleInput (n k dc dq : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ) (B A Cq H₀ c₀ r W v : ℝ) where
  center : ℕ
  centerLow : low≤center
  centerHigh : center≤high
  D₀ : ℝ
  xs : ℝ
  H : ℝ
  Dpos : 0<D₀
  xspos : 0<xs
  Hnonneg : 0≤H
  cs : List (ℝ×ℕ)
  anchor : Fin cs.length→ℝ
  duration : Fin cs.length→ℝ
  last : lastLayerCut cs center=
    (clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1)))).length+1
  ends : ∀ j : Fin cs.length,cutPredecessor cs center j≤(cs.get j).2 ∧
    (cs.get j).2≤(clockSteps as (cumulativeIncrements (q 0) (fun z=>q (z+1)))).length+1
  clocks : ∀ j,0<anchor j ∧ D₀≤duration j ∧ duration j≤B ∧
    PhysicalProjectionClock n (clockSteps as (cumulativeIncrements (q 0) (fun z=>q (z+1))))
      low (cutPredecessor cs center j) (cs.get j).2 (anchor j) (duration j)
  scales : ∀ i j,i≤j.succ → xs+physicalCutMass 0
    (clockSteps as (cumulativeIncrements (q 0) (fun z=>q (z+1))))
      (overlapComponentEnd cs center i)≤H*(anchor j)^2
  count : ((physicalOverlapResidualPairs cs).card:ℝ)^2≤A*(Real.log (n:ℝ))^dc
  fullRaw : (physicalRawRatio n (k+1)
    (clockSteps as (cumulativeIncrements (q 0) (fun z=>q (z+1)))) 0 xs
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))) id measurable_id)^2≤
      Cq*(Real.log (n:ℝ))^dq
  highAnchor : H≤H₀/v
  innovation : c₀*W^3/Real.log (n:ℝ)≤D₀

theorem eventually_original_boundary_from_full_schedule_input
    (k dc dq : ℕ) (B A Cq H₀ c₀ : ℝ)
    (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as : List PositiveMass) (ho : MassOrdered 0 as)
      (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ),high≤as.length →
    ∀ (r W v : ℝ),0<r → 0<W → 0<v → (n:ℝ)^(-(1:ℝ)/6+m)≤r →
      FullOriginalBoundaryScheduleInput n k dc dq as q low high B A Cq H₀ c₀ r W v →
      originalBoundaryResamplingMoment n (k+1) as q low high≤
        (2*(n:ℝ)^(-delta)*savedExteriorScale r W v)^(2*(k+1)) := by
  filter_upwards [OAI.SKFluctuations.eventually_original_boundary_resampling_from_full_schedule
    k dc dq B A Cq H₀ c₀ hA hCq hH₀ hc₀ hgap] with n hn
  intro as ho q low high hhigh r W v hr hW hv hcrit I
  exact hn as ho q low high I.center I.centerLow I.centerHigh hhigh I.D₀ I.xs I.H
    r W v I.Dpos I.xspos I.Hnonneg hr hW hv hcrit I.cs I.anchor I.duration
    I.last I.ends I.clocks I.scales I.count I.fullRaw I.highAnchor I.innovation

theorem eventually_actual_mixed_forest_from_bounded_rows
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ Cb Cr Cc c BW : ℝ)
    (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    (hCb : 0≤Cb) (hCr : 0≤Cr) (hCc : 0≤Cc) (hc : 0<c) (hBW : 0<BW)
    {m delta : ℝ} (hgap : 2*delta<6*m) (hsitegap : delta<1/2+3*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0≤b z) → (∀ z,0≤h z) →
    ∀ (t : ℝ),t∈Icc (0:ℝ) 1 →
    ∀ (D : ActualMixedBoundaryForest n a T b h) (r W v scale : ℝ),
      0<r → 0<W → 0<v → W≤BW → v≤1 → 0<scale →
      ((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m)≤r →
      (∀ e,|D.β e|≤Cb) → nativeBoundaryRowFactor n T b h≤Cr →
      nativeBoundaryCompletionFactor n T b≤Cc → (∀ e,c*scale≤D.rho e) →
      (∀ e,D.j e ≠ D.k e → FullOriginalBoundaryScheduleInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (D.i e) (D.j e))
        (T.splitIndex (D.j e) (D.k e)) B A Cq H₀ c₀ r W v) →
      T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t) (fun σ=>D.difference σ^2) 0 ≤
        ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
          ((n+1:ℕ):ℝ)^(-delta)*savedExteriorScale r W v/scale)*(∏ e,D.rho e))^2 := by
  have HE := (tendsto_add_atTop_nat 1).eventually
    (eventually_omitted_site_le_saved_boundary hsitegap hBW)
  have HF := (tendsto_add_atTop_nat 1).eventually
    (eventually_original_boundary_from_full_schedule_input (a-1) dc dq
      B A Cq H₀ c₀ hA hCq hH₀ hc₀ hgap)
  filter_upwards [HF,HE] with n hn hsite
  intro U as T ho b h hb hh hb0 hh0 t ht D r W v scale
    hr hW hv hWB hv1 hscale hcrit hβ hrow hcompletion hrho I
  let s := ((n+1:ℕ):ℝ)^(-delta)*savedExteriorScale r W v
  have hs : 0<s := mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (div_pos (pow_pos hr _) (Real.sqrt_pos.2 (by positivity)))
  have hconst : 0<actualBoundaryScalarConstant Cb Cr Cc c := by
    unfold actualBoundaryScalarConstant
    positivity
  have hsite' : 2/(n+1:ℕ) ≤ 2*s := by
    have H := mul_le_mul_of_nonneg_left (hsite r W v hr hW hv hWB hv1 hcrit)
      (by norm_num : (0:ℝ)≤2)
    simpa only [mul_one_div] using H
  have hdom (e : Fin a) (_he : D.j e ≠ D.k e) :=
    actual_boundary_scalar_budget_le a ha hCb hCr hCc hc hscale (hrho e) hs.le
      (hβ e) (by unfold nativeBoundaryRowFactor; positivity) hrow
      (by unfold nativeBoundaryCompletionFactor; positivity) hcompletion
      (by positivity : (0:ℝ)≤2/(n+1:ℕ)) hsite'
  rw [mul_assoc (actualBoundaryScalarConstant Cb Cr Cc c)
    (((n+1:ℕ):ℝ)^(-delta)) (savedExteriorScale r W v)]
  apply actual_full_mixed_forest_from_physical_resampling n U T ho b h hb hh hb0 hh0 ht
    ha D.α D.β D.i D.j D.k D.distinctLeft D.distinctRight D.sameLow D.retainedHigh D.lowInGrid
    D.rho D.rhoPos (div_pos (mul_pos hconst hs) hscale) D.raw
  intro e he
  have H := hn as ho (physicalCompletedClock (n+1) b h)
    (T.splitIndex (D.i e) (D.j e)) (T.splitIndex (D.j e) (D.k e))
    (T.splitIndex_le_clockLength _ _) r W v hr hW hv hcrit (I e he)
  have ha' : a-1+1=a := by omega
  rw [ha'] at H
  have H' : originalBoundaryResamplingMoment (n+1) a as (physicalCompletedClock (n+1) b h)
      (T.splitIndex (D.i e) (D.j e)) (T.splitIndex (D.j e) (D.k e))≤(2*s)^(2*a) := by
    simpa only [s,mul_assoc] using H
  apply le_trans _ (by simpa only [s,mul_assoc] using hdom e he)
  unfold nativeMixedBoundaryReplacementBudget
  have hcomp0 : 0≤nativeBoundaryCompletionFactor n T b := by
    unfold nativeBoundaryCompletionFactor
    positivity
  have hcoef0 : 0≤|D.β e|^(2*a)*nativeBoundaryRowFactor n T b h*(2:ℝ)^(2*a-1) := by
    unfold nativeBoundaryRowFactor
    positivity
  have HM := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left H' hcomp0) (le_refl ((2/(n+1:ℕ):ℝ)^(2*a)))) hcoef0
  simpa only [s,mul_assoc] using HM

theorem eventually_actual_original_boundary_clone_from_bounded_rows
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ Cb Cr Cc c BW : ℝ)
    (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    (hCb : 0≤Cb) (hCr : 0≤Cr) (hCc : 0≤Cc) (hc : 0<c) (hBW : 0<BW)
    {m delta : ℝ} (hgap : 2*delta<6*m) (hsitegap : delta<1/2+3*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0≤b z) → (∀ z,0≤h z) →
    ∀ (t : ℝ),t∈Icc (0:ℝ) 1 →
    ∀ (D : ActualMixedBoundaryForest n a T b h) (s : T.Slot) (cut : ℕ),
      (∀ e,T.splitIndex s (D.i e)<cut) →
    ∀ (r W v scale : ℝ),0<r → 0<W → 0<v → W≤BW → v≤1 → 0<scale →
      ((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m)≤r → (∀ e,|D.β e|≤Cb) →
      nativeBoundaryRowFactor n (ClockTree.nativeCloneBlockAtSlot T s cut).tree b h≤Cr →
      nativeBoundaryCompletionFactor n (ClockTree.nativeCloneBlockAtSlot T s cut).tree b≤Cc →
      (∀ e,c*scale≤D.rho e) →
      (∀ e,cut≤T.splitIndex s (D.j e) → FullOriginalBoundaryScheduleInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (D.i e) (D.j e))
        cut B A Cq H₀ c₀ r W v) →
      zeroContinuation (Measure.pi fun i=>gaussianReal 0
        (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
        (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T s cut
          (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
            (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
          (fun σ τ=>(D.product σ-D.product τ)^2)) 0 ≤
        ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
          ((n+1:ℕ):ℝ)^(-delta)*savedExteriorScale r W v/scale)*(∏ e,D.rho e))^2 := by
  filter_upwards [eventually_actual_mixed_forest_from_bounded_rows a dc dq ha
    B A Cq H₀ c₀ Cb Cr Cc c BW hA hCq hH₀ hc₀ hCb hCr hCc hc hBW hgap hsitegap]
    with n hn
  intro U as T ho b h hb hh hb0 hh0 t ht D target cut hout r W v scale
    hr hW hv hWB hv1 hscale hcrit hβ hrow hcompletion hrho I
  let p:=ClockTree.nativeCloneBlockAtSlot T target cut
  let P:=D.cloneAt target cut hout
  have hI : ∀ e,P.j e≠P.k e → FullOriginalBoundaryScheduleInput (n+1) (a-1) dc dq as
      (physicalCompletedClock (n+1) b h) (p.tree.splitIndex (P.i e) (P.j e))
      (p.tree.splitIndex (P.j e) (P.k e)) B A Cq H₀ c₀ r W v := by
    intro e he
    have hin : cut≤T.splitIndex target (D.j e) := by
      by_contra H
      exact he (ClockTree.nativeCloneBlockAtSlot_exterior_shared T target cut (D.j e) (by omega))
    have HG := ClockTree.nativeCloneBlockAtSlot_boundary_geometry T target
      (D.j e) (D.i e) cut hin (hout e)
    change FullOriginalBoundaryScheduleInput (n+1) (a-1) dc dq as
      (physicalCompletedClock (n+1) b h)
      (p.tree.splitIndex (p.oldEmbed (D.i e)) (p.oldEmbed (D.j e)))
      (p.tree.splitIndex (p.oldEmbed (D.j e)) (p.newEmbed (D.j e))) B A Cq H₀ c₀ r W v
    rw [HG.2.1,HG.2.2.2]
    exact I e hin
  have H := hn U as p.tree ho b h hb hh hb0 hh0 t ht P r W v scale
    hr hW hv hWB hv1 hscale hcrit hβ hrow hcompletion hrho hI
  rw [actual_original_cloned_boundary_forest_moment_eq n U a T ho b h t D target cut hout]
  exact H

theorem eventually_actual_minimum_boundary_clone_from_bounded_rows
    (a : ℕ) (ha : 0 < a) (Bclock ce Rmacro F exponent Cb Cr Cc c BW : ℝ)
    {m delta eta cl cu Az C0 Ct D0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m) (hgap : 2*eta  <  6*m)
    (hsitegap : eta < 1/2+3*m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hce : 0 < ce) (hmacro : 0 < Rmacro)
    (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hCb : 0 ≤ Cb) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc) (hc : 0 < c) (hBW : 0 < BW) :
    ∀ᶠ n : ℕ in atTop,
    ∀ M : LaplaceWindowFormalization.NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D0 Bclock,
    ∀ (u : PositiveMass),u.val ≤ 1  →
    ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1)  →
    ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
      ∀ᶠ j : ℕ in atTop,
        let as:=finiteCutMasses us j
        let steps:=sampleClockSteps (completedPathClock (n+1) M.bf M.hf) 0 as
        let Q:=stepClockValues (fun i=>(completedPathClock (n+1) M.bf M.hf 0 i:ℝ)) steps
        ∀ (b h : ℕ → ℝ),Q = physicalCompletedClock (n+1) b h  →
          Monotone b  →  Monotone h  →  (∀z,0 ≤ b z)  →  (∀z,0 ≤ h z)  →
        ∀ (U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),t∈Icc (0:ℝ) 1  →
        ∀ (G : ActualMixedBoundaryForest n a T b h) (target : T.Slot) (cut : ℕ),
          (∀e,T.splitIndex target (G.i e) < cut)  →  cut ≤ as.length  →
        ∀ (s W r scale : ℝ),0 < s  →  0 < W  →  0 < r  →  0 < scale  →
          W ≤ s  →  M.xs ≤ s  →  M.z ≤ s/2  →  2*s ≤ Rmacro  →  W ≤ BW  →
          ((n+1:ℕ):ℝ)^(-exponent) ≤ s  →  ((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m) ≤ r  →
          ce*W^2 ≤ LaplaceWindowFormalization.laplaceComparisonStrength M.context.d M.lam W  →
          0 < partitionPoint 0 as cut  →  partitionPoint 0 as cut ≤ 1  →
          M.R (partitionPoint 0 as cut) = 4*s  →
          (∀e,cut ≤ T.splitIndex target (G.j e)  →
            M.R (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))) ≤ s/2)  →
          (∀e,|G.β e| ≤ Cb)  →
          nativeBoundaryRowFactor n (ClockTree.nativeCloneBlockAtSlot T target cut).tree b h ≤ Cr  →
          nativeBoundaryCompletionFactor n (ClockTree.nativeCloneBlockAtSlot T target cut).tree b ≤ Cc  →
          (∀e,c*scale ≤ G.rho e)  →
          zeroContinuation (Measure.pi fun i=>gaussianReal 0
            (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
            (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
              (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
                (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
              (fun σ τ=>(G.product σ-G.product τ)^2)) 0  ≤
            ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
              ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 as cut)/scale)*
              (∏e,G.rho e))^2 := by
  have HS := (tendsto_add_atTop_nat 1).eventually
    (LaplaceWindowFormalization.eventually_native_minimum_original_boundary_resampling
      (D:=D0) (a-1) Bclock ce Rmacro F exponent hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hce hmacro hRhalf hFmass hFradius)
  have HE := (tendsto_add_atTop_nat 1).eventually
    (eventually_omitted_site_le_saved_boundary hsitegap hBW)
  filter_upwards [HS,HE] with n hn hsite
  intro M u hu extra hextra
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hn M u hu extra hextra
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  intro b h hQ hb hh hb0 hh0 U T t ht G target cut hout hcut
    s W r scale hs hW hr hscale hWs hxss hzs hsR hWB hslow hcrit hstrength
    hv hv1 hhigh hlow hβ hrow hcompletion hrho
  let as:=finiteCutMasses us j
  let p:=ClockTree.nativeCloneBlockAtSlot T target cut
  let P:=G.cloneAt target cut hout
  let v:=partitionPoint 0 as cut
  let save:=((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W v
  have hsave : 0 < save := mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (div_pos (pow_pos hr _) (Real.sqrt_pos.2 (by positivity)))
  have hconst : 0 < actualBoundaryScalarConstant Cb Cr Cc c := by
    unfold actualBoundaryScalarConstant
    positivity
  have hsite' : 2/(n+1:ℕ) ≤ 2*save := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (hsite r W v hr hW hv hWB hv1 hcrit) (by norm_num : (0:ℝ) ≤ 2)
  have hmoment : p.tree.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t) (fun σ=>P.difference σ^2) 0 ≤
      ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*save/scale)*(∏e,G.rho e))^2 := by
    apply actual_full_mixed_forest_from_physical_resampling n U p.tree
      (finiteCutMasses_ordered us hus j) b h hb hh hb0 hh0 ht ha
      P.α P.β P.i P.j P.k P.distinctLeft P.distinctRight P.sameLow P.retainedHigh P.lowInGrid
      P.rho P.rhoPos (div_pos (mul_pos hconst hsave) hscale) P.raw
    intro e he
    have hin : cut ≤ T.splitIndex target (G.j e) := by
      by_contra H
      exact he (ClockTree.nativeCloneBlockAtSlot_exterior_shared T target cut (G.j e) (by omega))
    have HG := ClockTree.nativeCloneBlockAtSlot_boundary_geometry T target
      (G.j e) (G.i e) cut hin (hout e)
    have H := hj s W r (T.splitIndex (G.i e) (G.j e)) cut hs hW hr hWs hxss hzs hsR
      hslow hcrit hstrength hcut (hlow e hin) hhigh
    rw [hQ] at H
    have ha' : a-1+1 = a := by omega
    rw [ha'] at H
    have H' : originalBoundaryResamplingMoment (n+1) a as (physicalCompletedClock (n+1) b h)
        (T.splitIndex (G.i e) (G.j e)) cut≤(2*save)^(2*a) := by
      simpa only [save,mul_assoc] using H
    have Hdom := actual_boundary_scalar_budget_le a ha hCb hCr hCc hc hscale (hrho e)
      hsave.le (hβ e) (by unfold nativeBoundaryRowFactor;positivity) hrow
      (by unfold nativeBoundaryCompletionFactor;positivity) hcompletion
      (by positivity : (0:ℝ) ≤ 2/(n+1:ℕ)) hsite'
    apply le_trans _ (by simpa only [save,mul_assoc,P,ActualMixedBoundaryForest.cloneAt] using Hdom)
    unfold nativeMixedBoundaryReplacementBudget
    change _*_*_*(_*originalBoundaryResamplingMoment (n+1) a as
      (physicalCompletedClock (n+1) b h)
      (p.tree.splitIndex (p.oldEmbed (G.i e)) (p.oldEmbed (G.j e)))
      (p.tree.splitIndex (p.oldEmbed (G.j e)) (p.newEmbed (G.j e)))+_) ≤ _
    rw [HG.2.1,HG.2.2.2]
    have hcomp0 : 0≤nativeBoundaryCompletionFactor n p.tree b := by
      unfold nativeBoundaryCompletionFactor
      positivity
    have hcoef0 : 0≤|G.β e|^(2*a)*nativeBoundaryRowFactor n p.tree b h*(2:ℝ)^(2*a-1) := by
      unfold nativeBoundaryRowFactor
      positivity
    have HM := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left H' hcomp0) (le_refl ((2/(n+1:ℕ):ℝ)^(2*a)))) hcoef0
    simpa only [save,mul_assoc,P,ActualMixedBoundaryForest.cloneAt] using HM
  rw [actual_original_cloned_boundary_forest_moment_eq n U a T
    (finiteCutMasses_ordered us hus j) b h t G target cut hout]
  simpa only [save,mul_assoc] using hmoment

end OAI.SKFluctuations.Cavity
