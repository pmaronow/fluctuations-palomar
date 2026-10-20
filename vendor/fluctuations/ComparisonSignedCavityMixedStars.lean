module

public import ComparisonSignedCavityGroupedContinuation

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeMixedBoundaryRawBudget (n l : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (j : ℕ) (α β : ℝ) : ℝ :=
  (2:ℝ)^(2*l-1)*(|α|^(2*l)+|β|^(2*l)*finitePhysicalDeletedRawBudget n l as b h j)

def nativeMixedBoundaryReplacementBudget (n l : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b h : ℕ→ℝ) (β : ℝ) (low high : ℕ) : ℝ :=
  |β|^(2*l)*nativeBoundaryRowFactor n T b h*(2:ℝ)^(2*l-1)*
    (nativeBoundaryCompletionFactor n T b*originalBoundaryResamplingMoment (n+1) l as
      (physicalCompletedClock (n+1) b h) low high+(2/(n+1:ℕ):ℝ)^(2*l))

theorem actual_full_mixed_pair_moment_le (n l U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    (j : ℕ) (hj : j ≤ as.length) (α β : ℝ) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).2
        (ClockTree.pairSpin as j σ).1|^(2*l)) 0 ≤
      nativeMixedBoundaryRawBudget n l as b h j α β := by
  have H := actual_low_row_moment_le n (2*l) (ClockTree.pairClock as j) ho 0
    (finitePhysicalCavityVariance n U as b h t) 0
    (ClockTree.pairRightSlot as j) (ClockTree.pairLeftSlot as j) β α 0 1
  simp_rw [low_row_covariance_centered n β α 0 1] at H
  simp only [ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,
    low_row_covariance_centered,abs_mul,abs_spinValue,mul_zero,add_zero,sub_zero,
    one_mul,abs_one,one_pow,fullBoundaryAffineFactor] at H ⊢
  apply H.trans
  have Hd := finitePhysicalDeleted_moment_le_raw n l U ho ht b h hb hh hb0 hh0 j hj
  have hsym (σ τ : Spin (n+1)) : deletedOverlap n σ τ=deletedOverlap n τ σ := by
    unfold deletedOverlap; congr 1; apply Finset.sum_congr rfl; intro z _; ring
  simp_rw [hsym (joinSpin (ClockTree.pairSpin as j _).2)
    (joinSpin (ClockTree.pairSpin as j _).1)]
  unfold nativeMixedBoundaryRawBudget
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left Hd (by positivity))) (by positivity)

theorem actual_full_mixed_edge_resampling_le (n l U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (β : ℝ) (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|β*(deletedOverlap n (joinSpin (T.atSlot σ j))
        (joinSpin (T.atSlot σ i))-deletedOverlap n (joinSpin (T.atSlot σ k))
          (joinSpin (T.atSlot σ i)))|^(2*l)) 0 ≤
      nativeMixedBoundaryReplacementBudget n l T b h β (T.splitIndex i j) (T.splitIndex j k) := by
  let K := finitePhysicalMixedClock (n+1) as b h
  let R := T.relabelSpin (spinEquiv n)
  let i' := T.relabelSlot (spinEquiv n) i
  let j' := T.relabelSlot (spinEquiv n) j
  let k' := T.relabelSlot (spinEquiv n) k
  have hjk' : j' ≠ k' := fun H=>hjk ((T.relabelSlot (spinEquiv n)).injective H)
  have hlo' : R.splitIndex i' j'=R.splitIndex i' k' := by
    simpa only [R,i',j',k',ClockTree.splitIndex_relabel] using hlow
  have hgap' : R.splitIndex i' j'<R.splitIndex j' k' := by
    simpa only [R,i',j',k',ClockTree.splitIndex_relabel] using hgap
  have H := cavityPath_boundary_difference_le_physical n (2*l) U T ho
    (by norm_num : (0:ℝ) ∈ Icc 0 1) ht hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0)
    hb0 hh0 (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) i j k
  dsimp only at H
  have hsym (σ τ : Spin (n+1)) : orderedOverlap (n+1) σ τ=orderedOverlap (n+1) τ σ := by
    unfold orderedOverlap; congr 1; apply Finset.sum_congr rfl; intro z _; ring
  have hobs : (fun σ:R.Assignment=>
      |orderedOverlap (n+1) (R.atSlot σ j') (R.atSlot σ i')-
        orderedOverlap (n+1) (R.atSlot σ k') (R.atSlot σ i')|^(2*l)) =
      fun σ=>|orderedOverlap (n+1) (R.atSlot σ i') (R.atSlot σ j')-
        orderedOverlap (n+1) (R.atSlot σ i') (R.atSlot σ k')|^(2*l) := by
    funext σ
    rw [hsym (R.atSlot σ j') (R.atSlot σ i'),hsym (R.atSlot σ k') (R.atSlot σ i')]
  change T.disorderExpect _ _ _ _ _ _ ≤ _*_*(_*R.disorderExpect _ _ _ _ _ _+_) at H
  rw [hobs] at H
  rw [←original_boundary_resampling_eq_full_tree (n+1) l R ho
    (physicalCompletedClock (n+1) b h) i' j' k' hjk' hlo' hgap'] at H
  dsimp only [R,i',j',k'] at H
  simp only [ClockTree.splitIndex_relabel] at H
  have HM := mul_le_mul_of_nonneg_left H (pow_nonneg (abs_nonneg (β)) (2*l))
  have hq : cavityPath n U 0 t (fun z=>Sum.elim (fun _=>b z) (fun _=>h z)) b h K=
      finitePhysicalCavityVariance n U as b h t := by
    funext z c; rfl
  rw [hq] at HM
  have he : (fun σ=>|β*(deletedOverlap n (joinSpin (T.atSlot σ j))
      (joinSpin (T.atSlot σ i))-deletedOverlap n (joinSpin (T.atSlot σ k))
        (joinSpin (T.atSlot σ i)))|^(2*l)) =
      fun σ=>|β|^(2*l)*
        |deletedOverlap n (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
          deletedOverlap n (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^(2*l) := by
    funext σ; rw [abs_mul,mul_pow]
  rw [he,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  simpa only [nativeMixedBoundaryReplacementBudget,nativeBoundaryRowFactor,
    nativeBoundaryCompletionFactor,K,mul_assoc] using HM

theorem actual_full_mixed_polynomial_from_physical_resampling (n U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {a : ℕ} (ha : 0<a)
    (α β : Fin a→ℝ) (i j k : Fin a→T.Slot)
    (hij : ∀ e,i e ≠ j e) (hik : ∀ e,i e ≠ k e) (hjk : ∀ e,j e ≠ k e)
    (hlow : ∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e))
    (hgap : ∀ e,T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e))
    (hcut : ∀ e,T.splitIndex (i e) (j e) ≤ as.length)
    (rho : Fin a→ℝ) (hrho : ∀ e,0<rho e) {xi : ℝ} (hxi : 0<xi)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n a as b h
      (T.splitIndex (i e) (j e)) (α e) (β e) ≤ (rho e)^(2*a))
    (hphysical : ∀ e,nativeMixedBoundaryReplacementBudget n a T b h (β e)
      (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) ≤ (xi*rho e)^(2*a)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>(fullBoundaryAffineProduct n α β
        (fun e=>T.atSlot σ (j e)) (fun e=>T.atSlot σ (i e))-
        fullBoundaryAffineProduct n α β
        (fun e=>T.atSlot σ (k e)) (fun e=>T.atSlot σ (i e)))^2) 0 ≤
      ((a:ℝ)*xi*(∏ e,rho e))^2 := by
  let q := finitePhysicalCavityVariance n U as b h t
  let f := fun e σ=>fullBoundaryAffineFactor n (α e) (β e)
    (T.atSlot σ (j e)) (T.atSlot σ (i e))
  let g := fun e σ=>fullBoundaryAffineFactor n (α e) (β e)
    (T.atSlot σ (k e)) (T.atSlot σ (i e))
  apply finite_weighted_resampled_product_square ha
    (fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0) f g
    (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0).1 rho hrho hxi
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|f e σ|^(2*a)) 0 ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
      (i e) (j e) (hij e) (fun d c=>|fullBoundaryAffineFactor n (α e) (β e) c d|^(2*a))]
    exact (actual_full_mixed_pair_moment_le n a U ho ht b h hb hh hb0 hh0 _
      (hcut e) (α e) (β e)).trans (hraw e)
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|g e σ|^(2*a)) 0 ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
      (i e) (k e) (hik e) (fun d c=>|fullBoundaryAffineFactor n (α e) (β e) c d|^(2*a)),←hlow e]
    exact (actual_full_mixed_pair_moment_le n a U ho ht b h hb hh hb0 hh0 _
      (hcut e) (α e) (β e)).trans (hraw e)
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|f e σ-g e σ|^(2*a)) 0 ≤ _
    have he : (fun σ=>|f e σ-g e σ|^(2*a)) =
        fun σ=>|β e*(deletedOverlap n (joinSpin (T.atSlot σ (j e)))
          (joinSpin (T.atSlot σ (i e)))-deletedOverlap n (joinSpin (T.atSlot σ (k e)))
          (joinSpin (T.atSlot σ (i e))))|^(2*a) := by
      funext σ; congr 2; dsimp [f,g,fullBoundaryAffineFactor]; ring
    rw [he]
    exact (actual_full_mixed_edge_resampling_le n a U T ho b h hb hh hb0 hh0 ht
      (β e) (i e) (j e) (k e) (hjk e) (hlow e) (hgap e)).trans (hphysical e)

theorem eventually_actual_full_mixed_polynomial_from_primitives
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0 ≤ b z) → (∀ z,0 ≤ h z) →
    ∀ (t : ℝ),t ∈ Icc (0:ℝ) 1 →
    ∀ (α β : Fin a→ℝ) (i j k : Fin a→T.Slot),
      (∀ e,i e ≠ j e) → (∀ e,i e ≠ k e) → (∀ e,j e ≠ k e) →
      (∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e)) →
      (∀ e,T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e)) →
      (∀ e,T.splitIndex (i e) (j e) ≤ as.length) →
    ∀ (rho : Fin a→ℝ) (r W xi : ℝ) (v : Fin a→ℝ),
      (∀ e,0<rho e) → 0<r → 0<W → 0<xi → (∀ e,0<v e) →
      ((n+1:ℕ) : ℝ)^(-(1:ℝ)/6+m) ≤ r →
      (∀ e,nativeMixedBoundaryRawBudget n a as b h (T.splitIndex (i e) (j e)) (α e) (β e) ≤ (rho e)^(2*a)) →
      (∀ e,OriginalBoundaryPrimitiveInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (i e) (j e))
        (T.splitIndex (j e) (k e)) B A Cq H₀ c₀ r W (v e)) →
      (∀ e,|β e|^(2*a)*nativeBoundaryRowFactor n T b h*
        (2:ℝ)^(2*a-1)*(nativeBoundaryCompletionFactor n T b*
          (2*((n+1:ℕ) : ℝ)^(-delta)*savedExteriorScale r W (v e))^(2*a)+
          (2/(n+1:ℕ):ℝ)^(2*a)) ≤ (xi*rho e)^(2*a)) →
      T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavityVariance n U as b h t)
        (fun σ=>(fullBoundaryAffineProduct n
          α β
            (fun e=>T.atSlot σ (j e)) (fun e=>T.atSlot σ (i e))-
          fullBoundaryAffineProduct n
          α β
            (fun e=>T.atSlot σ (k e)) (fun e=>T.atSlot σ (i e)))^2) 0 ≤
        ((a:ℝ)*xi*(∏ e,rho e))^2 := by
  have HE := (tendsto_add_atTop_nat 1).eventually
    (eventually_original_boundary_resampling_from_primitives (a-1) dc dq B A Cq H₀ c₀
      hA hCq hH₀ hc₀ hgap)
  filter_upwards [HE] with n hn
  intro U as T ho b h hb hh hb0 hh0 t ht α β i j k hij hik hjk hlow hgap' hcut
    rho r W xi v hrho hr hW hxi hv hrscale hraw I hdom
  apply actual_full_mixed_polynomial_from_physical_resampling n U T ho b h hb hh hb0 hh0
    ht ha α β i j k hij hik hjk hlow hgap' hcut rho hrho hxi hraw
  intro e
  have he := hn as ho (physicalCompletedClock (n+1) b h)
    (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) (hgap' e).le
    (T.splitIndex_le_clockLength _ _) r W (v e) hr hW (hv e) hrscale (I e)
  have ha' : a-1+1=a := by omega
  rw [ha'] at he
  apply le_trans _ (hdom e)
  unfold nativeMixedBoundaryReplacementBudget
  gcongr <;> simp only [nativeBoundaryRowFactor,nativeBoundaryCompletionFactor] <;> positivity

theorem full_mixed_centered_product_eq (n : ℕ) {a : ℕ} (S : Fin a→ℝ)
    (c d : Fin a→Spin n×Bool) :
    fullBoundaryAffineProduct n (fun e=>-S e) (fun _=>1) c d =
      ∏ e : Fin a, (deletedOverlap n (joinSpin (c e)) (joinSpin (d e))-S e) := by
  unfold fullBoundaryAffineProduct fullBoundaryAffineFactor
  apply Finset.prod_congr rfl
  intro e _
  ring

end OAI.SKFluctuations.Cavity
