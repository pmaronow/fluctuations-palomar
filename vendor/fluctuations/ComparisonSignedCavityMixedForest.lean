module

public import ComparisonSignedCavityMixedStars

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem actual_full_mixed_forest_from_physical_resampling (n U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {a : ℕ} (ha : 0<a)
    (α β : Fin a→ℝ) (i j k : Fin a→T.Slot)
    (hij : ∀ e,i e ≠ j e) (hik : ∀ e,i e ≠ k e) 
    (hlow : ∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e))
    (hgap : ∀ e,j e ≠ k e → T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e))
    (hcut : ∀ e,T.splitIndex (i e) (j e) ≤ as.length)
    (rho : Fin a→ℝ) (hrho : ∀ e,0<rho e) {xi : ℝ} (hxi : 0<xi)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n a as b h
      (T.splitIndex (i e) (j e)) (α e) (β e) ≤ (rho e)^(2*a))
    (hphysical : ∀ e,j e ≠ k e → nativeMixedBoundaryReplacementBudget n a T b h (β e)
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
    by_cases heq : j e=k e
    · simp only [f,g,heq,sub_self,abs_zero,zero_pow (by omega : 2*a ≠ 0),
        ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg (mul_nonneg hxi.le (hrho e).le) _
    have he : (fun σ=>|f e σ-g e σ|^(2*a)) =
        fun σ=>|β e*(deletedOverlap n (joinSpin (T.atSlot σ (j e)))
          (joinSpin (T.atSlot σ (i e)))-deletedOverlap n (joinSpin (T.atSlot σ (k e)))
          (joinSpin (T.atSlot σ (i e))))|^(2*a) := by
      funext σ; congr 2; dsimp [f,g,fullBoundaryAffineFactor]; ring
    rw [he]
    exact (actual_full_mixed_edge_resampling_le n a U T ho b h hb hh hb0 hh0 ht
      (β e) (i e) (j e) (k e) heq (hlow e) (hgap e heq)).trans (hphysical e heq)

theorem eventually_actual_full_mixed_forest_from_primitives
    (a dc dq : ℕ) (ha : 0<a) (B A Cq H₀ c₀ : ℝ)
    (hA : 0 ≤ A) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (U : ℕ) (as : List PositiveMass)
      (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
      (b h : ℕ→ℝ),Monotone b → Monotone h → (∀ z,0 ≤ b z) → (∀ z,0 ≤ h z) →
    ∀ (t : ℝ),t ∈ Icc (0:ℝ) 1 →
    ∀ (α β : Fin a→ℝ) (i j k : Fin a→T.Slot),
      (∀ e,i e ≠ j e) → (∀ e,i e ≠ k e) → 
      (∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e)) →
      (∀ e,j e ≠ k e → T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e)) →
      (∀ e,T.splitIndex (i e) (j e) ≤ as.length) →
    ∀ (rho : Fin a→ℝ) (r W xi : ℝ) (v : Fin a→ℝ),
      (∀ e,0<rho e) → 0<r → 0<W → 0<xi → (∀ e,0<v e) →
      ((n+1:ℕ) : ℝ)^(-(1:ℝ)/6+m) ≤ r →
      (∀ e,nativeMixedBoundaryRawBudget n a as b h (T.splitIndex (i e) (j e)) (α e) (β e) ≤ (rho e)^(2*a)) →
      (∀ e,j e ≠ k e → OriginalBoundaryPrimitiveInput (n+1) (a-1) dc dq as
        (physicalCompletedClock (n+1) b h) (T.splitIndex (i e) (j e))
        (T.splitIndex (j e) (k e)) B A Cq H₀ c₀ r W (v e)) →
      (∀ e,j e ≠ k e → |β e|^(2*a)*nativeBoundaryRowFactor n T b h*
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
  intro U as T ho b h hb hh hb0 hh0 t ht α β i j k hij hik hlow hgap' hcut
    rho r W xi v hrho hr hW hxi hv hrscale hraw I hdom
  apply actual_full_mixed_forest_from_physical_resampling n U T ho b h hb hh hb0 hh0
    ht ha α β i j k hij hik hlow hgap' hcut rho hrho hxi hraw
  intro e heq
  have he := hn as ho (physicalCompletedClock (n+1) b h)
    (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) (hgap' e heq).le
    (T.splitIndex_le_clockLength _ _) r W (v e) hr hW (hv e) hrscale (I e heq)
  have ha' : a-1+1=a := by omega
  rw [ha'] at he
  apply le_trans _ (hdom e heq)
  unfold nativeMixedBoundaryReplacementBudget
  gcongr <;> simp only [nativeBoundaryRowFactor,nativeBoundaryCompletionFactor] <;> positivity

theorem actual_full_linear_combination_square (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (N : ℕ) (c m : Fin N→ℝ) (F : Fin N→T.Assignment→ℝ)
    (hm : ∀ r,0 ≤ m r)
    (hF : ∀ r,T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>F r σ^2) x ≤ m r^2) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(∑ r,c r*F r σ)^2) x ≤
        (N:ℝ)*(∑ r,|c r| * m r)^2 := by
  let w := fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) v q σ x
  have hw := (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x).1
  have hp σ : (∑ r,c r*F r σ)^2 ≤ (N:ℝ)*∑ r,(c r*F r σ)^2 := by
    have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N=>(1:ℝ))
      (fun r=>c r*F r σ)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one] using H
  change (∑ σ,w σ*(∑ r,c r*F r σ)^2) ≤ _
  calc
    _ ≤ ∑ σ,w σ*((N:ℝ)*∑ r,(c r*F r σ)^2) :=
      Finset.sum_le_sum fun σ _=>mul_le_mul_of_nonneg_left (hp σ) (hw σ)
    _ = (N:ℝ)*∑ r,c r^2*(∑ σ,w σ*F r σ^2) := by
      simp only [mul_pow,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ ≤ (N:ℝ)*∑ r,(|c r| * m r)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro r _
      have H := mul_le_mul_of_nonneg_left (hF r) (sq_nonneg (c r))
      simpa only [mul_pow,sq_abs,ClockTree.disorderExpect,w] using H
    _ ≤ (N:ℝ)*(∑ r,|c r| * m r)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_sq_le_sq_sum_of_nonneg fun r _=>mul_nonneg (abs_nonneg _) (hm r)

end OAI.SKFluctuations.Cavity
