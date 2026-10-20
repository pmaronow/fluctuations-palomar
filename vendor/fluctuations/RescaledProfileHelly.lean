module

public import NonnegativeMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open Filter Set Function
open scoped Topology

def rescaledHellyProfile (a : boundedMassProfiles) {x : ℝ} (hx : 0 < x) :
    NonnegativeMassProfile where
  mass t := a.val (x*t)/x
  nonneg t := div_nonneg (a.property.1 (x*t)).1 hx.le
  monotone := fun _s _t hst =>
    div_le_div_of_nonneg_right (a.property.2 (mul_le_mul_of_nonneg_left hst hx.le)) hx.le

theorem rescaledProfiles_tendsto_subseq (a : ℕ → boundedMassProfiles)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hb : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (a n).val (x n*R)/x n ≤ C) :
    ∃ (U : NonnegativeMassProfile) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ t : ℝ, Tendsto (fun n => (a (φ n)).val (x (φ n)*t)/x (φ n)) atTop (𝓝 (U.mass t)) :=
  nonnegativeMassProfile_locallyBounded_tendsto_subseq
    (fun n => rescaledHellyProfile (a n) (hx n)) hb

theorem profiles_and_rescalings_tendsto_subseq (a : ℕ → boundedMassProfiles)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hb : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (a n).val (x n*R)/x n ≤ C) :
    ∃ (b : boundedMassProfiles) (U : NonnegativeMassProfile) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 b) ∧
        ∀ t : ℝ, Tendsto (fun n => (a (φ n)).val (x (φ n)*t)/x (φ n))
          atTop (𝓝 (U.mass t)) := by
  obtain ⟨b, φ, hφ, ht⟩ := boundedMassProfiles_tendsto_subseq a
  have hb' : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (a (φ n)).val (x (φ n)*R)/x (φ n) ≤ C := by
    intro R hR
    obtain ⟨C, hC⟩ := hb R hR
    exact ⟨C, hφ.tendsto_atTop.eventually hC⟩
  obtain ⟨U, ψ, hψ, hU⟩ := rescaledProfiles_tendsto_subseq (a ∘ φ) (x ∘ φ)
    (fun n => hx (φ n)) hb'
  exact ⟨b, U, φ ∘ ψ, hφ.comp hψ, ht.comp hψ.tendsto_atTop, hU⟩

theorem boundedMassProfiles_pair_tendsto_subseq (a b : ℕ → boundedMassProfiles) :
    ∃ (A B : boundedMassProfiles) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (a ∘ φ) atTop (𝓝 A) ∧ Tendsto (b ∘ φ) atTop (𝓝 B) := by
  obtain ⟨A, φ, hφ, ht⟩ := boundedMassProfiles_tendsto_subseq a
  obtain ⟨B, ψ, hψ, hu⟩ := boundedMassProfiles_tendsto_subseq (b ∘ φ)
  exact ⟨A, B, φ ∘ ψ, hφ.comp hψ, ht.comp hψ.tendsto_atTop, hu⟩

theorem profile_pair_and_rescalings_tendsto_subseq (a b : ℕ → boundedMassProfiles)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (ha : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (a n).val (x n*R)/x n ≤ C)
    (hb : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (b n).val (x n*R)/x n ≤ C) :
    ∃ (A B : boundedMassProfiles) (U V : NonnegativeMassProfile) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 A) ∧ Tendsto (b ∘ φ) atTop (𝓝 B) ∧
        (∀ t : ℝ, Tendsto (fun n => (a (φ n)).val (x (φ n)*t)/x (φ n))
          atTop (𝓝 (U.mass t))) ∧
        (∀ t : ℝ, Tendsto (fun n => (b (φ n)).val (x (φ n)*t)/x (φ n))
          atTop (𝓝 (V.mass t))) := by
  obtain ⟨A, B, φ, hφ, hA, hB⟩ := boundedMassProfiles_pair_tendsto_subseq a b
  have ha' : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (a (φ n)).val (x (φ n)*R)/x (φ n) ≤ C := by
    intro R hR
    obtain ⟨C, hC⟩ := ha R hR
    exact ⟨C, hφ.tendsto_atTop.eventually hC⟩
  obtain ⟨U, ψ, hψ, hU⟩ := rescaledProfiles_tendsto_subseq (a ∘ φ) (x ∘ φ)
    (fun n => hx (φ n)) ha'
  have hb' : ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, (b (φ (ψ n))).val (x (φ (ψ n))*R)/x (φ (ψ n)) ≤ C := by
    intro R hR
    obtain ⟨C, hC⟩ := hb R hR
    exact ⟨C, (hφ.comp hψ).tendsto_atTop.eventually hC⟩
  obtain ⟨V, χ, hχ, hV⟩ := rescaledProfiles_tendsto_subseq
    (b ∘ (φ ∘ ψ)) (x ∘ (φ ∘ ψ)) (fun n => hx (φ (ψ n))) hb'
  exact ⟨A, B, U, V, (φ ∘ ψ) ∘ χ, (hφ.comp hψ).comp hχ,
    (hA.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop,
    (hB.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop,
    fun t => (hU t).comp hχ.tendsto_atTop, hV⟩

end OAI.SKFluctuations.Hierarchy
