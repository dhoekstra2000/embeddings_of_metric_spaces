import Mathlib

/-!
# Embeddings of finite dimensional metric spaces
This files proves that any finite dimensional compact metric spaces admits
an embedding into R^{2n+1}
-/


variable {X Y : Type*}

def epsilonInjective [MetricSpace X] [MetricSpace Y] (f : X → Y) (ε : ℝ) : Prop :=
∀ y , Bornology.IsBounded (f ⁻¹' {y}) ∧ Metric.diam (f ⁻¹' {y}) < ε

/-
TODO:
- Show the space of epsilon embeddings is dense under the right assumptions
- Define general position
-/

lemma stabilityOfEpsilonInjective [MetricSpace X] [CompactSpace X] [MetricSpace Y] (f : X → Y)
    (hf1 : Continuous f) (ε : ℝ) (hf2 : epsilonInjective f ε) :
    ∃ δ > 0 , ∀ x y , dist (f x) (f y) < δ → dist x y < ε := by
  by_contra! hcontra

  -- we can find a pair of sequences ...
  obtain ⟨x, y, hdf, hd⟩ : ∃ x y : ℕ → X,
      Filter.Tendsto (fun n ↦ dist (f (x n)) (f (y n))) .atTop (nhds 0) ∧
      ∀ n, ε ≤ (dist (x n) (y n)) := by
    choose x y hdf hd using (fun n ↦ hcontra ((1 / 2) ^ n) (by norm_num))
    refine ⟨x, y, ?_, hd⟩
    simp only [Metric.tendsto_atTop, dist_zero_right, norm, abs_dist]
    intro ε' hε'
    obtain ⟨N, hN⟩ : ∃ N, (1 / 2) ^ N < ε' := exists_pow_lt_of_lt_one hε' (by norm_num)
    refine ⟨N, fun n hn ↦ ?_⟩
    have : ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ N :=
      pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num) |>.mpr hn
    order [hdf n]

  -- we can find a pair of convergent subsequences ...
  obtain ⟨x₀, i, himono, hxi⟩ := CompactSpace.tendsto_subseq x
  obtain ⟨y₀, j, hjmono, hyij⟩ := CompactSpace.tendsto_subseq (y ∘ i)
  have hijmono : StrictMono (i ∘ j) := himono.comp hjmono
  have hxij := Filter.Tendsto.comp hxi hjmono.tendsto_atTop
  rw [Function.comp_assoc] at hxij hyij

  -- we see that ..., so ...
  have h₀ : dist (f x₀) (f y₀) = 0 := by
    rw [continuous_iff_seqContinuous] at hf1
    have h1 := Filter.Tendsto.dist (hf1 hxij) (hf1 hyij)
    have h2 := Filter.Tendsto.comp hdf hijmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  rw [dist_eq_zero] at h₀

  -- (so ...)
  have : dist x₀ y₀ < ε := by
    obtain ⟨hb, h⟩ := hf2 (f x₀)
    have h1 := Set.mem_preimage.mpr (Set.mem_singleton (f x₀))
    have h2 := h₀ ▸ Set.mem_preimage.mpr (Set.mem_singleton (f y₀))
    order [Metric.dist_le_diam_of_mem hb h1 h2]

  -- on the other hand, ...
  have : ε ≤ dist x₀ y₀ := by
    have h1 := Filter.Tendsto.dist hxij hyij
    exact ge_of_tendsto' h1 fun n ↦ hd ((i ∘ j) n)
  order

variable (X Y)

def spaceOfEpsilonInjective [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) :=
  {f : C(X, Y) | epsilonInjective f ε}

lemma epsilonInjectiveMonotone [MetricSpace X] [MetricSpace Y] (f : X → Y) (ε : ℝ) (δ : ℝ )
    (hδ : ε < δ) (hf : epsilonInjective f ε) : epsilonInjective f δ := by
  simp [epsilonInjective] at hf ⊢
  intro y
  specialize hf y
  constructor
  exact hf.1
  linarith

lemma diameterIsAttained [MetricSpace X] (S : Set X) (hS : IsCompact S) (ne_S : S.Nonempty) :
    ∃ w ∈ S, ∃ z ∈  S, dist w z = Metric.diam (S) := by
  have := IsCompact.prod hS hS
  rcases this.exists_isMaxOn (ne_S.prod ne_S) continuous_dist.continuousOn with ⟨x, hx, hhx⟩
  use x.1, hx.1, x.2, hx.2
  rw [isMaxOn_iff] at hhx
  have : ∀ x1 ∈ S, ∀ x2 ∈ S, dist x1 x2 ≤ dist x.1 x.2 := by
    intro x1 hx1 x2 hx2
    specialize hhx ⟨x1, x2⟩ ⟨hx1, hx2⟩
    exact hhx
  have ineq1 := Metric.diam_le_of_forall_dist_le_of_nonempty ne_S this
  have ineq2 := Metric.dist_le_diam_of_mem hS.isBounded hx.1 hx.2
  linarith

lemma epsilonInjectiveOpen [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) (hε : ε > 0) :
    IsOpen (spaceOfEpsilonInjective X Y ε) := by
  rw [Metric.isOpen_iff]
  intro f hf
  unfold spaceOfEpsilonInjective at hf
  simp at hf
  obtain ⟨δ, hhδ, hδ⟩ := stabilityOfEpsilonInjective f f.2 ε hf
  use δ/2
  constructor
  linarith
  intro g hg
  simp [spaceOfEpsilonInjective, epsilonInjective]
  intro y
  constructor
  exact Metric.isBounded_of_compactSpace
  have : ∀ a ∈  g ⁻¹' {y}, ∀ b ∈ g ⁻¹' {y}, dist a b < ε := by
    intro a ha b hb
    apply hδ a b
    calc
      dist (f a) (f b) ≤ dist (f a) (g a) + dist (g a) (f b) := dist_triangle (f a) (g a) (f b)
      _ ≤ dist (f a) (g a) + (dist (g a) (g b) + dist (g b) (f b)) := by
        gcongr
        exact dist_triangle (g a) (g b) (f b)
      _ = dist (f a) (g a) + dist (g b) (f b) := by
        rw [add_left_cancel_iff]
        conv_rhs => rw [← zero_add (dist (g b) (f b))]
        rw [add_right_cancel_iff]
        rw [dist_eq_zero]
        have ha : g a = y := by
          rw [← Set.mem_singleton_iff]
          rw [← Set.mem_preimage]
          exact ha
        have hb : g b = y := by
          rw [← Set.mem_singleton_iff]
          rw [← Set.mem_preimage]
          exact hb
        rw [ha, hb]
      _ < δ := by
        have dfgest : ∀ (x : X), dist (f x) (g x) < δ / 2 := by
          have : δ / 2 > 0 := by linarith
          rw [← ContinuousMap.dist_lt_iff this]
          rw [← Metric.mem_ball']
          exact hg
        suffices h : dist (f a) (g a) < δ / 2 ∧ dist (g b) (f b )< δ / 2  by
          obtain ⟨hha, hhb⟩ := h
          linarith
        constructor
        exact dfgest a
        rw [dist_comm]
        exact dfgest b
  have cpt_fibs : IsCompact (g ⁻¹' {y}) := by
    apply IsClosed.isCompact
    apply IsClosed.preimage g.2
    apply isClosed_singleton
  -- rw [isCompact_iff_compactSpace] at cpt_fibs
  obtain (h | h) := isEmpty_or_nonempty (g ⁻¹' {y})
  have : Metric.diam (g ⁻¹' {y}) = 0 := by
    rw [Set.isEmpty_coe_sort.mp h]
    simp
  linarith
  rw [Set.nonempty_coe_sort] at h
  have tmp : ∃ w ∈ g ⁻¹' {y}, ∃ z ∈ g ⁻¹' {y}, dist w z = Metric.diam (g ⁻¹' {y}) := diameterIsAttained X (g ⁻¹' {y}) cpt_fibs h
  rcases tmp with ⟨w, hw, z, hz, hwz⟩
  specialize this w hw z hz
  rw [← hwz]
  exact this

lemma epsilonInjective_to_injective [MetricSpace X] [MetricSpace Y] (f : X → Y) (hf : ∀ ε > 0, epsilonInjective f ε) : f.Injective := by
  intro a b hhf
  rw [← zero_eq_dist]

  have : ∀ ε > 0 , dist a b < 0 + ε := by
    intro ε hε
    have ⟨hbound, bound⟩ := hf ε hε (f a)
    have ha : a ∈ f ⁻¹' {f a} := by simp
    have hb : b ∈ f ⁻¹' {f a} := by
      rw [hhf]
      simp
    have := Metric.dist_le_diam_of_mem hbound ha hb
    linarith

  exact le_antisymm (dist_nonneg (x := a) (y := b)) (le_of_forall_pos_lt_add this)
