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
  have hfd₀ : dist (f x₀) (f y₀) = 0 := by
    rw [continuous_iff_seqContinuous] at hf1
    have h1 := Filter.Tendsto.dist (hf1 hxij) (hf1 hyij)
    have h2 := Filter.Tendsto.comp hdf hijmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  rw [dist_eq_zero] at hfd₀

  -- (so ...)
  have hd₀ : dist x₀ y₀ < ε := by
    obtain ⟨hb, h⟩ := hf2 (f x₀)
    have hx₀ : x₀ ∈ f ⁻¹' {f x₀} := by simp
    have hy₀ : y₀ ∈ f ⁻¹' {f x₀} := by simp [hfd₀]
    order [Metric.dist_le_diam_of_mem hb hx₀ hy₀]

  -- on the other hand, ...
  have : ε ≤ dist x₀ y₀ := by
    have h1 := Filter.Tendsto.dist hxij hyij
    exact ge_of_tendsto' h1 fun n ↦ hd ((i ∘ j) n)
  order

variable (X Y) in
def spaceOfEpsilonInjective [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) :=
  {f : C(X, Y) | epsilonInjective f ε}

lemma epsilonInjectiveMonotone [MetricSpace X] [MetricSpace Y] (f : X → Y) (ε : ℝ) (δ : ℝ )
    (hδ : ε < δ) (hf : epsilonInjective f ε) : epsilonInjective f δ :=
  fun y ↦ ⟨(hf y).left, lt_trans (hf y).right hδ⟩

lemma diameterIsAttained [MetricSpace X] (S : Set X) (hS : IsCompact S) (ne_S : S.Nonempty) :
    ∃ w ∈ S, ∃ z ∈  S, dist w z = Metric.diam S := by
  obtain ⟨⟨w, z⟩, ⟨hw, hz⟩, hwz⟩ :=
    hS.prod hS |>.exists_isMaxOn (ne_S.prod ne_S) continuous_dist.continuousOn
  simp only [isMaxOn_iff, Set.mem_prod, and_imp, Prod.forall] at hw hz hwz
  refine ⟨w, hw, z, hz, le_antisymm ?_ ?_⟩
  · exact Metric.dist_le_diam_of_mem hS.isBounded hw hz
  · exact Metric.diam_le_of_forall_dist_le_of_nonempty ne_S fun x hx y hy ↦ hwz x y hx hy

lemma epsilonInjectiveOpen [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) (hε : 0 < ε) :
    IsOpen (spaceOfEpsilonInjective X Y ε) := by
  rw [Metric.isOpen_iff]
  intro f hf
  simp only [spaceOfEpsilonInjective, Set.mem_ofPred_eq] at hf
  obtain ⟨δ, hhδ, hδ⟩ := stabilityOfEpsilonInjective f f.continuous_toFun ε hf
  refine ⟨δ/2, by linarith, fun g hg ↦ ?_⟩
  simp only [spaceOfEpsilonInjective, epsilonInjective, Set.mem_ofPred_eq]

  refine fun y ↦ ⟨Metric.isBounded_of_compactSpace, ?_⟩

  rw [Metric.mem_ball, ContinuousMap.dist_lt_iff (by linarith)] at hg

  have hcalc {a b : X} (hab : g a = g b) : dist a b < ε := hδ a b (calc
    _ ≤ dist (f a) (g a) + dist (g a) (f b) := dist_triangle (f a) (g a) (f b)
    _ ≤ dist (f a) (g a) + (dist (g a) (g b) + dist (g b) (f b)) := by
      simp [dist_triangle (g a) (g b) (f b)]
    _ = dist (f a) (g a) + dist (g b) (f b) := by simp [hab]
    _ < δ := by linarith [dist_comm (g a) _ ▸ hg a, hg b])

  have cpt_fibs : IsCompact (g ⁻¹' {y}) :=
    IsCompact.preimage_continuous (by simp) g.continuous_toFun

  by_cases! h : g ⁻¹' {y} = ∅
  · simp [h, hε]
  · obtain ⟨w, hw, z, hz, hwz⟩ := diameterIsAttained (g ⁻¹' {y}) cpt_fibs h
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw hz
    exact hwz ▸ hcalc (hz ▸ hw)

lemma epsilonInjective_to_injective [MetricSpace X] [MetricSpace Y] (f : X → Y)
    (hf : ∀ ε > 0, epsilonInjective f ε) : f.Injective := by
  intro a b hhf
  rw [← zero_eq_dist]
  refine le_antisymm dist_nonneg (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  have ⟨hbound, bound⟩ := hf ε hε (f a)
  have ha : a ∈ f ⁻¹' {f a} := by simp
  have hb : b ∈ f ⁻¹' {f a} := by simp [hhf]
  linarith [Metric.dist_le_diam_of_mem hbound ha hb]
