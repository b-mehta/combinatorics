import data.finset
import data.fintype
import algebra.big_operators
import tactic.fin_cases
import tactic.omega
import logic.function
open finset
open function


lemma pigeonhole {α : Type*} [decidable_eq α]
  (s : finset α) (f g : α → ℕ) (big : s.sum f < s.sum g) :
  ∃ (a ∈ s), f a < g a :=
begin
  by_contra, push_neg at a, apply not_le_of_lt big (finset.sum_le_sum a)
end
lemma strong_pigeonhole {α β : Type*} [decidable_eq α] [decidable_eq β] 
  (s : finset α) (f : α → ℕ) (g : α → finset β) (tot : s.sum f < finset.card (s.bind g)):
  ∃ a ∈ s, f a < finset.card (g a) :=
pigeonhole s f _ (lt_of_lt_of_le tot finset.card_bind_le)

lemma finite_pigeonhole_const {α β : Type*} [decidable_eq α] [decidable_eq β] 
  (s : finset α) (f : α → ℕ) (k : ℕ) (big : s.sum f < finset.card s * k) :
  ∃ a ∈ s, f a < k :=
begin
  apply pigeonhole s f, rwa [finset.sum_const, nat.smul_eq_mul]
end

local attribute [instance, priority 10] classical.prop_decidable
noncomputable theory


@[reducible] def rset' (r : ℕ) {α : Type*} (m : finset α) : finset (finset α) := powerset_len r m 
local notation r`-edges-of `X := powerset_len r X
local notation `edges-of `X := powerset_len 2 X

lemma mem_rset {α : Type*} {r : ℕ} {m : finset α} (A : finset α): A ∈ (r-edges-of m) ↔ A.card = r ∧ A ⊆ m :=
mem_powerset_len.trans and.comm

-- def ramsey_form (r k t : ℕ) : Prop := ∀ (K : finset ℕ), K.card = k → ∃ n, ∀ (V : finset ℕ), n ≤ card V → 
--   ∀ (c : finset ℕ → ℕ), (∀ e ∈ (r-edges-of V), c e ∈ K) → 
--   ∃ (M ⊆ V), t ≤ M.card ∧ ∃ col : ℕ, ∀ e ∈ (r-edges-of M), c e = col

lemma sum_fin_2 (f : fin 2 → ℕ) : sum univ f = f 0 + f 1 :=
begin
  show multiset.sum (multiset.map f (list.fin_range 2)) = f 0 + f 1,
  rw multiset.coe_map, 
  rw multiset.coe_sum, 
  rw list.fin_range,
  rw list.map_pmap, 
  rw ← list.of_fn_eq_pmap, 
  rw list.of_fn_succ,
  rw list.sum_cons, 
  rw list.of_fn_succ, 
  rw list.sum_cons, 
  rw list.of_fn_zero, 
  rw list.sum_nil, 
  rw add_zero, refl
end

-- lemma trivial_ramsey {r t : ℕ} : ramsey_form r 0 t := 
-- begin
--   rw ramsey_form, intros K hK, use r, 
-- end

-- this sucks. use something much better, like in inf ramsey
def colour_components {α : Type*} (V : finset ℕ) (c : finset ℕ → α) (v : ℕ) (col : α) : finset ℕ :=
(V.erase v).filter (λ w, c {v,w} = col)

lemma mem_colour_components {α : Type*} {V : finset ℕ} (c : finset ℕ → α) {v w : ℕ} (col : α) : 
w ∈ colour_components V c v col ↔ w ≠ v ∧ w ∈ V ∧ c {v,w} = col :=
by simp [colour_components, and_assoc]

lemma colour_components_sub {α : Type*} {V : finset ℕ} {c : finset ℕ → α} {v : ℕ} {col : α} :
colour_components V c v col ⊆ V :=
begin
  intro t, rw mem_colour_components, tauto
end

lemma center_not_in_colour_components {α : Type*} {V : finset ℕ} {c : finset ℕ → α} {v : ℕ} {col : α} : 
  v ∉ colour_components V c v col :=
begin
  rw mem_colour_components, intro a, exact a.1 rfl, 
end

lemma all_colours_is_all {α : Type*} {V : finset ℕ} {K : finset α} {c : finset ℕ → α} (h : ∀ e ∈ (edges-of V), c e ∈ K) {v : ℕ} (hv : v ∈ V) :
K.bind (colour_components V c v) = V.erase v :=
begin
  ext, simp only [mem_bind, exists_prop, mem_erase, mem_colour_components], split,
    rintro ⟨_, _, p, q, _⟩, exact ⟨p, q⟩,
  rintro ⟨p, q⟩, refine ⟨_, _, p, q, rfl⟩, 
  apply h, rw mem_rset, simp, split, rw card_insert_of_not_mem, rw card_singleton, rwa not_mem_singleton, 
  rw insert_subset, refine ⟨q, set.singleton_subset_iff.2 hv⟩
end

-- def build {α : Type*} (x y : α) : fin 2 → α
-- | ⟨0, _⟩ := x
-- | _ := y
-- lemma two_ramsey (size : fin 2 → ℕ) : 
--   ∃ n ≤ nat.choose (size 0 + size 1) (size 0), ∀ (c : finset ℕ → fin 2) (V : finset ℕ), 
--   n ≤ card V → ∃ (M ⊆ V), ∃ col, size col ≤ card M ∧ ∀ e ∈ (edges-of M), c e = col :=

lemma two_ramsey (s t : ℕ) : 
  ∃ n ≤ nat.choose (s+t) s, ∀ (c : finset ℕ → ℕ) (V : finset ℕ) (hc : ∀ e ∈ (edges-of V), c e < 2),
  n ≤ card V →
  (∃ M ⊆ V, s ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 0) ∨ 
  (∃ M ⊆ V, t ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 1) :=
begin
  revert s t, 
  suffices z: ∀ s : (ℕ × ℕ), ∃ n ≤ nat.choose (s.1+s.2) s.1, 
    ∀ (c : finset ℕ → ℕ) (V : finset ℕ) (hc : ∀ e ∈ (edges-of V), c e < 2), 
    n ≤ card V →
    (∃ M ⊆ V, s.1 ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 0) ∨ 
    (∃ M ⊆ V, s.2 ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 1),
    intros s t, exact z (s,t), 
  intro s, refine @well_founded.recursion (ℕ × ℕ) (measure (λ (a : ℕ × ℕ), a.1 + a.2)) (measure_wf _) _ s _, 
  clear s, rintros ⟨s,t⟩ ih,
  cases nat.eq_zero_or_pos s with h sp, rw h at *,
    refine ⟨0, zero_le _, _⟩, intros c V hc hV, left, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
    intros e he, rw [mem_rset, subset_empty] at he, have z := he.1, rw he.2 at z,
    apply (nat.succ_ne_zero _ z.symm).elim, 
  cases nat.eq_zero_or_pos t with h tp, rw h at *,
    refine ⟨0, zero_le _, _⟩, intros c V hc hV, right, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
    intros e he, rw [mem_rset, subset_empty] at he, have z := he.1, rw he.2 at z,
    apply (nat.succ_ne_zero _ z.symm).elim, 
  obtain ⟨a, ha₁, ha₂⟩ := ih ⟨s-1, t⟩ _, 
    swap, rw [measure, inv_image, add_lt_add_iff_right], apply nat.sub_lt sp zero_lt_one,
  obtain ⟨b, hb₁, hb₂⟩ := ih ⟨s, t-1⟩ _, 
    swap, rw [measure, inv_image, add_lt_add_iff_left], apply nat.sub_lt tp zero_lt_one,
  conv at hb₂ in (_ ∨ _) { rw or_comm }, -- for later
  clear ih, 
  refine ⟨max 1 (a+b), _, _⟩,
    apply max_le, apply nat.choose_pos, exact nat.le.intro rfl, 
    have := nat.choose_succ_succ (s + t - 1) (s - 1), 
    rw [← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos (nat.add_pos_left sp _), 
        ← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos sp] at this,
    rw this, convert add_le_add ha₁ hb₁, rw ← nat.sub_add_comm sp, refl, rw ← nat.add_sub_assoc tp, refl,
  intros c V hc hV, 
  obtain ⟨v, hv⟩: ∃ v, v ∈ V, apply exists_mem_of_ne_empty, rw ← card_pos, apply trans (le_max_left 1 (a+b)) hV, 
  have cards: card ((range 2).bind (colour_components V c v)) = card (V.erase v), congr, 
    apply all_colours_is_all (λ e he, mem_range.2 (hc e he)) hv,
  have: ¬ (card (colour_components V c v 0) < a ∧ card (colour_components V c v 1) < b),
    rintro ⟨smallred, smallgreen⟩, rw card_erase_of_mem hv at cards, 
    rw [range_succ, bind_insert, range_one, insert_empty_eq_singleton, singleton_bind, card_disjoint_union, add_comm] at cards,
      apply ne_of_lt _ cards, apply lt_of_lt_of_le _ (nat.pred_le_pred (trans (le_max_right _ _) hV)), 
      rw nat.pred_eq_sub_one, rw nat.add_sub_assoc (nat.one_le_of_lt smallgreen), apply lt_of_lt_of_le, 
      rwa add_lt_add_iff_right,  apply add_le_add_left (nat.le_pred_of_lt smallgreen),
    rw disjoint_left, simp only [mem_colour_components, not_and], rintros _ ⟨_, _, t₁⟩ _ _, rw t₁, exact one_ne_zero,
  push_neg at this, cases this,
    clear hb₁ hb₂ hV b ha₁, 
    swap,
    clear ha₁ ha₂ hV a hb₁, 
    rename hb₂ ha₂, rename b a, rw or_comm,
    swap,
  all_goals {
    specialize ha₂ c (colour_components V c v _) (λ e he, hc e (powerset_len_mono colour_components_sub he)) this,
    rcases ha₂ with ⟨things, sub, big, col⟩ | ⟨things, sub, big, col⟩,
      left, refine ⟨insert v things, _, _, _⟩, rw insert_subset, exact ⟨hv, trans sub colour_components_sub⟩, 
        rw card_insert_of_not_mem, rw ← nat.sub_le_right_iff_le_add, exact big,
        intro, apply center_not_in_colour_components (sub a_1), 
      intros e he, by_cases e ∈ (2-edges-of things), apply col e h, 
      rw mem_rset at h, rw mem_rset at he, simp [he.1] at h, rw subset_insert_iff at he,
      have: v ∈ e, by_contra a, apply h, rwa erase_eq_of_not_mem a at he, exact he.2, 
      obtain ⟨v₂, hv₂⟩: ∃ v₂, erase e v = finset.singleton v₂, rw ← card_eq_one, rw card_erase_of_mem ‹v ∈ e›, rw he.1, refl,
      have: v₂ ∈ colour_components V c v _, apply sub, apply he.2, rw hv₂, apply mem_singleton_self,
      rw mem_colour_components at this, rcases this with ⟨_, _, c'⟩, convert c', symmetry, rw has_insert_eq_insert, 
      apply eq_of_subset_of_card_le, rw insert_subset, split, apply mem_of_mem_erase, rw hv₂, apply mem_singleton_self,
      exact set.singleton_subset_iff.2 this, rw he.1, apply le_of_eq, rw [insert_empty_eq_singleton, card_insert_of_not_mem, card_singleton],
      rwa not_mem_singleton, 
    right, refine ⟨things, trans sub colour_components_sub, big, col⟩ }
end

lemma lt_two_iff_eq_zero_or_one : ∀ {n : ℕ}, n < 2 ↔ n = 0 ∨ n = 1 := by omega
-- | 0 := by simp
-- | 1 := by simp; norm_num
-- | _ := by simp

lemma one_ramsey (s t : ℕ) : 
  ∃ n ≤ s + t - 1, ∀ (c : finset ℕ → ℕ) (V : finset ℕ) (hc : ∀ e ∈ (1-edges-of V), c e < 2),
  n ≤ card V →
  (∃ M ⊆ V, s ≤ card M ∧ ∀ e ∈ (1-edges-of M), c e = 0) ∨ 
  (∃ M ⊆ V, t ≤ card M ∧ ∀ e ∈ (1-edges-of M), c e = 1) :=
begin
  refine ⟨s + t - 1, le_refl _, _⟩, intros c V hc hV, 
  rcases nat.eq_zero_or_pos s with rfl | sp, 
    left, refine ⟨∅, empty_subset _, le_refl _, λ e he, _⟩, rw mem_rset at he, rw subset_empty at he, 
    exfalso, apply nat.zero_ne_one, rw ← he.1, rw he.2, rw card_empty,
  rcases nat.eq_zero_or_pos t with rfl | tp, 
    right, refine ⟨∅, empty_subset _, le_refl _, λ e he, _⟩, rw mem_rset at he, rw subset_empty at he, 
    exfalso, apply nat.zero_ne_one, rw ← he.1, rw he.2, rw card_empty,
  obtain ⟨v, hv⟩: ∃ v, v ∈ V, apply exists_mem_of_ne_empty, rw ← card_pos, 
    have: t - 1 < s + (t - 1) := lt_add_of_pos_left (t - 1) sp, rw ← nat.add_sub_assoc tp at this, 
    apply nat.one_le_of_lt (lt_of_lt_of_le this hV), 
  obtain ⟨col, hcol, hcol₂⟩ := strong_pigeonhole (range 2) (λ x, ite (x=0) (s-1) (t-1)) 
                                                 (λ col, V.filter (λ t, c (finset.singleton t) = col)) _, 
  rw mem_range at hcol, dsimp at hcol₂, split_ifs at hcol₂, 
    rw h at *, left, 
    refine ⟨(filter (λ t, c (finset.singleton t) = 0) V), filter_subset _, nat.le_of_pred_lt hcol₂, _⟩, 
    intros e he, simp [mem_rset, card_eq_one] at he, rcases he with ⟨⟨e₁, rfl⟩, he⟩, 
    exact (mem_filter.1 (he (mem_singleton_self e₁))).2, 
  have: col = 1, apply le_antisymm, rwa ← nat.lt_succ_iff, apply nat.pos_of_ne_zero h, 
    rw this at *, right,
    refine ⟨(filter (λ t, c (finset.singleton t) = 1) V), filter_subset _, nat.le_of_pred_lt hcol₂, _⟩, 
    intros e he, simp [mem_rset, card_eq_one] at he, rcases he with ⟨⟨e₁, rfl⟩, he⟩, 
    exact (mem_filter.1 (he (mem_singleton_self e₁))).2, 
  simp [sum_range_succ, range_succ], 
  have: filter (λ t, c (finset.singleton t) = 1) V ∪ filter (λ t, c (finset.singleton t) = 0) V = V,
  ext t, simp, 
    split, rintro (⟨p, _⟩ | ⟨p, _⟩); exact p,
    intro k, specialize hc (finset.singleton t) _, rw lt_two_iff_eq_zero_or_one at hc, 
    tauto, rw mem_rset, simp, exact set.singleton_subset_iff.2 k, 
  rw this, apply lt_of_lt_of_le _ hV, clear hV hv hc this c V, omega
end

-- lemma two_ramsey' (s t : ℕ) : 
--   ∃ n ≤ nat.choose (s+t) s, ∀ (c : finset ℕ → ℕ) (V : finset ℕ) (hc : ∀ e ∈ (edges-of V), c e < 2),
--   n ≤ card V →
--   (∃ M ⊆ V, s ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 0) ∨ 
--   (∃ M ⊆ V, t ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 1) :=
-- begin
--    revert s t, 
--   suffices z: ∀ s : (ℕ × ℕ), ∃ n ≤ nat.choose (s.1+s.2) s.1, 
--     ∀ (c : finset ℕ → ℕ) (V : finset ℕ) (hc : ∀ e ∈ (edges-of V), c e < 2), 
--     n ≤ card V →
--     (∃ M ⊆ V, s.1 ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 0) ∨ 
--     (∃ M ⊆ V, s.2 ≤ card M ∧ ∀ e ∈ (edges-of M), c e = 1),
--     intros s t, exact z (s,t), 
--   intro s, refine @well_founded.recursion (ℕ × ℕ) (measure (λ (a : ℕ × ℕ), a.1 + a.2)) (measure_wf _) _ s _, 
--   clear s, rintros ⟨s,t⟩ ih,
--   rcases nat.eq_zero_or_pos s with rfl | sp, 
--     refine ⟨0, zero_le _, _⟩, intros c V hc hV, left, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
--     intros e he, rw [mem_rset, subset_empty] at he, have z := he.1, rw he.2 at z,
--     apply (nat.succ_ne_zero _ z.symm).elim, 
--   rcases nat.eq_zero_or_pos t with rfl | tp, 
--     refine ⟨0, zero_le _, _⟩, intros c V hc hV, right, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
--     intros e he, rw [mem_rset, subset_empty] at he, have z := he.1, rw he.2 at z,
--     apply (nat.succ_ne_zero _ z.symm).elim, 
--   obtain ⟨a, ha₁, ha₂⟩ := ih ⟨s-1, t⟩ _, 
--   swap, rw [  measure, inv_image, add_lt_add_iff_right], apply nat.sub_lt sp zero_lt_one,
--   obtain ⟨b, hb₁, hb₂⟩ := ih ⟨s, t-1⟩ _, 
--     swap, rw [measure, inv_image, add_lt_add_iff_left], apply nat.sub_lt tp zero_lt_one,
--   -- conv at hb₂ in (_ ∨ _) { rw or_comm }, -- for later
--   clear ih, 
--   refine ⟨max 1 (a+b), _, _⟩,
--     apply max_le, apply nat.choose_pos, exact nat.le.intro rfl, 
--     have := nat.choose_succ_succ (s + t - 1) (s - 1), 
--     rw [← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos (nat.add_pos_left sp _), 
--         ← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos sp] at this,
--     rw this, convert add_le_add ha₁ hb₁, rw ← nat.sub_add_comm sp, refl, rw ← nat.add_sub_assoc tp, refl,
--   intros c V hc hV, 
--   obtain ⟨v, hv⟩: ∃ v, v ∈ V, apply exists_mem_of_ne_empty, rw ← card_pos, apply trans (le_max_left 1 (a+b)) hV, 
--   set c' : finset ℕ → ℕ := λ F, c (insert v F),
--   obtain ⟨n, hn₁, hn₂⟩ := one_ramsey (s-1) (t-1), 
--     apply or.imp _ _ (hn₂ c' (erase V v) _ _), 

--     sorry,
--     sorry,
--   intros e he, apply hc, rw mem_rset at ⊢ he, rw insert_subset, rw card_insert_of_not_mem, rw he.1,
--   refine ⟨rfl, hv, trans he.2 (erase_subset _ _)⟩, 
--   intro, apply not_mem_erase v V, apply he.2 a_1, 
--   rw card_erase_of_mem hv, apply trans hn₁, apply nat.pred_le_pred, 
--   apply trans _ hV, apply le_max_right
-- end