import data.finset
import data.fintype

open finset

variable {α : Type*}
variable {r : ℕ}

def is_layer (A : finset (finset α)) (r : ℕ) : Prop := ∀ x ∈ A, card x = r

lemma union_layer [decidable_eq α] {A B : finset (finset α)} : is_layer A r ∧ is_layer B r ↔ is_layer (A ∪ B) r :=
begin
  split; intros p, 
    rw is_layer,
    intros,
    rw mem_union at H,
    exact H.elim (p.1 _) (p.2 _),
  split,
  all_goals {rw is_layer, intros, apply p, rw mem_union, tauto}, 
end

lemma mem_powerset_len_iff_card [fintype α] {r : ℕ} : ∀ (x : finset α), x ∈ powerset_len r (fintype.elems α) ↔ card x = r :=
by intro x; rw mem_powerset_len; exact and_iff_right (subset_univ _)

lemma powerset_len_iff_is_layer [fintype α] {𝒜 : finset (finset α)} : is_layer 𝒜 r ↔ 𝒜 ⊆ powerset_len r (fintype.elems α) :=
begin
  split; intros p A h,
    rw mem_powerset_len_iff_card,
    exact (p _ h),
  rw ← mem_powerset_len_iff_card, 
  exact p h
end

lemma size_in_layer [fintype α] {𝒜 : finset (finset α)} (h : is_layer 𝒜 r) : card 𝒜 ≤ nat.choose (fintype.card α) r :=
begin
  rw [fintype.card, ← card_powerset_len],
  apply card_le_of_subset,
  rwa [univ, ← powerset_len_iff_is_layer]
end