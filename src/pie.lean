import data.finset
import data.fintype
import order.bounded_lattice
import to_mathlib

open finset

instance {α : Type*} [fintype α] [decidable_eq α] : lattice.semilattice_inf_top (finset α) := 
{ top := univ, le_top := subset_univ, ..finset.lattice.lattice }

lemma powerset_len_all {α} {K : finset α} {r : ℕ} (h : finset.card K = r) : powerset_len r K = finset.singleton K :=
begin
  ext, simp [mem_powerset_len], split, rintro ⟨h₁, h₂⟩, apply eq_of_subset_of_card_le h₁, rw [h₂, h], 
  rintro rfl, refine ⟨subset.refl _, ‹_›⟩,
end

lemma powerset_len_zero {α} {K : finset α} : powerset_len 0 K = finset.singleton ∅ :=
begin
  ext, simp [mem_powerset_len], split, exact (λ t, t.2), rintro rfl, exact ⟨empty_subset _, rfl⟩
end

lemma powerset_len_insert {α} [decidable_eq α] {K : finset α} {x : α} (hx : x ∉ K) (r : ℕ) : 
  powerset_len (r + 1) (insert x K) = powerset_len (r + 1) K ∪ image (insert x) (powerset_len r K) :=
begin
  ext A, simp [mem_powerset_len], split, rintro ⟨sub, card⟩, 
    by_cases x ∈ A, right, refine ⟨erase A x, ⟨subset_insert_iff.1 sub, _⟩, insert_erase h⟩, 
      rw card_erase_of_mem h, rw card, refl,
    left, rw subset_insert_iff at sub, rw erase_eq_of_not_mem h at sub, refine ⟨‹_›, ‹_›⟩,
  rintro (⟨_, _⟩ | ⟨_, ⟨sub, rfl⟩, rfl⟩), refine ⟨trans ‹_› (subset_insert _ _), ‹_›⟩, 
  rw subset_insert_iff, rw erase_insert (λ t, hx (‹a_w ⊆ K› t)), refine ⟨sub, _⟩, 
  rw card_insert_of_not_mem (λ t, hx (‹a_w ⊆ K› t))
end
lemma powerset_len_insert' {α} [decidable_eq α] {K : finset α} {x : α} (hx : x ∉ K) (r : ℕ) : 
  disjoint (powerset_len (r + 1) K) (image (insert x) (powerset_len r K)) :=
begin
  rw disjoint_left, intros _ _ _, simp [mem_powerset_len] at a_1, simp at a_2,
  rcases a_2 with ⟨_, _, rfl⟩, apply hx, apply a_1.1, apply mem_insert_self
end

lemma inclusion_exclusion2' {α : Type*} [decidable_eq α] (A B : finset α) : 
  card (A ∪ B) + card (A ∩ B) = card A + card B :=
begin
  rw [← union_sdiff_self_eq_union, card_disjoint_union disjoint_sdiff, 
      inter_comm, add_assoc, ← card_disjoint_union (sdiff_inter_inter B A),
      sdiff_union_inter]
end

lemma inclusion_exclusion2 {α : Type*} [decidable_eq α] (A B : finset α) : 
  (card (A ∪ B) : ℤ) = card A + card B - card (A ∩ B) :=
begin
  rw ← union_sdiff_self_eq_union, rw card_disjoint_union disjoint_sdiff, symmetry, 
  apply sub_eq_of_eq_add, norm_cast, rw inter_comm, rw add_assoc, 
  rw ← card_disjoint_union (sdiff_inter_inter B A), rw sdiff_union_inter
end

theorem inclusion_exclusion {α : Type*} [decidable_eq α] [fintype α] {n : ℕ} (A : ℕ → finset α) : 
  (card ((range n).bind A) : ℤ) = (range n).sum (λ k, ((-1)^k) * (sum (powerset_len (k+1) (range n)) (λ K, card (inf K A)))) := 
begin
  induction n with n ih generalizing A, simp, 
  rw sum_range_succ, rw range_succ, rw bind_insert, rw powerset_len_all, swap, 
    rw card_insert_of_not_mem not_mem_range_self, rw card_range, 
  rw sum_singleton, rw inf_insert, 
  rw inclusion_exclusion2, simp only [powerset_len_insert, not_mem_range_self, not_false_iff], 
  conv_rhs { congr, skip, congr, skip, funext, rw sum_union (powerset_len_insert' not_mem_range_self _), rw mul_add, skip },
  rw sum_add_distrib, rw ← ih, rw sub_eq_add_neg, rw add_right_comm, rw ← add_assoc, conv_rhs {rw add_right_comm}, 
  congr' 1, rw inter_bind, 
  have z: ∀ x, ∀ a ∈ powerset_len x (range n), ∀ b ∈ powerset_len x (range n), insert n a = insert n b → a = b,
    intros, rw mem_powerset_len at H H_1, have: n ∉ a := λ t, not_mem_range_self (H.1 t), rw ← erase_insert this, 
    have: n ∉ b := λ t, not_mem_range_self (H_1.1 t), rw ← erase_insert this, rw a_1,
  conv_rhs { congr, skip, congr, skip, funext, rw sum_image (z _), simp }, clear z,
  have: ↑(card (A n ⊓ inf (range n) A)) = (sum (powerset_len n (range n)) (λ (x : finset ℕ), (card (A n ∩ inf x A) : ℤ))), 
    rw powerset_len_all (card_range _), rw sum_singleton, refl,
  rw this, rw ← sum_range_succ (λ t, (-1 : ℤ) ^ t * sum (powerset_len t (range n)) (λ x, (card (A n ∩ inf x A) : ℤ))), 
  rw sum_range_succ', conv_rhs {conv {congr, skip, rw pow_zero, rw one_mul, rw powerset_len_zero, rw sum_singleton, rw inf_empty, congr, congr, rw ← inf_eq_inter, rw lattice.inf_top_eq }, rw add_comm },
  congr, simp [function.comp_app], conv_rhs {congr, skip, funext, rw pow_succ, rw mul_assoc}, rw ← mul_sum, rw neg_one_mul, congr, 
  rw ih, congr, funext, congr' 1, funext, apply sum_congr, congr, 
  intros K hK, congr, apply le_antisymm, apply subset_inter, 
    have: ∃ A, A ∈ K, rw exists_mem_iff_ne_empty, rw ← card_eq_zero, rw mem_powerset_len at hK, rw hK.2, apply nat.succ_ne_zero, 
    cases this with i hi, have: A n ∩ A i ⊆ A n, apply inter_subset_left, apply subset.trans _ this, have := @inf_le _ _ _ _ (λ (x : ℕ), A n ∩ A x) _ hi,
    exact this,  
  rw ← le_iff_subset, apply inf_mono_fun _, intros i hi, rw ← inf_eq_inter, apply @lattice.inf_le_right _ _ (A n) (A i), 
  apply le_inf _, intros i hi, apply subset_inter, apply inter_subset_left, apply subset.trans (inter_subset_right _ _) _, 
  rw ← le_iff_subset, apply inf_le hi
end