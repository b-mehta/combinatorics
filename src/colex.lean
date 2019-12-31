import data.finset
import data.fintype

variable {α : Type*}

open finset

def colex_order [has_lt α] (A B : finset α) : Prop := ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B
infix ` <ᶜ `:50 := colex_order

lemma colex_hom {β : Type*} [linear_order α] [decidable_eq β] [preorder β] (f : α → β) (h₁ : strict_mono f) (A B : finset α) : 
  image f A <ᶜ image f B ↔ A <ᶜ B :=
begin
  split, 
    rintro ⟨k, z, knotinfa, kinfb⟩,
    rw mem_image at kinfb,
    rcases kinfb with ⟨k', k'inb, fk'⟩,
    refine ⟨k', _, _, k'inb⟩,
    intros x hx, have := (strict_mono.lt_iff_lt h₁).2 hx,
    rw fk' at this, have := z this, 
    { split, any_goals { 
      intro p, have q := mem_image_of_mem f p, 
      rw ← this at q <|> rw this at q,
      rw mem_image at q,
      rcases q with ⟨x', h, z⟩,
      convert h, exact strict_mono.injective h₁ z.symm } }, 
    intro a, apply knotinfa, rw mem_image, exact ⟨k', a, ‹_›⟩, 
  rintro ⟨k, z, knotina, kinb⟩, 
  refine ⟨f k, _, _, _⟩, intros x hx, simp only [mem_image], 
    split; rintro ⟨x', x'in, q⟩,
    refine ⟨x', _, q⟩, 
    rwa ← z _, rw ← strict_mono.lt_iff_lt h₁, rwa q, 
    refine ⟨x', _, q⟩, 
    rwa z _, rw ← strict_mono.lt_iff_lt h₁, rwa q,
  intro, rw mem_image at a, rcases a with ⟨_, _, _⟩,
  apply knotina, rwa ← strict_mono.injective h₁ a_h_h, 
  apply mem_image_of_mem f kinb, 
end

instance [has_lt α] : is_irrefl (finset α) (<ᶜ) := ⟨λ A h, exists.elim h (λ _ q, q.2.1 q.2.2)⟩
instance [linear_order α] : is_trans (finset α) (<ᶜ) := 
begin
  constructor,
  rintros A B C ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  have: k₁ ≠ k₂ := ne_of_mem_of_not_mem inB notinB,
  cases lt_or_gt_of_ne this,
    refine ⟨k₂, _, by rwa k₁z h, inC⟩, 
    intros x hx, rw ← k₂z hx, apply k₁z (trans h hx), 
  refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩, 
  intros x hx, rw k₁z hx, apply k₂z (trans h hx)
end
instance [linear_order α] : is_asymm (finset α) (<ᶜ) := by apply_instance
instance [linear_order α] : is_strict_order (finset α) (<ᶜ) := {}
instance [decidable_linear_order α] : is_trichotomous (finset α) (<ᶜ) :=
begin
  constructor,
  intros A B, 
  set diff := (A \ B) ∪ (B \ A),
  by_cases h: diff = ∅,
    right, left,
    apply subset.antisymm,
    any_goals { rw ← sdiff_eq_empty_iff_subset, rw ← subset_empty, rw ← h }, 
      apply subset_union_left,
    apply subset_union_right,
  set k := max' diff h,
  have := max'_mem diff h, simp only [mem_union, mem_sdiff] at this,
  rcases this with ⟨_, _⟩ | ⟨_, _⟩,
    right, right, swap, left,
  all_goals 
  { refine ⟨k, _, ‹_›, ‹_›⟩,
    intros x hx, by_contra,
    apply not_le_of_lt hx,
    apply le_max', simp only [mem_union, mem_sdiff],
    tauto }
end
instance [decidable_linear_order α] : is_incomp_trans (finset α) (<ᶜ) :=
begin
  constructor,
  rintros A B C ⟨nAB, nBA⟩ ⟨nBC, nCB⟩, 
  have: A = B, apply or.resolve_right (or.resolve_left (trichotomous A B) nAB) nBA, 
  have: B = C, apply or.resolve_right (or.resolve_left (trichotomous B C) nBC) nCB, 
  rw [‹A = B›, ‹B = C›], rw and_self, apply irrefl
end
instance [decidable_linear_order α] : is_strict_weak_order (finset α) (<ᶜ) := {}
instance [decidable_linear_order α] : is_strict_total_order (finset α) (<ᶜ) := {}
instance [decidable_linear_order α] [fintype α] (A B : finset α) : decidable (A <ᶜ B) :=
by rw colex_order; apply_instance
instance colex_decidable_rel [decidable_linear_order α] [fintype α] : decidable_rel ((<ᶜ) : finset α → finset α → Prop) :=
by intros A B; apply_instance