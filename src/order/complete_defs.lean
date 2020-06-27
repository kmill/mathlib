import order.boolean_algebra

universes u v

variables {α : Type u} {ι : Sort v}

open set

set_option old_structure_cmd true

/-- class for the `Sup` operator -/
class has_Sup (α : Type u) := (Sup : set α → α)
/-- class for the `Inf` operator -/
class has_Inf (α : Type u) := (Inf : set α → α)

export has_Sup (Sup)
export has_Inf (Inf)

/-- Supremum of a set -/
add_decl_doc has_Sup.Sup
/-- Infimum of a set -/
add_decl_doc has_Inf.Inf

/-- Indexed supremum -/
def supr [has_Sup α] (s : ι → α) : α := Sup (range s)
/-- Indexed infimum -/
def infi [has_Inf α] (s : ι → α) : α := Inf (range s)

notation `⨆` binders `, ` r:(scoped f, supr f) := r
notation `⨅` binders `, ` r:(scoped f, infi f) := r

set_option default_priority 100 -- see Note [default priority]

/-- A complete lattice is a bounded lattice which
  has suprema and infima for every subset. -/
class complete_lattice (α : Type u) extends bounded_lattice α, has_Sup α, has_Inf α :=
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class complete_linear_order (α : Type u) extends complete_lattice α, decidable_linear_order α

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice α extends complete_lattice α :=
(infi_sup_le_sup_Inf : ∀a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)
(inf_Sup_le_supr_inf : ∀a s, a ⊓ Sup s ≤ (⨆ b ∈ s, a ⊓ b))

@[priority 100] -- see Note [lower instance priority]
instance complete_distrib_lattice.bounded_distrib_lattice [d : complete_distrib_lattice α] :
  bounded_distrib_lattice α :=
{ le_sup_inf := λ x y z, by rw [← Inf_pair, ← Inf_pair, sup_Inf_eq, ← Inf_image, set.image_pair],
  ..d }


class complete_boolean_algebra α extends boolean_algebra α, complete_distrib_lattice α
