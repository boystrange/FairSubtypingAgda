open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Sum

module Examples.Colists.Auxiliary.MaxOf where

  max : ℕ → ℕ → ℕ
  max zero zero = zero
  max zero (suc y) = suc y
  max (suc x) zero = suc x
  max (suc x) (suc y) = suc (max x y)

  max-refl : (x y : ℕ) → (x ≡ max x y) ⊎ (y ≡ max x y)
  max-refl zero zero = inj₂ refl
  max-refl zero (suc y) = inj₂ refl
  max-refl (suc x) zero = inj₁ refl
  max-refl (suc x) (suc y) with max-refl x y
  max-refl (suc x) (suc y) | inj₁ eq = inj₁ (cong (λ x₁ → suc x₁) eq)
  max-refl (suc x) (suc y) | inj₂ eq = inj₂ (cong (λ x₁ → suc x₁) eq)

  max-refl-eq : ∀{x y z} → z ≡ max x y → z ≡ x ⊎ z ≡ y
  max-refl-eq {x} {y} {z} refl with max-refl x y
  max-refl-eq {x} {y} {.(max x y)} refl | inj₁ x₁ = inj₁ (sym x₁)
  max-refl-eq {x} {y} {.(max x y)} refl | inj₂ y₁ = inj₂ (sym y₁)

  max-self : ∀ {n} → n ≡ max n n
  max-self {zero} = refl
  max-self {suc n} = cong (λ x → suc x) max-self

  max-trans : ∀{x y z} → y ≡ max y z → x ≡ max x y → x ≡ max x z
  max-trans {zero} {zero} {zero} _ _ = refl
  max-trans {suc x} {zero} {zero} refl refl = refl
  max-trans {suc x} {suc y} {zero} refl _ = refl
  max-trans {suc x} {suc y} {suc z} eq eq1 =
    let eq-pred = cong pred eq in
    let eq1-pred = cong pred eq1 in
    cong suc (max-trans eq-pred eq1-pred)

  max-comm : ∀{x y z} → x ≡ max y z → x ≡ max z y
  max-comm {x} {zero} {zero} eq = eq
  max-comm {x} {suc y} {zero} eq = eq
  max-comm {x} {zero} {suc z} eq = eq
  max-comm {suc x} {suc y} {suc z} eq = cong suc (max-comm (cong pred eq))