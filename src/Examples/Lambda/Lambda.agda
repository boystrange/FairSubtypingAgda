open import Data.Nat
open import Data.Fin

module Examples.Lambda.Lambda where

  {- Terms & Values -}
  data Term (n : ℕ) : Set where
    var : Fin n → Term n
    lambda : Term (suc n) → Term n
    app : Term n → Term n → Term n

  data Value : Set where
    lambda : Term 1 → Value

  term : Value → Term 0
  term (lambda x) = lambda x

  {- Substitution -}
  ext : ∀{n m} → (Fin n → Fin m) → (Fin (suc n) → Fin (suc m))
  ext f zero = zero
  ext f (suc n) = suc (f n)

  rename : ∀{n m} → (Fin n → Fin m) → (Term n → Term m)
  rename f (var x) = var (f x)
  rename f (lambda t) = lambda (rename (ext f) t)
  rename f (app t t₁) = app (rename f t) (rename f t₁)

  exts : ∀{n m} → (Fin n → Term m) → (Fin (suc n) → Term (suc m))
  exts _ zero = var zero
  exts f (suc n) = rename suc (f n)

  subst : ∀{n m} → (Fin n → Term m) → (Term n → Term m)
  subst f (var x) = f x
  subst f (lambda t) = lambda (subst (exts f) t)
  subst f (app t t₁) = app (subst f t) (subst f t₁)

  subst-0 : ∀{n} → Term (suc n) → Term n → Term n
  subst-0 {n} t t₁ = subst {suc n}{n} f t where
    f : Fin (suc n) → Term n
    f zero = t₁
    f (suc n) = var n