-- MIT License

-- Copyright (c) 2021 Luca Ciccone and Luca Padovani

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

import Level

open import Data.Empty
open import Data.Product
open import Data.List using (_∷_; []; _++_)
open import Data.List.Properties using (∷-injectiveʳ)

open import Relation.Unary using (Pred; _⊆_; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Common

module TraceSet {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import Transitions message
open import HasTrace message

TraceSet : Set₁
TraceSet = Pred Trace Level.zero

⟦_⟧ : SessionType -> TraceSet
⟦_⟧ = _HasTrace_

_⊆⊇_ : TraceSet -> TraceSet -> Set
X ⊆⊇ Y = X ⊆ Y × Y ⊆ X

PrefixClosed : TraceSet -> Set
PrefixClosed X = ∀{φ ψ} -> ψ ⊑ φ -> X φ -> X ψ

Coherent : TraceSet -> Set
Coherent X = ∀{φ ψ₁ ψ₂ x y} -> X (φ ++ I x ∷ ψ₁) -> X (φ ++ O y ∷ ψ₂) -> ⊥

_∂_ : TraceSet -> Action -> TraceSet
(X ∂ α) φ = X (α ∷ φ)

--| CO-SETS |--

CoSet : TraceSet -> TraceSet
CoSet X φ = X (co-trace φ)

co-set-involution : ∀{X} -> CoSet (CoSet X) ≡ X
co-set-involution {X} =
  extensionality λ φ -> subst (λ z -> X z ≡ X φ) (sym (co-trace-involution φ)) refl

co-set-⊆ : ∀{X Y} -> X ⊆ Y -> CoSet X ⊆ CoSet Y
co-set-⊆ sub xcφ = sub xcφ

co-set-right->left : ∀{X Y} -> X ⊆ CoSet Y -> CoSet X ⊆ Y
co-set-right->left {X} {Y} sub xcφ with co-set-⊆ {X} {CoSet Y} sub
... | sub' = subst Y (co-trace-involution _) (sub' xcφ)

co-definition : ∀{X φ} -> φ ∈ X -> co-trace φ ∈ CoSet X
co-definition {_} {φ} xφ rewrite co-trace-involution φ = xφ

co-inversion : ∀{X φ} -> co-trace φ ∈ CoSet X -> φ ∈ X
co-inversion {_} {φ} coφ rewrite co-trace-involution φ = coφ

--| COMPLETE TRACES |--

data Complete : TraceSet -> Trace -> Set where
  complete : ∀{X φ} (wit : φ ∈ X) (F : ∀{ψ} -> φ ⊑ ψ -> ψ ∈ X -> ψ ≡ φ) -> Complete X φ

complete-sub : ∀{X} -> Complete X ⊆ X
complete-sub (complete x _) = x

derive-complete : ∀{α φ X} -> α ∷ φ ∈ Complete X -> φ ∈ Complete (X ∂ α)
derive-complete (complete wit F) = complete wit λ le p -> ∷-injectiveʳ (F (some le) p)

input-complete : ∀{x φ f} -> I x ∷ φ ∈ Complete ⟦ inp f ⟧ -> φ ∈ Complete ⟦ f x .force ⟧
input-complete (complete (_ , def , step inp tr) F) =
  complete (_ , def , tr) λ { le tψ -> ∷-injectiveʳ (F (some le) (inp-has-trace tψ)) }

output-complete : ∀{x φ f} -> O x ∷ φ ∈ Complete ⟦ out f ⟧ -> φ ∈ Complete ⟦ f x .force ⟧
output-complete (complete (_ , def , step (out _) tr) F) =
  complete (_ , def , tr) λ { le tψ -> ∷-injectiveʳ (F (some le) (out-has-trace tψ)) }
