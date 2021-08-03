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

{-# OPTIONS --guardedness #-}

open import Data.Product
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.List.Properties using (∷-injective)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Common

module Trace {ℙ : Set} (message : Message ℙ)
  where

open import Action message public
open import SessionType message

Trace : Set
Trace = List Action

--| CO-TRACES |--

co-trace : Trace -> Trace
co-trace = Data.List.map co-action

co-trace-involution : (φ : Trace) -> co-trace (co-trace φ) ≡ φ
co-trace-involution [] = refl
co-trace-involution (α ∷ φ) rewrite co-action-involution α | co-trace-involution φ = refl

co-trace-++ : (φ ψ : Trace) -> co-trace (φ ++ ψ) ≡ co-trace φ ++ co-trace ψ
co-trace-++ []      _ = refl
co-trace-++ (α ∷ φ) ψ = cong (co-action α ∷_) (co-trace-++ φ ψ)

co-trace-injective : ∀{φ ψ} -> co-trace φ ≡ co-trace ψ -> φ ≡ ψ
co-trace-injective {[]} {[]} eq = refl
co-trace-injective {x ∷ φ} {x₁ ∷ ψ} eq with ∷-injective eq
... | eq1 , eq2 rewrite co-action-injective eq1 | co-trace-injective eq2 = refl

--| PREFIX RELATION |--

data _⊑_ : Trace -> Trace -> Set where
  none : ∀{φ}     -> [] ⊑ φ
  some : ∀{φ ψ α} -> φ ⊑ ψ -> (α ∷ φ) ⊑ (α ∷ ψ)

⊑-refl : (φ : Trace) -> φ ⊑ φ
⊑-refl [] = none
⊑-refl (_ ∷ φ) = some (⊑-refl φ)

⊑-tran : ∀{φ ψ χ} -> φ ⊑ ψ -> ψ ⊑ χ -> φ ⊑ χ
⊑-tran none _ = none
⊑-tran (some le1) (some le2) = some (⊑-tran le1 le2)

⊑-++ : ∀{φ χ} -> φ ⊑ (φ ++ χ)
⊑-++ {[]} = none
⊑-++ {_ ∷ φ} = some (⊑-++ {φ})

⊑-precong-++ : ∀{φ ψ χ} -> ψ ⊑ χ -> (φ ++ ψ) ⊑ (φ ++ χ)
⊑-precong-++ {[]} le = le
⊑-precong-++ {_ ∷ _} le = some (⊑-precong-++ le)

⊑-co-trace : ∀{φ ψ} -> φ ⊑ ψ -> co-trace φ ⊑ co-trace ψ
⊑-co-trace none = none
⊑-co-trace (some le) = some (⊑-co-trace le)

⊑-trace : ∀{φ ψ} -> ψ ⊑ φ -> ∃[ φ' ] (φ ≡ ψ ++ φ')
⊑-trace {φ} none = φ , refl
⊑-trace {α ∷ φ} (some le) with ⊑-trace le
... | φ' , eq rewrite eq = φ' , refl

absurd-++-≡ : ∀{φ ψ : Trace}{α} -> (φ ++ α ∷ ψ) ≢ []
absurd-++-≡ {[]} ()
absurd-++-≡ {_ ∷ _} ()

absurd-++-⊑ : ∀{φ α ψ} -> ¬ (φ ++ α ∷ ψ) ⊑ []
absurd-++-⊑ {[]} ()
absurd-++-⊑ {_ ∷ _} ()

--| STRICT PREFIX RELATION |--

data _⊏_ : Trace -> Trace -> Set where
  none : ∀{α φ} -> [] ⊏ (α ∷ φ)
  some : ∀{φ ψ α} -> φ ⊏ ψ -> (α ∷ φ) ⊏ (α ∷ ψ)

⊏-irreflexive : ∀{φ} -> ¬ φ ⊏ φ
⊏-irreflexive (some lt) = ⊏-irreflexive lt

⊏-++ : ∀{φ ψ α} -> φ ⊏ (φ ++ (ψ ∷ʳ α))
⊏-++ {[]} {[]} = none
⊏-++ {[]} {_ ∷ _} = none
⊏-++ {_ ∷ φ} = some (⊏-++ {φ})

⊏->≢ : ∀{φ ψ} -> φ ⊏ ψ -> φ ≢ ψ
⊏->≢ (some lt) refl = ⊏-irreflexive lt

⊏->⊑ : ∀{φ ψ} -> φ ⊏ ψ -> φ ⊑ ψ
⊏->⊑ none = none
⊏->⊑ (some lt) = some (⊏->⊑ lt)
