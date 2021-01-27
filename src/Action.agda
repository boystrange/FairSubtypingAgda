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

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common

module Action {ℙ : Set} (message : Message ℙ)
  where

open Message message

data Action : Set where
  I O : ℙ -> Action

input-injective : ∀{x y} -> I x ≡ I y -> x ≡ y
input-injective refl = refl

output-injective : ∀{x y} -> O x ≡ O y -> x ≡ y
output-injective refl = refl

co-action : Action -> Action
co-action (I x) = O x
co-action (O x) = I x

co-action-injective : ∀{x y} -> co-action x ≡ co-action y -> x ≡ y
co-action-injective {I x} {I .x} refl = refl
co-action-injective {O x} {O .x} refl = refl

co-action-involution : (α : Action) -> co-action (co-action α) ≡ α
co-action-involution (I _) = refl
co-action-involution (O _) = refl

action-equality-dec : (α β : Action) -> Dec (α ≡ β)
action-equality-dec (I x) (I y) with x ?= y
... | yes eq rewrite eq = yes refl
... | no neq = no λ eq -> neq (input-injective eq)
action-equality-dec (I x) (O y) = no λ ()
action-equality-dec (O x) (I y) = no λ ()
action-equality-dec (O x) (O y) with x ?= y
... | yes eq rewrite eq = yes refl
... | no neq = no λ eq -> neq (output-injective eq)
