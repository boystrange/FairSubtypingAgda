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

open import Level

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List using (List)

open import Relation.Nullary
open import Relation.Unary using (Pred; _∈_; _⊆_; Empty; Satisfiable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common

module SessionType {ℙ : Set} (message : Message ℙ)
  where

data    SessionType : Set
record ∞SessionType : Set where
  constructor box_
  coinductive
  field force : SessionType
open ∞SessionType public

Continuation : Set
Continuation = ℙ -> ∞SessionType

data SessionType where
  nil : SessionType
  inp : (f : Continuation) -> SessionType
  out : (f : Continuation) -> SessionType

data Defined : SessionType -> Set where
  inp : ∀{f} -> Defined (inp f)
  out : ∀{f} -> Defined (out f)

Defined? : (T : SessionType) -> Dec (Defined T)
Defined? nil     = no λ ()
Defined? (inp _) = yes inp
Defined? (out _) = yes out

Defined-eq : ∀{T : SessionType} (p : Defined T) (q : Defined T) -> p ≡ q
Defined-eq inp inp = refl
Defined-eq out out = refl

dom : Continuation -> Pred ℙ Level.zero
dom f x = Defined (f x .force)

_∈?_ : (x : ℙ) (f : Continuation) -> Dec (x ∈ dom f)
x ∈? f with f x .force
... | nil   = no λ ()
... | inp _ = yes inp
... | out _ = yes out

EmptyContinuation : Continuation -> Set
EmptyContinuation f = Empty (dom f)

Witness : Continuation -> Set
Witness f = Satisfiable (dom f)

Empty? : (f : Continuation) -> EmptyContinuation f ⊎ Witness f
Empty? f with excluded-middle {Witness f}
... | yes w = inj₂ w
... | no nw = inj₁ λ x def -> nw (x , def)

-- WARNING: Win and End must be different predicates, because
-- client-wise they are different, whereas Server-wise they are
-- equivalent. inp cannot be End or else an ended client may receive
-- a message and fail!

data Win : SessionType -> Set where
  out : ∀{f} (U : EmptyContinuation f) -> Win (out f)

data End : SessionType -> Set where
  inp : ∀{f} (U : EmptyContinuation f) -> End (inp f)
  out : ∀{f} (U : EmptyContinuation f) -> End (out f)

win : SessionType
win = out λ _ -> λ where .force -> nil

Win-win : Win win
Win-win = out λ { _ () }

win->defined : ∀{T} -> Win T -> Defined T
win->defined (out _) = out

-- if T is not Defined, then it is nil
not-def->nil : ∀{T} → ¬ (Defined T) → T ≡ nil
not-def->nil {nil} nd = refl
not-def->nil {inp f} nd = ⊥-elim (nd inp)
not-def->nil {out f} nd = ⊥-elim (nd out)
