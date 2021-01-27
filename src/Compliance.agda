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

open import Data.Empty using (⊥-elim)
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Function.Base using (case_of_)

open import Common

module Compliance {ℙ : Set} (message : Message ℙ)
  where

open import Action message
open import SessionType message
open import Transitions message
open import Session message
open import Progress message

data   Compliance : Session -> Set
record ∞Compliance (S : Session) : Set where
  constructor delay_
  coinductive
  field force : Compliance S
open ∞Compliance public

data Compliance where
  win#def : ∀{T S} (w : Win T) (def : Defined S) -> Compliance (T # S)
  out#inp : ∀{f g} (W : Witness f) (F : ∀{x} (!x : x ∈ dom f) -> ∞Compliance (f x .force # g x .force)) -> Compliance (out f # inp g)
  inp#out : ∀{f g} (W : Witness g) (F : ∀{x} (!x : x ∈ dom g) -> ∞Compliance (f x .force # g x .force)) -> Compliance (inp f # out g)

subject-reduction : ∀{S S'} -> Compliance S -> Reduction S S' -> ∞Compliance S'
force (subject-reduction (win#def (out U) def) (sync {I _} (out !x) s)) = ⊥-elim (U _ !x)
force (subject-reduction (inp#out _ F) (sync inp (out !x))) = F !x .force
force (subject-reduction (out#inp _ F) (sync (out !x) inp)) = F !x .force

subject-reduction* : ∀{S S'} -> Compliance S -> Reductions S S' -> ∞Compliance S'
force (subject-reduction* comp ε) = comp
subject-reduction* comp (red ◅ reds) = subject-reduction* (subject-reduction comp red .force) reds

compliance->progress : ∀{S} -> Compliance S -> Progress S
compliance->progress (win#def w def) = win#def w def
compliance->progress (out#inp W F) = out#inp W
compliance->progress (inp#out W F) = inp#out W

compliance->defined : ∀{T S} -> Compliance (T # S) -> Defined T × Defined S
compliance->defined (win#def (out _) def) = out , def
compliance->defined (out#inp _ _)         = out , inp
compliance->defined (inp#out _ _)         = inp , out

compliance-sound : ∀{S} -> Compliance S -> ComplianceS S
compliance-sound comp reds = progress-sound (compliance->progress (subject-reduction* comp reds .force))

compliance-complete : ∀{S} -> ComplianceS S -> ∞Compliance S
force (compliance-complete {T # S} spec) with spec ε
... | inj₁ (win#def w def) = win#def w def
... | inj₂ (_ , sync inp (out !x)) =
  inp#out (_ , !x) λ !x -> compliance-complete λ reds -> spec (sync inp (out !x) ◅ reds)
... | inj₂ (_ , sync (out !x) inp) =
  out#inp (_ , !x) λ !x -> compliance-complete λ reds -> spec (sync (out !x) inp ◅ reds)
