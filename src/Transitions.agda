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

open import Data.Product
open import Data.List using ([]; _∷_; _∷ʳ_)

open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.HeterogeneousEquality as Het

open import Common

module Transitions {ℙ : Set} (message : Message ℙ)
  where

open import SessionType message
open import Trace message

data Transition : SessionType -> Action -> SessionType -> Set where
  inp : ∀{f x}                 -> Transition (inp f) (I x) (f x .force)
  out : ∀{f x} (!x : x ∈ dom f) -> Transition (out f) (O x) (f x .force)

data Transitions : SessionType -> Trace -> SessionType -> Set where
  refl : ∀{T} -> Transitions T [] T
  step : ∀{T α T' φ T''} (t : Transition T α T') (tr : Transitions T' φ T'') -> Transitions T (α ∷ φ) T''

transition->defined : ∀{T a S} -> Transition T a S -> Defined T
transition->defined inp     = inp
transition->defined (out _) = out

output-transition->defined : ∀{T x S} -> Transition T (O x) S -> Defined S
output-transition->defined (out !x) = !x

output-transitions->defined : ∀{T φ x S} -> Transitions T (φ ∷ʳ O x) S -> Defined S
output-transitions->defined {_} {[]} (step (out fx) refl) = fx
output-transitions->defined {_} {_ ∷ _} (step _ tr) = output-transitions->defined tr

unsnoc-transitions : ∀{T φ α S} -> Transitions T (φ ∷ʳ α) S -> ∃[ R ] (Transitions T φ R × Transition R α S)
unsnoc-transitions {_} {[]} (step t refl) = _ , refl , t
unsnoc-transitions {_} {x ∷ φ} (step t tr) with unsnoc-transitions tr
... | _ , sr , s = _ , step t sr , s

transitions+defined->defined : ∀{T as S} -> Transitions T as S -> Defined S -> Defined T
transitions+defined->defined refl def = def
transitions+defined->defined (step t _) _ = transition->defined t

transitions-eq : ∀{T T' T'' φ} (tr : Transitions T φ T') (sr : Transitions T φ T'') ->
  T' ≡ T'' × tr Het.≅ sr
transitions-eq refl refl = refl , Het.refl
transitions-eq (step inp tr) (step inp sr) with transitions-eq tr sr
... | refl , Het.refl = refl , Het.refl
transitions-eq (step (out fx) tr) (step (out gx) sr) with Defined-eq fx gx | transitions-eq tr sr
... | refl | refl , Het.refl = refl , Het.refl
