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

open import Data.Empty
open import Data.Product
open import Data.List using ([]; _∷_; _++_)

open import Relation.Nullary
open import Relation.Unary using (_⊆_)
open import Relation.Nullary.Negation using (contraposition)

open import Common

module TraceInclusion {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import Transitions message
open import Session message
open import Subtyping message
open import HasTrace message
open import TraceSet message

TraceInclusionS : SessionType -> SessionType -> Set
TraceInclusionS T S = ⟦ T ⟧ ⊆ ⟦ S ⟧

TraceExclusionS : SessionType -> SessionType -> Set
TraceExclusionS T S = ∃[ φ ] (T HasTrace φ × ¬ S HasTrace φ)

nil<=any : ∀{T} -> TraceInclusionS nil T
nil<=any (_ , () , refl)
nil<=any (_ , _ , step () _)

end<=def : ∀{T S} -> End T -> Defined S -> TraceInclusionS T S
end<=def e def (_ , tdef , refl) = _ , def , refl
end<=def (inp U) _ (_ , tdef , step inp tr) = ⊥-elim (U _ (transitions+defined->defined tr tdef))
end<=def (out U) _ (_ , tdef , step (out !x) _) = ⊥-elim (U _ !x)

inclusion-preserves-success : ∀{T S} -> TraceInclusionS T S -> ImplyS MaySucceed T S
inclusion-preserves-success spec ((R' # T') , reds , win#def w def) =
  let as , rr , tr = unzip-red* reds in
  let (S' , def' , sr) = spec (_ , def , tr) in
  _ , zip-red* rr sr , win#def w def'

input-excluded-trace :
  ∀{f : Continuation}{x as}
  (ntr : ¬ inp f HasTrace (I x ∷ as)) ->
  ¬ f x .force HasTrace as
input-excluded-trace ntr (_ , def , tr) = ntr (_ , def , step inp tr)

output-excluded-trace :
  ∀{f x as}
  (ntr : ¬ out f HasTrace (O x ∷ as)) ->
  ¬ f x .force HasTrace as
output-excluded-trace {f} {x} ntr (_ , def , tr) with x ∈? f
... | yes fx = ntr (_ , def , step (out fx) tr)
output-excluded-trace {_} {_} _ (_ , def , refl) | no nfx = ⊥-elim (nfx def)
output-excluded-trace {_} {_} _ (_ , _ , step t _) | no nfx = ⊥-elim (nfx (transition->defined t))

has-trace-input : ∀{f x as} -> inp f HasTrace (I x ∷ as) -> f x .force HasTrace as
has-trace-input (_ , def , step inp tr) = _ , def , tr

has-trace-output : ∀{f x as} -> out f HasTrace (O x ∷ as) -> f x .force HasTrace as
has-trace-output (_ , def , step (out _) tr) = _ , def , tr
