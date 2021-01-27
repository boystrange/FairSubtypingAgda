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
open import Data.Sum
open import Data.List using ([]; _∷_; _∷ʳ_; _++_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)

open import Function.Base using (case_of_)

open import Common

module Convergence {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import Transitions message
open import HasTrace message
open import Session message
open import Subtyping message
open import TraceInclusion message
open import FairCompliance message
open import Divergence message

PreConvergence : (SessionType -> SessionType -> Set) -> SessionType -> SessionType -> Set
PreConvergence rel T S =
  ∀{φ} (tφ : T HasTrace φ) (sφ : ¬ S HasTrace φ) ->
  ∃[ ψ ] ∃[ x ] (ψ ⊑ φ × ∃ λ (tψ : T HasTrace (ψ ∷ʳ O x)) ->
                         ∃ λ (sψ : S HasTrace (ψ ∷ʳ O x)) ->
                         rel (after tψ) (after sψ))

data _↓_ : SessionType -> SessionType -> Set where
  converge : ∀{T S} -> PreConvergence _↓_ T S -> T ↓ S

Convergence : SessionType -> SessionType -> Set
Convergence = PreConvergence _↓_

con-sound : ∀{T S} -> T ↓ S -> ConvergenceS T S
con-sound {T} {S} (converge C) {R} comp with fair-compliance->may-succeed comp
... | (R' # T') , reds , win#def w tdef with unzip-red* reds
... | φ , rr , tr with S HasTrace? φ
... | yes (S' , sdef , sr) = _ , zip-red* rr sr , win#def w sdef
... | no nsφ with C (_ , tdef , tr) nsφ
... | (ψ , x , prefix , tψx , sψx , con)
  with ⊑-has-co-trace prefix (_ , win->defined w , rr) | has-trace-snoc sψx
... | rψ | sψ@(_ , sdef , _) , _ with client-wins-or-accepts-prefix comp rψ tψx
... | inj₁ wψ = _ , zip-traces rψ sψ , win#def wψ sdef
... | inj₂ rψx with zip-traces rψx tψx
... | reds' with con-sound con (fair-compliance-red* comp reds')
... | (_ , reds'' , success) = _ , zip-traces rψx sψx ◅◅ reds'' , success

inclusion->convergence : ∀{T S} -> TraceInclusionS T S -> T ↓ S
inclusion->convergence sub = converge λ tφ nsφ -> ⊥-elim (nsφ (sub tφ))

not-convergence->exclusion : ∀{T S} -> ¬ T ↓ S -> ¬ TraceInclusionS T S
not-convergence->exclusion not sub = not (inclusion->convergence sub)

not-convergence+divergence : ∀{T S} -> T ↓ S -> T ↑ S -> ⊥
not-convergence+divergence (converge F) div =
  let φ = _↑_.trace div in
  let tφ = _↑_.with-trace div in
  let nsφ = _↑_.without-trace div in
  let _ , _ , pre , tψx , sψx , con' = F tφ nsφ in
  let div' = _↑_.divergence div pre tψx sψx in
  not-convergence+divergence con' div'
