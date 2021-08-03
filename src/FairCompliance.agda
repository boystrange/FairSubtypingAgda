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

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _++_; _∷_; _∷ʳ_)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_; return)

open import Common

module FairCompliance {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import Session message
open import SessionType message
open import Transitions message
open import HasTrace message

fair-compliance-red* : ∀{S S'} -> FairComplianceS S -> Reductions S S' -> FairComplianceS S'
fair-compliance-red* comp reds reds' = comp (reds ◅◅ reds')

fair-compliance->may-succeed : ∀{S} -> FairComplianceS S -> MaySucceed S
fair-compliance->may-succeed fcomp = fcomp ε

fc-after-output :
  ∀{f g x} ->
  FairComplianceS (out f # inp g) ->
  x ∈ dom f ->
  FairComplianceS (f x .force # g x .force)
fc-after-output comp fx reds = comp (sync (out fx) inp ◅ reds)

fc-after-input :
  ∀{f g x} ->
  FairComplianceS (inp f # out g) ->
  x ∈ dom g ->
  FairComplianceS (f x .force # g x .force)
fc-after-input comp gx reds = comp (sync inp (out gx) ◅ reds)

fc-input : ∀{R f} -> FairComplianceS (R # inp f) ->
            Win R ⊎ ∃[ g ] (R ≡ out g × Witness g × (∀{x} (!x : x ∈ dom g) -> FairComplianceS (g x .force # f x .force)))
fc-input {nil} spec with spec ε
... | _ , ε , win#def () _
... | _ , sync () _ ◅ _ , _
fc-input {inp _} spec with spec ε
... | _ , ε , win#def () _
... | _ , sync () inp ◅ _ , _
fc-input {out g} spec with Empty? g
... | inj₁ U = inj₁ (out U)
... | inj₂ W = inj₂ (g , refl , W , λ !x -> fair-compliance-red* spec (return (sync (out !x) inp)))

fc-output : ∀{R f} -> FairComplianceS (R # out f) ->
            Win R ⊎ ∃[ g ] (R ≡ inp g × Witness f × (∀{x} (!x : x ∈ dom f) -> FairComplianceS (g x .force # f x .force)))
fc-output {nil} spec with spec ε
... | _ , ε , win#def () out
... | _ , sync () _ ◅ _ , _
fc-output {inp g} {f} spec with Empty? f
... | inj₂ W = inj₂ (g , refl , W , λ !x -> fair-compliance-red* spec (return (sync inp (out !x))))
... | inj₁ U with spec ε
... | _ , ε , win#def () _
... | _ , sync inp (out !x) ◅ _ , _ = ⊥-elim (U _ !x)
fc-output {out g} spec with Empty? g
... | inj₁ U = inj₁ (out U)
... | inj₂ (_ , !x) with spec ε
... | _ , ε , win#def (out U) out = ⊥-elim (U _ !x)
... | _ , sync () (out _) ◅ _ , _

fc-transitions :
  ∀{R R' T T' φ} ->
  Transitions R (co-trace φ) R' ->
  Transitions T φ T' ->
  FairComplianceS (R # T) ->
  FairComplianceS (R' # T')
fc-transitions rr tr comp = fair-compliance-red* comp (zip-red* rr tr)

fc-trace :
  ∀{R T φ} ->
  FairComplianceS (R # T) ->
  (rφ : R HasTrace (co-trace φ))
  (tφ : T HasTrace φ) ->
  FairComplianceS (after rφ # after tφ)
fc-trace comp (_ , _ , rr) (_ , _ , tr) = fc-transitions rr tr comp

fc-output-trace :
  ∀{R T x} ->
  FairComplianceS (R # T) ->
  T HasTrace (O x ∷ []) ->
  Win R ⊎ (R HasTrace (I x ∷ []))
fc-output-trace {nil} comp tφ with comp ε
... | _ , ε , win#def () _
... | _ , sync () _ ◅ _ , _
fc-output-trace {inp f} {_} {x} comp (_ , _ , step (out gx) refl) with x ∈? f
... | yes fx = inj₂ (_ , fx , step inp refl)
... | no nfx with comp (return (sync inp (out gx)))
... | _ , ε , win#def w _ = ⊥-elim (nfx (win->defined w))
... | _ , sync r _ ◅ _ , _ = ⊥-elim (contraposition transition->defined nfx r)
fc-output-trace {out f} comp (_ , _ , step (out _) refl) with comp ε
... | _ , ε , win#def w _ = inj₁ w
... | _ , sync () (out _) ◅ _ , _

has-trace-snoc :
  ∀{T φ α} -> T HasTrace (φ ∷ʳ α) ->
  ∃ λ (tφ : T HasTrace φ) -> after tφ HasTrace (α ∷ [])
has-trace-snoc {_} {[]} tα@(_ , _ , step inp refl) = (_ , inp , refl) , tα
has-trace-snoc {_} {[]} tα@(_ , _ , step (out _) refl) = (_ , out , refl) , tα
has-trace-snoc {_} {_ ∷ φ} (_ , def , step t tr) =
  let (_ , tdef , sr) , tφ/α = has-trace-snoc (_ , def , tr) in
  (_ , tdef , step t sr) , tφ/α

client-wins-or-accepts-prefix :
  ∀{R T φ x}
  (comp : FairComplianceS (R # T))
  (rφ : R HasTrace (co-trace φ))
  (tφ : T HasTrace (φ ∷ʳ O x)) ->
  Win (after rφ) ⊎ R HasTrace (co-trace (φ ∷ʳ O x))
client-wins-or-accepts-prefix {_} {_} {φ} comp rφ tφα with has-trace-snoc tφα
... | tφ , tφ/α with fc-trace comp rφ tφ
... | comp/φ with fc-output-trace comp/φ tφ/α
... | inj₁ w = inj₁ w
... | inj₂ rφ/α =
  let rφα = join-trace rφ rφ/α in
  inj₂ (subst (_ HasTrace_) (sym (co-trace-++ φ _)) rφα)
