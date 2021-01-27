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

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Common

module Semantics {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import HasTrace message
open import TraceSet message
open import SessionType message
open import Transitions message

record Semantics (X : TraceSet) : Set where
  field
    closed   : PrefixClosed X
    coherent : Coherent X
open Semantics public

data Classification : TraceSet -> Set where
  emp : ∀{X}   -> X ⊆ ∅        -> Classification X
  eps : ∀{X}   -> X ⊆⊇ ｛ [] ｝ -> Classification X
  inp : ∀{X x} -> I x ∷ [] ∈ X -> Classification X
  out : ∀{X x} -> O x ∷ [] ∈ X -> Classification X

is-emp : ∀{X} -> Semantics X -> [] ∉ X -> X ⊆ ∅
is-emp sem nxε xφ with closed sem none xφ
... | xε = ⊥-elim (nxε xε)

is-eps :
  ∀{X} ->
  Semantics X ->
  (¬ (∃[ x ] (I x ∷ [] ∈ X))) ->
  (¬ (∃[ x ] (O x ∷ [] ∈ X))) ->
  X ⊆ ｛ [] ｝
is-eps sem nix nox {[]} xφ = refl
is-eps sem nix nox {I x ∷ φ} xφ with closed sem (some none) xφ
... | ix = ⊥-elim (nix (x , ix))
is-eps sem nix nox {O x ∷ φ} xφ with closed sem (some none) xφ
... | ox = ⊥-elim (nox (x , ox))

kind? : ∀{X} -> Semantics X -> Classification X
kind? {X} sem with excluded-middle {∃[ x ] (I x ∷ [] ∈ X)}
... | yes (_ , ix) = inp ix
... | no nix with excluded-middle {∃[ x ] (O x ∷ [] ∈ X)}
... | yes (_ , ox) = out ox
... | no nox with excluded-middle {[] ∈ X}
... | yes xε = eps (is-eps sem nix nox , λ { refl -> xε })
... | no nxε = emp (is-emp sem nxε)

sem-sound : (T : SessionType) -> Semantics ⟦ T ⟧
closed (sem-sound T) = ⊑-has-trace
coherent (sem-sound T) = trace-coherence

derive-semantics : ∀{X} -> Semantics X -> (α : Action) -> Semantics (X ∂ α)
closed (derive-semantics sem _) pre hasφ = closed sem (some pre) hasφ
coherent (derive-semantics {X} sem γ) {φ} {α} {β} hasφα hasφβ = coherent {X} sem {γ ∷ φ} hasφα hasφβ

co-semantics : ∀{X} -> Semantics X -> Semantics (CoSet X)
closed (co-semantics sem) le coφ = closed sem (⊑-co-trace le) coφ
coherent (co-semantics sem) {φ} {ψ₁} {ψ₂} {x} {y} iφx oφx
  rewrite co-trace-++ φ (I x ∷ ψ₁) | co-trace-++ φ (O y ∷ ψ₂) =
  coherent sem {co-trace φ} {co-trace ψ₂} {co-trace ψ₁} {y} {x} oφx iφx

non-empty-semantics-contains-[] : ∀{X : TraceSet}{φ} -> Semantics X -> φ ∈ X -> [] ∈ X
non-empty-semantics-contains-[] sem w = closed sem none w

decode : ∀{X} -> Semantics X -> ∞SessionType
force (decode sem) with kind? sem
... | emp _ = nil
... | eps _ = win
... | inp _ = inp λ x -> decode (derive-semantics sem (I x))
... | out _ = out λ x -> decode (derive-semantics sem (O x))

decode-sub : ∀{X} (sem : Semantics X) -> ⟦ decode sem .force ⟧ ⊆ X
decode-sub sem tφ with kind? sem
decode-sub _ (_ , () , refl) | emp _
decode-sub _ (_ , _ , step () _) | emp _
decode-sub _ (_ , _ , refl) | eps (_ , sup) = sup refl
decode-sub _ (_ , _ , step (out ()) _) | eps _
decode-sub sem (_ , _ , refl) | inp w = non-empty-semantics-contains-[] sem w
decode-sub sem (_ , def , step inp tr) | inp w =
  decode-sub (derive-semantics sem (I _)) (_ , def , tr)
decode-sub sem (_ , _ , refl) | out w = non-empty-semantics-contains-[] sem w
decode-sub sem (_ , def , step (out !x) tr) | out w =
  decode-sub (derive-semantics sem (O _)) (_ , def , tr)

decode-sup : ∀{X} (sem : Semantics X) -> X ⊆ ⟦ decode sem .force ⟧
decode-sup sem {φ} hasφ with kind? sem
... | emp sub = ⊥-elim (sub hasφ)
... | eps (sub , _) rewrite sym (sub hasφ) = _ , out , refl
decode-sup sem {[]} hasφ | inp _ = _ , inp , refl
decode-sup sem {I _ ∷ _} hasφ | inp _ =
  let _ , def , tr = decode-sup (derive-semantics sem (I _)) hasφ in
  _ , def , step inp tr
decode-sup sem {O _ ∷ _} hasφ | inp w = ⊥-elim (coherent sem {[]} w hasφ)
decode-sup sem {[]} hasφ | out _ = _ , out , refl
decode-sup sem {I _ ∷ _} hasφ | out w = ⊥-elim (coherent sem {[]} hasφ w)
decode-sup sem {O _ ∷ _} hasφ | out _ =
  let _ , def , tr = decode-sup (derive-semantics sem (O _)) hasφ in
  _ , def , step (out (transitions+defined->defined tr def)) tr

decode+complete->win :
  ∀{X φ}
  (sem : Semantics X)
  (rφ : decode sem .force HasTrace φ) ->
  φ ∈ Complete X ->
  Win (after rφ)
decode+complete->win sem rφ comp with kind? sem
decode+complete->win sem (_ , () , refl) comp | emp sub
decode+complete->win sem (_ , _ , step () _) comp | emp sub
decode+complete->win sem (_ , _ , refl) comp | eps _ = Win-win
decode+complete->win sem (_ , _ , step (out ()) _) comp | eps _
decode+complete->win sem (_ , def , refl) (complete _ F) | inp w with F none w
... | ()
decode+complete->win sem (_ , def , step inp tr) comp | inp _ =
  decode+complete->win (derive-semantics sem (I _)) (_ , def , tr) (derive-complete comp)
decode+complete->win sem (_ , def , refl) (complete _ F) | out w with F none w
... | ()
decode+complete->win sem (_ , def , step (out !x) tr) comp | out w =
  decode+complete->win (derive-semantics sem (O _)) (_ , def , tr) (derive-complete comp)

win->complete :
  ∀{T φ ψ} ->
  φ ⊑ ψ ->
  (tφ : T HasTrace φ) ->
  T HasTrace ψ ->
  Win (after tφ) ->
  φ ≡ ψ
win->complete le (_ , tdef , refl) (_ , sdef , refl) w = refl
win->complete le (_ , tdef , refl) (_ , sdef , step (out !x) sr) (out U) = ⊥-elim (U _ !x)
win->complete (some le) (_ , tdef , step inp tr) (_ , sdef , step inp sr) w
  rewrite win->complete le (_ , tdef , tr) (_ , sdef , sr) w = refl
win->complete (some le) (_ , tdef , step (out _) tr) (_ , sdef , step (out _) sr) w
  rewrite win->complete le (_ , tdef , tr) (_ , sdef , sr) w = refl

decode+win->complete :
  ∀{X φ}
  (sem : Semantics X)
  (rφ : decode sem .force HasTrace φ) ->
  Win (after rφ) ->
  φ ∈ Complete X
decode+win->complete {X} {φ} sem rφ w =
  complete (decode-sub sem rφ) λ le xψ -> let rψ = decode-sup sem xψ in
                                          sym (win->complete le rφ rψ w)
