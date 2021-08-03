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

{-# OPTIONS --guardedness --sized-types #-}

open import Size

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _∷_; _∷ʳ_; _++_)

open import Codata.Thunk

open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (_∈_; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; return)

open import Function.Base using (case_of_)

open import Common

module FairSubtyping {ℙ : Set} (message : Message ℙ) where

open import Trace message
open import SessionType message
open import Transitions message
open import Session message
open import Compliance message
open import HasTrace message
open import TraceInclusion message
open import Convergence message
open import FairCompliance message

data FairSub : SessionType -> SessionType -> Size -> Set where
  nil<|any : ∀{T i} -> FairSub nil T i
  end<|def : ∀{T S i} (e : End T) (def : Defined S) -> FairSub T S i
  inp<|inp :
    ∀{f g i}
    (con : inp f ↓ inp g)
    (inc : dom f ⊆ dom g)
    (F : (x : ℙ) -> Thunk (FairSub (f x .force) (g x .force)) i) ->
    FairSub (inp f) (inp g) i
  out<|out :
    ∀{f g i}
    (con : out f ↓ out g)
    (W : Witness g)
    (inc : dom g ⊆ dom f)
    (F : ∀{x} (!x : x ∈ dom g) -> Thunk (FairSub (f x .force) (g x .force)) i) ->
    FairSub (out f) (out g) i

_<|_ : SessionType -> SessionType -> Set
_<|_ T S = FairSub T S ∞

-- sub-defined : ∀{T S} -> T <| S -> Defined T -> Defined S
-- sub-defined (end<|def _ def) _ = def
-- sub-defined (inp<|inp _ _) _   = inp
-- sub-defined (out<|out _ _ _) _ = out

fs->convergence : ∀{T S} -> T <| S -> T ↓ S
fs->convergence nil<|any = inclusion->convergence nil<=any
fs->convergence (end<|def e def) = inclusion->convergence (end<=def e def)
fs->convergence (inp<|inp con inc F) = con
fs->convergence (out<|out con W inc F) = con

fc-not-transition+end :
  ∀{R R' T α} ->
  FairComplianceS (R # T) ->
  Transition R α R' ->
  End T ->
  ⊥
fc-not-transition+end comp inp (inp U) with comp ε
... | _ , ε , win#def () _
... | _ , sync () inp ◅ _ , _
fc-not-transition+end comp inp (out U) with comp ε
... | _ , ε , win#def () _
... | _ , sync _ (out fx) ◅ _ , _ = ⊥-elim (U _ fx)
fc-not-transition+end comp (out fx) (inp V) with comp ε
... | _ , ε , win#def (out U) _ = ⊥-elim (U _ fx)
... | _ , sync (out _) inp ◅ reds , win#def w def =
  let _ , rr , tr = unzip-red* reds in
  ⊥-elim (V _ (transitions+defined->defined tr def))
fc-not-transition+end comp (out fx) (out _) with comp ε
... | _ , ε , win#def (out U) _ = ⊥-elim (U _ fx)
... | _ , sync () (out _) ◅ _ , _

sub-red :
  ∀{T S S' R R' α} ->
  FairComplianceS (R # T) ->
  T <| S ->
  Transition R (co-action α) R' ->
  Transition S α S' ->
  ∃[ T' ] (Transition T α T' × T' <| S')
sub-red comp nil<|any _ _ with comp ε
... | _ , ε , win#def _ ()
... | _ , sync _ () ◅ _ , _
sub-red comp (end<|def e _) r _ = ⊥-elim (fc-not-transition+end comp r e)
sub-red comp (inp<|inp con inc F) (out {h} hx) (inp {f}) = _ , inp , F _ .force
sub-red comp (out<|out con W inc F) inp (out fx) = _ , out (inc fx) , F fx .force

sub-red* :
  ∀{T S S' R R' φ} ->
  FairComplianceS (R # T) ->
  T <| S ->
  Transitions R (co-trace φ) R' ->
  Transitions S φ S' ->
  ∃[ T' ] (Transitions T φ T' × T' <| S')
sub-red* comp sub refl refl = _ , refl , sub
sub-red* comp sub (step r rr) (step s sr) =
  let _ , t , sub' = sub-red comp sub r s in
  let comp' = fc-transitions (step r refl) (step t refl) comp in
  let _ , tr , sub'' = sub-red* comp' sub' rr sr in
  _ , step t tr , sub''

sub-sound : ∀{T S R} -> FairComplianceS (R # T) -> T <| S -> FairComplianceS (R # S)
sub-sound comp sub {_ # _} reds =
  let _ , rr , sr = unzip-red* reds in
  let _ , tr , sub' = sub-red* comp sub rr sr in
  let comp' = fair-compliance-red* comp (zip-red* rr tr) in
  con-sound (fs->convergence sub') comp'

