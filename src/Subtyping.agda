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

open import Function.Base using (case_of_)

open import Common

module Subtyping {ℙ : Set} (message : Message ℙ)
  where

open Message message

open import Trace message
open import SessionType message
open import Transitions message
open import Session message
open import Compliance message
open import HasTrace message

data Sub : SessionType -> SessionType -> Size -> Set where
  nil<:any : ∀{T i} -> Sub nil T i
  end<:def : ∀{T S i} (e : End T) (def : Defined S) -> Sub T S i
  inp<:inp : ∀{f g i}                 (inc : dom f ⊆ dom g) (F : (x : ℙ) -> Thunk (Sub (f x .force) (g x .force)) i) -> Sub (inp f) (inp g) i
  out<:out : ∀{f g i} (W : Witness g) (inc : dom g ⊆ dom f) (F : ∀{x} (!x : x ∈ dom g) -> Thunk (Sub (f x .force) (g x .force)) i) -> Sub (out f) (out g) i

_<:_ : SessionType -> SessionType -> Set
_<:_ T S = Sub T S ∞

sub-defined : ∀{T S} -> T <: S -> Defined T -> Defined S
sub-defined (end<:def _ def) _ = def
sub-defined (inp<:inp _ _) _   = inp
sub-defined (out<:out _ _ _) _ = out

sub-sound : ∀{T S R} -> Compliance (R # T) -> T <: S -> ∞Compliance (R # S)
force (sub-sound (win#def w def) sub) = win#def w (sub-defined sub def)
force (sub-sound (out#inp (_ , !x) F) (end<:def (inp U) def)) with U _ (proj₂ (compliance->defined (F !x .force)))
... | ()
force (sub-sound (out#inp (_ , !x) F) (inp<:inp _ G)) =
  out#inp (_ , !x) λ !x -> sub-sound (F !x .force) (G _ .force)
force (sub-sound (inp#out (_ , !x) F) (end<:def (out U) def)) = ⊥-elim (U _ !x)
force (sub-sound (inp#out (_ , !x) F) (out<:out {f} {g} (_ , !y) inc G)) =
  inp#out (_ , !y) λ !x -> sub-sound (F (inc !x) .force) (G !x .force)

SubtypingQ : SessionType -> SessionType -> Set
SubtypingQ T S = ∀{R} -> Compliance (R # T) -> Compliance (R # S)

if-eq : ℙ -> SessionType -> SessionType -> Continuation
force (if-eq x T S y) with x ?= y
... | yes _ = T
... | no _  = S

input* : SessionType
input* = inp λ _ -> λ where .force -> win

input : ℙ -> SessionType -> SessionType -> SessionType
input x T S = inp (if-eq x T S)

input*-but : ℙ -> SessionType
input*-but x = input x nil win

output : ℙ -> SessionType -> SessionType -> SessionType
output x T S = out (if-eq x T S)

input-if-eq-comp :
  ∀{f x T} ->
  Compliance (T # f x .force) ->
  ∀{y} (!y : y ∈ dom f) ->
  ∞Compliance (if-eq x T win y .force # f y .force)
force (input-if-eq-comp {_} {x} comp {y} !y) with x ?= y
... | yes refl = comp
... | no neq = win#def Win-win !y

output-if-eq-comp :
  ∀{f : Continuation}{x}{T} ->
  Compliance (T # f x .force) ->
  ∀{y} (!y : y ∈ dom (if-eq x T nil)) ->
  ∞Compliance (if-eq x T nil y .force # f y .force)
force (output-if-eq-comp {_} {x} comp {y} !y) with x ?= y
... | yes refl = comp
force (output-if-eq-comp {_} {x} comp {y} ()) | no neq

input*-comp : ∀{f} (W : Witness f) -> Compliance (input* # out f)
input*-comp W = inp#out W λ !x -> λ where .force -> win#def Win-win !x

input*-but-comp :
  ∀{f x}
  (W : Witness f)
  (N : ¬ x ∈ dom f) ->
  Compliance (input*-but x # out f)
input*-but-comp {f} {x} W N = inp#out W aux
  where
    aux : ∀{y : ℙ} -> (fy : y ∈ dom f) -> ∞Compliance (if-eq x nil win y .force # f y .force)
    force (aux {y} fy) with x ?= y
    ... | yes refl = ⊥-elim (N fy)
    ... | no neq = win#def Win-win fy

∈-output-if-eq : ∀{R} (x : ℙ) -> Defined R -> x ∈ dom (if-eq x R nil)
∈-output-if-eq x def with x ?= x
... | yes refl = def
... | no neq = ⊥-elim (neq refl)

input-comp : ∀{g x R} -> Compliance (R # g x .force) -> Compliance (input x R win # out g)
input-comp {g} {x} comp = inp#out (x , proj₂ (compliance->defined comp)) (input-if-eq-comp {g} comp)

output-comp : ∀{f x R} -> Compliance (R # f x .force) -> Compliance (output x R nil # inp f)
output-comp {f} {x} comp = out#inp (_ , ∈-output-if-eq x (proj₁ (compliance->defined comp))) (output-if-eq-comp {f} comp)

sub-inp-inp :
  ∀{f g}
  (spec : SubtypingQ (inp f) (inp g))
  (x : ℙ) ->
  SubtypingQ (f x .force) (g x .force)
sub-inp-inp spec x comp with spec (output-comp comp)
... | win#def (out U) def = ⊥-elim (U _ (∈-output-if-eq x (proj₁ (compliance->defined comp))))
... | out#inp (y , fy) F with F fy .force
... | comp' with x ?= y
... | yes refl = comp'
sub-inp-inp spec x comp | out#inp (y , fy) F | win#def () def | no neq

sub-out-out :
  ∀{f g}
  (spec : SubtypingQ (out f) (out g)) ->
  ∀{x} -> x ∈ dom g ->
  SubtypingQ (f x .force) (g x .force)
sub-out-out spec {x} gx comp with spec (input-comp comp)
... | inp#out W F with F gx .force
... | comp' with x ?= x
... | yes refl = comp'
... | no neq = ⊥-elim (neq refl)

sub-out->def :
  ∀{f g}
  (spec : SubtypingQ (out f) (out g))
  (Wf : Witness f) ->
  ∀{x} (gx : x ∈ dom g) ->
  x ∈ dom f
sub-out->def {f} spec Wf {x} gx with x ∈? f
... | yes fx = fx
... | no nfx with spec (input*-but-comp Wf nfx)
... | inp#out W F with F gx .force
... | res with x ?= x
sub-out->def {f} spec Wf {x} gx | no nfx | inp#out W F | win#def () def | yes refl
... | no neq = ⊥-elim (neq refl)

sub-inp->def : ∀{f g} (spec : SubtypingQ (inp f) (inp g)) -> ∀{x} (fx : x ∈ dom f) -> x ∈ dom g
sub-inp->def {f} spec {x} fx with spec {output x win nil} (output-comp (win#def Win-win fx))
... | win#def (out U) def = ⊥-elim (U _ (∈-output-if-eq x out))
... | out#inp W F with F (∈-output-if-eq x out) .force
... | comp = proj₂ (compliance->defined comp)

sub-complete : ∀{T S i} -> SubtypingQ T S -> Thunk (Sub T S) i
force (sub-complete {nil} {_} spec) = nil<:any
force (sub-complete {inp f} {nil} spec) with spec {win} (win#def Win-win inp)
... | win#def _ ()
force (sub-complete {inp _} {inp _} spec) = inp<:inp (sub-inp->def spec) λ x -> sub-complete (sub-inp-inp spec x)
force (sub-complete {inp f} {out _} spec) with Empty? f
... | inj₁ U = end<:def (inp U) out
... | inj₂ (x , ?x) with spec {output x win nil} (output-comp (win#def Win-win ?x))
... | win#def (out U) def = ⊥-elim (U x (∈-output-if-eq x out))
force (sub-complete {out f} {nil} spec) with spec {win} (win#def Win-win out)
... | win#def _ ()
force (sub-complete {out f} {inp _} spec) with Empty? f
... | inj₁ U = end<:def (out U) inp
... | inj₂ W with spec {input*} (input*-comp W)
... | win#def () _
force (sub-complete {out f} {out g} spec) with Empty? f
... | inj₁ Uf = end<:def (out Uf) out
... | inj₂ Wf with Empty? g
... | inj₂ Wg = out<:out Wg (sub-out->def spec Wf) λ !x -> sub-complete (sub-out-out spec !x)
... | inj₁ Ug with spec {input*} (input*-comp Wf)
... | inp#out (_ , !x) F = ⊥-elim (Ug _ !x)

SubtypingQ->SubtypingS : ∀{T S} -> SubtypingQ T S -> SubtypingS T S
SubtypingQ->SubtypingS spec comp = compliance-sound (spec (compliance-complete comp .force))

SubtypingS->SubtypingQ : ∀{T S} -> SubtypingS T S -> SubtypingQ T S
SubtypingS->SubtypingQ spec comp = compliance-complete (spec (compliance-sound comp)) .force

sub-excluded :
  ∀{T S φ}
  (sub : T <: S)
  (tφ  : T HasTrace φ)
  (nsφ : ¬ S HasTrace φ) ->
  ∃[ ψ ] ∃[ x ]
  (ψ ⊑ φ × T HasTrace ψ × S HasTrace ψ × T HasTrace (ψ ∷ʳ O x) × ¬ S HasTrace (ψ ∷ʳ O x))
sub-excluded nil<:any tφ nsφ = ⊥-elim (nil-has-no-trace tφ)
sub-excluded (end<:def e def) tφ nsφ with end-has-empty-trace e tφ
... | eq rewrite eq = ⊥-elim (nsφ (_ , def , refl))
sub-excluded (inp<:inp inc F) (_ , tdef , refl) nsφ =
  ⊥-elim (nsφ (_ , inp , refl))
sub-excluded (inp<:inp {f} {g} inc F) (_ , tdef , step inp tr) nsφ =
  let ψ , x , pre , tψ , sψ , tψx , nψx = sub-excluded (F _ .force) (_ , tdef , tr) (contraposition inp-has-trace nsφ) in
  _ , _ , some pre , inp-has-trace tψ , inp-has-trace sψ , inp-has-trace tψx , inp-has-no-trace nψx
sub-excluded (out<:out W inc F) (_ , tdef , refl) nsφ =
  ⊥-elim (nsφ (_ , out , refl))
sub-excluded (out<:out {f} {g} W inc F) (_ , tdef , step (out {_} {x} fx) tr) nsφ with x ∈? g
... | yes gx =
  let ψ , x , pre , tψ , sψ , tψx , nψx = sub-excluded (F gx .force) (_ , tdef , tr) (contraposition out-has-trace nsφ) in
  _ , _ , some pre , out-has-trace tψ , out-has-trace sψ , out-has-trace tψx , out-has-no-trace nψx
... | no ngx =
  [] , _ , none , (_ , out , refl) , (_ , out , refl) , (_ , fx , step (out fx) refl) , λ { (_ , _ , step (out gx) _) → ⊥-elim (ngx gx) }

sub-after : ∀{T S φ} (tφ : T HasTrace φ) (sφ : S HasTrace φ) -> T <: S -> after tφ <: after sφ
sub-after (_ , _ , refl) (_ , _ , refl) sub = sub
sub-after tφ@(_ , _ , step inp _) (_ , _ , step inp _) (end<:def e _) with end-has-empty-trace e tφ
... | ()
sub-after (_ , tdef , step inp tr) (_ , sdef , step inp sr) (inp<:inp _ F) =
  sub-after (_ , tdef , tr) (_ , sdef , sr) (F _ .force)
sub-after tφ@(_ , _ , step (out _) _) (_ , _ , step (out _) _) (end<:def e _) with end-has-empty-trace e tφ
... | ()
sub-after (_ , tdef , step (out _) tr) (_ , sdef , step (out gx) sr) (out<:out _ _ F) =
  sub-after (_ , tdef , tr) (_ , sdef , sr) (F gx .force)

sub-simulation :
  ∀{R R' T S S' φ}
  (comp : Compliance (R # T))
  (sub  : T <: S)
  (rr   : Transitions R (co-trace φ) R')
  (sr   : Transitions S φ S') ->
  ∃[ T' ] (Transitions T φ T' × T' <: S')
sub-simulation comp sub refl refl = _ , refl , sub
sub-simulation (win#def (out U) def) sub (step (out hx) rr) (step inp sr) = ⊥-elim (U _ hx)
sub-simulation (out#inp W F) (end<:def (inp U) def) (step (out hx) rr) (step inp sr) with F hx .force
... | comp = ⊥-elim (U _ (proj₂ (compliance->defined comp)))
sub-simulation (out#inp W F) (inp<:inp inc G) (step (out hx) rr) (step inp sr) =
  let _ , tr , sub = sub-simulation (F hx .force) (G _ . force) rr sr in
  _ , step inp tr , sub
sub-simulation (inp#out {h} {f} (_ , fx) F) (end<:def (out U) def) (step inp rr) (step (out gx) sr) with F fx .force
... | comp = ⊥-elim (U _ (proj₂ (compliance->defined comp)))
sub-simulation (inp#out W F) (out<:out W₁ inc G) (step inp rr) (step (out fx) sr) =
  let _ , tr , sub = sub-simulation (F (inc fx) .force) (G fx .force) rr sr in
  _ , step (out (inc fx)) tr , sub
