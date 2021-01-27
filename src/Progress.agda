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
open import Data.Sum

open import Common

module Progress {ℙ : Set} (message : Message ℙ)
  where

open import SessionType message
open import Transitions message
open import Session message

data Progress : Session -> Set where
  win#def : ∀{T S} (w : Win T) (def : Defined S) -> Progress (T # S)
  inp#out : ∀{f g} (W : Witness g) -> Progress (inp f # out g)
  out#inp : ∀{f g} (W : Witness f) -> Progress (out f # inp g)

progress-sound : ∀{S} -> Progress S -> ProgressS S
progress-sound (win#def e def) = inj₁ (win#def e def)
progress-sound (inp#out (_ , !x)) = inj₂ (_ , sync inp (out !x))
progress-sound (out#inp (_ , !x)) = inj₂ (_ , sync (out !x) inp)

progress-complete : ∀{S} -> ProgressS S -> Progress S
progress-complete (inj₁ (win#def e def)) = win#def e def
progress-complete (inj₂ (_ , sync inp (out !x))) = inp#out (_ , !x)
progress-complete (inj₂ (_ , sync (out !x) inp)) = out#inp (_ , !x)
