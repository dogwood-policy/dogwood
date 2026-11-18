/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

macro "unfold_applicative" : tactic => do
  `(tactic | (
  unfold Seq.seq
  unfold Applicative.toSeq
  unfold Alternative.toApplicative
  unfold instAlternativeOption
  simp
  unfold Monad.toApplicative
  unfold instMonadOption
  simp
  ))

public theorem applicative_none  {α β : Type} (f : Option (α → β)) (o : Option α) :
  f = none →
  f <*> o = none
  := by
  intros h
  rw [h]
  unfold_applicative

public theorem applicative_of_none {α β : Type} (f : Option (α → β )) (o : Option α) :
  o = none →
  f <*> o = none
  := by
  intros h
  rw [h]
  unfold_applicative

public theorem applicative_some {α β : Type} (f' : α → β) (v : α) :
  (some f') <*> (some v) = some (f' v)
  := by
  unfold_applicative

public theorem applicative_step {α β : Type} (f : α →  β) (x : α) :
  (some f) <*> (some x) = some (f x)
  := by
  apply applicative_some
  repeat rfl
