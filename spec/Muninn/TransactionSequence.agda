{-# OPTIONS --safe #-}
module Muninn.TransactionSequence where
import Muninn.OwnedState as O
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

-- Composition is inside one transaction; an abort rolls everything back.
then : ∀ {A : Set} → DB.Transaction A → (A → DB.Transaction A) → DB.Transaction A
then (DB.commit value) next = next value
then (DB.abort value) next = DB.abort value
then (DB.scan inspect) next = DB.scan (λ rows → then (inspect rows) next)
then (DB.eraseRows bound keep body) next = DB.eraseRows bound keep (then body next)
then (DB.read key body) next = DB.read key (λ value → then (body value) next)
then (DB.put key value body) next = DB.put key value (then body next)
then (DB.remove key body) next = DB.remove key (then body next)

committed : ∀ {A : Set} (body : DB.Transaction A) next before result middle →
  DB.evaluate body before ≡ DB.committed result middle →
  DB.evaluate (then body next) before ≡ DB.evaluate (next result) middle
committed (DB.commit value) next before .value .before refl = refl
committed (DB.abort value) next before result middle ()
committed (DB.scan inspect) next before result middle proof = committed (inspect before) next before result middle proof
committed (DB.eraseRows bound keep body) next before result middle proof = committed body next (DB.erase bound keep before) result middle proof
committed (DB.read key body) next before result middle proof = committed (body (DB.lookup key before)) next before result middle proof
committed (DB.put key value body) next before result middle proof = committed body next (DB.write key value before) result middle proof
committed (DB.remove key body) next before result middle proof = committed body next (DB.delete key before) result middle proof
