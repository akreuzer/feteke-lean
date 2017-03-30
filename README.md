# Feteke's Lemma

Let X(n) be a sequence of &reals;.
This sequence is called  *subadditive* if &forall; n,m (n &lt; m &rightarrow; X(n+m) &les; X(n)+X(m)).

Feteke's lemma is the statement that for a subadditive sequence X(n),
the infimum and the limit of the the sequence X(n)/n are equal.
This should be understood in the way, that if one of them exists the other exists, too.

For more details see [Wikipedia|Subadditivity](https://en.wikipedia.org/wiki/Subadditivity).
Feteke's lemma is the main ingredient for *Kingman's Subadditive Ergodic Theorem*.

# Formal proof

The formal proof was developed in [LEAN 0.2](https://leanprover.github.io/).

ak_utils.lean contains proofs of some facts which might be useful in other proofs, too.
ak_compat.lean contains some fact from an earlier version of lean on which this proof depends.

&copy; [Alexander Kreuzer](http://aleph.one/matkaps) 2016, 2017

Old address (https://akreuzer@gitlab.com/akreuzer/feteke-lean.git)

