# Feteke's Lemma

Let X(n) be a sequence of &reals;.
This sequence is called  *subadditive* if &forall; n,m (n &lt; m &rightarrow; X(n+m) &les; X(n)+X(m)).

Feteke's lemma is the statement that for a subadditive sequence X(n),
the infimum and the limit of the the sequence X(n)/n are equal.
This should be understood in the way, that if one of them exists the other exists, too.

For more details see [Wikipedia|Subadditivity](https://en.wikipedia.org/wiki/Subadditivity)
Feteke's lemma is the main ingredient for *Kingman's Subadditive Ergodic Theorem*.

# Formal proof

The formal proof was developed in [LEAN](https://leanprover.github.io/).
To the date it just features the difficult direction, i.e., the infimum is already the limit of the sequence.

ak_utils.lean contains proofs of some facts which might be useful in other proofs, too.

&copy; [Alexander Kreuzer](http://aleph.one/matkaps) 2016
