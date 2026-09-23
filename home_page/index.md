---
usemathjax: true
---

This project formalizes, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), the first chapter of
Peter Gács, *Descriptional Complexity and Randomness*
([arXiv:2105.04704](https://arxiv.org/abs/2105.04704)).

The blueprint below follows his text closely. Statements and proofs are his, reproduced
with the author's permission, and each one carries a link to the corresponding Lean
declaration. Where our formalized statement departs from the printed one, a
**formalization note** says so and explains why.

Chapter 1 is formalized, with no `sorry` and no additional axioms beyond the three
standard ones that Mathlib itself uses. Two results are stated in the blueprint without
being formalized, and show as open nodes in the dependency graph. Clauses (a) and (d) of
Proposition 1.5.5 concern functions of a real variable, a setting this library does not
develop. Theorem 1.6.4, on exact domination, is not proved; the library has the ordinary
domination of every lower semicomputable semimeasure by the universal one, but not that
sharpened form. Five side definitions of Gács's text also have no Lean counterpart,
because nothing formalized depends on them: the universal lower semicomputable function
$S_p$ and its Gödel numbers, simple sets, first shortest descriptions, and the
linear-overhead universal machine used in his proof of Theorem 1.7.4 (the Lean proof
does not need it). Each carries a formalization note in the blueprint saying so.

Useful links:

* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [API documentation]({{ site.url }}/docs/)
* [Source repository](https://github.com/SWaeldchen/kolmogorov-to-AIXI)
* [Zulip chat for Lean](https://leanprover.zulipchat.com/) for coordination

## How to read the dependency graph

Each node is a definition or a statement. Green means formalized in Lean, blue means
stated in the blueprint and ready to be formalized, orange means it still needs
blueprint work. Clicking a node gives its statement, its Lean name, and links into both
the source and the generated documentation.
