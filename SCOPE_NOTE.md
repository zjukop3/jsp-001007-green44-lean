# Scope note for JSP-001007

The current Justin Sun Prize catalog describes JSP-001007 in broad language:
"How many integers can simultaneously avoid about half the residue classes
modulo each of several primes?"

The Lean theorem in this package negates the exact fixed-parameter formulation
of **Ben Green Problem 44**:
1000 increasing primes below `N^(9/10)`, removal of `floor(p/2)` classes modulo
each prime, and the proposed bound `remaining <= N/10`.

Before the prize record is changed to `Lean proof: Yes`, curators should confirm
that this fixed Green-44 formulation is the completed-solution scope selected for
JSP-001007. If the prize requires the more general Erdős #1202 negative theorem,
this package is evidence for the Green-44 case but is not by itself a formalization
of every quantified generalization.
