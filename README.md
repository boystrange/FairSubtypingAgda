# A Formalization of Fair Subtyping in Agda

This Agda library formalizes the following predicates and relations
on **dependent session types**:

* **weak termination** of a session type T, namely the property that
  it is always possible to terminate the protocol T no matter how
  long it has been carried out;
* **fair compliance** of a session type R with respect to a session
  type T, namely the property that any interaction between two
  processes behaving as R and T can always be extended so as to
  satisfy the process behaving as R without disrupting the process
  behaving as T.
* **fair subtyping** ([Padovani 2013], [Padovani 2016]), a liveness
  preserving refinement relation for session types. In addition to
  satisfying the *safe substitution principle* for session types
  ([Gay Hole 2005]), whereby it is safe to use a session endpoint of
  type T where a session endpoint of type S is expected if T is a
  **subtype** of S, it ensures that any process that is fair
  compliant with T is also fair compliant with S.

The library presents two distinct formalizations of each property: a
"semantic" one, given in terms of the labeled transition system of
session types, and a "syntactic" one, given as a *generalized
inference system* ([Ancona Dagnino Zucca 2017], [Dagnino 2019]) making
use of *corules*.

[Gay Hole 2005]: http://dx.doi.org/10.1007/s00236-005-0177-z
[Ancona Dagnino Zucca 2017]: http://dx.doi.org/10.1007/978-3-662-54434-1\_2
[Dagnino 2019]: http://dx.doi.org/10.23638/LMCS-15(1:26)2019
[Padovani 2013]: http://dx.doi.org/10.1007/978-3-642-39212-2\_34
[Padovani 2016]: http://dx.doi.org/10.1017/S096012951400022X