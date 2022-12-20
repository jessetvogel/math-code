# Grothendieck ring

In mathematics, the Grothendieck ring of varieties is an algebraic ring. It is defined as the quotient of the free abelian group on the set of isomorphism classes of varieties over a field k​, by relations of the form [X] = [X - Z] + [Z], where Z is a closed subvariety of X. Multiplication is distributively induced by [X] ∙ [Y] = [ (X × Y)<sub>red</sub> ].

This repository contains (Python) code to compute classes of complex varieties, in terms of the class of the affine line q = [ A<sup>1</sup><sub>C</sub> ]. As an example, the class of the variety X = { (x, y) in C<sup>2</sup> : xy = 1 and x ≠ 3 } would be computed using the following code.

```python
import sympy as sp

x, y = sp.symbols('x, y')

system = System([ x, y ], [ x*y - 1 ], [ x - 3 ])

solver = Solver()
solver.compute_grothendieck_class(system)
```

The output will be `q - 2`, as expected.