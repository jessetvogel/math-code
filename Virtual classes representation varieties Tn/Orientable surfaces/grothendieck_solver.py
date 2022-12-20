#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sympy as sp
from IPython.display import Math

q = sp.Symbol('q')


# In[2]:


def reduce_equation(eq):
    # Reduce equations, i.e. removing exponents
    f = sp.factor(eq)
    if f.is_Pow:
        return f.base
    if f.is_Mul:
        return sp.Mul(*[ reduce_equation(g) for g in f.args ])
    return eq


# In[6]:


# A System represents an affine variety given by some equations
# System.gens   = list of variables
# System.eqs    = list of equations
# System.op_eqs = list of open equations

class System:
    
    def __init__(self, gens, eqs, op_eqs = []):
        # Defining data
        self.gens = gens
        self.eqs = eqs
        self.op_eqs = op_eqs
        
        # Flags
        self.is_groebner = False
        
    def __repr__(self):
        return f'{self.eqs} - {self.op_eqs} in {self.gens}'
    
    def latex(self):
        if not self.gens:
            return '\\{ \\star \\}'    
        v = f'{sp.latex(tuple(self.gens))} \\in k^{{{str(len(self.gens))}}}'
        e = '' if not self.eqs and not self.op_eqs else '\\;|\\; ' + ','.join([ sp.latex(eq) + ' = 0' for eq in self.eqs ] + [ sp.latex(eq) + ' \\ne 0' for eq in self.op_eqs ])
        return f'\\left\\{{{v} {e}\\right\\}}'
        
    def simplify_equations(self):
        # If there are no generators, we want [] or [1]
        if not self.gens:
            self.eqs = [sp.sympify(1)] if any(eq != 0 for eq in self.eqs) else []
            return
        
        # Reduce equations
        self.eqs = [ reduce_equation(eq) for eq in self.eqs ]
        # Remove zeros
        self.eqs = [ eq for eq in self.eqs if eq != 0 ]
        # Reduce each equation with respect to the others
        # Also, reduce each op_equation with respect to the closed equations
        # This makes only sense to do when there are variables (otherwise sp.reduced fails)
        while True:
            for i, eq in enumerate(self.eqs):
                r = sp.reduced(eq, [ e for j, e in enumerate(self.eqs) if j != i and e != 0 ], self.gens)[1]
                if sp.expand(eq - r) != 0:
                    self.eqs[i] = reduce_equation(r)
                    break
            else:
                break
        
        # Again, remove zeros
        self.eqs = [ eq for eq in self.eqs if eq != 0 ]
        # Reduce the op_eqs
        self.op_eqs = [ sp.reduced(eq, self.eqs, self.gens)[1] for eq in self.op_eqs ]
        
    def factor(self):
        # Decomposes a system which is a product variety into two systems
        # Keep factoring out factors Y based on the equations and op_equations
        factors = []
        eqs = list(self.eqs)
        op_eqs = list(self.op_eqs)
        while eqs or op_eqs:
            # Pick the first equation or opposite equation from the remaining ones
            Y_eqs = []
            Y_op_eqs = []
            Y_gens = []
            if eqs:
                eq = eqs.pop(0)
                Y_eqs.append(eq)
                Y_gens.extend(list(eq.free_symbols))
            else:
                op_eq = op_eqs.pop(0)
                Y_op_eqs.append(op_eq)
                Y_gens.extend(list(op_eq.free_symbols))

            # Find all equations containing variables from Y_vars, which are not yet in Y_eqs
            # Repeat this until no more such equations can be found
            while True:
                new_Y_eqs = [ f for f in eqs if not f.free_symbols.isdisjoint(Y_gens) ]
                new_Y_op_eqs = [ f for f in op_eqs if not f.free_symbols.isdisjoint(Y_gens) ]
                if new_Y_eqs or new_Y_op_eqs:
                    Y_eqs.extend(new_Y_eqs)
                    Y_op_eqs.extend(new_Y_op_eqs)
                    Y_gens = [ x for x in self.gens if any(x in f.free_symbols for f in Y_eqs + Y_op_eqs) ]
                    eqs = [ f for f in eqs if f not in new_Y_eqs ]
                    op_eqs = [ f for f in op_eqs if f not in new_Y_op_eqs ]
                else:
                    break

            factors.append(System(Y_gens, Y_eqs, Y_op_eqs))

        # If there are any free variables left, add them as a factor as well
        for x in self.gens:
            if not any(x in Y.gens for Y in factors):
                factors.append(System([ x ], [], []))

        return factors


# In[19]:


# Tactic takes 'method' which is a method that takes a System as input
# and it outputs an array of decompositions, e.g.
# [ [(q, System), (System,), (q**2 - 1,)], ... ]
# where by a decomposition we mean an array of tuples (X_1, X_2, X_3, ...)
# with each X_i either a System or E-polynomial. Such a tuple represents
# [X_1] * [X_2] * [X_3] * ...

class Tactic:
    
    def __init__(self, name, method):
        self.name = name
        self.method = method
    
    def apply(self, system):
        return self.method(system)


# ### Tactics

# In[8]:


def method_trivial(system):
    # Case empty variety
    if any(eq.is_Number and eq != 0 for eq in system.eqs):
        return [[]]
    
    # Case affine space (no equations at all)
    if len(system.eqs) == 0 and len(system.op_eqs) == 0:
        return [[(q**len(system.gens),)]]
    
    # If there is a zero op_eq, return 0
    if any(eq == 0 for eq in system.op_eqs):
        return [[]]
    
    return []

tactic_trivial = Tactic('', method_trivial)


# In[6]:


def method_linearity(system):
    # Search for equations of the form x = ... for some variable x
    for x in system.gens:
        for eq in system.eqs:
            # eq should be linear in x
            if sp.degree(eq, gen = x) != 1:
                continue
            
            # Write eq = x * u + v
            [u], v = sp.reduced(eq, [x])
            
            # For this method we want u to be constant, so that we can directly solve for x
            if not u.is_Number:
                continue

            # Substitute x = -v/u and remove x from vars
            new_eqs = [ f.subs(x, -v/u) for f in system.eqs if f != eq ]
            new_op_eqs = [ f.subs(x, -v/u) for f in system.op_eqs ]
            new_vars = [ y for y in system.gens if y != x ]
            return [[ (System(new_vars, new_eqs, new_op_eqs),) ]] # Note: simple substitutions can be returned immediately, there should be no harm in doing them!
    
    # Search for equations of the form x*u + v = 0 with u and v not divisible by x
    # Then distinguish cases u = 0 and u != 0
    for x in system.gens:
        for eq in system.eqs:
            # eq should be linear in x
            if sp.degree(eq, gen = x) != 1:
                continue

            # Write eq = x * u + v
            [u], v = sp.reduced(eq, [x])
            
            # Case 1: u = 0 and v = 0
            case_1 = System(system.gens, [ u, v ] + [ f for f in system.eqs if f != eq ], system.op_eqs)
            
            # Case 2: u != 0 and x = -v/u
            case_2_vars = [ y for y in system.gens if y != x ]
            case_2_eqs = [ sp.Poly(f, x).transform(sp.Poly(-v, x), sp.Poly(u, x)).expr for f in system.eqs if f != eq ]
            case_2_op_eqs = [ sp.Poly(f, x).transform(sp.Poly(-v, x), sp.Poly(u, x)).expr for f in system.op_eqs] + [ u ]
            case_2 = System(case_2_vars, case_2_eqs, case_2_op_eqs)
            
            return [[ (case_1,), (case_2,) ]]
            
    return []

tactic_linearity = Tactic('linearity', method_linearity)


# In[7]:


def method_factor(system):
    for eq in system.eqs:
        # Try to factor each equation. The factorization must have at least two factors
        # that are polynomials of degree > 0.
        eq_factored = sp.factor(eq)
        if not eq_factored.is_Mul:
            continue
        factors = [ f for f in eq_factored.args if sp.total_degree(f, *system.gens) > 0]
        if len(factors) <= 1:
            continue
        
        # Can decompose eq = u * v where u is the first factor, and v the product of all other factors
        u, v = factors[0], sp.Mul(*(factors[1:]))
        
        new_eqs = [ e for e in system.eqs if e != eq ]
        return [[
            (System(system.gens, [ u ] + new_eqs, system.op_eqs),), # Case 1: u = 0
            (System(system.gens, [ v ] + new_eqs, system.op_eqs + [ u ]),), # Case 2: u != 0 and v = 0
        ]]
    
    return []

tactic_factor = Tactic('factor', method_factor)


# In[10]:


def method_product(system):
    # Factor system into a product of varieties
    factors = system.factor()
    
    # Only return a decomposition if there is more than one factor
    if len(factors) <= 1:
        return []
    
    return [[ tuple(factors) ]]
    
tactic_product = Tactic('product', method_product)


# In[12]:


# Solves any system consisting of one quadratic equation
def method_quadratic_hypersurface(system):
    # Requires there to be a single equation
    if len(system.eqs) != 1 or len(system.op_eqs) != 0:
        return []

    # Equation must be quadratic
    eq_poly = sp.Poly(system.eqs[0], system.gens)
    if eq_poly.total_degree() != 2:
        return []
    
    # Account for non-homogenous case
    is_homogenous = (eq_poly.homogeneous_order() != None)
    if not is_homogenous:
        alpha = sp.Dummy()
        eq_poly = eq_poly.homogenize(alpha)
    
    # Determine coefficient matrix corresponding to eq
    n = len(eq_poly.gens)
    M = sp.zeros(n, n)
    for i in range(n):
        for j in range(i, n):
            monom = tuple((2 if k == i and k == j else (1 if k == i or k == j else 0)) for k in range(n))
            M[i, j] = eq_poly.coeff_monomial(monom)
    
    # Symmetrize M
    M = M + M.transpose()
    
    # Obtain rank
    rank = M.rank()
    
    # Return value
    if rank == 0:
        c = q**n
    elif rank % 2 == 1:
        c =  q**(n - 1)    
    else:
        c = (q - 1) * q**(n - rank // 2 - 1) + q**(n - 1) 

    if is_homogenous:
        return [[(c,)]]
    else:
        # Need to remove the part at infinity, i.e. where alpha = 0
        # This will be a quadratic hypersurface again
        return [[(c / (q - 1),), (-1 / (q - 1), System(system.gens, [ eq_poly.expr.subs(alpha, 0) ], []))]]
    
tactic_quadratic_hypersurface = Tactic('quadratic hypersurface', method_quadratic_hypersurface)


# In[13]:


def method_open_equation(system):
    # There should be an open equation
    if not system.op_eqs:
        return []
    
    # Take the first open equation (TODO: take the 'simplest' one: based on total degree?)
    f, new_op_eqs = system.op_eqs[0], system.op_eqs[1:]
    
    # Case 1: f can have any value
    # Case 2: f = 1
    case_1 = System(system.gens, system.eqs, new_op_eqs)
    case_2 = System(system.gens, system.eqs + [ f ], new_op_eqs)
    
    return [[(case_1,), (-1, case_2)]]
    
tactic_open_equation = Tactic('open equation', method_open_equation)


# In[14]:


# This tactic makes the equations of the system into a Gröbner basis, in order to try to simplify the equations
def method_groebner(system):
    # Only makes sense if the system is not yet in a Gröbner basis, and there are at least two equations
    if system.is_groebner or len(system.eqs) <= 1:
        return []
    
    # Compute Gröbner basis
    G = list(sp.groebner(system.eqs, gens = system.gens, order = 'grevlex', method = 'f5b'))
    # Create system, and indicate that its equations are a Gröbner basis, so that we don't get into an infinite loop!
    system = System(system.gens, G, system.op_eqs)
    system.is_groebner = True
    
    return [[(system,)]]

tactic_groebner = Tactic('groebner', method_groebner)


# In[15]:


# # Solves any system consisting of one equation which
# # (possibly after homogenizing) defines a non-singular
# # hypersurface in projective space

# def method_nonsingular_proj_hypersurface(system):
#     # Requires there to be a single equation
#     if len(system.eqs) != 1:
#         return []
    
#     # Account for non-homogenous case
#     eq = system.eqs[0]
#     eq_poly = sp.Poly(eq, system.gens)
#     is_homogenous = (eq_poly.homogeneous_order() != None)
#     if not is_homogenous:
#         alpha = sp.Dummy()
#         eq_poly = eq_poly.homogenize(alpha)
#         eq = eq_poly.expr
    
#     # The (homogenized) equation must define a non-singular hypersurface in projective space
#     # Use Jacobian criterion: on each affine patch the derivatives of eq must be invertible w.r.t. eq
#     eq_with_diffs = [ eq.diff(x) for x in eq_poly.gens ] + [ eq ]
#     nonsingular = all(1 in sp.groebner([ x - 1 ] + eq_with_diffs) for x in eq_poly.gens)
#     if not nonsingular:
#         return []

#     # Determine E-polynomial
#     n = len(eq_poly.gens) - 1 # the dimension of the projective space = #variables - 1
#     d = eq_poly.total_degree()
    
#     if is_homogenous:
#         # Homogenous case:
#         # { eq = 0 } = cone of { projective hypersurface } = (q - 1) [ projective hypersurface ] + 1
#         return [[
#             ((q - 1), sp.Symbol('E^{{{}}}_{{{}}}'.format(n, d))), # projective hypersurface
#             (1,) # the apex
#         ]]
#     else:
#         # Non-homogenous case:
#         # { eq = 0 } = [ projective hypersurface ] - [ part at infinity (i.e. alpha = 0) ]
#         return [[
#             (sp.Symbol('E^{{{}}}_{{{}}}'.format(n, d)),), # projective hypersurface
#             (-1 / (q - 1), System(system.gens, [ eq.subs(alpha, 0) ])), # part at infinity
#             (1 / (q - 1),) # (note that there does not exist a point (0 : ... : 0), which is counted at infinity, so we remove it here again)
#         ]]

# tactic_nonsingular_proj_hypersurface = Tactic('non-singular projective hypersurface', method_nonsingular_proj_hypersurface)


# In[16]:


# # Tries to perform a blowup, in the 'singular locus' of the variety

# # Write f as sum_{k = 0} a_k * g^k
# def decompose(f, g, gens):
#     assert(g != 0), 'Cannot divide by zero!'
#     assert(sp.total_degree(g) > 0), 'Cannot decompose w.r.t. constant!'
    
#     f = sp.Poly(f, gens)
#     g = sp.Poly(g, gens)
    
#     a = [ f ]
#     i = 0
#     while True:
#         a.append(0)
#         h = a[i]
#         while h != 0:
#             lt_h = sp.Poly(sp.LT(h), gens)
#             q, r = lt_h.div(g)
#             if q == 0:
#                 h -= lt_h
#                 continue
#             a[i] -= q * g
#             a[i + 1] += q
#             h -= q * g
#         if a[-1] == 0:
#             break
#         i += 1
    
#     a.pop() # Remove the last 0
#     a = [ c.as_expr() for c in a ] # Convert sp.Poly to sp.Expr
#     assert(sum([ c * g**i for i, c in enumerate(a) ]) - f == 0), 'decomposing failed..' # Quick check 
#     return a

# # Remove all factors g from f
# def kill_factors(f, g, gens):
#     while True:
#         q, r = sp.Poly(f, gens).div(sp.Poly(g, gens))
#         if q == 0 or r != 0:
#             return f
#         f = q.expr
        
# # Blowup the ideal I at the center (ideal) Z
# def blowup(I, Z, gens):
#     # Introduce new projective coordinates u_i
#     k = len(Z)
#     u = [ sp.Dummy('u_{{{}}}'.format(j)) for j in range(k) ]
    
#     # Determine equations for blowup:
#     #  u_i * g_j - u_j * g_i
#     J = []
#     for i in range(k):
#         for j in range(i + 1, k):
#             J.append(u[i] * Z[j] - u[j] * Z[i])
        
#     # Determine the affine patches: one for each g_i
#     patches = []
#     for i in range(k):
#         K = []
#         # Transform each f in I, I hope this works ..
#         for f in I:
#             for j in range(k):
#                 if j != i:
#                     f = sum([ a * (u[j] * Z[i])**k for k, a in enumerate(decompose(f, Z[j], gens + u)) ])
#             f = kill_factors(f, Z[i], gens)
#             K.append(f)
        
#         system = System(gens + [ u[j] for j in range(k) if j != i ], K + [ h.subs(u[i], 1) for h in J ])
#         patches.append(system)
#     return u, patches

# def method_blowup(system):
#     # Compute the singular locus (if the variety is smooth, no need to blowup)
#     Z = system.singular_locus()
#     if not Z:
#         return []
#     S = System(system.gens, Z)
#     S.simplify()
#     Z = S.eqs
    
#     # Blowup at Z
#     proj_coords, affine_patches = blowup(system.eqs, Z, system.gens)
#     sorted_patches = []
#     for i, Y in enumerate(affine_patches):
#         d = max([ sp.total_degree(eq) for eq in Y.eqs ])
#         sorted_patches.append((i, Y, d))
    
#     # Sort from least singular to most singular
#     # TODO: 'most singular' has to be defined differently I guess.. y^5 - x^7 shows that singular order on just the affine patch is not enough.. (at least not when we want to continue solving)
#     sorted_patches.sort(key = lambda tupl : tupl[2])
    
#     # Create decomposition
#     decomposition = []
#     indices = []
#     for i, Y, _ in sorted_patches:
#         # In order to be a stratification, we must remove intersections with the patches we already had
#         for j in indices:
#             Y.eqs.append(proj_coords[j])
#         indices.append(i)

#         # Simplify and append
#         Y.simplify()
#         decomposition.append((Y,))
        
#         # Remove 'exceptional divisors'
#         E = System(Y.gens, Y.eqs + [ Z[i] ])
#         E.simplify()
#         decomposition.append((-1, E))
        
#     # Don't forget the singular locus
#     decomposition.append((S,))
    
#     return [ decomposition ]

# tactic_blowup = Tactic('blowup', method_blowup)


# In[17]:


# def method_rehomogenize(system):    
#     # Compute the singular locus
#     Z = system.singular_locus()
#     S = System(system.gens, Z)
#     S.simplify()
#     Z = S.eqs
    
#     # Singular locus should be zero
#     if Z:
#         return []
    
#     # Homogenize equations
#     alpha = sp.Dummy('\\alpha')
#     eqs_hom = [ sp.Poly(eq, system.gens).homogenize(alpha).expr for eq in system.eqs ]
    
#     for x in system.gens:
#         # Rehomogenize to x = 1 (and subs alpha --> x so that we can use the same variables still)
#         Y = System(system.gens, [ eq.subs(x, 1).subs(alpha, x) for eq in eqs_hom ])
        
#         # If Y is non-singular, rehomogenize to Y
#         Z = Y.singular_locus()
#         if Z:
#             return [[
#                 (Y,), # Affine patch of Y
#                 (1 / (q - 1), System(system.gens, [ eq.subs(x, 0).subs(alpha, x) for eq in eqs_hom ])), # Part at infinity (w.r.t. Y)
#                 (-1 / (q - 1), System(system.gens, [ eq.subs(alpha, 0) for eq in eqs_hom ])) # Part at infinity (w.r.t. system)
#             ]] # Note that the apexes cancel out, so no need to include them as correcting terms
        
#     # At this point the system defines a smooth projective variety!
#     return []

# tactic_rehomogenize = Tactic('rehomogenize', method_rehomogenize)


# In[18]:


# def method_projective_conic(system):    
#     for u in system.gens:
#         for v in system.gens:
#             if u == v:
#                 continue
                
#             eqs_with_uv = [ eq for eq in system.eqs if u in eq.free_symbols or v in eq.free_symbols ]
#             if len(eqs_with_uv) != 1:
#                 continue
                
#             poly_uv = sp.Poly(eqs_with_uv[0], u, v)
#             if poly_uv.total_degree() != 2:
#                 continue
            
#             # poly_uv = Au^2 + Buv + Cv^2 + Du + Ev + F
#             coeffs = [0, 0, 0, 0, 0, 0] # [ F, E, C, D, B, A ]
#             for term in poly_uv.terms():    
#                 coeffs[term[0][0] * 3 + term[0][1] - (1 if term[0][0] == 2 else 0)] = term[1]
#             F, E, C, D, B, A = coeffs
                
#             Delta = B**2 - 4*A*C
            
#             vars_base = [ x for x in system.gens if x != u and x != v ]
#             eqs_base = [ eq for eq in system.eqs if eq != eqs_with_uv[0] ]
            
#             return [[
#                 (System(system.gens, system.eqs + [ Delta ]),),
            
#                 ((q + 1), System(vars_base, eqs_base)), (-(q + 1), System(vars_base, eqs_base + [ Delta ])),
            
#                 (System(vars_base + [ u ], eqs_base + [ A*u**2 + B*u + C ]),), (-1, System(vars_base + [ u ], eqs_base + [ A*u**2 + B*u + C, Delta ])),
            
#                 (System(vars_base, eqs_base + [ A ]),), (-1, System(vars_base, eqs_base + [ A, Delta ]))
#             ]]
    
#     return []

# tactic_projective_conic = Tactic('projective conic', method_projective_conic)


# ### Solver

# In[23]:


# A Solver computes classes of Systems using Tactics
# One can add tactics using `add_tactic` and compute classes using `compute`

class Solver:
    
    def __init__(self):
        self.debug = False
        
    def compute_grothendieck_class(self, system):
        return self.compute_with_tactics(system, [
            tactic_trivial,
            tactic_product,
            tactic_quadratic_hypersurface,
            tactic_linearity,
            tactic_factor,
            tactic_groebner,
            tactic_open_equation
        ])
        
    def compute_with_tactics(self, system, tactics):
        system.simplify_equations()
        
        if self.debug:
            display(Math('\\text{Considering }' + system.latex()))
        
        for tactic in tactics:
            decompositions = tactic.apply(system)
            for decomposition in decompositions:
                if self.debug and tactic.name != '':
                    print(f'Apply `{tactic.name}` to find: {decomposition}')
                
                # Sum over the strata
                total = 0
                subsystems = len([ Y for stratum in decomposition for Y in stratum if type(Y) == System ])
                for stratum in decomposition:
                    # Take the product over the factors
                    product = 1
                    for Y in stratum:
                        if type(Y) == System:
                            Y = self.compute_with_tactics(Y, tactics)
                            if Y is None:
                                product = None
                                break
                        product *= Y
                        if product == 0:
                            break
                    
                    if product is None:
                        break
                    
                    total += product
                else: # That is, if the for-loop did not break
                    total = sp.simplify(total)
                    if self.debug:
                        display(Math('\\text{Class of } ' + system.latex() + ' \\text{ is } ' + sp.latex(total)))
                    return total
        if self.debug:
            print(f'Could not compute System {system}')
        return None


# In[ ]:




