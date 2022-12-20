#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sympy as sp
# from IPython.display import display, Math
from grothendieck_solver import System, Solver
import time
from zeta import simplify_zeta


# ## Algorithm

# In[2]:


ZERO, ONE = sp.sympify(0), sp.sympify(1)
q, s = sp.symbols('q s')
solver = Solver()


# In[3]:


# Writes v = a1 * x1 + ... + an * xn, where gens = [x1, ... , xn]
# and returns [a1, ... , an].
def linear_coefficients(gens, v):
    if v == 0:
        return [ 0 ] * len(gens)
    else:
        assert sp.total_degree(v, *gens) == 1, f'Not linear ({v} in {gens})'
        return sp.reduced(v, gens)[0]


# In[4]:


# Checks if the function `f` is invertible in `system`.
def is_invertible(system, f):
    f = sp.factor(f)
    factors = [ f ]
    if f.is_Mul:
        factors = f.args
    if f.is_Pow:
        factors = [ f.args[0] ]
    return all(g in [1, -1] or g in system.op_eqs or -g in system.op_eqs for g in factors)


# In[5]:

def apply_system(system, M):
    M = sp.Matrix(M) # Make a copy!
    if not system.gens:
        return M
    m, n = M.shape
    for i in range(m):
        for j in range(n):
            M[i, j] = sp.reduced(M[i, j], [ eq for eq in system.eqs if eq != 0 ], system.gens)[1] # Should system.eqs be in Gröbner form ?
    return M


# In[6]:


class Substitution:
    
    def __init__(self, subs = None):
        self.subs = subs
        
    def compose(self, other):
        if other.subs == None:
            return self
        if self.subs == None:
            return other
        keys = set(self.subs).union(other.subs)
        return Substitution({
            x: other.apply(self.subs[x]) if x in self.subs else other.subs[x] for x in keys
        })
    
    def apply(self, X):
        if self.subs == None:
            return X
        return X.xreplace(self.subs)
    
    def modulo(self, f):
        if self.subs == None:
            return self
        return Substitution({
            x: sp.reduced(self.subs[x], [ f ])[1] for x in self.subs
        })


# In[7]:


# Input:
# - gens: list of symbols
# - eq: equation linear in gens
# - x: the variable to solve for in eq
# - X: object to be transformed

# Output: (Y, subs) where
# - Y is the transformed object
# - subs is a Substitutions object describing the substitutions applied in the process

def apply_linear_eq(gens, eq, x0, X):
    # Write eq = x0 * f0 + x1 * f1 + ... + xk * fk = 0 with xi in gens and fi coefficients
    # Then x0 = - (x1 * f1 + ... + xk * fk) / f0, so
    # replace xi = \tilde{xi} * f0 for all i = 1, ... , k to make everything integral again
    # Note: writing fi / f0 = u / v (in reduced form), we can also replace xi = \tilde{xi} * v
    f0 = sp.reduced(eq, [ x0 ])[0][0]
    
    # If f0 = \pm 1, we don't need a Substitution object
    if f0 in [1, -1]:
        return (X.replace(x0, sp.expand(x0 * f0 - eq) / f0), Substitution())
    
    subs = {}
    for term in sp.Poly(eq, gens).terms():
        xi = gens[term[0].index(1)]
        fi = term[1]
        if xi != x0:
            subs[xi] = xi * sp.fraction(fi / f0)[1]
    subs = Substitution(subs)
    new_X = subs.apply(X).subs(x0, sp.expand(x0 * f0 - eq))
    return (new_X, subs)


# In[8]:


# Input:
# - system: System
# - gens: list of symbols
# - eqs: equations which are linear in `gens`
# - X: the object to be transformed

# Output: list of pairs (system, X, subs)
# - system describes the case
# - X is transformed object
# - subs is dict of substitutions made

def apply_linear_eqs(system, gens, eqs, X, subs = None):
    # Initialize subs if None
    if subs == None:
        subs = Substitution()
    
    # First try to solve all equations which can be solved directly (i.e. where no case distinction is needed)
    while True:
        # (remove all trivial equations)
        eqs = [ eq for eq in eqs if eq != 0 ]
        for eq in eqs:
            (x0, f0) = (None, None)
            for x in gens:
                f = sp.reduced(eq, [ x ], gens)[0][0]
                if x in eq.free_symbols and is_invertible(system, f):
                    (x0, f0) = (x, f)
                    break
            else:
                # assert False, "Cannot solve for any variable in " + str(eq)
                continue
                
            # Convert X and keep track of substitutions made
            X, new_subs = apply_linear_eq(gens, eq, x0, X)
            
            # Also apply the substitutions to each equation
            # Note: `new_subs` does not account for x0 -> x0_value!
            x0_value = sp.expand(sp.factor(new_subs.apply(sp.expand(x0 * f0 - eq) / f0))) 
            eqs = [ new_subs.apply(e).subs(x0, x0_value) for e in eqs if e != eq ]
            
            # Update subs
            subs = subs.compose(new_subs)
            break
        else:
            # If no more solutions can be solved for (directly), break
            break
            
    # If all equations are solved for, we are done!
    if not eqs:
        return [(system, X, subs)]
    
    # Otherwise, we do a case distinction.
    # Write eq = f * x + g
    eq = eqs[0]
    x = [ y for y in gens if y in eq.free_symbols ][0]
    [ f ], g = sp.reduced(eq, [ x ])
    cases = []
    # (1) If f = 0, then continue
    new_system = System(system.gens, system.eqs + [ f ], system.op_eqs)
    new_eqs = [ sp.reduced(eq, [ f ])[1] for eq in eqs ] # simplify equations
    cases.extend(apply_linear_eqs(new_system, gens, new_eqs, X, subs))
    
    # (2) If f != 0, then solve for x = - g / f
    new_system = System(system.gens, system.eqs, system.op_eqs + [ f ])
    new_X, more_subs = apply_linear_eq(gens, eq, x, X)
    new_eqs = [ more_subs.apply(eq) for eq in eqs[1:] ]
    new_subs = subs.compose(more_subs)
    cases.extend(apply_linear_eqs(new_system, gens, new_eqs, new_X, new_subs))
    return cases


# In[9]:


def find_independent_columns(system, M, k = 0, A = None, A_inv = None):    
    # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))
    M = apply_system(system, M) # Reduce M w.r.t. system (this also makes a copy of M!)
    
    m, n = M.shape
    ijs = [ (i, j) for i in range(k, m) for j in range(k, n) ]
        
    (i0, j0, i0j0_invertible) = (None, None, None)
    if A == None:
        A = sp.eye(m)
    if A_inv == None:
        A_inv = sp.eye(m)
    
    for i, j in ijs:
        # First try to find an entry on which we don't need case distinctions!
        if is_invertible(system, M[i, j]):
            (i0, j0, i0j0_invertible) = (i, j, True)
            break
    else:
        for i, j in ijs:
            if M[i, j] != 0 and not M[i, j].is_Number:
                (i0, j0, i0j0_invertible) = (i, j, False)
                break
    
    if (i0, j0) == (None, None):
        if not all(M[i, j] == 0 for i, j in ijs):
            assert False, "No suitable column found!"
        else:
            return [ (system, k, A, A_inv) ]
    
    eq = M[i, j]
    cases = []
    if not i0j0_invertible:
        # Case eq = 0:
        new_system = System(system.gens, system.eqs + [ eq ], system.op_eqs)
        cases.extend(find_independent_columns(new_system, M, k, A, A_inv))
                
    # Case eq != 0:
    if i0 != k:
        A = A.elementary_col_op('n<->m', i0, k)
        A_inv = A_inv.elementary_row_op('n<->m', i0, k)
        M = M.elementary_row_op('n<->m', i0, k)
        # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))
        
    if j0 != k:
        M = M.elementary_col_op('n<->m', j0, k)
        # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))

    Mkk = M[k, k]
    A = A.elementary_col_op('n->kn', k, Mkk)
    A_inv = A_inv.elementary_row_op('n->kn', k, 1 / Mkk)
    M = M.elementary_row_op('n->kn', k, 1 / Mkk) # Make M[k, k] = 1
    
    for j in range(k + 1, n): # make columns integral again
        if sp.fraction(M[k, j])[1] != 1:
            M = M.elementary_col_op('n->kn', j, Mkk) # Note: this doesn't change A
            # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))
    for i in range(k + 1, m): # make entries below M[k, k] zero
        if M[i, k] != 0:
            A = A.elementary_col_op('n->n+km', k, M[i, k], i)
            A_inv = A_inv.elementary_row_op('n->n+km', i, - M[i, k], k)
            M = M.elementary_row_op('n->n+km', i, - M[i, k], k)
            # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))
    for j in range(k + 1, n): # make entries right of  M[k, k] zero
        if M[k, j] != 0:
            M = M.elementary_col_op('n->n+km', j, - M[k, j], k)
            # display(Math('A = ' + sp.latex(A) + ', M = ' + sp.latex(M)))

    new_system = system if eq in [1, -1] else System(system.gens, system.eqs, system.op_eqs + [ eq ])
    cases.extend(find_independent_columns(new_system, M, k + 1, A, A_inv))
    
    return cases


# In[10]:


def permute_matrix_to_upper_triangular(H):
    (n, n) = H.shape
    ordered = []
    to_order = list(range(n))
    while to_order:
        for j in to_order:
            if all(i == j or H[i, j] == 0 for i in to_order):
                ordered.append(j)
                to_order.remove(j)
                break
        else:
            assert False, "Cannot be brought to upper triangular form using permutations"
    P = sp.Matrix([[ 1 if j == ordered[i] else 0 for j in range(n) ] for i in range(n) ])
    return P * H * P.inv()


# In[11]:


# Input:
# - system: System
# - H_symbols: list of symbols that generate H
# - H: matrix representing elements of H
# - chi: (row) vector representing character

# Output: [ (system, chi, stabilizer, index) ], where
# - system: System
# - chi: representative for an orbit
# - stabilizer: Substition object of solutions of H_symbols in order to obtain the stabilizer
# - index: a polynomial in q which is the index of the stabilizer in H

# ?(Note that the index of the stabilizer in H is the length of the dict `stabilizer`) ???

# It is assumed H is upper triangular!
def find_orbit_stabilizer_representatives(system, H_symbols, H, chi, stabilizer = None, depth = 0):
    # display(Math('[ H = ' + sp.latex(H) + ' \\text{ over } ' + system.latex() + ' \\text{ acting on } \\chi = ' + sp.latex(chi) + ' ]'))  
    
    # Create a stabilizer substitution if there is none yet
    if stabilizer == None:
        stabilizer = Substitution()
        
    # If H_symbols = {}, then the group H is trivial, so we are done
    # (This check is done because we cannot use H_symbols as a generating set when its empty)
    if not H_symbols:
        return [(system, chi, stabilizer, 1)]
        
    if depth > 20:
        # print('Maximum-depth reached for:')
        # print('system = ' + str(system))
        # print('H_symbols = ' + str(H_symbols))
        # print('H = ' + str(H))
        # print('chi = ' + str(chi))
        # print('stabilizer = ' + str(stabilizer))
        # display(Math('H = ' + sp.latex(H) + ' \\text{ in } ' + sp.latex(H_symbols) + ' \\text{ over } ' + system.latex() + ' \\text{ acting on } \\chi = ' + sp.latex(chi)))  
        assert False, "Maximum depth reached!"

    # Compute the image of chi (H acts by right-multiplication)
    im_chi = apply_system(system, chi * H)
    
    # display(Math('[ \\chi = ' + sp.latex(chi) + ' \\overset{H}{\\mapsto} ' + sp.latex(im_chi) + ' ]'))
        
    # Starting at the back, we try to make as many entries of chi equal to 0 or 1
    for z, im_z in zip(reversed(chi), reversed(im_chi)):
        # If z is constant, it should be invariant under H
        if z == 0 or z == 1:
            assert sp.expand(im_z) == z, "Mistake in stabilizer: " + str(z) + " ↦ " + str(im_z)
            continue
        
        # Write z ↦ u * z + v
        u, v = sp.Poly(im_z, z).all_coeffs()
                
        # If v = 0, we consider two cases:
        #  (1) If u = 1, then z is invariant under H
        #  (2) If u ≠ 1, then distinguish between cases:
        #       - z = 0, then z is also invariant under H
        #       - z ≠ 0, then we can use the action of H to get z = 1.
        #         The stabilizer should have u = 1.
        if v == 0:
            # Case (1)
            if u == 1:
                continue
            
            # Case (2) with z = 0
            cases = []
            
            update_stabilizer = Substitution({ z: ZERO })
            new_stabilizer = stabilizer.compose(update_stabilizer)
            
            new_eqs = [ sp.expand(eq.subs(z, ZERO)) for eq in system.eqs ]
            new_eqs = [ eq for eq in new_eqs if eq != 0 ]
            new_system = System([ x for x in system.gens if x != z ], new_eqs, list(set([ eq.subs(z, ZERO) for eq in system.op_eqs ])))
            new_chi = chi.subs(z, ZERO)
            new_chi = apply_system(new_system, new_chi)

            new_H = update_stabilizer.apply(H)
            new_H = apply_system(new_system, new_H)
            
            cases.extend(find_orbit_stabilizer_representatives(
                new_system, H_symbols, new_H, new_chi, new_stabilizer, depth + 1
            ))
            
            # Case (2) with z ≠ 0
            update_stabilizer = Substitution({ z: ONE, u: ONE })
            new_stabilizer = stabilizer.compose(update_stabilizer)
            
            new_eqs = [ sp.expand(eq.subs(z, ONE)) for eq in system.eqs ]
            new_eqs = [ eq for eq in new_eqs if eq != 0 ]
            new_system = System([ x for x in system.gens if x != z ], new_eqs, list(set([ eq.subs(z, ONE) for eq in system.op_eqs ])))
            new_chi = chi.subs(z, ONE)
            new_chi = apply_system(new_system, new_chi)
            
            new_H = update_stabilizer.apply(H)
            new_H = apply_system(new_system, new_H)
            new_H_symbols = [ x for x in H_symbols if x != u ] # remove u from the H_symbols
            
            for (sy, ch, st, indx) in find_orbit_stabilizer_representatives(new_system, new_H_symbols, new_H, new_chi, new_stabilizer, depth + 1):
                cases.append((sy, ch, st, (q - 1) * indx))
            
            return cases
        
        # Write v as a polynomial in H_symbols
        v_poly = sp.Poly(v, H_symbols)
        
        # Write v = a0 * f0 + a1 * f1 + ... + ak * fk, with ai ∈ H_symbols and fi ∈ k[system.gens]
        # Find pair (ai, fi) such that fi is invariant under the action of H
        # [⚠️ WARNING] I don't know if this is always possible!
        # Now:
        #  (1) Either fi != 0, and we can choose z = 0 by an appropriate choice of ai
        #      In this case, (z = 0) ↦ u * (z = 0) + a0 * f0 + a1 * f1 + ... + ak * fk,
        #      so we must have v = a0 * f0 + a1 * f1 + ... + ak * fk = 0 as a condition on the stabilizer H.
        #      We impose this condition by solving for ai = - (a1 * f1 + ... (not ai * fi) ... + ak * fk) / fi.
        #      However, since we don't want to divide by fi (we don't like rational functions),
        #      we reparametrize aj = \tilde{aj} * fi for all j such that fj != 0, so that
        #      ai = - (\tilde{a1} * f1 + ... (not ai * fi) ... + \tilde{ak} * fk).
        #      Furthermore, since we fixed z = 0, we can/should omit z from system.gens
        (ai, fi) = (None, None)
        repl = { x: im_x for x, im_x in zip(chi, im_chi) if x.is_Symbol }
        for term in v_poly.terms():
            f = term[1]
            im_f = f.xreplace(repl)
            df = sp.expand(sp.reduced(im_f - f, system.eqs, system.gens)[1])
            if df == 0:
                a = H_symbols[term[0].index(1)]
                # LITTLE HACK: also require that `a` does not appear in `im_y` for any `y` (not equal to `z`) which
                # also appears in `im_z`
                if any(a in im_y.free_symbols for y, im_y in zip(chi, im_chi) if y.is_Symbol and y != z and y in im_z.free_symbols):
                    continue
                (ai, fi) = (a, f)
                break
        else:
            continue
            # assert False, "No invariant f_i found!"
        
        update_stabilizer = Substitution({ z: ZERO, ai: sp.expand(ai * fi - v), **{
            aj: aj * fi for aj in v.free_symbols.intersection(H_symbols) if aj != ai
        }})
                        
        new_eqs = [ sp.expand(eq.subs(z, ZERO)) for eq in system.eqs ]
        new_eqs = [ eq for eq in new_eqs if eq != 0 ]
        new_system = System([ x for x in system.gens if x != z ], new_eqs, list(set([ eq.subs(z, ZERO) for eq in system.op_eqs ] + [ fi ])))
        new_chi = chi.subs(z, ZERO)
        new_chi = apply_system(new_system, new_chi)
        new_stabilizer = stabilizer.compose(update_stabilizer)
        
        new_H = update_stabilizer.apply(H)
        new_H = apply_system(new_system, new_H)
        new_H_symbols = [ x for x in H_symbols if x != ai ] # remove the a_i from H_symbols
        
        cases = []
        for (sy, ch, st, indx) in find_orbit_stabilizer_representatives(new_system, new_H_symbols, new_H, new_chi, new_stabilizer, depth + 1):
            cases.append((sy, ch, st, q * indx))
        
        #  (2) Or fi = 0. In this case we just add it as an equation and repeat.
        #      (Note: if fi is invertible, we don't need to bother here!)
        if not is_invertible(system, fi):
            new_system = System(system.gens, system.eqs + [ fi ], system.op_eqs)
            new_chi = apply_system(new_system, chi)
            new_H = apply_system(new_system, H)
            new_stabilizer = stabilizer.modulo(fi)
        
            # print(f'Case 2 ({f0} = 0)')
            cases.extend(find_orbit_stabilizer_representatives(new_system, H_symbols, new_H, new_chi, new_stabilizer, depth + 1))
        
        return cases
    
    # At this point, chi should be invariant under H
    assert chi == im_chi, 'Oops, chi ≠ im_chi'
    
    # If chi is completely invariant, then H is the stabilizer (i.e. further no equations)
    return [ (system, chi, stabilizer, 1) ]


# In[12]:


class LookupTable:
    
    def __init__(self):
        self.table = {}
        
    def put(self, G, value):
        self.table[tuple(G)] = value
        
    def get(self, G):
        t = tuple(G)
        if t not in self.table:
            return None
        
        return self.table[t]
    
LOOKUP_TABLE = LookupTable()


# In[22]:


flag_display = False

class TGroup:
    
    def __init__(self, system, G, ident_level = 0):
        self.system = system
        self.G = G
        self.G_symbols = list(G.free_symbols.difference(system.gens))
        self.multiplier = 1
        self.ident_level = ident_level
        self.ident = '\\quad' * ident_level
                        
    def display_math(self, math):
        display(Math(self.ident + ' ' + math))
    
    def simplify_presentation(self):
        self.system.simplify_equations()
        # If the GCD of all coefficients in front of some G_symbol x is invertible,
        # then make a substitution x = \tilde{x} / GCD
        gcd_changes = False
        for x in self.G_symbols:
            # Coefficients in front of x can be obtained by differentiating G w.r.t. x
            gcd = sp.factor(sp.gcd(list(self.G.diff(x))))
            if gcd == 0 or gcd == 1:
                continue
            gcd_factors = gcd.args if gcd.is_Mul else [ gcd ]
            for f in gcd_factors:
                if is_invertible(self.system, f):
                    self.G = self.G.subs(x, x / f)
                    gcd_changes = True
        
        # This seems inefficient, but needs to be done in order to clear up any mess made by the above
        if gcd_changes:
            (n, n) = self.G.shape
            for i in range(n):
                for j in range(i + 1, n):
                    self.G[i, j] = sp.expand(sp.factor(self.G[i, j]))
        
        # Factor system if possible. All variables/equations of which G is independent can be solved beforehand
        gens = []
        eqs = []
        op_eqs = []
        used_symbols = self.G.free_symbols.intersection(self.system.gens)
        for Y in self.system.factor():
            if used_symbols.isdisjoint(Y.gens):
                self.multiplier *= solver.compute_grothendieck_class(Y)
            else:
                gens.extend(Y.gens)
                eqs.extend(Y.eqs)
                op_eqs.extend(Y.op_eqs)
        self.system = System(gens, eqs, op_eqs)
        self.system.simplify_equations()

    def zeta_function(self):
        try:
            # First simplify the presentation!
            self.simplify_presentation()

            # Short-cut
            if self.multiplier == 0:
                return 0

            (n, n) = self.G.shape
            
            # If n = 0, then G is trivial
            if n == 0:
                return self.multiplier
            
            # If G_{n, n} != 1, then change variables in order to make G_{n, n} = 1
            # This can be done by scaling the whole matrix by 1 / G_{n, n}
            # After a suitable change of variables, it should (RIGHT?) be enough to
            # change all 1's on the diagonal to G_{n, n}, and then change G_{n, n} to 1
            if self.G[n - 1, n - 1] != 1:
                assert self.G[n - 1, n - 1].is_Symbol
                had_ones = False
                for i in range(n):
                    if self.G[i, i] == self.G[n - 1, n - 1]:
                        self.G[i, i] = 1
                    elif self.G[i, i] == 1:
                        self.G[i, i] = self.G[n - 1, n - 1]
                        had_ones = True
                if not had_ones:
                    self.multiplier *= (q - 1)
            
            # Base case: the trivial group has 1 representation
            if not self.G_symbols:
                assert not self.system.gens # Since we simplified the presentation, (G = trivial) => (system = trivial)
                return self.multiplier
            
            # Try lookup table (only when G is constant, i.e. `system` is a point)
            if not self.system.gens:
                v = LOOKUP_TABLE.get(self.G)
                if v:
                    total = self.multiplier * v
                    return total
            
            if flag_display:
                self.display_math('\\text{Considering } G = ' + sp.latex(self.G) + ' \\text{ over } ' + self.system.latex())

            subtotal = 0 # this will be the zeta function before multiplying by self.multiplier

            # Matrix representing elements of H = G / N
            H = self.G[0:n - 1, 0:n - 1]
            # Goal: identify an additive group G_a^r
            # Write      | H | N |
            #        G = +---+---+
            #            | 0 | 1 |
            N = self.G[0:n - 1, n - 1]
            # Writing G = N \rtimes H, we can identify N by taking H = 1
            N_eqs = [ H[i, j] for i in range(n - 1) for j in range(i + 1, n - 1) ]
            N_cases = apply_linear_eqs(self.system, self.G_symbols, N_eqs, N)
            for (system, N, subs) in N_cases:
                N_symbols = list(N.free_symbols.intersection(self.G_symbols))
                r = len(N_symbols)
                
                # Short-cut for when N = trivial
                if r == 0:
                    subtotal += TGroup(system, H, self.ident_level + 1).zeta_function()
                    continue

                # Apply the substitutions to H
                H_subs = apply_system(system, subs.apply(H))

                # Let M be the (n - 1) x r matrix representing the coefficients of
                # the entries of G[0:n - 1, n - 1] in terms of N_symbols
                M = sp.Matrix([ linear_coefficients(N_symbols, x) for x in N ])
                
                # Write M = A * (I_k & 0 \\ 0 & 0) * B, with A and B invertible, and k the rank of M.
                # Then the first k columns of A are generators of the column space of M
                # This decomposition may depend on certain equations
                for (system, k, A, A_inv) in find_independent_columns(system, M):
                    # If k = 0, we have G = H, so we can just continue with H
                    if k == 0:
                        subtotal += TGroup(system, apply_system(system, H_subs), self.ident_level + 1).zeta_function()
                        continue
                    # H_eff describes how H acts on the linearly independent columns
                    H_eff = (A_inv * H_subs * A)[0:k, 0:k]
                    # After a permutation of the x_i, H_gens should be in upper triangular form
                    H_eff = permute_matrix_to_upper_triangular(H_eff)
                    # Since det(A) need not be 1, there might be denominators in H_eff. We must clear them!
                    # Also, there might be unsimplified fractions in there: we use sp.expand(sp.factor(-)) for this.
                    for i in range(k):
                        for j in range(i, k):                            
                            H_eff[i, j] = sp.expand(sp.factor(H_eff[i, j]))
                            denom = sp.fraction(H_eff[i, j])[1]
                            if denom != 1:
                                H_eff = Substitution({
                                    x: x * denom for x in H_eff[i, j].free_symbols.intersection(self.G_symbols)
                                }).apply(H_eff)
                    
                    # So now, chi \mapsto chi * H_eff
                    first_i = max([ 0 ] + [ int(str(x)[4:-1]) + 1 for x in system.gens if x.is_Dummy ]) # TODO: this is a bit hacky..
                    chi = sp.Matrix([[ sp.Dummy(f'x_{{{first_i + i}}}') for i in range(k) ]])
                    im_chi = chi * H_eff

                    if flag_display:
                        self.display_math('\\text{Considering } H = ' + sp.latex(H_subs) + '\\text{ acting on } \\chi = ' + sp.latex(chi) + '\\overset{H}{\\mapsto} ' + sp.latex(im_chi))

                    # Find representatives
                    new_system = System(system.gens + list(chi), system.eqs, system.op_eqs)
                    representatives = find_orbit_stabilizer_representatives(new_system, self.G_symbols, H_eff, chi)
                    for (system, chi, stabilizer, index) in representatives:
                        new_G = sp.Matrix(stabilizer.apply(H_subs)) # make sure this is a copy, so that H_subs doesn't get altered magically!

                        if flag_display:
                            self.display_math('\\bullet \\text{ Representative } \\chi = ' + sp.latex(chi) + ' \\text{ over } ' + system.latex() + '\\text{ has stabilizer } ' + sp.latex(new_G) + ' \\text{ of index } ' + sp.latex(index))

                        part = TGroup(system, new_G, self.ident_level + 1).zeta_function() * index**(-s)

                        if flag_display:
                            self.display_math('\\Rightarrow ' + sp.latex(part))

                        subtotal += part

            # Store result in lookup table (only if G is constant)
            if not self.system.gens:
                LOOKUP_TABLE.put(self.G, subtotal)

            # Multiply by self.multiplier
            total = self.multiplier * subtotal

            if flag_display:
                self.display_math('\\text{In total, obtain } ' + sp.latex(total))

            return total
        except Exception as e:
            self.display_math('\\text{Error in } G = ' + sp.latex(self.G) + ' \\text{ over } ' + self.system.latex())
            assert False, str(e)


# ## Applications

# In[23]:


LOOKUP_TABLE = LookupTable()


# In[24]:


# Unipotent groups G = Un for n = 1, ... , 10
ZETA_Un = {}
for n in range(1, 11):
    flag_display = False

    A = sp.Matrix([[ sp.Symbol(f'a_{{{i},{j}}}') if j > i else (1 if i == j else 0) for j in range(n) ] for i in range(n) ])
    H = TGroup(System([], [], []), A)

    time_before = time.perf_counter()
    zeta = simplify_zeta(H.zeta_function())
    time_after = time.perf_counter()
    time_elapsed = time_after - time_before
    
    ZETA_Un[n] = zeta
    
    # display(Math(f'n = {n} \ ({time_elapsed:.2f} \\text{{ sec}}): {sp.latex(zeta)}'))
    print(f'n = {n} ({time_elapsed:.2f} sec): {str(zeta)}')


# In[ ]:


# Upper triangular groups G = Tn for n = 1, ... , 10
ZETA_Tn = {}
for n in range(1, 11):
    flag_display = False

    A = sp.Matrix([[ sp.Symbol(f'a_{{{i},{j}}}') if i <= j else 0 for j in range(n) ] for i in range(n) ])
    H = TGroup(System([], [], []), A)

    time_before = time.perf_counter()
    zeta = simplify_zeta(H.zeta_function())
    time_after = time.perf_counter()
    time_elapsed = time_after - time_before
    
    ZETA_Tn[n] = zeta
    
    # display(Math(f'n = {n} \ ({time_elapsed:.2f} \\text{{ sec}}): {sp.latex(zeta)}'))
    print(f'n = {n} ({time_elapsed:.2f} sec): {str(zeta)}')
