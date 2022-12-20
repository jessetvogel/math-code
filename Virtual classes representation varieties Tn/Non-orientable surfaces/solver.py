#!/usr/bin/env python
# coding: utf-8

# ## Imports

# In[1]:


import sympy as sp
import time

q = sp.Symbol('q')


# ## Util functions

# In[2]:


# Input: polynomial f, variable x, polynomials u and v
# Output: f with x replaced by u / v, then 'homogenized'

def subs_frac(f, x, u, v):
    return sp.Poly(sp.Poly(f, x).transform(sp.Poly(u, x), sp.Poly(v, x)), f.gens)


# In[3]:


# Input: some symbolic expression e, a set of variables v
# Output: sp.Poly(e, v) if v is nonempty, sp.Poly(e, { 1 }) otherwise
# Note: this is because sp.Poly's cannot be initialized without generators

def to_poly(e, v):
    return sp.Poly(e, v if v else { sp.sympify(1) })


# In[4]:


# Input: polynomial f
# Output: True if is nonzero constant, False otherwise

def is_nonzero_constant(f):
    return f.total_degree() == 0 and f != 0


# In[22]:


# Input: system
# Output: (list of triples (eqs, op_eqs, X_vars), unused_variables)

def split_system(system):
    # Data which to divide (eq, vars, is_op)
    data =        [ (eq, eq.free_symbols.difference(system.S_vars), False) for eq in system.eqs ]
    data = data + [ (eq, eq.free_symbols.difference(system.S_vars), True)  for eq in system.op_eqs ]
    n = len(data)
    
    # Divide them
    groups = []
    while data:
        eq, eq_vars, is_op = data.pop()
        n -= 1
        
        group = ([] if is_op else [ eq ], [ eq ] if is_op else [], eq_vars.union(system.S_vars))
        groups.append(group)
        while True:
            for i in range(n):
                eq, eq_vars, is_op = data[i]
                if not eq_vars.isdisjoint(group[2]):
                    group[1 if is_op else 0].append(eq)
                    group[2].update(eq_vars)
                    data.pop(i)
                    n -= 1
                    break
            else:
                break
    
    # Change gens for polynomials, and find list of used variables
    used_vars = set(system.S_vars)
    for g_eqs, g_op_eqs, g_vars in groups:
        g_eqs[:]    = [ to_poly(eq, g_vars) for eq in g_eqs ]
        g_op_eqs[:] = [ to_poly(eq, g_vars) for eq in g_op_eqs ]
        used_vars.update(g_vars)

    # Determine unused variables
    unused_vars = system.X_vars.difference(used_vars)

    return groups, unused_vars


# In[6]:


# Input: F, G are lists of polynomials
# Output: True if isomorphic, otherwise False

def are_isomorphic(F, G, S_vars = set()):
    # Number of equations should match
    if len(F) != len(G):
        return False
    n_eqs = len(F)

    # Trivial case
    if n_eqs == 0:
        return True

    # Number of variables should match
    if len(F[0].gens) != len(G[0].gens):
        return False
    n_vars = len(F[0].gens)
    
    # S_vars must be in both generating sets
    if not (S_vars.issubset(F[0].gens) and S_vars.issubset(G[0].gens)):
        return False

    # Now try to match equations
    match_eqs, match_vars = [ None ] * n_eqs, [ None ] * n_vars
    
    # S_vars must map to S_vars directly
    for x in S_vars:
        u = F[0].gens.index(x)
        v = G[0].gens.index(x)
        match_vars[u] = v

    # Convert polynomials to their term representation
    F = [ f.terms() for f in F ]
    G = [ g.terms() for g in G ]
        
    def match_eq(match_eqs, match_vars, i):
        # If this was the last equation that needed to be matched, we are done!
        if i == n_eqs:
            return True

        f_terms = F[i]
        n_terms = len(f_terms)
        for j in [ j for j in range(n_eqs) if j not in match_eqs and len(G[j]) == n_terms ]:
            # Try to match equation F[i] to G[j]
            g_terms = G[j]

            # Now try to match terms
            match_eqs[i] = j
            match_terms = [ None ] * n_terms
            result = match_term(match_eqs, match_vars, i, j, match_terms, n_terms, 0)
            if result == True:
                return True
            match_eqs[i] = None

        return False

    def match_term(match_eqs, match_vars, i, j, match_terms, n_terms, k):
        # If all terms are matched, go on to the next equation
        if k == n_terms:
            return match_eq(match_eqs, match_vars, i + 1)

        # Find match for F[i][k]
        f_term = F[i][k]
        for l in [ l for l in range(n_terms) if l not in match_terms and could_match_term(f_term, G[j][l])]:
            g_term = G[j][l]
            options = []
            if not find_options_match_term(f_term[0], g_term[0], options, match_vars, 0):
                return False

            match_terms[k] = l
            for option in options:
                result = match_term(match_eqs, option, i, j, match_terms, n_terms, k + 1)
                if result == True:
                    return True
            match_terms[k] = None
        
        return False

    def find_options_match_term(T, S, options, option, u):
        # If all u's are matched, add to options
        if u == n_vars:
            options.append(option.copy())
            return True
        
        # If u was already matched, but it cannot make T and S match, return False
        if option[u] != None and T[u] != S[option[u]]:
            return False
        
        # If u was already matched, or if T[u] == 0, just continue with u + 1
        if option[u] != None or T[u] == 0:
            return find_options_match_term(T, S, options, option, u + 1)
        
        # Otherwise, find new matches for v
        matches_v = [ v for v in range(n_vars) if S[v] == T[u] and v not in option ]
        if not matches_v:
            return False

        for v in matches_v:
            option[u] = v
            if not find_options_match_term(T, S, options, option, u + 1):
                option[u] = None        
                return False
        
        option[u] = None
        return True

    def could_match_term(T, S):
        # Coefficients should match
        if T[1] != S[1]:
            return False
        
        # Powers should match
        k = max(T[0] + S[0]) + 1
        P = [ 0 ] * k
        for a in T[0]:
            P[a] += 1
        for a in S[0]:
            P[a] -= 1
        
        return not any(P)

    return match_eq(match_eqs, match_vars, 0)


# In[7]:


def time_solve(system, solver = None):
    if solver == None:
        solver = Solver()
    
    time_start = time.time()
    c = solver.compute_class(system)
    time_end = time.time()
    return time_end - time_start, c

def benchmark(system, N):
    total_time = 0
    for i in range(N):
        t, _ = time_solve(system)
        total_time += t

    print('\nTime elapsed per solve: {}'.format(total_time / N))
    sp.factor(_)


# ## Class Solver

# In[28]:


class Solver:
    
    def __init__(self):
        self.dictionary = []
        self.unknowns = 0
        self.debug = False
    
    # Input: system
    # Output: class in Grothendieck ring
    def compute_class(self, system):    
        if self.debug:
            print('System {}'.format(system))
        
        # Reduce system equations
        system.reduce()
                
        # Special cases (empty variety or affine space)
        if system.eqs == [ 1 ] or system.op_eqs == [ 0 ]:
            return 0
                        
        if not system.eqs and not system.op_eqs:
            return q ** (len(system.X_vars) - len(system.S_vars))
        
        # Check for product variety whenever:
        # (i) There are multiple groups (NOTE: all groups must have less variables than the original one. Otherwise an infinite loop may occur!)
        # OR (ii) there are unused variables
        groups, unused_vars = split_system(system)        
        if unused_vars or (len(groups) > 1 and all(len(set().union(*[ eq.free_symbols for eq in g_eqs ], *[ eq.free_symbols for eq in g_op_eqs ])) < len(system.X_vars) for g_eqs, g_op_eqs, _ in groups)):
            c = q ** len(unused_vars)
            
            # Compute groups with fewer variables first
            groups.sort(key = lambda g: len(g[2]) )
            
            if self.debug:
                for i in range(len(groups)):
                    g_eqs, g_op_eqs, g_vars = groups[i]
                    print('Group[{}] = {} - {} in {}'.format(i, g_eqs, g_op_eqs, g_vars))
                
            for g_eqs, g_op_eqs, g_vars in groups:
                if self.debug:
                    print('Group {} - {} in {}'.format([ f.expr for f in g_eqs ], [ f.expr for f in g_op_eqs ], g_vars))
                s = System(g_eqs, g_op_eqs, g_vars, system.S_vars, system.factored_eqs)
                c *= self.compute_class(s)
                
                # A shortcut if possible
                if c == 0:
                    return 0
            return c
                
        # Search in dictionary (of affine varieties, i.e. op_eqs is empty)
        if not system.op_eqs:
            for entry in self.dictionary:
                if are_isomorphic(entry[0], system.eqs, system.S_vars):
                    if self.debug:
                        print('Found match!')
                    return entry[1]

        # Apply solving techniques
        c = self.solve_system(system)
        c = sp.expand(c)

        # Store in dictionary
        if not system.op_eqs:
            if self.debug:
                print('Save {} --> {}'.format([ eq.expr for eq in system.eqs ], c))
            self.dictionary.append((system.eqs.copy(), c))
        
        return c
    
    def new_unknown(self):
        x = sp.Symbol('X_' + str(self.unknowns))
        self.unknowns += 1
        return x
    
#   -------- SOLVING TECHNIQUE METHODS --------
    
    def check_univariate_equations(self, system, eq):
        # Check for equations with only one free variable x, then solve for x
        eq_vars = eq.free_symbols
        if len(eq_vars) != 1:
            return None

        # Variable must not be of S
        x = eq_vars.pop()
        if x in system.S_vars:
            return None

        # Simply consider all solutions and add the classes
        x_solutions = sp.solve(eq, x)
        Y_vars = system.X_vars.difference({ x, })
        c = 0
        for v in x_solutions:
            Y_eqs    = [ to_poly(f.subs(x, v), Y_vars) for f in system.eqs if f != eq ]
            Y_op_eqs = [ to_poly(f.subs(x, v), Y_vars) for f in system.op_eqs ]
            s = System(Y_eqs, Y_op_eqs, Y_vars, system.S_vars, system.factored_eqs)
            c += self.compute_class(s)
            
        return c
    
    def check_linear_equations(self, system, eq):
        # Look for something of the form 'x * u + v = 0'
        for x in [ x for x in eq.free_symbols if x not in system.S_vars and eq.degree(x) == 1]:
            v = to_poly(eq.subs(x, 0), system.X_vars)
            u = to_poly((eq - v) / x, system.X_vars)

            c = 0

            # Case 1: u = 0, v = 0
            if not is_nonzero_constant(u) and not is_nonzero_constant(v):
                Y_eqs = [ f for f in system.eqs if f != eq ] + [ u, v ]
                s = System(Y_eqs, system.op_eqs, system.X_vars, system.S_vars, system.factored_eqs)
                c += self.compute_class(s)

            # Case 2: u != 0, x = -v / u
            Y_vars = system.X_vars.difference({ x, })
            Y_eqs    = [ to_poly(subs_frac(f, x, -v, u), Y_vars) for f in system.eqs if f != eq ]
            Y_op_eqs = [ to_poly(subs_frac(f, x, -v, u), Y_vars) for f in system.op_eqs ] + [ u ]
            s = System(Y_eqs, Y_op_eqs, Y_vars, system.S_vars, system.factored_eqs)
            c += self.compute_class(s)

            return c
            
        return None
    
    def check_product_equations(self, system, eq):
        # Check for equations of the form 'u * v = 0'
        factors = system.factored_eqs[eq.expr]
        if len(factors) < 2:
            return None
        
        # Determine u and v
        u = factors[0]
        v = 1
        for f in factors[1:]:
            v *= f
        v = to_poly(v, system.X_vars)
        
        # Construct dictionary of factored eqs
        Y_factored_eqs = system.factored_eqs.copy()
        Y_factored_eqs[u.expr] = [ u ]
        Y_factored_eqs[v.expr] = factors[1:]
        
        c = 0

        # Case 1: u = 0
        Y_eqs = [ f for f in system.eqs if f != eq ] + [ u ]
        s = System(Y_eqs, system.op_eqs, system.X_vars, system.S_vars, Y_factored_eqs)
        c += self.compute_class(s)

        # Case 2: u != 0, v = 0
        Y_eqs    = [ f for f in system.eqs if f != eq ] + [ v ]
        Y_op_eqs = system.op_eqs + [ u ]
        s = System(Y_eqs, Y_op_eqs, system.X_vars, system.S_vars, Y_factored_eqs)
        c += self.compute_class(s)

        return c
    
    def check_open_equations(self, system, op_eq):
        c = 0
        
        # Case 1: op_eq = whatever
        Y_op_eqs = [ f for f in system.op_eqs if f != op_eq ]
        s = System(system.eqs, Y_op_eqs, system.X_vars, system.S_vars, system.factored_eqs)
        c += self.compute_class(s)
        
        # Case 2: op_eq = 0
        Y_eqs = system.eqs + [ op_eq ]
        s = System(Y_eqs, Y_op_eqs, system.X_vars, system.S_vars, system.factored_eqs)
        c -= self.compute_class(s)
        
        return c
    
    def solve_system(self, system):
        system.eqs.sort(key = lambda eq : len(eq.terms()))
        
        # Chcek univariate equations
        for eq in system.eqs:            
            c = self.check_univariate_equations(system, eq)
            if c != None:
                return c
        
        # Check product equations
        for eq in system.eqs:
            c = self.check_product_equations(system, eq)
            if c != None:
                return c
        
        # Check linear equations
        for eq in system.eqs:
            c = self.check_linear_equations(system, eq)
            if c != None:
                return c
            
        # Check open equations
        for op_eq in system.op_eqs:
            c = self.check_open_equations(system, op_eq)
            if c != None:
                return c

        # If all failed, create new symbol
        return self.new_unknown()


# ## Class System

# In[29]:


class System:
    # Represents a variety $X \to S$
    
    def __init__(self, eqs, op_eqs, X_vars, S_vars = set(), factored_eqs = {}):
        self.eqs = eqs
        self.op_eqs = op_eqs
        self.X_vars = X_vars
        self.S_vars = S_vars
        self.factored_eqs = factored_eqs

        if any(not f.is_Poly for f in self.eqs) or any(not f.is_Poly for f in self.op_eqs):
            self.eqs    = [ to_poly(f, self.X_vars) for f in self.eqs ]
            self.op_eqs = [ to_poly(f, self.X_vars) for f in self.op_eqs ]
    
    def __repr__(self):
        return '{} - {} in {}'.format([ f.expr for f in self.eqs ], [ f.expr for f in self.op_eqs ], self.X_vars)
    
    def reduce_groebner(self):
        # Special cases
        if self.eqs == [ 0 ]:
            self.eqs = []
            return
        
        if len(self.eqs) <= 1:
            return
        
        if not self.X_vars:
            self.eqs = [ to_poly(1, self.X_vars) ] if any(eq != 0 for eq in self.eqs) else []
            return

        # Compute Gröbner basis
        self.eqs = list(sp.groebner(self.eqs, self.X_vars, order = 'grevlex'))
        
    def reduce_squarefree(self):
        eqs_sqf = []
        factored_eqs_sqf = {}
        flag = False
        
        for eq in self.eqs:
            # If factored before, just copy the factorization
            eq_expr = eq.expr
            if eq_expr in self.factored_eqs:
                eqs_sqf.append(eq)
                factored_eqs_sqf[eq_expr] = self.factored_eqs[eq_expr]
                continue
                        
            factors = sp.factor_list(eq, extension = True)
            factors = [ factor[0] for factor in factors[1] ]
            
            eq_sqf = to_poly(1, self.X_vars)
            for factor in factors:
                eq_sqf *= factor
            eq_sqf = to_poly(eq_sqf / eq_sqf.LC(order = 'grevlex'), self.X_vars)

            eqs_sqf.append(eq_sqf)
            factored_eqs_sqf[eq_sqf.expr] = factors
        
            if not flag and eq_sqf.LM() != eq.LM():
                flag = True
        
        self.eqs = eqs_sqf 
        self.factored_eqs = factored_eqs_sqf
        return flag
        
    def reduce_direct_solve(self):
        # Look for equations which are linear in some variable
        for eq in self.eqs:            
            for x in [ x for x in eq.free_symbols.difference(self.S_vars) if eq.degree(x) == 1 ]:                
                # See if we can directly solve for x
                r = eq.subs(x, 0)
                q = (eq - r) / x
                                    
                if sp.total_degree(q) != 0:
                    continue
                    
                # Solve for x and remove x from X_vars
                x_value = -r / q
                self.X_vars = self.X_vars.copy()
                self.X_vars.remove(x)                
                self.eqs    = [ to_poly(f.subs(x, x_value), self.X_vars) for f in self.eqs if f != eq ]
                self.op_eqs = [ to_poly(f.subs(x, x_value), self.X_vars) for f in self.op_eqs ]
                return True
        else:
            return False
    
    def reduce_open_equations(self):            
        # Reduce open equations
        red_op_eqs = []
        for op_eq in self.op_eqs:
            _, r = sp.reduced(op_eq, self.eqs, self.X_vars) if self.X_vars else 0, op_eq
            if r == 0:
                self.op_eqs = [ to_poly(0, self.X_vars) ]
                return
            if not is_nonzero_constant(r):
                red_op_eqs.append(r)
        self.op_eqs = red_op_eqs
        
    def reduce(self):        
        # Do direct solves first, because computing Gröbner bases with lots of variables is difficult
        while self.reduce_direct_solve():
            pass
    
        # Reduce closed equations
        while True:
            
            self.reduce_groebner()

            if self.reduce_direct_solve():
                continue
            
            if self.reduce_squarefree():
                continue
            
            break
        
        # Reduce open equations
        self.reduce_open_equations()

