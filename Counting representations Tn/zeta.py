import sympy as sp

q, s = sp.symbols('q s')

# Simplify (a^b)^c to a^(b * c)
# Simplify (a * b)^c to a^c * b^c
def unfold_exponents(expr):
    if expr.is_Pow and expr.args[0].is_Pow:
        return unfold_exponents(sp.factor(expr.args[0].args[0]) ** (expr.args[0].args[1] * expr.args[1]))
    
    if expr.is_Pow and expr.args[0].is_Mul:
        return unfold_exponents(sp.Mul(*[ f ** expr.args[1] for f in expr.args[0].args ]))
    
    if expr.is_Pow and sp.factor(expr.args[0]) != expr.args[0]:
        return unfold_exponents(sp.factor(expr.args[0]) ** expr.args[1])

    if expr.is_Mul:
        return sp.Mul(*[ unfold_exponents(factor) for factor in expr.args ])
    
    if expr.is_Add:
        return sp.Add(*[ unfold_exponents(term) for term in expr.args ])
    
    return expr

# Simplifies a zeta function in terms of q and s
def simplify_zeta(expr):
    expr = sp.expand(expr)
    expr = unfold_exponents(expr)

    if expr.is_Pow:
        return expr
    
    # Store the coefficients belonging to each q^(as) * (q - 1)^(bs)
    coeffs = {}
    terms = expr.args if expr.is_Add else [ expr ]
    for term in terms:
        a = 0 # linear coefficient of s in power of q
        b = 0 # linear coefficient of s in power of (q - 1)
        coeff = 1 # coefficient
        factors = term.args if term.is_Mul else [ term ]
        for factor in factors:
            if factor.is_Pow and factor.args[0] == q:
                [u], v = sp.reduced(factor.args[1], [ s ])
                a += u
                coeff *= q**v
            elif factor.is_Pow and factor.args[0] == q - 1:
                [u], v = sp.reduced(factor.args[1], [ s ])
                b += u
                coeff *= (q - 1)**v
            else:
                coeff *= factor
            
        # Update coeffs
        coeffs[(a, b)] = coeffs[(a, b)] + coeff if (a, b) in coeffs else coeff
    
    # Create new expression from coeffs
    total = 0
    for (a, b) in sorted(coeffs.keys()):
        coeff = sp.factor(coeffs[(a, b)])
        # Find powers c and d of q and (q - 1), respectively, in coeff
        c, d = 0, 0        
        factors = coeff.args if coeff.is_Mul else [ coeff ]
        for factor in factors:
            if factor.is_Pow and factor.args[0] == q:
                c += factor.args[1]
            elif factor.is_Pow and factor.args[0] == q - 1:
                d += factor.args[1]
            elif factor == q:
                c += 1
            elif factor == q - 1:
                d += 1
        
        total += sp.factor(coeffs[(a, b)] * q**(-c) * (q - 1)**(-d)) * q**(a*s + c) * (q - 1)**(b*s + d)
    return total
