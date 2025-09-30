from Qlapoti.sage_implementation.ideal_to_isogeny.deuring.broker import starting_curve
from Qlapoti.sage_implementation.ideal_to_isogeny.deuring.correspondence import constructive_deuring

# p = 2**69 * 3**29 * 7**13 - 1
# p = 2^59 * 3^19 * 7 - 1
p = 2*3*5 - 1
p = 2**9*3**6*5-1
Fp2.<w> = GF(p^2)
E0, iota, O0 = starting_curve(Fp2)
Quat = O0.quaternion_algebra()

def image_sum(isog_list, point):
    '''
    Returns image of point under the sum of isogenies in the list
    '''
    domain = isog_list[0].domain()
    assert point in domain
    return sum(isogeny(point) for isogeny in isog_list)

def compose_sums(isog_list1, isog_list2):
    '''
    "Composes" isogenies, in the sense of concatenating lists
    '''
    return [isog_list1, isog_list2]

depth = lambda L: isinstance(L, list) and max(map(depth, L))+1

# Depth is 0-based
def isogeny_sum_at_depth(isog_sum_comp, t):
    '''
    From a nested list of isogenies (i.e. composition), takes the (t+1)-th isogeny
    '''
    t += 1
    result = isog_sum_comp
    d = depth(isog_sum_comp)
    assert t > 0 and t <= d
    if t < d:
        for _ in range(t-2):
            result = result[1]
        return result[0]
    else:
        for _ in range(t-1):
            result = result[1]
        return result

def image_compose_sum(isog_sum_comp, point):
    '''
    Given a composition of sums of isogenies (i.e. a nested list of isogenies), returns the image of point under the composition of sums
    '''
    d = depth(isog_sum_comp)
    image = point
    for i in range(0,d-1, -1):
        image = image_sum(isogeny_sum_at_depth(isog_sum_comp, ), image)
    return image


def generate_phi(F, E, degree):
    '''
    Returns the isogeny that we want to translate. For now only rational for examples 
    '''
    prime = F.characteristic()
    if (prime + 1) % degree == 0 and degree % 2 != 0:
        P = E.random_point()
        cofactor = (prime + 1) / degree
        while True:
            P *= cofactor
            if P.order() == degree:
                break
        return E.isogeny(P), P
    else:
        print('HD representation not implemented yet.')
        return None

def kernel2D(F, phi, psi, P, Q):
    '''
    Returns a basis of the 2-dimensional kernel of Φ, where P and Q are a basis of E[av_tors]
    '''
    return [(phi(point), psi(point)) for point in [P,Q]]

def represent_in_basis(R, basis, order):
    '''
    Returns the coordinates of R in the basis
    '''
    P, Q = basis
    pq = P.weil_pairing(Q, order)
    rq = R.weil_pairing(Q, order)
    pr = P.weil_pairing(R, order)
    x = discrete_log(rq, pq, order, operation='*', algorithm='lambda')
    y = discrete_log(pr, pq, order, operation='*', algorithm='lambda')
    return x, y

def matrix_on_basis(ring, map, basis, order):
    '''
    Returns the representation of the action of an isogeny on the order-torsion as a matrix
    '''
    P, Q = basis
    mapP = map(P)
    mapQ = map(Q)
    xP, yP = represent_in_basis(mapP, basis, order)
    xQ, yQ = represent_in_basis(mapQ, basis, order)
    return Matrix(ring, [[ring(xP), ring(xQ)], [ring(yP), ring(yQ)]])

def kernel2ideal(ring, basis, mats, kernel, norm, order):

    x, y = represent_in_basis(kernel, basis, norm)

    rows = []
    row0 = [(M[0,0] * ring(x) + M[0,1] * ring(y)) for M in mats]
    row1 = [(M[1,0] * ring(x) + M[1,1] * ring(y)) for M in mats]
    A = Matrix(ring, [row0, row1])

    nullspace = A.right_kernel()
    vec = nullspace.gens()[0]

    coeffs_mod = [Integer(int(v) % norm) for v in list(vec)]
    beta_basis = order.basis()
    alpha = sum(coeffs_mod[i] * beta_basis[i] for i in range(4))
    # return alpha, coeffs_mod
    return order * alpha + order * norm

def connecting_ideal(O0, O1):
    I = O0 * O1
    I = I * ZZ(denominator(I.norm()))
    return I

# Hard-coding 2 here
def matrix_mod_l(phi, isogeny, basis1, basis2, case = 0):
    cols = []
    if case ==0:
        for P in basis2:
            R = phi(isogeny(P))       
            x, y = represent_in_basis(R, basis1, 2)
            cols.append(vector(GF(2), [x,y]))
    else:
        for P in basis1:
            R = isogeny(phi.dual()(P))       
            x, y = represent_in_basis(R, basis2, 2)
            cols.append(vector(GF(2), [x,y]))
    return matrix(GF(2), 2, 2, cols)

# Hard-coding 2 here
# Case 0 is the first described in KLPT2 paper, Case 1 is the symmetric
def matrix_action_torsion(isogeny, domain_curve, domain_order, intermediate_order, iota_intermediate, basis_domain, basis_codomain, case=0):
    V = GF(2)**4
    intermediate_curve = isogeny.domain()
    codomain_curve = isogeny.codomain()
    action = []
    while True:
        I = connecting_ideal(intermediate_order, domain_order)
        domain_curve_prime, delta, _ = constructive_deuring(I, intermediate_curve, iota_intermediate)
        assert domain_curve.j_invariant() == domain_curve_prime.j_invariant()
        isom = domain_curve_prime.isomorphism_to(domain_curve)
        post_delta = isom * delta
        if case==0:
            dual_delta = post_delta.dual()
            M = matrix_mod_l(isogeny, dual_delta, basis_codomain, basis_domain)
        else:
            M = matrix_mod_l(isogeny, dual_delta, basis_codomain, basis_domain, case = 1)
        # testing linear independence of matrices
        if V.linear_dependence([vector(M.list())] + [vector(matrix[0].list()) for matrix in action]) == []:
            action.append((M, dual_delta))
        if len(action) == 4:
            return action

# Hard-coding 2 here

def find_connecting_matrix(curve1, curve2, end0, end2, kernel, basis_domain, basis_codomain, action21, action12):

    proj1 = [kernel[0][0], kernel[0][1]]
    proj2 = [kernel[1][0], kernel[1][1]]
    
    # Kernel points on E2 in coordinates
    coord_proj1_1 = represent_in_basis(proj1[0], basis_domain, 2)
    coord_proj1_2 = represent_in_basis(proj1[1], basis_domain, 2)
    
    # Kernel points on E1 in coordinates
    coord_proj2_1 = represent_in_basis(proj2[0], basis_domain, 2)
    coord_proj2_2 = represent_in_basis(proj2[1], basis_domain, 2)

    if proj1[0].order() == 2 and proj1[1].order() == 2:
        # Full 2-torsion on E1

        target = vector(coord_proj2_1 + coord_proj2_2)
        row0 = [coord_proj1_1[0] * M[0][0,0] + coord_proj1_1[1] * M[0][0,1] for M in action12]
        row1 = [coord_proj1_1[0] * M[0][1,0] + coord_proj1_1[1] * M[0][1,1] for M in action12]
        row2 = [coord_proj1_2[0] * M[0][0,0] + coord_proj1_2[1] * M[0][0,1] for M in action12]
        row3 = [coord_proj1_2[0] * M[0][1,0] + coord_proj1_2[1] * M[0][1,1] for M in action12]
        A = Matrix(IntegerMod(2), [row0, row1, row2, row3])

        solution = A.solve_right(b)
        sigma_minus = [-coeff * isogeny[1] for coeff, isogeny in zip(solution, action12)]

        return [[curve1.scalar_multiplication(2),0], [sigma, curve2.scalar_multiplication(1)]]

    elif proj2[0].order() == 2 and proj2[1].order() == 2:
        # Full 2-torsion on E2
        
        target = vector(coord_proj1_1 + coord_proj1_2)
        row0 = [coord_proj2_1[0] * M[0][0,0] + coord_proj2_1[1] * M[0][0,1] for M in action21]
        row1 = [coord_proj2_1[0] * M[0][1,0] + coord_proj2_1[1] * M[0][1,1] for M in action21]
        row2 = [coord_proj2_2[0] * M[0][0,0] + coord_proj2_2[1] * M[0][0,1] for M in action21]
        row3 = [coord_proj2_2[0] * M[0][1,0] + coord_proj2_2[1] * M[0][1,1] for M in action21]
        A = Matrix(IntegerMod(2), [row0, row1, row2, row3])

        solution = A.solve_right(b)
        sigma = [-coeff * isogeny[1] for coeff, isogeny in zip(solution, action21)]

        return [[curve1.scalar_multiplication(1),sigma], [0, curve2.scalar_multiplication(2)]]

    else:
        # Cyclic&Cyclic case
        
        if proj2[0].order()==2:
            not_target = coord_proj1_2
            cyclic = 2
        else:
            not_target = coord_proj1_1
            cyclic = 1

        # Target outside the subgroup generated by P_1'
        target = vector(IntegerModRing(2), (0,0)) + not_target
        row0 = [coord_proj2_1[0] * M[0][0,0] + coord_proj2_1[1] * M[0][0,1] for M in action21]
        row1 = [coord_proj2_1[0] * M[0][1,0] + coord_proj2_1[1] * M[0][1,1] for M in action21]
        row2 = [coord_proj2_2[0] * M[0][0,0] + coord_proj2_2[1] * M[0][0,1] for M in action21]
        row3 = [coord_proj2_2[0] * M[0][1,0] + coord_proj2_2[1] * M[0][1,1] for M in action21]
        A = Matrix(IntegerMod(2), [row0, row1, row2, row3])

        solution = A.solve_right(b)
        alpha = [coeff * isogeny[1] for coeff, isogeny in zip(solution, action21)]

        if cyclic == 1:
            new_proj1 = [kernel[0][0], image_sum(alpha, kernel[0][1])]
        else:
            new_proj1 = [image_sum(alpha, kernel[0][0]), kernel[0][1]]
        new_proj2 = proj2


        ###################
        # To be finished...
        ###################

        return [[2, 2 * alpha], [-sigma, -sigma * alpha + 1]]


# Set parameters

phi_degree = 5
psi_degree = 3

# Generate the challenge φ: E -> E1

phi, kerphi = generate_phi(Fp2, E0, phi_degree)
E1 = phi.codomain()
P1, Q1 = E1.torsion_basis(2)

# Generate the auxiliary isogeny ψ: E -> E2

psi, kerpsi = generate_phi(Fp2, E0, psi_degree)
E2 = psi.codomain()
P2, Q2 = E2.torsion_basis(2)

# Transfer the EndRing to E2 through ψ

S, T = E0.torsion_basis(psi_degree)
pi = E0.frobenius_isogeny()
k_isogeny = iota * pi

Z3b = IntegerModRing(psi_degree)
Miota = matrix_on_basis(Z3b, iota, (S,T), psi_degree)
Mpi = matrix_on_basis(Z3b, pi, (S,T), psi_degree)
Mk = matrix_on_basis(Z3b, k_isogeny, (S,T), psi_degree)
Mij2 = (Miota + Mpi) * Z3b(2).inverse()
M1k2 = (identity_matrix(Z3b, 2) + Mk) * Z3b(2).inverse()
mats = [identity_matrix(Z3b, 2), Miota, Mij2, M1k2] 

Ipsi = kernel2ideal(Z3b, (S, T), mats, kerpsi, psi_degree, O0)
O2 = Ipsi.right_order()

E2p, delta, _ = constructive_deuring(Ipsi, E0, iota)
print(E2p.j_invariant())
print(E2.j_invariant())
assert E2p.j_invariant() == E2.j_invariant()

# Find a basis of isogenies E2 -δ-> E -φ-> Ε1 acting on the 2-torsion

action_21 = matrix_action_torsion(phi, E2, O2, O0, iota, (P2, Q2), (P1, Q1), case=0)
action_12 = matrix_action_torsion(phi, E2, O2, O0, iota, (P2, Q2), (P1, Q1), case=1)




