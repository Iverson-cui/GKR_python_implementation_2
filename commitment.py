from py_ecc.bn128 import multiply, add, FQ
from py_ecc.bn128 import curve_order as prime
import random


def random_field_element():
    """
    Returns a random field element with field order p.
    """
    return random.randint(0, prime)


# these EC points have unknown discrete logs:
# FQ means finite field element. In this case, FQ(x) means finite field version of int value x. Operations between two FQ values are also done in finite field.
G = (
    FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759),
    FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138),
)

B = (
    FQ(12848606535045587128788889317230751518392478691112375569775390095112330602489),
    FQ(18818936887558347291494629972517132071247847502517774285883500818572856935411),
)

# scalar multiplication example: multiply(G, 42)
# EC addition example: add(multiply(G, 42), multiply(G, 100))

# remember to do all arithmetic modulo p


def commit(f, gamma, G, B):
    C = add(multiply(G, f), multiply(B, gamma))  # f_0 * G + gamma_0 * B
    return C


def commit_3_degree_poly(f_0, f_1, f_2, gamma_0, gamma_1, gamma_2, G, B):
    """
    # Create a Pedersen commitment for each coefficient
    # Each commitment has the form: coefficient * G + blinding_factor * B
    # This hides the coefficient while still allowing us to prove things about it
    Returns the Pedersen commitments for three polynomial coefficients f_0, f_1, f_2.

    INPUTS:
    - f_0, f_1, f_2: Coefficients of the polynomial f(x) = f_0 + f_1*x + f_2*x^2. They are all ints.
    - gamma_0, gamma_1, gamma_2: Blinding factors for each coefficient. They are also ints.
    - G: Generator point for the elliptic curve.
    - B: Another point on the elliptic curve used for blinding.

    OUTPUTS:
    - C0, C1, C2: The Pedersen commitments for f_0, f_1, f_2 respectively.
    Each C is a tuple representing an elliptic curve point (x, y).
    """

    C0 = commit(f_0, gamma_0, G, B)  # f_0 * G + gamma_0 * B
    C1 = commit(f_1, gamma_1, G, B)  # f_1 * G + gamma_1 * B
    C2 = commit(f_2, gamma_2, G, B)  # f_2 * G + gamma_2 * B

    return (C0, C1, C2)


def commit_4_degree_poly(f_0, f_1, f_2, f_3, gamma_0, gamma_1, gamma_2, gamma_3, G, B):
    """
    # Create a Pedersen commitment for each coefficient
    # Each commitment has the form: coefficient * G + blinding_factor * B
    # This hides the coefficient while still allowing us to prove things about it
    Returns the Pedersen commitments for three polynomial coefficients f_0, f_1, f_2.

    Here, the degree 4 means there are 4 coefficients, not really of degree 4. It actually has DEGREE OF 3.

    INPUTS:
    - f_0, f_1, f_2: Coefficients of the polynomial f(x) = f_0 + f_1*x + f_2*x^2. They are all ints.
    - gamma_0, gamma_1, gamma_2: Blinding factors for each coefficient. They are also ints.
    - G: Generator point for the elliptic curve.
    - B: Another point on the elliptic curve used for blinding.

    OUTPUTS:
    - C0, C1, C2: The Pedersen commitments for f_0, f_1, f_2 respectively.
    Each C is a tuple representing an elliptic curve point (x, y).
    """

    C0 = commit(f_0, gamma_0, G, B)  # f_0 * G + gamma_0 * B
    C1 = commit(f_1, gamma_1, G, B)  # f_1 * G + gamma_1 * B
    C2 = commit(f_2, gamma_2, G, B)  # f_2 * G + gamma_2 * B
    C3 = commit(f_3, gamma_3, G, B)  # f_3 * G + gamma_3 * B

    return (C0, C1, C2, C3)


def commit_n_degree_poly(coefficients, gammas, G, B):
    """
    Create Pedersen commitments for polynomial coefficients of any degree.

    INPUTS:
    - coefficients: List of polynomial coefficients [f_0, f_1, ..., f_n]
    - gammas: List of blinding factors [gamma_0, gamma_1, ..., gamma_n]
    - G: Generator point for the elliptic curve
    - B: Another point on the elliptic curve used for blinding

    OUTPUTS:
    - Tuple of Pedersen commitments (C0, C1, ..., Cn)
    """
    if len(coefficients) != len(gammas):
        raise ValueError("Coefficients and gammas lists must have the same length")

    commitments = []
    for i in range(len(coefficients)):
        C_i = commit(coefficients[i], gammas[i], G, B)
        commitments.append(C_i)

    return tuple(commitments)


def evaluate(f_0, f_1, f_2, u):
    """
    This function returns the evaluation of the polynomial f at point u.
    """
    return (f_0 + f_1 * u + f_2 * u**2) % prime


def prove(gamma_0, gamma_1, gamma_2, u):
    """
    The proof is simply the blinding polynomial evaluated at u
    This gives us γ(u) = gamma_0 + gamma_1*u + gamma_2*u^2
    We need this to "open" our commitment later in verification

    This function returns the pi, proof that the prover gives to the verifier to help him open the commitment.
    """

    pi = (gamma_0 + gamma_1 * u + gamma_2 * u**2) % prime
    return pi


def eval_commit_3_degree_poly(C0, C1, C2, u, p):
    """
    This function evaluates the commitment value of a commitment poly evaluated at u.

    INPUTS:
    - C0, C1, C2: The Pedersen commitments for f_0, f_1, f_2 respectively.
    - u: The point at which the polynomial is evaluated. It is an int.

    OUTPUTS:
    - C_u: The commitment value of the polynomial evaluated at u.
    """
    u_squared = (u * u) % p

    # C1 * u
    C1_times_u = multiply(C1, u)
    # C2 * u^2
    C2_times_u_squared = multiply(C2, u_squared)

    # C(u) = C0 + u*C1 + u^2*C2
    C_u = add(add(C0, C1_times_u), C2_times_u_squared)

    return C_u


def eval_commit_4_degree_poly(C0, C1, C2, C3, u):
    """
    This function evaluates the commitment value of a commitment poly evaluated at u.

    INPUTS:
    - C0, C1, C2, C3: The Pedersen commitments for f_0, f_1, f_2, f_3 respectively.
    - u: The point at which the polynomial is evaluated. It is an int.

    OUTPUTS:
    - C_u: The commitment value of the polynomial evaluated at u.
    """
    u_squared = (u * u) % prime
    u_cubed = (u * u_squared) % prime

    # C1 * u
    C1_times_u = multiply(C1, u)
    # C2 * u^2
    C2_times_u_squared = multiply(C2, u_squared)
    # C3 * u^3
    C3_times_u_cubed = multiply(C3, u_cubed)
    # C(u) = C0 + u*C1 + u^2*C2 + u^3*C3
    C_u = add(add(add(C0, C1_times_u), C2_times_u_squared), C3_times_u_cubed)

    return C_u


def eval_commit_n_degree_poly(commitments, u):
    """
    This function evaluates the commitment value of a commitment polynomial evaluated at u.

    INPUTS:
    - commitments: List or tuple of Pedersen commitments [C0, C1, C2, ..., Cn]
    - u: The point at which the polynomial is evaluated. It is an int.

    OUTPUTS:
    - C_u: The commitment value of the polynomial evaluated at u.
    """
    if len(commitments) == 0:
        raise ValueError("Commitments list cannot be empty")

    # Start with the constant term C0
    C_u = commitments[0]

    # Compute powers of u and add each term
    u_power = u % int(prime)  # u^1
    for i in range(1, len(commitments)):
        # Add C_i * u^i to the result
        C_i_times_u_power = multiply(commitments[i], u_power)
        C_u = add(C_u, C_i_times_u_power)

        # Update u_power for next iteration: u^i -> u^(i+1)
        if i < len(commitments) - 1:  # Don't compute unnecessary power
            u_power = (u_power * u) % int(prime)

    return C_u


def verify(C0, C1, C2, G, B, f_u, pi, u):
    """
    # Compute the "commitment to f(u)" by linearly combining the coefficient commitments
    # This uses the fact that if f(x) = f_0 + f_1*x + f_2*x^2,
    # then f(u) = f_0 + f_1*u + f_2*u^2
    # So C(u) = C0 + C1*u + C2*u^2 should equal f_u*G + pi*B

    INPUTS:
    - C0, C1, C2: The Pedersen commitments for f_0, f_1, f_2 respectively.
    - G: Generator point for the elliptic curve.
    - B: Another point on the elliptic curve used for blinding.
    - f_u: The evaluation of the polynomial at point u, i.e., f(u). This is given by the prover.
    - pi: The proof that the prover gives to the verifier, which is γ(u)
    - u: The point at which the polynomial is evaluated.

    If this function returns True, this means that the the poly evaluated at u is f_u.
    """
    # C(u) = C0 + u*C1 + u^2*C2
    C_u = eval_commit_3_degree_poly(C0, C1, C2, u)

    # Now compute what C(u) should equal: f_u*G + pi*B
    expected = add(multiply(G, f_u), multiply(B, pi))

    # Verification succeeds if these are equal
    # Note: In practice, you'd compare the coordinates, but for simplicity:
    return C_u[0] == expected[0] and C_u[1] == expected[1]


# ## step 0: Prover and verifier agree on G and B

# ## step 1: Prover creates the commitments
# ### f(x) = f_0 + f_1x + f_2x^2
# f_0 = random_field_element()
# f_1 = random_field_element()
# f_2 = random_field_element()

# ### blinding terms
# gamma_0 = random_field_element()
# gamma_1 = random_field_element()
# gamma_2 = random_field_element()
# # This function is called by the prover to commit the polys.
# C0, C1, C2 = commit_3_degree_poly(f_0, f_1, f_2, gamma_0, gamma_1, gamma_2, G, B)

# ## step 2: Verifier picks u
# u = random_field_element()

# ## step 3: Prover evaluates f(u) and pi
# # These two functions are also called by the prover, to generate two values that will be passed to the verifier.
# f_u = evaluate(f_0, f_1, f_2, u)
# pi = prove(gamma_0, gamma_1, gamma_2, u)

# ## step 4: Verifier accepts or rejects
# # verify is called by the verifier to check if the commitment is valid.
# if verify(C0, C1, C2, G, B, f_u, pi, u):
#     print("accept")
# else:
#     print("reject")

# # print(G1)


# poly_original = [1, 2, 3]
# poly_commitment = commit_3_degree_poly(
#     poly_original[0], poly_original[1], poly_original[2], 0, 0, 0, G, B
# )
# after_commitment = add(
#     eval_commit_3_degree_poly(
#         poly_commitment[0], poly_commitment[1], poly_commitment[2], 1, p
#     ),
#     eval_commit_3_degree_poly(
#         poly_commitment[0], poly_commitment[1], poly_commitment[2], 0, p
#     ),
# )
# before_commitment = add(multiply(poly_commitment[0], 2), poly_commitment[1])
# real_value = commit(
#     evaluate(poly_original[0], poly_original[1], poly_original[2], 1)
#     + evaluate(poly_original[0], poly_original[1], poly_original[2], 0),
#     0,
#     G,
#     B,
# )
# assert after_commitment == real_value, "Commitment evaluation failed"


def proof_of_product_step_1(x, y, rx, ry, rz, G, B):
    """
    This function is used by the prover for the first step of creating a proof of product commitment.
    It returns the commitments and the values that will be used in the verification step.
    """
    X = commit(x, rx, G, B)
    Y = commit(y, ry, G, B)
    Z = commit(x * y, rz, G, B)

    b = [random.randint(1, prime) for _ in range(5)]
    alpha = commit(b[0], b[1], G, B)
    beta = commit(b[2], b[3], G, B)
    delta = commit(b[2], b[4], X, B)

    return (X, Y, Z, alpha, beta, delta, *b)


def proof_of_product_step_2(x, y, b: list, rx, ry, rz, c):
    """
    This function is used by the prover for the second step of creating a proof of product commitment.
    """
    z = [0] * 5
    z[0] = (b[0] + c * x) % prime
    z[1] = (b[1] + c * rx) % prime
    z[2] = (b[2] + c * y) % prime
    z[3] = (b[3] + c * ry) % prime
    z[4] = (b[4] + c * (rz - rx * y)) % prime
    return z


def proof_of_product_verification(X, Y, Z, alpha, beta, delta, z, c, G, B):
    """
    This function verifies the proof of product commitment.
    It checks if the commitments and the values match the expected values.
    This function is called by the verifier.
    """
    assert add(alpha, multiply(X, c)) == add(multiply(G, z[0]), multiply(B, z[1]))
    assert add(beta, multiply(Y, c)) == add(multiply(G, z[2]), multiply(B, z[3]))
    assert add(delta, multiply(Z, c)) == add(multiply(X, z[2]), multiply(B, z[4]))
    print("Proof of product commitment is valid!")


temp_lst = proof_of_product_step_1(3, 4, 0, 0, 0, G, B)
c = random.randint(1, prime)
z = proof_of_product_step_2(3, 4, temp_lst[6:], 0, 0, 0, c)
proof_of_product_verification(
    temp_lst[0],
    temp_lst[1],
    temp_lst[2],
    temp_lst[3],
    temp_lst[4],
    temp_lst[5],
    z,
    c,
    G,
    B,
)

# # Below are what the prover needs to prepare in step 1.
# # X, Y, Z, alpha, beta, delta are known to the verifier.
# x = 3
# y = 4
# X = commit(x, 0, G, B)
# Y = commit(y, 0, G, B)
# Z = commit(x * y, 0, G, B)
# b = [random.randint(1, prime) for _ in range(5)]
# alpha = commit(b[0], b[1], G, B)
# beta = commit(b[2], b[3], G, B)
# delta = commit(b[2], b[4], X, B)
# # Verifier returns c, random challenge.
# c = random.randint(1, prime)
# # Prover sends these 5 values of z to Verifier. These 5 values are all known to the verifier.
# z = [0] * 5
# z[0] = (b[0] + c * x) % prime
# z[1] = b[1]
# z[2] = (b[2] + c * y) % prime
# z[3] = b[3]
# z[4] = b[4]

# # Below are checks performed by the verifier.
# assert add(alpha, multiply(X, c)) == add(multiply(G, z[0]), multiply(B, z[1]))
# assert add(beta, multiply(Y, c)) == add(multiply(G, z[2]), multiply(B, z[3]))
# assert add(delta, multiply(Z, c)) == add(multiply(X, z[2]), multiply(B, z[4]))
# print("Proof of product commitment is valid!")

int_prime = int(prime)
print(int_prime)
print(type(int_prime))
