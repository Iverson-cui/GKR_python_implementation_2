from py_ecc.bn128 import G1, multiply, add, FQ
from py_ecc.bn128 import curve_order as p
import random


def random_field_element():
    """
    Returns a random field element with field order p.
    """
    return random.randint(0, p)


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


def evaluate(f_0, f_1, f_2, u):
    """
    This function returns the evaluation of the polynomial f at point u.
    """
    return (f_0 + f_1 * u + f_2 * u**2) % p


def prove(gamma_0, gamma_1, gamma_2, u):
    """
    The proof is simply the blinding polynomial evaluated at u
    This gives us γ(u) = gamma_0 + gamma_1*u + gamma_2*u^2
    We need this to "open" our commitment later in verification

    This function returns the pi, proof that the prover gives to the verifier to help him open the commitment.
    """

    pi = (gamma_0 + gamma_1 * u + gamma_2 * u**2) % p
    return pi


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

    # First, compute C(u) = C0 + u*C1 + u^2*C2
    u_squared = (u * u) % p

    # C1 * u
    C1_times_u = multiply(C1, u)
    # C2 * u^2
    C2_times_u_squared = multiply(C2, u_squared)

    # C(u) = C0 + u*C1 + u^2*C2
    C_u = add(add(C0, C1_times_u), C2_times_u_squared)

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


original_value = 5
a = commit(original_value, 0, G, B)
C0, C1, C2 = commit_3_degree_poly(2, 2, 1, 0, 0, 0, G, B)
value_commitment = evaluate(2, 2, 1, 1)
print(C0, C1, C2)
print(verify(C0, C1, C2, G, B, value_commitment, 0, 1))
