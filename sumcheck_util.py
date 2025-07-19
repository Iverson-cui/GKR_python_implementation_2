#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jun 23 21:25:47 2022

@author: raju
"""

import numpy as np
import math
import random


from timeit import default_timer as timer


def int_to_bin(i: int, d: int) -> tuple:
    """
    int_to_bin
    Inputs: i (integer) means the int we are about to convert to binary, d (integer) means the number of digits

    Outputs: tuple of the binary representation of i, with a total of d digits, if information is correctly constructed.

    5->(0,0,1,0,1) if d=5

    """

    # make sure the number can be expressed in d digits.
    if i < 0 or 2**d < i:
        print("out of bounds, i={}".format(i))
    #        return tuple([])
    assert i >= 0 and i <= 2**d, "i={} is out of bounds for d={}".format(i, d)

    # bin(5)='0b101', bin(5)[2:] = '101'
    str_bin = bin(i)[2:]  # bin = '0b...'

    # padding with leading 0s, if necessary.
    if len(str_bin) < d:
        str_bin = "0" * (d - len(str_bin)) + str_bin

    # added to correctly deal with d = 0:
    if d == 0:
        return tuple([])
    return tuple([int(i) for i in str_bin])


def build_function_from_matrix(M: np.array, n: int) -> (dict, int):
    """
    build_function_from_matrix

    INPUTS: an np array M and an integer n, such that M has dimension nxn.

    OUTPUT: function_on_hypercube (dictionary), 2 * digit (integer)

    dictionary function_on_hypercube is a dictionary that keeps the values of the function on boolean hypercube. 2*digit is the length of the dictionary keys, which is the dimension of the boolean hypercube.

    """

    assert M.shape == (n, n), "The matrix M has the wrong dimensions"

    # new_mat_dim is the padded matrix dimension, which means that we will pad
    # until the dimensions are powers of 2.

    # if n=5,new_mat_dim = 8, digits = 3
    new_mat_dim = 2 ** (math.ceil(math.log2(n)))
    digits = math.ceil(math.log2(n))
    function_on_hypercube = {}
    for i in range(new_mat_dim):
        for j in range(new_mat_dim):
            # index is the concatenation of i and j in binary,
            # in tuple form. That is, it is a tuple of length
            # 2 * new_dim. (note: the binary expansions of i and
            # j have leading 0s.)

            # concatenate the binary representations of i and j into a single tuple. Such as (1,0)+(0,1) = (1,0,0,1)
            index = int_to_bin(i, digits) + int_to_bin(j, digits)
            if i < n and j < n:
                function_on_hypercube[index] = M[i][j]
            else:
                function_on_hypercube[index] = 0
    # return function as a dictionary, and the "dimension", i.e,
    # the function is on {0,1}^{2*new_dim}, we return function as dict,
    # and the dimension of the boolean hypercube.
    return function_on_hypercube, 2 * digits


def quadratic_interpolate(values: list, p: int) -> list:
    """
    quadratic_interpolate
    INPUT:  values, p
            values is a list of three integers
            p is a prime.
    OUTPUT:
            answer (list), which is a list of length 3
            that represents the coefficients of the unique
            quadratic polynomial q such that:

                q(0)=values[0], q(1)=values[1], and q(2)=values[2]

            the elements of answer are in increasing degree order (i.e.,
            the constant coefficient is the first)

    """
    assert len(values) == 3, "the list values does not have 3 elements"

    # answer will be in terms of lowest to highest.
    A = [
        values[0] * pow(2, -1, mod=p) % p,
        -values[1] % p,
        values[2] * pow(2, -1, mod=p) % p,
    ]
    answer = [
        values[0] % p,
        (-3 * A[0] - 2 * A[1] - A[2]) % p,
        (A[0] + A[1] + A[2]) % p,
    ]
    return answer


def cubic_interpolate(values: list, p: int) -> list:
    """
    cubic_interpolate
    INPUT:  values, p
            values is a list of four integers
            p is a prime.
    OUTPUT:
            answer (list), which is a list of length 4
            that represents the coefficients of the unique
            cubic polynomial q such that:

                q(0)=values[0], q(1)=values[1], q(2)=values[2], q(3)=values[3]

            the elements of answer are in increasing degree order (i.e.,
            the constant coefficient is the first)
    Examples:
    >>> cubic_interpolate([1, 2, 3, 4], 7)
    [1, 1, 0, 0]
    >>> cubic_interpolate([0, 1, 8, 27], 97)
    [0, 0, 0, 1]
    >>> cubic_interpolate([0, 1, 4, 9], 97)
    [0, 0, 1, 0]
    >>> cubic_interpolate([1, 1, 1, 1], 7)
    [1, 0, 0, 0]
    >>> cubic_interpolate([0, 0, 0, 0], 7)
    [0, 0, 0, 0]
    >>> cubic_interpolate([1, 3, 5, 7], 11)
    [1, 2, 0, 0]

    """
    assert len(values) == 4, "the list values does not have 4 elements"

    # Using Lagrange interpolation formula for points (0,v0), (1,v1), (2,v2), (3,v3)
    # The cubic polynomial is: q(x) = sum(values[i] * L_i(x)) for i = 0,1,2,3
    # where L_i(x) are the Lagrange basis polynomials

    v0, v1, v2, v3 = values

    # Calculate coefficients directly using the Lagrange interpolation formula
    # For points at x = 0, 1, 2, 3, we can derive the closed form

    # Constant term (coefficient of x^0)
    a0 = v0 % p

    # Linear term (coefficient of x^1)
    a1 = (-11 * v0 + 18 * v1 - 9 * v2 + 2 * v3) * pow(6, -1, p) % p

    # Quadratic term (coefficient of x^2)
    a2 = (6 * v0 - 15 * v1 + 12 * v2 - 3 * v3) * pow(6, -1, p) % p

    # Cubic term (coefficient of x^3)
    a3 = (-v0 + 3 * v1 - 3 * v2 + v3) * pow(6, -1, p) % p

    answer = [a0, a1, a2, a3]
    return answer


def quadratic_evaluation(g: list, x: int, p: int) -> int:
    """
    quadratic_evaluation
    INPUT: g (list), x, p
            where g are the coefficients of a quadratic polynomial
            x is an integer, and p is a prime
    OUTPUT: g(x) mod p
    """
    assert (
        len(g) == 3
    ), "the list of coefficients of the polynomial does not have only 3 entries"
    return (g[0] + g[1] * x + g[2] * (x**2)) % p


def cubic_evaluation(g: list, x: int, p: int) -> int:
    """
    cubic_evaluation
    INPUT: g (list), x, p
            where g are the coefficients of a cubic polynomial
            x is an integer, and p is a prime
    OUTPUT: g(x) mod p
    """
    assert (
        len(g) == 4
    ), "the list of coefficients of the polynomial does not have only 4 entries"
    return (g[0] + g[1] * x + g[2] * (x**2) + g[3] * (x**3)) % p


def Lagrange_basis(xcoords: list, n: int, p: int) -> list:
    """
    More about Lagrange basis polynomials can be found in the p18 of the book.

    given a length n+1 list of x-coordinates this function returns a list, containing n+1 Lagrange basis polynomials. These n+1 polynomials can be combined with n+1 values to produce a polynomial of degree n that passes through these n+1 points.
    """
    assert (
        len(xcoords) <= n + 1
    ), "n is too big to be uniquely determined by a list of this length"
    LB = []
    for i in range(n + 1):
        current_polynomial = [1]
        current_denom = 1
        for j in range(n + 1):
            if j != i:
                #                print(j)
                #                print(len(xcoords))
                current_polynomial = np.polymul(current_polynomial, [1, -xcoords[j]])
                current_denom = (
                    current_denom * pow(xcoords[i] - xcoords[j], -1, p)
                ) % p
        current_polynomial = (current_polynomial * current_denom) % p
        LB.append(current_polynomial)
    return LB


def polynomial_interpolation(values: list, n: int, p: int):
    """polynomial_interpolation takes in a list of (xcoord,ycoord), a degree
    and a prime number p, and spits out the np.polynomial that interpolates

    values: a list of pairs containing x-coordinates and y-coordinates

    return a list of coefficients of the polynomial that passes through value pairs of points
    """

    xcoords = [pair[0] for pair in values]
    ycoords = [pair[1] for pair in values]
    LB = Lagrange_basis(xcoords, n, p)
    answer = [0]
    for i, basis_poly in enumerate(LB):
        weighted_poly = (basis_poly * ycoords[i]) % p
        # np.polyadd returns numpy array
        answer = np.polyadd(answer, weighted_poly) % p
    return answer


def polynomial_evaluation(poly, x, p):
    """
    Return the value of the polynomial evaluated at x mod p

    Here, poly is a list of coefficients of the polynomial like what the above function returns. x is a single evaluation point.

    This function may perform the same operation as the `cubic_evaluation` or `quadratic_evaluation` functions, but it is more general and can handle polynomials of any degree.
    """
    reverse_poly = poly[::-1]
    answer = 0
    for i in range(len(poly)):
        answer = (answer + pow(x, i, p) * reverse_poly[i]) % p
    return answer


def string_of_polynomial(poly):
    """
    Return a string representation of the polynomial.
    """
    deg_of_poly = len(poly) - 1
    string_of_poly = "+".join(
        ["{}*x^{}".format(poly[k], deg_of_poly - k) for k in range(deg_of_poly + 1)]
    )
    return string_of_poly


def chi(a: tuple, z: tuple, N: int, p: int):
    """chi
    INPUTS: a (boolean tuple), z (tuple of integers), N, p (prime)
    this returns the value of the MLE of the ``delta'' function L[a]* \delta_a at z. In other words, this is simply: \prod_{i=1..N} (a[i]*z[i] + (1-a[i])*(1-z[i])) mod p

    More can be found on p29 of the book. Here, a is w in the book and z is x in the book.

    The function takes as input a set of x and w, and returns a set of MLE basis polynomials.

    N here is the input length, i.e., the number of variables in the boolean hypercube.
    """
    assert (
        len(a) == N and len(z) == N
    ), "a and z must both be of length N. Now a is of length {} and z is of length {}, while N={}".format(
        len(a), len(z), N
    )

    answer = 1
    for i in range(N):
        next_term = a[i] * z[i] + (1 - a[i]) * (1 - z[i]) % p
        answer = answer * next_term % p
    return answer


def eval_MLE(L: dict, r: tuple, N: int, p: int) -> int:
    """
    eval_MLE
    INTPUTS: L (dict), r (tuple or list), N (int), p (int)
            Here, L is the dictionary that has keys in (0,1)^N

            r will be the vector in F_p^n that we are evaluating our multi-linear extension on

            N is the dimension of the boolean hypercube

            p is the prime number, with respect to which we work

    OUTPUTS: answer which is \tilde{L}(r), i.e., the value of the (unique) MLE on input r.

    NOTE: this algorithm may be found in Section 3.5 of Thaler's book.
    """
    answer = 0
    for w in L:
        answer = (answer + L[w] * chi(w, r, N, p)) % p
    return answer


def DP_eval_MLE(L: dict, r: tuple, N: int, p: int) -> int:
    """
    DP_eval_MLE
    INTPUTS: L (dict), r (tuple or list), N (int), p (int)
            Here, L is the dictionary that has keys in (0,1)^N
            r will be the vector in F_p^n that we are evaluating
            our multi-linear extension on
            N is the dimension of the boolean hypercube
            p is the prime number, with respect to which we work
    OUTPUTS: answer
            which is \tilde{L}(r), i.e., the value of the (unique)
            MLE on input r.

    NOTE: this algorithm may be found in Section 3.5 of Thaler's book. It differs
    from the above in that it uses dynamic programming. It saves a log factor in
    time but uses linear space.

    This function takes in the same arguments as eval_MLE, but uses a dynamic programming approach to compute the MLE.
    """

    assert (
        len(L) == 2**N
    ), "Number of elements in L must be 2^N. Now L is of length {}, but N is {}".format(
        len(L), N
    )
    assert (
        len(r) == N
    ), "r must be of length N. Now r is of length {}, but N is {}".format(len(r), N)
    answer = 0
    chi_values = [1]
    for i in range(N):
        temp = []
        for j in range(2**i):
            temp.append((1 - r[i]) * chi_values[j] % p)
            temp.append((r[i]) * chi_values[j] % p)
        chi_values = temp

    # Now chi_values is a list of length 2^N. It contains all of the values of chi evaluated at different x, starting from x=[000...0] to x=[111...1].
    # You can check p32 of the book, in which there is a graph.
    for key in L:
        # dec is the decimal representation of the key, which is a binary tuple. So if key in L is (1,0,1) then dec=5.
        # After dec is evaluated, answer is updated by multiplying the value of chi and the value of dict.
        dec = 0
        for i in range(N):
            dec = dec + 2 ** (N - i - 1) * key[i]
        answer = (answer + L[key] * chi_values[dec]) % p
    return answer


def tuple_to_int(binary_tuple):
    """
    Input is a binary tuple like (1, 0, 1, 0) and output is the integer representation of that tuple.

    This function has passed tests.
    """
    result = 0
    for i, bit in enumerate(binary_tuple):
        result += bit * (2 ** (len(binary_tuple) - 1 - i))
    return result


def Cormode_eval_W(
    W_binary: dict,
    input_so_far: tuple,
    step: int,
    num_var: int,
    prime: int,
):
    """
    This function does the same thing as eval_MLE, but it's the special version used in sumcheck situations. This function is based on Cormode's method.

    If we want to use this function, we assume the W_i+1 we are about to evaluate has part of their variables binary and the rest in finite field, since in sumcheck, not all W_i+1 are in this case. Other cases including full binary and full finite field are handled in the sum_fi function.

    INPUTS: W_binary keeps the value of W_i+1 in binary input and is of length 2^N. It's a dictionary that has tuples as its keys like (1,0,0,1). step is the index of variable being fixed, num_var is the number of variables of W_binary(Basically = k[i+1]). prime is the prime number of the circuit. Input is the first s variables in this step.

    OUTPUT: a list of length 2^{k[i+1]-s} that contains the evaluations of MLE W_i+1.

    There are in total k[i+1] variables in W_i+1, the first s variables are finite field elements and the rest are binary.
    """
    assert len(W_binary) == 2**num_var, "W_binary must be of length 2^N"
    assert (
        len(input_so_far) == step
    ), "input must be of length s, you provide input with length {} and step s is {}".format(
        len(input_so_far), step
    )
    # s-1 variables are random challenge elements, s-th variable is 0/1/2
    # current_random_elements holds the first s-1 random elements.
    # current_random_elements = self.get_layer_i_sumcheck_random_elements(layer)

    # 2 ** (num_var - step) is the number of variables left to be fixed, which is also the number of binary variables.
    result = [0] * (2 ** (num_var - step))
    # label is the gate label like (1,0,0,1), value is the value of W_i+1 at that label.
    for label, value in W_binary.items():
        class_index = tuple_to_int(label[step:])
        # chi want 2 tuples. First is the tuple of the gate label, which is in variable label. second is the tuple consisting of s bit input and num_var - s bit gate label.
        # Or we can think of it like this: first is the former s bits of the gate label, second is the input.
        chi_value = chi(label[:step], input_so_far, step, prime)
        # update the corresponding class of the result.
        result[class_index] = (result[class_index] + chi_value * value) % prime
    assert len(result) == 2 ** (num_var - step), "result must be of length 2^{k[i+1]-s}"
    return result


def list_recombination(list_of_lists: list, num_var: int, p: int) -> list:
    """
    ARGS:
    list_of_lists: a list of lists, each of which is a list of length 2^{num_var}
    num_var: the number of variables in the list.
    p: the prime number of the circuit.

    OUTPUT:
    a list containing the recombination of the input lists.

    This function takes 2^m lists each of length 2^num_var and returns a list. The returning list takes the first element of each list and append them to the new list. Then it takes the second element and so on. So the result is a cycle list of all the lists.
    In our case, this function is mainly used for tilde{W}_i+1 values.
    """
    for i, lst in enumerate(list_of_lists):
        assert isinstance(
            lst, list
        ), f"Element {i} in list_of_lists must be a list, but got {type(lst)}"
        assert (
            len(lst) == 2**num_var
        ), f"Element {i} in list_of_lists must have length 2^{num_var} (={2**num_var}), but got {len(lst)}"

    # If no lists provided, return empty list
    if not list_of_lists:
        return []

    # Initialize result list
    result = []

    # For each position (0 to 2^num_var - 1)
    for pos in range(2**num_var):
        # Take the element at position 'pos' from each list
        for lst in list_of_lists:
            result.append(lst[pos] % p)  # Apply modulo p for finite field arithmetic

    return result


def reusing_work_chi(z: tuple, num_var: int, p: int):
    """
    This function is part of DP_eval_MLE. It calculates chi function values given z in finite field. num_var is the number of variables, p is the prime number.

    This function returns a list of length 2^num_var, each corresponding to a binary assignment of input variables.

    Compared with chi function, which takes in two tuples, one as finite field elements and the other as binary, this function only takes in the finite field elements and returns a list of chi values. So the binary elements in chi is equal to the index of the returning list of this function.
    """
    chi_values = [1]
    for i in range(num_var):
        temp = []
        for j in range(2**i):
            temp.append((1 - z[i]) * chi_values[j] % p)
            temp.append((z[i]) * chi_values[j] % p)
        chi_values = temp

    assert isinstance(
        chi_values, list
    ), f"chi_values must be a list, but got {type(chi_values)}"
    assert (
        len(chi_values) == 2**num_var
    ), f"chi_values must have length 2^{num_var} (={2**num_var}), but got {len(chi_values)}"
    return chi_values


def finite_field_inverse(z, p):
    """
    Compute the multiplicative inverse of z in the finite field Z/pZ.

    Args:
        z: The finite field element (integer)
        p: The prime number defining the finite field

    Returns:
        The multiplicative inverse z^(-1) mod p

    Raises:
        ValueError: If z is 0 or if p is not prime (basic check)
    """
    # First, let's validate our inputs
    if z == 0:
        raise ValueError("Zero has no multiplicative inverse in any field")

    if p <= 1:
        raise ValueError("Prime p must be greater than 1")

    # Normalize z to be in the range [0, p-1]
    z = z % p

    # Check if z and p are coprime (necessary for inverse to exist)
    # In a prime field, this means z should not be 0 mod p
    if z == 0:
        raise ValueError("z is congruent to 0 mod p, so no inverse exists")

    # Use Fermat's Little Theorem: z^(-1) ≡ z^(p-2) (mod p)
    # Python's pow function can efficiently compute modular exponentiation
    inverse = pow(z, p - 2, p)

    return inverse


def reusing_work_update(c_array: tuple, z_j: int, r_j: int, p: int):
    """
    This function is used to update the array given round j random challenge r_j and round j input z_j. This function is based on the "Time Optimal" paper page 21.

    Assume the length of c_array is 2^k, where k is the number of variables in the circuit. The length of updated_array returned is 2^{k-1}, which is half of the length of c_array.

    This function can be used to update array, while also to calculate beta values. In that case, we replace r_j with t and get element with the specific index in the array.
    """
    z_j_inverse = finite_field_inverse(z_j, p)
    update_chi = (r_j * z_j + (1 - r_j) * (1 - z_j)) % p
    updated_array = tuple(
        c_array[len(c_array) // 2 + i] * update_chi * z_j_inverse % p
        for i in range(len(c_array) // 2)
    )
    assert (
        len(updated_array) == len(c_array) // 2
    ), f"updated_array must have length {len(c_array) // 2}, but got {len(updated_array)}"
    return updated_array


def rotate_dict_keys(original_dict, key_length, rotation_amount=1, direction="right"):
    """
    Creates a new dictionary where keys are rotated versions of the original keys.

    For each key in the new dictionary, we look up the value from the rotated
    version of that key in the original dictionary. This creates a systematic
    transformation of the data based on key rotation patterns.

    To put it simply, for the new dict, first rotate the input key then find it in the original dict.

    Parameters:
    - original_dict: The input dictionary with tuple keys
    - key_length: Length of the tuple keys (for validation)
    - rotation_amount: How many positions to rotate (default: 1)
    - direction: 'right' or 'left' rotation (default: 'right')

    Returns:
    - A new dictionary with the same keys but values retrieved from rotated positions

    Examples:

    Let's use a complete set of 2-tuples to avoid missing keys:
    >>> small_dict = {(0,0): 100, (0,1): 200, (1,0): 300, (1,1): 400}
    >>> result = rotate_dict_keys(small_dict, 2, 1, 'right')
    >>> sorted(result.items())  # Right rotation: (a,b) -> value_from_(b,a)
    [((0, 0), 100), ((0, 1), 300), ((1, 0), 200), ((1, 1), 400)]

    Understanding the transformation step by step:
    >>> # Key (0,1) in new dict gets value from key (1,0) in original
    >>> result[(0,1)] == small_dict[(1,0)]
    True
    >>> # Key (1,0) in new dict gets value from key (0,1) in original
    >>> result[(1,0)] == small_dict[(0,1)]
    True

    Left rotation works in the opposite direction:
    >>> left_result = rotate_dict_keys(small_dict, 2, 1, 'left')
    >>> left_result[(0,1)]  # Left rotation: (a,b) -> value_from_(b,a)
    300
    >>> left_result[(1,0)]  # Gets value from (0,1)
    200

    Testing with 3-tuples and different rotation amounts:
    >>> dict_3d = {(0,0,0): 1, (0,0,1): 2, (0,1,0): 3, (1,0,0): 4}
    >>> # Right rotation by 1: (a,b,c) -> value_from_(c,a,b)
    >>> r1 = rotate_dict_keys(dict_3d, 3, 1, 'right')
    >>> r1[(0,0,1)]  # Gets value from (1,0,0)
    4
    >>> r1[(1,0,0)]  # Gets value from (0,1,0)
    3

    Right rotation by 2: (a,b,c) -> value_from_(b,c,a)
    >>> r2 = rotate_dict_keys(dict_3d, 3, 2, 'right')
    >>> r2[(0,0,1)]  # Gets value from (0,1,0)
    3
    >>> r2[(0,1,0)]  # Gets value from (1,0,0)
    4

    Rotation amount larger than tuple length (wraps around):
    >>> # Rotation by 4 is same as rotation by 1 for 3-tuples (4 % 3 = 1)
    >>> r4 = rotate_dict_keys(dict_3d, 3, 4, 'right')
    >>> r4[(0,0,1)] == r1[(0,0,1)]  # Should be same as rotation by 1
    True

    Error case - wrong key length:
    >>> bad_dict = {(0,0): 100, (0,0,0): 200}  # Mixed lengths
    >>> rotate_dict_keys(bad_dict, 2, 1, 'right')
    Traceback (most recent call last):
    ...
    ValueError: Key (0, 0, 0) has length 3, expected 2

    Error case - invalid direction:
    >>> rotate_dict_keys(small_dict, 2, 1, 'sideways')
    Traceback (most recent call last):
    ...
    ValueError: Direction must be 'right' or 'left'

    Edge case - rotation amount of 0 (identity transformation):
    >>> identity = rotate_dict_keys(small_dict, 2, 0, 'right')
    >>> identity == small_dict
    True

    Demonstrating the cyclic nature - full rotation returns to original:
    >>> full_rotation = rotate_dict_keys(small_dict, 2, 2, 'right')  # 2 steps for 2-tuples
    >>> full_rotation == small_dict
    True
    """

    def rotate_tuple(t, amount, direction):
        """Helper function to rotate a tuple by given amount and direction."""
        n = len(t)
        if direction == "right":
            # Right rotation: last elements move to front
            # Amount 1: (a,b,c,d) -> (d,a,b,c)
            effective_rotation = amount % n
            if effective_rotation == 0:
                return t
            return t[-effective_rotation:] + t[:-effective_rotation]
        elif direction == "left":
            # Left rotation: first elements move to back
            # Amount 1: (a,b,c,d) -> (b,c,d,a)
            effective_rotation = amount % n
            if effective_rotation == 0:
                return t
            return t[effective_rotation:] + t[:effective_rotation]
        else:
            raise ValueError("Direction must be 'right' or 'left'")

    # Validate that all keys have the expected length
    for key in original_dict:
        if len(key) != key_length:
            raise ValueError(f"Key {key} has length {len(key)}, expected {key_length}")

    # Create the new dictionary
    new_dict = {}
    for key in original_dict:
        # For new key, find where its value should come from in original dict
        source_key = rotate_tuple(key, rotation_amount, direction)

        # Check if the source key exists in original dictionary
        if source_key not in original_dict:
            raise KeyError(f"Rotated key {source_key} not found in original dictionary")

        new_dict[key] = original_dict[source_key]

    return new_dict


def partition_swap_dict_keys(original_dict, key_length, split_position):
    """
    Creates a new dictionary where keys are rearranged by splitting and swapping parts.

    This function takes each key, splits it at the specified position, and swaps
    the two parts. For example, (a1, a2, b1, b2, b3) with split_position=2
    becomes (b1, b2, b3, a1, a2).

    Think of it as having two groups of elements in each key, and we want to
    put the second group first and the first group second, while maintaining
    the order within each group.

    Parameters:
    - original_dict: Dictionary with tuple keys to transform
    - key_length: Expected length of all tuple keys (for validation)
    - split_position: Where to split each key (0-indexed, exclusive of split point)
                     For example, split_position=2 means first 2 elements vs remaining

    Returns:
    - New dictionary where each key is the partition-swapped version of original keys

    Examples:

    Basic example with 5-element tuples, split at position 2:
    >>> original = {(0, 1, 2, 3, 4): 100, (1, 0, 3, 2, 4): 200}
    >>> result = partition_swap_dict_keys(original, 5, 2)
    >>> # Key (0,1,2,3,4) should get value from key (2,3,4,0,1)
    >>> # But (2,3,4,0,1) must exist in original for this to work
    >>> # Let's create a complete example that works:

    Working example with 4-element tuples:
    >>> test_dict = {
    ...     (0, 1, 2, 3): 10,
    ...     (2, 3, 0, 1): 20,
    ...     (1, 0, 3, 2): 30,
    ...     (3, 2, 1, 0): 40
    ... }
    >>> result = partition_swap_dict_keys(test_dict, 4, 2)
    >>> result[(0, 1, 2, 3)]  # Gets value from (2, 3, 0, 1)
    20
    >>> result[(2, 3, 0, 1)]  # Gets value from (0, 1, 2, 3)
    10

    Understanding the transformation step by step:
    >>> # Original key (0,1,2,3) splits into (0,1) and (2,3)
    >>> # Swapped becomes (2,3,0,1) - this is our lookup key
    >>> original_key = (0, 1, 2, 3)
    >>> first_part = original_key[:2]   # (0, 1)
    >>> second_part = original_key[2:]  # (2, 3)
    >>> lookup_key = second_part + first_part  # (2, 3, 0, 1)
    >>> result[original_key] == test_dict[lookup_key]
    True

    Different split positions create different transformations:
    >>> # Split at position 1: first 1 element vs remaining 3
    >>> result_split1 = partition_swap_dict_keys(test_dict, 4, 1)
    >>> # Key (0,1,2,3) becomes lookup key (1,2,3,0)
    >>> # We need to check if (1,2,3,0) exists in our test_dict
    >>> # It doesn't, so let's make a simpler example:

    Simple 3-element example:
    >>> simple = {(0, 1, 2): 100, (1, 2, 0): 200, (2, 0, 1): 300}
    >>> result3 = partition_swap_dict_keys(simple, 3, 1)
    >>> result3[(0, 1, 2)]  # Split: (0) and (1,2) -> lookup (1,2,0)
    200
    >>> result3[(1, 2, 0)]  # Split: (1) and (2,0) -> lookup (2,0,1)
    300

    Edge case - split at position 0 (everything goes to second part):
    >>> edge_result = partition_swap_dict_keys(simple, 3, 0)
    >>> edge_result[(0, 1, 2)]  # Split: () and (0,1,2) -> lookup (0,1,2)
    100
    >>> # This is identity transformation when split_position=0

    Edge case - split at end (everything goes to first part):
    >>> end_result = partition_swap_dict_keys(simple, 3, 3)
    >>> end_result[(0, 1, 2)]  # Split: (0,1,2) and () -> lookup (0,1,2)
    100
    >>> # This is also identity transformation when split_position=key_length

    Error cases:
    >>> partition_swap_dict_keys({(0, 1): 10}, 3, 1)  # Wrong key length
    Traceback (most recent call last):
    ...
    ValueError: Key (0, 1) has length 2, expected 3

    >>> partition_swap_dict_keys(simple, 3, 5)  # Split position out of range
    Traceback (most recent call last):
    ...
    ValueError: Split position 5 is out of range for key length 3

    >>> partition_swap_dict_keys(simple, 3, -1)  # Negative split position
    Traceback (most recent call last):
    ...
    ValueError: Split position -1 is out of range for key length 3
    """

    def partition_and_swap(key_tuple, split_pos):
        """
        Helper function to split a tuple and swap the parts.

        Args:
            key_tuple: The tuple to split and swap
            split_pos: Position where to split (first split_pos elements vs rest)

        Returns:
            New tuple with parts swapped
        """
        # Split the tuple into two parts
        first_part = key_tuple[:split_pos]  # Elements 0 to split_pos-1
        second_part = key_tuple[split_pos:]  # Elements split_pos to end

        # Swap: put second part first, then first part
        return second_part + first_part

    # Validation: Check split position is valid
    if split_position < 0 or split_position > key_length:
        raise ValueError(
            f"Split position {split_position} is out of range for key length {key_length}"
        )

    # Validation: Check all keys have expected length
    for key in original_dict:
        if len(key) != key_length:
            raise ValueError(f"Key {key} has length {len(key)}, expected {key_length}")

    # Create the transformed dictionary
    new_dict = {}
    for key in original_dict:
        # Transform the key to find where its value should come from
        lookup_key = partition_and_swap(key, split_position)

        # Verify the lookup key exists in original dictionary
        if lookup_key not in original_dict:
            raise KeyError(
                f"Transformed key {lookup_key} not found in original dictionary"
            )

        # Store the value from the transformed key location
        new_dict[key] = original_dict[lookup_key]

    return new_dict
