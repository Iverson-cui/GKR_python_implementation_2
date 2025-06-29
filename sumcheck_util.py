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
        print("out of bounds")
    #        return tuple([])
    assert i >= 0 and i <= 2**d

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
    ), "the list of coefficients of the polynomial does not have\
                        only 3 entries"
    return (g[0] + g[1] * x + g[2] * (x**2)) % p


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

    answer = 0
    chi_values = [1]
    for i in range(N):
        temp = []
        for j in range(2**i):
            temp.append((1 - r[i]) * chi_values[j] % p)
            temp.append((r[i]) * chi_values[j] % p)
        chi_values = temp

    for key in L:
        dec = 0
        for i in range(N):
            dec = dec + 2 ** (N - i - 1) * key[i]
        answer = (answer + L[key] * chi_values[dec]) % p
    return answer
