#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jul 18 21:38:43 2022

@author: raju
"""

import os

# current_dir is the folder which contains the current python file.
current_dir = os.path.dirname(os.path.abspath(__file__))
# print("current_dir:", current_dir)
data_dir = os.path.join(current_dir, "./test_circuit/parallel_test.csv")
# file_path = os.path.join(data_dir, "events_semantic.json")


# import numpy as np
# import math
# import random
import time
import timeit

# import copy
# import matplotlib.pyplot as plt
# import csv

import sumcheck_util as SU
import circuit
import prover_GKR as P_GKR
import verifier_GKR as V_GKR

DEBUG_INFO = True
TIME_INFO = False


def execute(C):
    """execute GKR for a circuit C"""
    if TIME_INFO:
        start_time = time.time()
    # This k is the size of each layer before assigning copy.
    # k is a list containing int. k[2] is the bit length of the gates in layer 2.
    # For now we assume the whole circuit conform to one assignment and the copy number is directly given.
    num_copy = C.get_num_copy()
    k = C.get_k()
    # copy_k contains the size of each layer after assigning copy.
    copy_k = C.get_copy_k()
    d = C.get_depth()
    # initialize prover and verifier
    # First step: Prover and Verifier agree on a circuit C. In this circuit, only gate type and wiring predicate is set. The value of the gates is not calculated. Only prover needs to do this calculation.
    prover_inst = P_GKR.Prover(C)
    verifier_inst = V_GKR.Verifier(C)
    if TIME_INFO:
        initialization_time = time.time()
        print("Initialization time:", initialization_time - start_time)
    # prover_output_communication is the first message the prover sends.
    # This is a dictionary of the output values, in dictionary form: {0,1}^{k[0]}->F_p
    # In this step, P tells V the claimed output of the circuit.
    prover_output_communication = prover_inst.output_layer_communication()
    # In this step, verifier accept the claimed output and returns a random challenge.
    # In more detail, Verifier runs ``output layer communication'' with input the dictionary that prover just sent. returns a random vector r_0 in F_p^{k[0]}
    random_vector_0 = verifier_inst.output_layer_communication(
        prover_output_communication
    )
    # same with the verifier output_layer_communication function, prover appends its random_vectors with what the verifier sent to him and calls append_evaluations_RV function to appends its evaluations_of_random_vectors with the value of output layer MLE evaluated at the random vector.
    prover_inst.receive_random_vector(0, random_vector_0)
    if DEBUG_INFO:
        print(
            "At layer 0, the random value provided by the verifier is", random_vector_0
        )
        print(
            "The value of the multilinear extension at ",
            random_vector_0,
            " is",
            prover_inst.get_evaluations_of_RV()[0],
        )
    if TIME_INFO:
        output_layer_time = time.time()
        print(
            "Output layer communication time:", output_layer_time - initialization_time
        )
    # iterate over the layers(Every iteration is a round of GKR)
    for i in range(d):
        if TIME_INFO:
            loop_start_time = time.time()
        # r is initialized to 0 because the first sumcheck needs no randomness.
        r = 0
        # iterate over the gates(Every iteration is a round of sumcheck)
        if TIME_INFO:
            gate_loop_start_time = time.time()
        if DEBUG_INFO:
            print(
                "At layer {}, gate_label is {} while copy label is {}, in total {}. The next layer has gate label {}".format(
                    i, copy_k[i], num_copy, k[i], copy_k[i + 1]
                )
            )

        # Now we can calculate C^(0) for every layer. z can be accessed by self.get_random_vector(i). C^(0) can be calculated by reusing_work_chi function.
        # the number of variables in layer i is num_copy. For now we assume num_copy is constant throughout the circuit.
        num_copy = prover_inst.get_num_copy()
        z_1 = prover_inst.get_random_vector(i)[num_copy:]
        assert (
            len(z_1) == copy_k[i]
        ), f"z_1 must have length copy_k[i]={copy_k[i]}, but got {len(z_1)}"
        z_2 = prover_inst.get_random_vector(i)[:num_copy]
        assert (
            len(z_2) == num_copy
        ), f"z_2 must have length num_copy={num_copy}, but got {len(z_2)}"
        prover_inst.C.append(SU.reusing_work_chi(z_2, num_copy, prover_inst.get_p()))
        assert (
            len(prover_inst.get_C()[0]) == 2**num_copy
        ), "C_0 must have length 2^num_copy, but got {}".format(
            len(prover_inst.get_C()[0])
        )
        for s in range(2 * copy_k[i + 1] + 1):
            # s spans from 0 to 2*copy_k[i+1].
            # when s=0, the prover just passes the MLE evaluated at the random vector passed by verifier. This is evident from p34 of the book. Prover needs to first send the sum of binary input of f_i.
            # i means layer number, s means step number, r means random element.
            # when s=1, fixing the first variable, there is no random element. This coincides with what the partial_sumcheck_check returns at s=0, namely, 0.
            prover_msg = prover_inst.partial_sumcheck(i, s, r)
            if DEBUG_INFO:
                string_of_prover_msg = "+".join(
                    ["{}*x^{}".format(prover_msg[l], l) for l in [2, 1, 0]]
                )
                print(
                    "at layer {} step {}, the polynomial the prover sends is {}".format(
                        i, s, string_of_prover_msg
                    )
                )
            # r is the random element used in the next round
            r = verifier_inst.partial_sumcheck_check(i, s, prover_msg)
            if DEBUG_INFO:
                if s != 0:
                    print(
                        "at layer {} step {}, verifier's randomness is {}".format(
                            i, s, r
                        )
                    )
        # mult layer, need another num-copy round of sumcheck.
        if i == d - 1:
            random_element = prover_inst.get_layer_i_sumcheck_random_elements(i)

            assert (
                len(random_element) == 2 * copy_k[i + 1]
            ), f"random_element must have length 2*copy_k[i+1]={2 * copy_k[i + 1]}, but got {len(random_element)}"
            # iteration for the last num_copy variables
            # mult value is the same across all of the num_copy sumcheck rounds.
            mult_value = prover_inst.circ.eval_MLE_mult(i, z_1 + random_element)
            # z_2_inverse_lst contains the inverse of each element in z_2.
            z_2_inverse_lst = [
                SU.finite_field_inverse(z, prover_inst.get_p()) for z in z_2
            ]
            for s in range(1, num_copy + 1):
                prover_msg = prover_inst.partial_sumcheck_mult(
                    i, s, r, mult_value, z_2[s - 2], z_2_inverse_lst[s - 2]
                )
                if DEBUG_INFO:
                    string_of_prover_msg = "+".join(
                        ["{}*x^{}".format(prover_msg[l], l) for l in [3, 2, 1, 0]]
                    )
                    print(
                        "at layer {} step {}, the polynomial the prover sends is {}".format(
                            i, s, string_of_prover_msg
                        )
                    )

                # r is the random element used in the next round
                r = verifier_inst.partial_sumcheck_check_mult(i, s, prover_msg)
                if DEBUG_INFO:
                    if s != 0:
                        print(
                            "at layer {} step {}, verifier's randomness is {}".format(
                                i, s, r
                            )
                        )

        # W_iplus1_with_line is what the prover claims \tilde{W}_i restricted to the line is.
        W_iplus1_with_line = prover_inst.send_Wi_on_line(i, r)
        if DEBUG_INFO:
            print(
                "The univariate polynomial that the prover sends at the end of step {} on the line is: {}".format(
                    i, SU.string_of_polynomial(W_iplus1_with_line)
                )
            )
        if TIME_INFO:
            gate_loop_end_time = time.time()
            print(
                "Time for layer {} gate loop: {}".format(
                    i, gate_loop_end_time - gate_loop_start_time
                )
            )

        if TIME_INFO:
            reduce_start_time = time.time()
        new_random_vector = verifier_inst.reduce_two_to_one(i, W_iplus1_with_line)
        if TIME_INFO:
            reduce_end_time = time.time()
            print(
                "Time for layer {} reduce two to one: {}".format(
                    i, reduce_end_time - reduce_start_time
                )
            )
        prover_inst.receive_random_vector(i + 1, new_random_vector)
        if TIME_INFO:
            receive_time = time.time()
            print(
                "Time for layer {} receive random vector: {}".format(
                    i, receive_time - reduce_end_time
                )
            )

        if TIME_INFO:
            loop_end_time = time.time()
            print("Time for layer {}: {}".format(i, loop_end_time - loop_start_time))
    if TIME_INFO:
        final_start_time = time.time()
    verifier_inst.final_verifier_check()
    if TIME_INFO:
        final_end_time = time.time()
        print(
            "Time for final verification: {}".format(final_end_time - final_start_time)
        )
    print("we win!!!")


# C = [circuit.createCircuit("circuitdata-{}.csv".format(i), 10007) for i in range(1, 5)]
# Deep_C = circuit.createCircuit("deep_circuit-1.csv", 10007)
test_circuit = circuit.createCircuit(data_dir, 2, 10007)
execution_time = timeit.timeit(lambda: execute(test_circuit), number=5)
print("Execution time for test_circuit: ", execution_time / 5, "seconds")
