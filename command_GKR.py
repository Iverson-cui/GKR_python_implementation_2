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

DEBUG_INFO = False
TIME_INFO = True


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

        if i == d - 1:
            for s in range(copy_k[i] + 2 * (k[i + 1] - num_copy[i]) + num_copy[i] + 1):
                if s == copy_k[i] + 2 * (k[i + 1] - num_copy[i]):
                    if TIME_INFO:
                        last_layer_a1_b1_c1_end_time = time.time()
                        print(
                            "\033[32mTime for layer {} a1 to c1 gate loop: {}\033[0m".format(
                                i, last_layer_a1_b1_c1_end_time - gate_loop_start_time
                            )
                        )
                prover_msg = prover_inst.partial_sumcheck_mult_layer(s, r)
                if DEBUG_INFO:
                    string_of_prover_msg = "+".join(
                        ["{}*x^{}".format(prover_msg[l], l) for l in [2, 1, 0]]
                    )
                    print(
                        "at layer {} step {}, the polynomial the prover sends is {}".format(
                            i, s, string_of_prover_msg
                        )
                    )
                r = verifier_inst.partial_sumcheck_check_mult_layer(i, s, prover_msg)
                if DEBUG_INFO:
                    if s != 0:
                        print(
                            "at layer {} step {}, verifier's randomness is {}".format(
                                i, s, r
                            )
                        )
        else:
            for s in range(2 * (k[i + 1] - num_copy[i]) + 1):
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
                "\033[32mTime for layer {} gate loop: {}\033[0m".format(
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
            print(
                "\033[34mTime for layer {}: {}\033[0m".format(
                    i, loop_end_time - loop_start_time
                )
            )
    if TIME_INFO:
        final_start_time = time.time()
    verifier_inst.final_verifier_check()
    if TIME_INFO:
        final_end_time = time.time()
        print(
            "Time for final verification: {}".format(final_end_time - final_start_time)
        )
    print("=" * 60)
    print("🎉 SUCCESS! GKR PROTOCOL EXECUTION COMPLETED! 🎉")
    print("=" * 60)
    print("🚀 Circuit computation verified successfully!")
    print("🔥 All layers processed without errors!")
    print("=" * 60)


# C = [circuit.createCircuit("circuitdata-{}.csv".format(i), 10007) for i in range(1, 5)]
# Deep_C = circuit.createCircuit("deep_circuit-1.csv", 10007)
test_circuit = circuit.createCircuit(data_dir, [2, 3, 4, 5, 6], 10007)
execution_time = timeit.timeit(lambda: execute(test_circuit), number=1)
print(
    "\033[33mExecution time for test_circuit: {}\033[0m seconds".format(
        execution_time / 1
    )
)
