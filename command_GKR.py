#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jul 18 21:38:43 2022

@author: raju
"""


# import numpy as np
# import math
# import random
import timeit
import time

# import copy
# import matplotlib.pyplot as plt
# import csv

import sumcheck_util as SU
import circuit
import prover_GKR as P_GKR
import verifier_GKR as V_GKR

TIME_INFO = True
DEBUG_INFO = False

import os


current_dir = os.path.dirname(os.path.abspath(__file__))
data_dir = os.path.join(current_dir, "test_circuit/1_3dconv.csv")


def execute(C):
    """execute GKR for a circuit C"""

    k = C.get_k()
    d = C.get_depth()
    # initialize prover and verifier
    # First step: Prover and Verifier agree on a circuit C. In this circuit, only gate type and wiring predicate is set. The value of the gates is not calculated. Only prover needs to do this calculation.
    prover_inst = P_GKR.Prover(C)
    verifier_inst = V_GKR.Verifier(C)
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

    # iterate over the layers(Every iteration is a round of GKR)
    for i in range(d):
        # r is initialized to 0 because the first sumcheck needs no randomness.
        r = 0
        # iterate over the gates(Every iteration is a round of sumcheck)
        if TIME_INFO:
            gate_start_time = time.time()
        for s in range(2 * k[i + 1] + 1):
            # s spans from 0 to 2*k[i+1].
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
        # end_of_sumcheck_poly is what the prover claims \tilde{W}_i restricted to the line is.
        end_of_sumcheck_poly = prover_inst.send_Wi_on_line(i, r)
        if DEBUG_INFO:

            print(
                "The univariate polynomial that the prover sends at the end of step {} on the line is: {}".format(
                    i, SU.string_of_polynomial(end_of_sumcheck_poly)
                )
            )
        if TIME_INFO:
            reduce_start_time = time.time()
            gate_end_time = time.time()
            print(
                "Time taken for layer {}: {:.4f} seconds".format(
                    i, gate_end_time - gate_start_time
                )
            )

        new_random_vector = verifier_inst.reduce_two_to_one_without_verification(
            i, end_of_sumcheck_poly
        )
        if TIME_INFO:
            reduce_end_time = time.time()
            print(
                "Time taken to reduce two eval_MLEs to one: {:.4f} seconds".format(
                    reduce_end_time - reduce_start_time
                )
            )
        prover_inst.receive_random_vector(i + 1, new_random_vector)
    verifier_inst.final_verifier_check()
    print("we win!!!")


# C = [circuit.createCircuit("circuitdata-{}.csv".format(i), 10007) for i in range(1, 5)]
# Deep_C = circuit.createCircuit("deep_circuit-1.csv", 10007)
test_circuit = circuit.createCircuit(data_dir, 10007)
execution_time = timeit.timeit(lambda: execute(test_circuit), number=3)
print("Execution time for test_circuit: ", execution_time / 3, "seconds")
